#!/usr/bin/env bash
# Round-trip and xdelta3 interoperability checks on generated inputs.
#
#   tests/interop.sh [bentdelta-binary]
#
# For each (source, target) pair: bentdelta's delta must decode with both
# bentdelta and xdelta3, and xdelta3's delta (-S none) must decode with
# bentdelta.
set -u
BD=${1:-./bentdelta}
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
n=0

gen() { # gen <name> <python expression producing (a, b)>
  python3 - "$T/$1" <<PY
import random, sys, os
import zlib; random.seed(zlib.crc32(b"$1"))
def rnd(n): return bytes(random.randrange(256) for _ in range(n))
def mut(a, k):
    a = bytearray(a)
    for _ in range(k):
        op = random.randrange(3); i = random.randrange(len(a) + 1)
        if op == 0: a[i:i] = rnd(random.randrange(1, 50))
        elif op == 1: del a[i:i + random.randrange(1, 50)]
        else: a[i:i + 1] = rnd(1)
    return bytes(a)
a, b = $2
open(sys.argv[1] + ".a", "wb").write(a)
open(sys.argv[1] + ".b", "wb").write(b)
PY
}

check() { # check <name> [nosrc]
  local f="$T/$1" src=(-s "$T/$1.a")
  [ "${2:-}" = nosrc ] && src=()
  n=$((n + 1))
  if ! "$BD" -e "${src[@]}" "$f.b" "$f.bd" 2>"$f.err"; then
    echo "FAIL $1: encode: $(cat "$f.err")"; fail=$((fail + 1)); return
  fi
  if ! "$BD" -d "${src[@]}" "$f.bd" "$f.out1" 2>"$f.err" || ! cmp -s "$f.out1" "$f.b"; then
    echo "FAIL $1: bentdelta cannot decode its own delta $(cat "$f.err")"; fail=$((fail + 1)); return
  fi
  if ! xdelta3 -f -d "${src[@]}" "$f.bd" "$f.out2" 2>"$f.err" || ! cmp -s "$f.out2" "$f.b"; then
    echo "FAIL $1: xdelta3 cannot decode bentdelta's delta $(cat "$f.err")"; fail=$((fail + 1)); return
  fi
  xdelta3 -f -e -S none "${src[@]}" "$f.b" "$f.xd" 2>/dev/null
  if ! "$BD" -d "${src[@]}" "$f.xd" "$f.out3" 2>"$f.err" || ! cmp -s "$f.out3" "$f.b"; then
    echo "FAIL $1: bentdelta cannot decode xdelta3's delta $(cat "$f.err")"; fail=$((fail + 1)); return
  fi
  printf '  ok %-14s %9d -> %8d bytes (xdelta3 %8d)\n' "$1" "$(stat -c %s "$f.b")" \
    "$(stat -c %s "$f.bd")" "$(stat -c %s "$f.xd")"
}

gen empty      '(b"", b"")'
gen emptytgt   '(rnd(1000), b"")'
gen emptysrc   '(b"", rnd(1000))'
gen tiny       '(b"a", b"ab")'
gen same       '((lambda x: (x, x))(rnd(100000)))'
gen random     '(rnd(50000), rnd(50000))'
gen edits      '((lambda x: (x, mut(x, 40)))(rnd(200000)))'
gen runs       '(b"\0" * 70000 + rnd(10) + b"x" * 5000, b"\0" * 30000 + b"x" * 9000 + rnd(100) + b"\0" * 40000)'
gen selfrep    '(b"", (rnd(1000) * 50) + rnd(3))'
gen shuffle    '((lambda x: (x, x[60000:] + x[:60000]))(rnd(150000)))'
gen bigwin     '((lambda x: (x, mut(x, 300)))(rnd(9000000)))'
gen text       '((lambda x: (x, mut(x, 100)))(open("/usr/share/dict/words","rb").read()[:3000000] if os.path.exists("/usr/share/dict/words") else rnd(3000000)))'
gen odd        '((lambda x: (x[:12345], mut(x, 7)[:23457]))(rnd(30000)))'

for c in empty emptytgt emptysrc tiny same random edits runs shuffle bigwin text odd; do check $c; done
check selfrep nosrc
check random nosrc
check edits nosrc

echo "$((n - fail))/$n passed"
[ "$fail" -eq 0 ]
