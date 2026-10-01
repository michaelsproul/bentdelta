#!/usr/bin/env bash
# tools/bp.sh proofs/x.bp ...: writes proofs/x.bend from each source
# (tools/bpp.py), puts every def after the defs it uses (tools/bendsort.py)
# and checks it.
set -e
D=$(dirname "$0")
for f in "$@"; do
  out="${f%.bp}.bend"
  python3 "$D/bpp.py" "$f" "$out"
  python3 "$D/bendsort.py" "$out"
  bend "$out" 2>&1 | head -c "${LIMIT:-3000}"
done
