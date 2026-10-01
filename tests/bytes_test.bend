import Base
import ../bytes.bend as B

# Randomized checks of the word-level byte routines against byte-at-a-time
# references.

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

def lcg(+x: U32) -> U32:
  ((x * 1664525 : U32) + 1013904223 : U32)

# A word array of 2^d words filled from seed x.
def rand.fill(n: Nat, a: Array<U32>, +i: U32, +x: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      +y = lcg(x)
      a2 = a[i] <- y
      rand.fill(p, a2, (i + 1 : U32), y)

def rand.arr(+d: Nat, +x: U32) -> Array<U32>:
  rand.fill(Nat.pow(2n, d), [0 : U32^d], 0, x)

# Whether two arrays of 2^d words agree everywhere.
def same.k(r: (Array<U32> & Array<U32>) & Bool) -> Bool:
  (ab, ok) = r
  ok

def same(+d: Nat, a: Array<U32>, b: Array<U32>) -> Bool:
  same.k(B.B.eq.words(Nat.pow(2n, d), 0, (True{}, (a, b))))

def ref.copy(dst: Array<U32>, +d: U32, src: Array<U32>, +s: U32, +n: U32) ->
  Array<U32> & Array<U32>:
  B.B.copy.bytes(U32.to_nat(n), dst, d, s, B.B.get(src, s))

def t.copy.k(+seed: U32, r1: Array<U32> & Array<U32>, r2: Array<U32> & Array<U32>) -> Bool:
  (s1, d1) = r1
  (s2, d2) = r2
  Bool.and(same(6n, d1, d2), same(6n, s1, s2))

# One copy case: 64-word arrays, offsets and length from the seed.
def t.copy(+x: U32) -> Bool:
  +d = (x % 97 : U32)
  +s = ((x >> 8n : U32) % 97 : U32)
  +n = ((x >> 16n : U32) % 120 : U32)
  t.copy.k(x, B.B.copy(rand.arr(6n, x), d, rand.arr(6n, lcg(x)), s, n),
    ref.copy(rand.arr(6n, x), d, rand.arr(6n, lcg(x)), s, n))

def t.move(+x: U32) -> Bool:
  +s = (x % 97 : U32)
  +k = (((x >> 8n : U32) % 13 : U32) + 1 : U32)
  +n = ((x >> 16n : U32) % 100 : U32)
  same(6n, B.B.move(rand.arr(6n, x), (s + k : U32), s, n),
    B.B.move.bytes(U32.to_nat(n), (s + k : U32), s, B.B.get(rand.arr(6n, x), s)))

def t.fill(+x: U32) -> Bool:
  +d = (x % 97 : U32)
  +n = ((x >> 16n : U32) % 120 : U32)
  same(6n, B.B.fill(rand.arr(6n, x), d, (x >> 8n : U32), n),
    B.B.fill.bytes(U32.to_nat(n), rand.arr(6n, x), d, (x >> 8n : U32)))

# Adler-32, one byte at a time, reducing every byte.
def ref.adler.go(n: Nat, +a: U32, +b: U32, +i: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      ((b << 16n : U32) .|. a : U32)
    case 1n+p:
      (s, +x) = r
      +a2 = ((a + x : U32) % 65521 : U32)
      +i2 = (i + 1 : U32)
      ref.adler.go(p, a2, ((b + a2 : U32) % 65521 : U32), i2, B.B.get(s, i2))

def t.adler.k(+want: U32, r: Array<U32> & U32) -> Bool:
  (s, +got) = r
  U32.is_eq(want, got)

def t.adler(+x: U32) -> Bool:
  +i = (x % 300 : U32)
  +n = ((x >> 12n : U32) % 15000 : U32)
  t.adler.k(ref.adler.go(U32.to_nat(n), 1, 0, i, B.B.get(rand.arr(13n, x), i)),
    B.B.adler32(rand.arr(13n, x), i, n))

def t.var.k2(+v: U32, +n: U32, w: B.VR) -> Bool:
  match w:
    case B.VR{a, +got, +pos, ok}:
      ok && U32.is_eq(got, v) && U32.is_eq(pos, (3 + n : U32))

def t.var.k(+v: U32, r: Array<U32> & U32) -> Bool:
  (a, +end) = r
  t.var.k2(v, (end - 3 : U32), B.B.var.get(a, 3, end))

def t.var(+x: U32) -> Bool:
  +v = (x >> U32.to_nat((x .&. 31 : U32)) : U32)
  t.var.k(v, B.B.var.put(rand.arr(4n, x), 3, v))

# Matches, against byte-at-a-time counts.
def ref.fwd(n: Nat, +i: U32, +j: U32, +c: U32, +on: Bool, r: Array<U32> & U32,
  q: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      c
    case 1n+p:
      (a, +x) = r
      (b, +y) = q
      +on2 = on && U32.is_eq(x, y)
      +i2 = (i + 1 : U32)
      +j2 = (j + 1 : U32)
      ref.fwd(p, i2, j2, (c + u32.pick(on2, 1, 0) : U32), on2, B.B.get(a, i2),
        B.B.get(b, j2))

def t.fwd.k(+want: U32, r: (Array<U32> & Array<U32>) & U32) -> Bool:
  (ab, +got) = r
  U32.is_eq(want, got)

def t.base.if(z: Bool, a: Array<U32>, +at: U32, +v: U32) -> Array<U32>:
  match z:
    case True{}:
      B.B.put(a, at, (v .^. 85 : U32))
    case False{}:
      a

def t.base.k(+k: U32, +i: U32, +x: U32, r: Array<U32> & Array<U32>) -> Array<U32>:
  (s, d) = r
  t.base.if(U32.is_eq(k, 1), d, (i + ((x >> 20n : U32) % 90 : U32) : U32), x)

def u32.max(+a: U32, +b: U32) -> U32:
  u32.pick((a < b : U32), b, a)

# rand.arr(6n, 5) shifted so byte i lines up with byte j, with one byte
# changed when k is 1.
def t.base(+k: U32, +i: U32, +j: U32, +x: U32) -> Array<U32>:
  t.base.k(k, i, x, B.B.copy(rand.arr(6n, 9), i, rand.arr(6n, 5), j, (200 - u32.max(i, j) : U32)))

# Two arrays equal but for a few bytes, so matches run long.
def t.fwd(+x: U32) -> Bool:
  +i = (x % 50 : U32)
  +j = ((x >> 8n : U32) % 50 : U32)
  +max = ((x >> 16n : U32) % 120 : U32)
  +k = ((x >> 4n : U32) % 3 : U32)
  t.fwd.k(ref.fwd(U32.to_nat(max), i, j, 0, True{}, B.B.get(t.base(k, i, j, x), i),
    B.B.get(rand.arr(6n, 5), j)),
    B.B.fwd(t.base(k, i, j, x), i, rand.arr(6n, 5), j, max))

def t.all(+x: U32) -> Bool:
  t.copy(x) && t.move(x) && t.fill(x) && t.var(x) && t.fwd(x)

def loop(n: Nat, +x: U32, +bad: U32) -> U32:
  match n:
    case 0n:
      bad
    case 1n+p:
      +y = lcg(x)
      loop(p, y, u32.pick(t.all(y), bad, (bad + 1 : U32)))

def loop2(n: Nat, +x: U32, +bad: U32) -> U32:
  match n:
    case 0n:
      bad
    case 1n+p:
      +y = lcg(x)
      loop2(p, y, u32.pick(t.adler(y), bad, (bad + 1 : U32)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("copy/move/fill/varint failures: " ++ U32.show(loop(20000n, 7, 0)))
    IO.print("adler failures: " ++ U32.show(loop2(300n, 11, 0)))
