import Base

# Byte strings, packed four bytes to a U32 word, little-endian: byte i is
# bits 8 * (i % 4) .. 8 * (i % 4) + 7 of word i / 4. On a little-endian host
# a word array is laid out exactly as the bytes are, so files load and store
# with a plain copy.
#
# Every read of an array hands the array back beside the value, and Bend
# matches only parameters, so a read is followed by a def that receives the
# pair: many helpers below are the second half of a read.

# Bytes
# =====

# `len` bytes held in words [0, ceil(len / 4)) of `buf`; bytes past `len`
# are padding.
type Bytes is Type:
  Bytes{len: U32, buf: Array<U32>}

# Helpers
# =======

def B.clone.k(+len: U32, r: Array<U32> & Array<U32>) -> Bytes & Bytes:
  (a, b) = r
  (Bytes{len, a}, Bytes{len, b})

# Two copies of a byte string.
def B.clone(b: Bytes) -> Bytes & Bytes:
  match b:
    case Bytes{+len, buf}:
      B.clone.k(len, Array.clone(U32, buf))

# The length of a byte string.
def B.len(b: Bytes) -> U32:
  match b:
    case Bytes{len, buf}:
      len

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

# The bit offset of byte i within its word.
def B.sh(+i: U32) -> Nat:
  U32.to_nat(((3 .&. i : U32) << 3n : U32))

# The smallest d with 2^d >= n.
def B.depth.go(k: Nat, done: Bool, +n: U32, +d: Nat, +p: U32) -> Nat:
  match k done:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+q False{}:
      +p2 = (p << 1n : U32)
      B.depth.go(q, (p2 >= n : U32), n, 1n+d, p2)

def B.depth(+n: U32) -> Nat:
  B.depth.go(31n, (1 >= n : U32), n, 0n, 1)

# The words that hold n bytes.
def B.words(+n: U32) -> U32:
  (((n + 3 : U32) >> 2n : U32))

# A word array that holds n bytes, all zero.
def B.zeros(+n: U32) -> Array<U32>:
  Array.new(U32, B.depth(B.words(n)), 0)

# Bytes and words
# ===============

def B.get.k(+i: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +w) = r
  (a, ((w >> B.sh(i) : U32) .&. 255 : U32))

# The byte at i.
def B.get(a: Array<U32>, +i: U32) -> Array<U32> & U32:
  B.get.k(i, a[(i >> 2n : U32)])

# The bytes [i, i + n) of the array in r (which holds the byte at i), as a
# list. A specification: never run.
def B.list.go(n: Nat, +i: U32, r: Array<U32> & U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (a, x) = r
      +i2 = (i + 1 : U32)
      x <> B.list.go(p, i2, B.get(a, i2))

# The bytes of b, as a list.
def B.list(b: Bytes) -> List<&2, U32>:
  match b:
    case Bytes{len, buf}:
      B.list.go(U32.to_nat(len), 0, B.get(buf, 0))

def B.put.k(+i: U32, +v: U32, r: Array<U32> & U32) -> Array<U32>:
  (a, +w) = r
  +sh = B.sh(i)
  a[(i >> 2n : U32)] <- ((w .&. U32.not((255 << sh : U32)) : U32)
    .|. ((v .&. 255 : U32) << sh : U32) : U32)

# Sets the byte at i to v (mod 256).
def B.put(a: Array<U32>, +i: U32, +v: U32) -> Array<U32>:
  B.put.k(i, v, a[(i >> 2n : U32)])

# The word made of bytes [8 * sh / 8, ..) of lo followed by hi: lo shifted
# down by sh bits, topped with hi.
def B.join(+lo: U32, +hi: U32, +sh: Nat) -> U32:
  ((lo >> sh : U32) .|. (hi << Nat.sub(32n, sh) : U32) : U32)

def B.word.k2(+sh: Nat, +lo: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +hi) = r
  (a, B.join(lo, hi, sh))

def B.word.k1(+i: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +lo) = r
  B.word.k2(B.sh(i), lo, a[((i >> 2n : U32) + 1 : U32)])

# The four bytes at i, i + 1, i + 2, i + 3 as a little-endian word.
def B.word(a: Array<U32>, +i: U32) -> Array<U32> & U32:
  B.word.k1(i, a[(i >> 2n : U32)])

# Copying
# =======

# dst[d, d + n) := src[s, s + n), a byte at a time.
def B.copy.bytes(n: Nat, dst: Array<U32>, +d: U32, +s: U32,
  r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (src, x) = r
      (src, dst)
    case 1n+p:
      (src, +x) = r
      +s2 = (s + 1 : U32)
      B.copy.bytes(p, B.put(dst, d, x), (d + 1 : U32), s2, B.get(src, s2))

# dst words [dw, dw + n) := src bytes from word sw, bit sh on; lo is word sw
# and r holds word sw + 1.
def B.copy.words(n: Nat, dst: Array<U32>, +dw: U32, +sw: U32, +sh: Nat,
  +lo: U32, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (src, x) = r
      (src, dst)
    case 1n+p:
      (src, +hi) = r
      dst2 = dst[dw] <- B.join(lo, hi, sh)
      +sw2 = (sw + 1 : U32)
      B.copy.words(p, dst2, (dw + 1 : U32), sw2, sh, hi, src[(sw2 + 1 : U32)])

def B.copy.tail(+n: U32, +d: U32, +s: U32, r: Array<U32> & Array<U32>) ->
  Array<U32> & Array<U32>:
  (src, dst) = r
  B.copy.bytes(U32.to_nat(n), dst, d, s, B.get(src, s))

def B.copy.body.k(+nw: U32, +d: U32, +s: U32, dst: Array<U32>,
  r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  (src, +lo) = r
  +sw = (s >> 2n : U32)
  B.copy.words(U32.to_nat(nw), dst, (d >> 2n : U32), sw, B.sh(s), lo,
    src[(sw + 1 : U32)])

def B.copy.body(+n: U32, +d: U32, +s: U32, r: Array<U32> & Array<U32>) ->
  Array<U32> & Array<U32>:
  (src, dst) = r
  +nw = (n >> 2n : U32)
  +done = (nw << 2n : U32)
  B.copy.tail((n .&. 3 : U32), (d + done : U32), (s + done : U32),
    B.copy.body.k(nw, d, s, dst, src[(s >> 2n : U32)]))

# dst[d, d + n) := src[s, s + n), where src and dst are different arrays:
# bytes up to a word boundary of d, then whole words, then the rest.
def B.copy(dst: Array<U32>, +d: U32, src: Array<U32>, +s: U32, +n: U32) ->
  Array<U32> & Array<U32>:
  +head = U32.min(n, ((4 - (d .&. 3 : U32) : U32) .&. 3 : U32))
  B.copy.body((n - head : U32), (d + head : U32), (s + head : U32),
    B.copy.bytes(U32.to_nat(head), dst, d, s, B.get(src, s)))

# The same within one array, forward, so a copy may read its own output
# (s < d), as VCDIFF COPY requires.
def B.move.bytes(n: Nat, +d: U32, +s: U32, r: Array<U32> & U32) ->
  Array<U32>:
  match n:
    case 0n:
      (a, x) = r
      a
    case 1n+p:
      (a, +x) = r
      +s2 = (s + 1 : U32)
      B.move.bytes(p, (d + 1 : U32), s2, B.get(B.put(a, d, x), s2))

# Whole words, for d word-aligned and s at least 4 bytes behind d: each
# word reads only bytes already final. r holds the word at s.
def B.move.words(n: Nat, +dw: U32, +s: U32, r: Array<U32> & U32) ->
  Array<U32>:
  match n:
    case 0n:
      (a, w) = r
      a
    case 1n+p:
      (a, +w) = r
      a2 = a[dw] <- w
      +s2 = (s + 4 : U32)
      B.move.words(p, (dw + 1 : U32), s2, B.word(a2, s2))

def B.move.tail(+n: U32, +d: U32, +s: U32, a: Array<U32>) -> Array<U32>:
  B.move.bytes(U32.to_nat(n), d, s, B.get(a, s))

def B.move.body(+n: U32, +d: U32, +s: U32, a: Array<U32>) -> Array<U32>:
  +nw = (n >> 2n : U32)
  +done = (nw << 2n : U32)
  B.move.tail((n .&. 3 : U32), (d + done : U32), (s + done : U32),
    B.move.words(U32.to_nat(nw), (d >> 2n : U32), s, B.word(a, s)))

def B.move.go(far: Bool, a: Array<U32>, +d: U32, +s: U32, +n: U32) ->
  Array<U32>:
  match far:
    case False{}:
      B.move.bytes(U32.to_nat(n), d, s, B.get(a, s))
    case True{}:
      +head = U32.min(n, ((4 - (d .&. 3 : U32) : U32) .&. 3 : U32))
      B.move.body((n - head : U32), (d + head : U32), (s + head : U32),
        B.move.bytes(U32.to_nat(head), d, s, B.get(a, s)))

# a[d, d + n) := a[s, s + n), forward, for s < d: the copy may read bytes it
# wrote itself, as VCDIFF COPY requires.
def B.move(a: Array<U32>, +d: U32, +s: U32, +n: U32) -> Array<U32>:
  B.move.go(((d - s : U32) >= 4 : U32), a, d, s, n)

# Filling
# =======

# A word of four copies of byte b.
def B.rep4(+b: U32) -> U32:
  +x = (255 .&. b : U32)
  (((x .|. (x << 8n : U32) : U32) .|. (x << 16n : U32) : U32) .|. (x << 24n : U32) : U32)

def B.fill.bytes(n: Nat, a: Array<U32>, +d: U32, +v: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      B.fill.bytes(p, B.put(a, d, v), (d + 1 : U32), v)

def B.fill.words(n: Nat, a: Array<U32>, +dw: U32, +w: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      a2 = a[dw] <- w
      B.fill.words(p, a2, (dw + 1 : U32), w)

def B.fill.body(+n: U32, +d: U32, +v: U32, a: Array<U32>) -> Array<U32>:
  +nw = (n >> 2n : U32)
  +done = (nw << 2n : U32)
  B.fill.bytes(U32.to_nat((n .&. 3 : U32)),
    B.fill.words(U32.to_nat(nw), a, (d >> 2n : U32),
      B.rep4(v)),
    (d + done : U32), v)

# a[d, d + n) := v.
def B.fill(a: Array<U32>, +d: U32, +v: U32, +n: U32) -> Array<U32>:
  +head = U32.min(n, ((4 - (d .&. 3 : U32) : U32) .&. 3 : U32))
  B.fill.body((n - head : U32), (d + head : U32), v,
    B.fill.bytes(U32.to_nat(head), a, d, v))

# Comparing
# =========

def B.eq.k(r: Array<U32> & U32, q: Array<U32> & U32) ->
  Bool & (Array<U32> & Array<U32>):
  (a, +x) = r
  (b, +y) = q
  (U32.is_eq(x, y), (a, b))

# Whether words [i, i + n) of the two arrays agree, given that the words
# before them did when s says so.
def B.eq.words(n: Nat, +i: U32, s: Bool & (Array<U32> & Array<U32>)) ->
  (Array<U32> & Array<U32>) & Bool:
  match n s:
    case 0n Tuple{same, ab}:
      (ab, same)
    case 1n+p Tuple{False{}, ab}:
      (ab, False{})
    case 1n+p Tuple{True{}, Tuple{a, b}}:
      B.eq.words(p, (i + 1 : U32), B.eq.k(a[i], b[i]))

def B.eq.fin(+la: U32, +lb: U32, r: (Array<U32> & Array<U32>) & Bool) ->
  (Bytes & Bytes) & Bool:
  (ab, same) = r
  (aa, ba) = ab
  ((Bytes{la, aa}, Bytes{lb, ba}), same)

# Whether two byte strings are the same: the same length and the same words
# holding their bytes. Padding counts, so byte strings that agree may still
# differ here (never so for ours, whose padding is zero); a check that says
# they agree is always right. Answers both back.
def B.eq(a: Bytes, b: Bytes) -> (Bytes & Bytes) & Bool:
  match a b:
    case Bytes{+la, aa} Bytes{+lb, ba}:
      B.eq.fin(la, lb, B.eq.words(U32.to_nat(B.words(la)), 0, (U32.is_eq(la, lb), (aa, ba))))

# Adler-32
# ========

# Sums without reduction (n bytes, or n words, at most 5552 bytes in all,
# the most that keeps b below 2^32, as zlib does).
def B.adler.bytes(n: Nat, +a: U32, +b: U32, +i: U32, r: Array<U32> & U32) ->
  Array<U32> & (U32 & U32):
  match n:
    case 0n:
      (s, x) = r
      (s, (a, b))
    case 1n+p:
      (s, +x) = r
      +a2 = (a + x : U32)
      +i2 = (i + 1 : U32)
      B.adler.bytes(p, a2, (b + a2 : U32), i2, B.get(s, i2))

def B.adler.words(n: Nat, +a: U32, +b: U32, +wi: U32, r: Array<U32> & U32) ->
  Array<U32> & (U32 & U32):
  match n:
    case 0n:
      (s, x) = r
      (s, (a, b))
    case 1n+p:
      (s, +w) = r
      +b0 = (w .&. 255 : U32)
      +b1 = ((w >> 8n : U32) .&. 255 : U32)
      +b2 = ((w >> 16n : U32) .&. 255 : U32)
      +b3 = (w >> 24n : U32)
      +nb = ((((b + (a << 2n : U32) : U32) + (b0 << 2n : U32) : U32)
        + (b1 * 3 : U32) : U32) + ((b2 << 1n : U32) + b3 : U32) : U32)
      +na = ((a + (b0 + b1 : U32) : U32) + (b2 + b3 : U32) : U32)
      +wi2 = (wi + 1 : U32)
      B.adler.words(p, na, nb, wi2, s[wi2])

def B.adler.red(r: Array<U32> & (U32 & U32)) -> Array<U32> & (U32 & U32):
  (s, ab) = r
  (a, b) = ab
  (s, ((a % 65521 : U32), (b % 65521 : U32)))

def B.adler.chunk(+wi: U32, +m: U32, r: Array<U32> & (U32 & U32)) ->
  Array<U32> & (U32 & U32):
  (s, ab) = r
  (a, b) = ab
  B.adler.red(B.adler.words(U32.to_nat(m), a, b, wi, s[wi]))

# k counts the chunks of at most 1388 words left.
def B.adler.go(k: Nat, +wi: U32, +nw: U32, r: Array<U32> & (U32 & U32)) ->
  Array<U32> & (U32 & U32):
  match k:
    case 0n:
      r
    case 1n+p:
      +m = U32.min(nw, 1388)
      B.adler.go(p, (wi + m : U32), (nw - m : U32), B.adler.chunk(wi, m, r))

def B.adler.fin(r: Array<U32> & (U32 & U32)) -> Array<U32> & U32:
  (s, ab) = r
  (a, b) = ab
  (s, ((b << 16n : U32) .|. a : U32))

def B.adler.tail(+i: U32, +n: U32, r: Array<U32> & (U32 & U32)) ->
  Array<U32> & U32:
  (s, ab) = r
  (a, b) = ab
  B.adler.fin(B.adler.red(B.adler.bytes(U32.to_nat(n), a, b, i, B.get(s, i))))

def B.adler.body(+i: U32, +n: U32, r: Array<U32> & (U32 & U32)) ->
  Array<U32> & U32:
  +nw = (n >> 2n : U32)
  B.adler.tail((i + (nw << 2n : U32) : U32), (n .&. 3 : U32),
    B.adler.go(U32.to_nat(((nw + 1387 : U32) / 1388 : U32)), (i >> 2n : U32), nw, r))

def B.adler.head(+i: U32, +n: U32, +h: U32, s: Array<U32>) -> Array<U32> & U32:
  B.adler.body((i + h : U32), (n - h : U32),
    B.adler.red(B.adler.bytes(U32.to_nat(h), 1, 0, i, B.get(s, i))))

# The Adler-32 checksum of bytes [i, i + n).
def B.adler32(s: Array<U32>, +i: U32, +n: U32) -> Array<U32> & U32:
  B.adler.head(i, n, U32.min(n, ((4 - (i .&. 3 : U32) : U32) .&. 3 : U32)), s)

# Varints
# =======

# Base-128, most significant group first, the high bit set on all but the
# last byte, at most 5 bytes for a U32.

# A read: the array, the value, the position after it, and whether it was
# well-formed and inside [.., end).
type VR is Type:
  VR{arr: Array<U32>, val: U32, pos: U32, ok: Bool}

def B.var.cont(r: Array<U32> & U32) -> Bool & (Array<U32> & U32):
  (a, +b) = r
  (U32.is_ne((128 .&. b : U32), 0), (a, b))

def B.var.go(n: Nat, +end: U32, +acc: U32, +pos: U32, ok: Bool,
  s: Bool & (Array<U32> & U32)) -> VR:
  match n s:
    case 0n Tuple{c, Tuple{a, b}}:
      VR{a, acc, pos, False{}}
    case 1n+p Tuple{False{}, Tuple{a, b}}:
      +fits = U32.is_eq((acc >> 25n : U32), 0) && (pos < end : U32)
      VR{a, ((acc << 7n : U32) .|. b : U32), (pos + 1 : U32), ok && fits}
    case 1n+p Tuple{True{}, Tuple{a, b}}:
      +fits = U32.is_eq((acc >> 25n : U32), 0) && (pos < end : U32)
      +next = (pos + 1 : U32)
      B.var.go(p, end, ((acc << 7n : U32) .|. (b .&. 127 : U32) : U32), next,
        ok && fits, B.var.cont(B.get(a, next)))

# The varint at pos, which must end before `end`.
def B.var.get(a: Array<U32>, +pos: U32, +end: U32) -> VR:
  B.var.go(5n, end, 0, pos, True{}, B.var.cont(B.get(a, pos)))

def B.byte.k(+pos: U32, +end: U32, r: Array<U32> & U32) -> VR:
  (a, b) = r
  VR{a, b, (pos + 1 : U32), (pos < end : U32)}

# The byte at pos, with the shape of a varint read.
def B.byte.get(a: Array<U32>, +pos: U32, +end: U32) -> VR:
  B.byte.k(pos, end, B.get(a, pos))

# The bytes of v as a varint.
def B.var.len(+v: U32) -> U32:
  u32.pick((v < 128 : U32), 1,
  u32.pick((v < 16384 : U32), 2,
  u32.pick((v < 2097152 : U32), 3,
  u32.pick((v < 268435456 : U32), 4, 5))))

def B.var.flag(+p: Nat) -> U32:
  match p:
    case 0n:
      0
    case 1n+q:
      128

# Writes the k low 7-bit groups of v, most significant first.
def B.var.put.go(+k: Nat, a: Array<U32>, +pos: U32, +v: U32) -> Array<U32>:
  match k:
    case 0n:
      a
    case 1n+p:
      +g = (127 .&. (v >> Nat.mul(7n, p) : U32) : U32)
      B.var.put.go(p, B.put(a, pos, (B.var.flag(p) .|. g : U32)), (pos + 1 : U32), v)

# Writes v as a varint at pos; answers the position after it.
def B.var.put(a: Array<U32>, +pos: U32, +v: U32) -> Array<U32> & U32:
  +n = B.var.len(v)
  (B.var.put.go(U32.to_nat(n), a, pos, v), (pos + n : U32))

# Matching
# ========

# The index of the lowest byte set in a nonzero x.
def B.low.byte(+x: U32) -> U32:
  u32.pick(U32.is_ne((x .&. 255 : U32), 0), 0,
  u32.pick(U32.is_ne((x .&. 65535 : U32), 0), 1,
  u32.pick(U32.is_ne((x .&. 16777215 : U32), 0), 2, 3)))

# A forward match reads each word once: a's bytes are words wa, wa + 1, ...
# shifted down by sa bits, b's likewise; alo and blo hold the words at wa
# and wb, and n bytes agree so far.
def B.fwd.k2(+n: U32, +max: U32, +sa: Nat, +sb: Nat, +alo: U32, +ahi: U32,
  +blo: U32, a: Array<U32>, r: Array<U32> & U32) ->
  Bool & (U32 & ((Array<U32> & Array<U32>) & (U32 & U32))):
  (b, +bhi) = r
  +d = (B.join(alo, ahi, sa) .^. B.join(blo, bhi, sb) : U32)
  +same = U32.is_eq(d, 0)
  (same && ((n + 4 : U32) < max : U32),
    ((n + u32.pick(same, 4, B.low.byte(d)) : U32), ((a, b), (ahi, bhi))))

def B.fwd.k1(+wb: U32, +n: U32, +max: U32, +sa: Nat, +sb: Nat, +alo: U32,
  +blo: U32, b: Array<U32>, r: Array<U32> & U32) ->
  Bool & (U32 & ((Array<U32> & Array<U32>) & (U32 & U32))):
  (a, +ahi) = r
  B.fwd.k2(n, max, sa, sb, alo, ahi, blo, a, b[(wb + 1 : U32)])

# One step: compares the four bytes from words wa and wb, reading the next
# word of each; answers whether to go on, the count, the arrays and the
# words read.
def B.fwd.step(+wa: U32, +wb: U32, +n: U32, +max: U32, +sa: Nat, +sb: Nat,
  +alo: U32, +blo: U32, a: Array<U32>, b: Array<U32>) ->
  Bool & (U32 & ((Array<U32> & Array<U32>) & (U32 & U32))):
  B.fwd.k1(wb, n, max, sa, sb, alo, blo, b, a[(wa + 1 : U32)])

def B.fwd.loop(k: Nat, +wa: U32, +wb: U32, +max: U32, +sa: Nat, +sb: Nat,
  s: Bool & (U32 & ((Array<U32> & Array<U32>) & (U32 & U32)))) ->
  (Array<U32> & Array<U32>) & U32:
  match k s:
    case 0n Tuple{m, Tuple{n, Tuple{ab, hs}}}:
      (ab, U32.min(n, max))
    case 1n+p Tuple{False{}, Tuple{n, Tuple{ab, hs}}}:
      (ab, U32.min(n, max))
    case 1n+p Tuple{True{}, Tuple{n0, Tuple{Tuple{a, b}, Tuple{alo0, blo0}}}}:
      +n = {n0 : U32}
      +alo = {alo0 : U32}
      +blo = {blo0 : U32}
      +wa2 = (wa + 1 : U32)
      +wb2 = (wb + 1 : U32)
      B.fwd.loop(p, wa2, wb2, max, sa, sb,
        B.fwd.step(wa2, wb2, n, max, sa, sb, alo, blo, a, b))

def B.fwd.s2(+wa: U32, +wb: U32, +max: U32, +sa: Nat, +sb: Nat, +alo: U32,
  a: Array<U32>, r: Array<U32> & U32) -> (Array<U32> & Array<U32>) & U32:
  (b, +blo) = r
  B.fwd.loop(U32.to_nat(((max >> 2n : U32) + 1 : U32)), wa, wb, max, sa, sb,
    B.fwd.step(wa, wb, 0, max, sa, sb, alo, blo, a, b))

def B.fwd.s1(+wa: U32, +wb: U32, +max: U32, +sa: Nat, +sb: Nat, b: Array<U32>,
  r: Array<U32> & U32) -> (Array<U32> & Array<U32>) & U32:
  (a, +alo) = r
  B.fwd.s2(wa, wb, max, sa, sb, alo, a, b[wb])

# How many bytes, up to max, a from i and b from j have in common.
def B.fwd(a: Array<U32>, +i: U32, b: Array<U32>, +j: U32, +max: U32) ->
  (Array<U32> & Array<U32>) & U32:
  +wa = (i >> 2n : U32)
  +wb = (j >> 2n : U32)
  B.fwd.s1(wa, wb, max, B.sh(i), B.sh(j), b, a[wa])

# The same within one array.
def B.fwd1.k3(+n: U32, +max: U32, +x: U32, r: Array<U32> & U32) ->
  Bool & (U32 & Array<U32>):
  (a, +y) = r
  +d = (x .^. y : U32)
  +same = U32.is_eq(d, 0)
  (same && ((n + 4 : U32) < max : U32),
    ((n + u32.pick(same, 4, B.low.byte(d)) : U32), a))

def B.fwd1.k2(+j: U32, +n: U32, +max: U32, r: Array<U32> & U32) ->
  Bool & (U32 & Array<U32>):
  (a, +x) = r
  B.fwd1.k3(n, max, x, B.word(a, (j + n : U32)))

def B.fwd1.step(+i: U32, +j: U32, +n: U32, +max: U32, a: Array<U32>) ->
  Bool & (U32 & Array<U32>):
  B.fwd1.k2(j, n, max, B.word(a, (i + n : U32)))

def B.fwd1.loop(k: Nat, +i: U32, +j: U32, +max: U32,
  s: Bool & (U32 & Array<U32>)) -> Array<U32> & U32:
  match k s:
    case 0n Tuple{m, Tuple{n, a}}:
      (a, U32.min(n, max))
    case 1n+p Tuple{False{}, Tuple{n, a}}:
      (a, U32.min(n, max))
    case 1n+p Tuple{True{}, Tuple{n, a}}:
      B.fwd1.loop(p, i, j, max, B.fwd1.step(i, j, n, max, a))

def B.fwd1(a: Array<U32>, +i: U32, +j: U32, +max: U32) -> Array<U32> & U32:
  B.fwd1.loop(U32.to_nat(((max >> 2n : U32) + 1 : U32)), i, j, max,
    B.fwd1.step(i, j, 0, max, a))

# A backward match: how many bytes, up to max, before i in a and before j
# in b agree.
def B.back.k2(+n: U32, +max: U32, a: Array<U32>, +x: U32,
  r: Array<U32> & U32) -> Bool & (U32 & (Array<U32> & Array<U32>)):
  (b, +y) = r
  +same = U32.is_eq(x, y)
  (same && ((n + 1 : U32) < max : U32),
    ((n + u32.pick(same, 1, 0) : U32), (a, b)))

def B.back.k1(+j: U32, +n: U32, +max: U32, b: Array<U32>,
  r: Array<U32> & U32) -> Bool & (U32 & (Array<U32> & Array<U32>)):
  (a, +x) = r
  B.back.k2(n, max, a, x, B.get(b, ((j - 1 : U32) - n : U32)))

def B.back.step(+i: U32, +j: U32, +n: U32, +max: U32, a: Array<U32>,
  b: Array<U32>) -> Bool & (U32 & (Array<U32> & Array<U32>)):
  B.back.k1(j, n, max, b, B.get(a, ((i - 1 : U32) - n : U32)))

def B.back.loop(k: Nat, +i: U32, +j: U32, +max: U32,
  s: Bool & (U32 & (Array<U32> & Array<U32>))) ->
  (Array<U32> & Array<U32>) & U32:
  match k s:
    case 0n Tuple{m, Tuple{n, ab}}:
      (ab, U32.min(n, max))
    case 1n+p Tuple{False{}, Tuple{n, ab}}:
      (ab, U32.min(n, max))
    case 1n+p Tuple{True{}, Tuple{n, Tuple{a, b}}}:
      B.back.loop(p, i, j, max, B.back.step(i, j, n, max, a, b))

def B.back(a: Array<U32>, +i: U32, b: Array<U32>, +j: U32, +max: U32) ->
  (Array<U32> & Array<U32>) & U32:
  B.back.loop(U32.to_nat(max), i, j, max, B.back.step(i, j, 0, max, a, b))

# How many bytes, up to max, from i equal v (a word of four copies of it).
def B.same.k(+n: U32, +max: U32, +v: U32, r: Array<U32> & U32) ->
  Bool & (U32 & Array<U32>):
  (a, +x) = r
  +d = (x .^. v : U32)
  +same = U32.is_eq(d, 0)
  (same && ((n + 4 : U32) < max : U32),
    ((n + u32.pick(same, 4, B.low.byte(d)) : U32), a))

def B.same.loop(k: Nat, +i: U32, +v: U32, +max: U32,
  s: Bool & (U32 & Array<U32>)) -> Array<U32> & U32:
  match k s:
    case 0n Tuple{m, Tuple{n, a}}:
      (a, U32.min(n, max))
    case 1n+p Tuple{False{}, Tuple{n, a}}:
      (a, U32.min(n, max))
    case 1n+p Tuple{True{}, Tuple{+n, a}}:
      B.same.loop(p, i, v, max, B.same.k(n, max, v, B.word(a, (i + n : U32))))

def B.same(a: Array<U32>, +i: U32, +b: U32, +max: U32) -> Array<U32> & U32:
  +v = B.rep4(b)
  B.same.loop(U32.to_nat(((max >> 2n : U32) + 1 : U32)), i, v, max,
    B.same.k(0, max, v, B.word(a, i)))

# Growing
# =======

def B.grow.k(r: Array<U32> & Array<U32>) -> Array<U32>:
  (old, new) = r
  new

def B.grow.if(z: Bool, a: Array<U32>, +used: U32, +need: U32) -> Array<U32>:
  match z:
    case True{}:
      a
    case False{}:
      +n2 = u32.pick((need < 1073741824 : U32), (need << 1n : U32), need)
      B.grow.k(B.copy(B.zeros(n2), 0, a, 0, used))

def B.grow.go(+used: U32, +need: U32, r: Array<U32> & U32) -> Array<U32>:
  (a, +cap) = r
  B.grow.if((B.words(need) <= cap : U32), a, used, need)

# An array holding at least need bytes, keeping its first `used` bytes.
def B.grow(a: Array<U32>, +used: U32, +need: U32) -> Array<U32>:
  B.grow.go(used, need, Array.size(U32, a))
