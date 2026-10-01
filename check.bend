import Base
import ./bytes.bend as B
import ./vcdiff.bend as V
import ./encode.bend as N

# The encoder, made trustworthy by checking its work: a delta from the fast
# encoder (encode.bend) is decoded with the decoder (vcdiff.bend), and
# replaced by a plain encoding of the target unless it gives the target back.
# LAWS.bend states, and PROOF.bend proves, that decoding the result always
# gives back the target.

# Helpers
# =======

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

def u32.max(+a: U32, +b: U32) -> U32:
  u32.pick((a < b : U32), b, a)

# The plain encoding
# ==================

# The target in windows of at most 2^23 bytes, each a single ADD (or no
# instruction, for an empty target), with no source and no checksum.

def FB.W() -> U32:
  8388608

# The instruction section of a window of t bytes: ADD with its size.
def fb.ilen(+t: U32) -> U32:
  u32.pick(U32.is_eq(t, 0), 0, (1 + B.B.var.len(t) : U32))

# The bytes of a window's delta encoding after its length field.
def fb.enc(+t: U32) -> U32:
  +il = fb.ilen(t)
  ((((((B.B.var.len(t) + 1 : U32) + B.B.var.len(t) : U32) + B.B.var.len(il) : U32)
    + 1 : U32) + t : U32) + il : U32)

def wr.byte(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +p) = r
  (B.B.put(a, p, v), (p + 1 : U32))

def wr.var(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +p) = r
  B.B.var.put(a, p, v)

def fb.inst(z: Bool, +t: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match z:
    case True{}:
      wr.var(t, wr.byte(1, r))
    case False{}:
      r

def fb.data.k(+p: U32, +t: U32, r: Array<U32> & Array<U32>) ->
  Array<U32> & (Array<U32> & U32):
  (tgt, d) = r
  (tgt, (d, (p + t : U32)))

# Copies tgt[w0, w0 + t) to the delta at p.
def fb.data(tgt: Array<U32>, +w0: U32, +t: U32, r: Array<U32> & U32) ->
  Array<U32> & (Array<U32> & U32):
  (d, +p) = r
  fb.data.k(p, t, B.B.copy.bytes(U32.to_nat(t), d, p, w0, B.B.get(tgt, w0)))

def fb.win.k(+t: U32, r: Array<U32> & (Array<U32> & U32)) ->
  Array<U32> & (Array<U32> & U32):
  (tgt, dp) = r
  (tgt, fb.inst(U32.is_ne(t, 0), t, dp))

# Writes the window for tgt[w0, w0 + t).
def fb.win(tgt: Array<U32>, +w0: U32, +t: U32, r: Array<U32> & U32) ->
  Array<U32> & (Array<U32> & U32):
  fb.win.k(t, fb.data(tgt, w0, t,
    wr.byte(0, wr.var(fb.ilen(t), wr.var(t, wr.byte(0, wr.var(t,
      wr.var(fb.enc(t), wr.byte(0, r)))))))))

def fb.loop(k: Nat, +len: U32, +w0: U32, r: Array<U32> & (Array<U32> & U32)) ->
  Array<U32> & (Array<U32> & U32):
  match k:
    case 0n:
      r
    case 1n+p:
      (tgt, dp) = r
      +t = U32.min(FB.W(), (len - w0 : U32))
      fb.loop(p, len, (w0 + t : U32), fb.win(tgt, w0, t, dp))

def fb.done(+len: U32, r: Array<U32> & (Array<U32> & U32)) ->
  B.Bytes & B.Bytes:
  (tgt, dp) = r
  (d, n) = dp
  (B.Bytes{len, tgt}, B.Bytes{n, d})

# The plain encoding of tgt. Answers tgt back.
def fallback(tgt: B.Bytes) -> B.Bytes & B.Bytes:
  match tgt:
    case B.Bytes{+len, buf}:
      +n = u32.max(1, (((len + FB.W() : U32) - 1 : U32) / FB.W() : U32))
      fb.done(len, fb.loop(U32.to_nat(n), len, 0, (buf,
        wr.byte(0, wr.byte(0, wr.byte(196, wr.byte(195, wr.byte(214,
          (B.B.zeros((((len + 5 : U32)) + (n * 40 : U32) : U32)), 0)))))))))

# Checking
# ========

def chk.ok(ok: Bool, t: B.Bytes, d: B.Bytes) -> B.Bytes:
  match ok:
    case True{}:
      d
    case False{}:
      Pair.snd(B.Bytes, B.Bytes, fallback(t))

def chk.cmp(t: B.Bytes, d: B.Bytes, r: (B.Bytes & B.Bytes) & Bool) -> B.Bytes:
  (xt, ok) = r
  chk.ok(ok, t, d)

def chk.res(t1: B.Bytes, t2: B.Bytes, d: B.Bytes,
  r: B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)) -> B.Bytes:
  match r:
    case Tuple{s, Tuple{d1, Done{x}}}:
      chk.cmp(t2, d, B.B.eq(x, t1))
    case Tuple{s, Tuple{d1, Fail{e}}}:
      Pair.snd(B.Bytes, B.Bytes, fallback(t2))

def chk.go(src: B.Bytes, tt: B.Bytes & B.Bytes, dd: B.Bytes & B.Bytes) ->
  B.Bytes:
  (t1, t2) = tt
  (d1, d2) = dd
  chk.res(t1, t2, d2, V.decode(src, d1))

# d if it decodes to tgt, else the plain encoding of tgt.
def check(src: B.Bytes, tgt: B.Bytes, d: B.Bytes) -> B.Bytes:
  chk.go(src, B.B.clone(tgt), B.B.clone(d))

def enc.go(s: B.Bytes & B.Bytes, t: B.Bytes & B.Bytes) -> B.Bytes:
  (s1, s2) = s
  (t1, t2) = t
  check(s2, t2, Pair.snd(B.Bytes & B.Bytes, B.Bytes, N.encode(s1, t1)))

# A delta that turns src into tgt.
def encode(src: B.Bytes, tgt: B.Bytes) -> B.Bytes:
  enc.go(B.B.clone(src), B.B.clone(tgt))

# What decoding d against src gives, as a list of bytes.
def restore.k(r: B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)) ->
  Result<&1, &1, U32, List<&2, U32>>:
  match r:
    case Tuple{s, Tuple{d, Done{x}}}:
      Done{B.B.list(x)}
    case Tuple{s, Tuple{d, Fail{e}}}:
      Fail{e}

def restore(src: B.Bytes, d: B.Bytes) -> Result<&1, &1, U32, List<&2, U32>>:
  restore.k(V.decode(src, d))
