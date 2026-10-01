import Base
import ./bytes.bend as B
import ./vcdiff.bend as V
import ./encode.bend as N

# The encoder, made trustworthy by checking its work: a delta from the fast
# encoder (encode.bend) is decoded with the decoder (vcdiff.bend), and
# replaced by a plain encoding of the target unless it gives the target back.
# LAWS.bend states, and PROOF.bend proves, that decoding the result always
# gives back the target.

# The plain encoding
# ==================

# The target a byte at a time: each byte is a window of its own, holding one
# ADD of size 1 (opcode 2), with no source and no checksum; an empty target
# is one empty window. Every window has the same nine bytes but one, which
# keeps the proof short; this encoding is only the fallback.

def wr.byte(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +p) = r
  (B.B.put(a, p, v), (p + 1 : U32))

def fb.win.k(dp: Array<U32> & U32, r: Array<U32> & U32) ->
  Array<U32> & (Array<U32> & U32):
  (tgt, +x) = r
  (tgt, wr.byte(2, wr.byte(x, wr.byte(0, wr.byte(1, wr.byte(1, wr.byte(0,
    wr.byte(1, wr.byte(7, wr.byte(0, dp))))))))))

# Writes the window for the byte at w: indicator, length of the rest, target
# length, delta indicator, the lengths of the three sections, the byte and
# the opcode.
def fb.win(tgt: Array<U32>, +w: U32, dp: Array<U32> & U32) ->
  Array<U32> & (Array<U32> & U32):
  fb.win.k(dp, B.B.get(tgt, w))

# Writes the windows for the k bytes from w.
def fb.loop(k: Nat, +w: U32, r: Array<U32> & (Array<U32> & U32)) ->
  Array<U32> & (Array<U32> & U32):
  match k r:
    case 0n r:
      r
    case 1n+p Tuple{tgt, dp}:
      fb.loop(p, (w + 1 : U32), fb.win(tgt, w, dp))

# The window of an empty target.
def fb.empty(dp: Array<U32> & U32) -> Array<U32> & U32:
  wr.byte(0, wr.byte(0, wr.byte(0, wr.byte(0, wr.byte(0, wr.byte(5,
    wr.byte(0, dp)))))))

def fb.body(z: Bool, +len: U32, tgt: Array<U32>, dp: Array<U32> & U32) ->
  Array<U32> & (Array<U32> & U32):
  match z:
    case True{}:
      (tgt, fb.empty(dp))
    case False{}:
      fb.loop(U32.to_nat(len), 0, (tgt, dp))

def fb.done(+len: U32, r: Array<U32> & (Array<U32> & U32)) ->
  B.Bytes & B.Bytes:
  (tgt, dp) = r
  (d, n) = dp
  (B.Bytes{len, tgt}, B.Bytes{n, d})

# The plain encoding of tgt. Answers tgt back. Its nine bytes per byte (and
# the header) fit in 16 * (len + 1) bytes, which needs no carry for targets
# under 2^27 bytes.
def fallback(tgt: B.Bytes) -> B.Bytes & B.Bytes:
  match tgt:
    case B.Bytes{+len, buf}:
      fb.done(len, fb.body(U32.is_eq(len, 0), len, buf,
        wr.byte(0, wr.byte(0, wr.byte(196, wr.byte(195, wr.byte(214,
          (B.B.zeros(((len + 1 : U32) << 4n : U32)), 0))))))))

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
