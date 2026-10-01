import Base
import ../bytes.bend as B
import ./u32.bend as V
import ./word.bend as W
import ./bytes.bend as Y

id BB.ins4 x w
  # A word's four bytes, written into any word, give it back.
  lhs Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(x, 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), 24n, Y.BP.ext(w, 24n))
  rhs w

id BB.join00 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 0n), 0n)
  rhs Y.BP.ext(lo, 0n)

id BB.join01 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 0n), 8n)
  rhs Y.BP.ext(lo, 8n)

id BB.join02 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 0n), 16n)
  rhs Y.BP.ext(lo, 16n)

id BB.join03 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 0n), 24n)
  rhs Y.BP.ext(lo, 24n)

id BB.join10 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 8n), 0n)
  rhs Y.BP.ext(lo, 8n)

id BB.join11 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 8n), 8n)
  rhs Y.BP.ext(lo, 16n)

id BB.join12 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 8n), 16n)
  rhs Y.BP.ext(lo, 24n)

id BB.join13 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 8n), 24n)
  rhs Y.BP.ext(hi, 0n)

id BB.join20 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 16n), 0n)
  rhs Y.BP.ext(lo, 16n)

id BB.join21 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 16n), 8n)
  rhs Y.BP.ext(lo, 24n)

id BB.join22 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 16n), 16n)
  rhs Y.BP.ext(hi, 0n)

id BB.join23 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 16n), 24n)
  rhs Y.BP.ext(hi, 8n)

id BB.join30 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 24n), 0n)
  rhs Y.BP.ext(lo, 24n)

id BB.join31 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 24n), 8n)
  rhs Y.BP.ext(hi, 0n)

id BB.join32 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 24n), 16n)
  rhs Y.BP.ext(hi, 8n)

id BB.join33 lo hi
  lhs Y.BP.ext(B.B.join(lo, hi, 24n), 24n)
  rhs Y.BP.ext(hi, 16n)

id BB.rep4_0 b
  lhs Y.BP.ext(B.B.rep4(b), 0n)
  rhs U32.and(b, 255)

id BB.rep4_1 b
  lhs Y.BP.ext(B.B.rep4(b), 8n)
  rhs U32.and(b, 255)

id BB.rep4_2 b
  lhs Y.BP.ext(B.B.rep4(b), 16n)
  rhs U32.and(b, 255)

id BB.rep4_3 b
  lhs Y.BP.ext(B.B.rep4(b), 24n)
  rhs U32.and(b, 255)

id BB.xb0 x y
  lhs Y.BP.ext(y, 0n)
  rhs U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n))

id BB.xb1 x y
  lhs Y.BP.ext(y, 8n)
  rhs U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n))

id BB.xb2 x y
  lhs Y.BP.ext(y, 16n)
  rhs U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(U32.xor(x, y), 16n))

id BB.xb3 x y
  lhs Y.BP.ext(y, 24n)
  rhs U32.xor(Y.BP.ext(x, 24n), Y.BP.ext(U32.xor(x, y), 24n))

id BB.mk10 z
  lhs Y.BP.ext(z, 0n)
  rhs Y.BP.ext(U32.and(z, 255), 0n)

id BB.mk20 z
  lhs Y.BP.ext(z, 0n)
  rhs Y.BP.ext(U32.and(z, 65535), 0n)

id BB.mk21 z
  lhs Y.BP.ext(z, 8n)
  rhs Y.BP.ext(U32.and(z, 65535), 8n)

id BB.mk30 z
  lhs Y.BP.ext(z, 0n)
  rhs Y.BP.ext(U32.and(z, 16777215), 0n)

id BB.mk31 z
  lhs Y.BP.ext(z, 8n)
  rhs Y.BP.ext(U32.and(z, 16777215), 8n)

id BB.mk32 z
  lhs Y.BP.ext(z, 16n)
  rhs Y.BP.ext(U32.and(z, 16777215), 16n)

id BB.xor0 a
  lhs U32.xor(a, 0)
  rhs a

id BB.and255 v
  lhs U32.and(U32.and(v, 255), 255)
  rhs U32.and(v, 255)
