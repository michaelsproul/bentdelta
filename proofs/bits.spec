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

id BB.v1 v
  lhs U32.or(0, U32.and(U32.or(0, U32.and(127, U32.shrn(v, 0n))), 255))
  rhs U32.and(v, 127)

id BB.v2f v
  lhs U32.or(0, U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 7n))), 255), 127))
  rhs U32.shrn(U32.and(v, 16383), 7n)

id BB.v2l v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 16383), 7n), 7n), U32.and(U32.or(0, U32.and(127, U32.shrn(v, 0n))), 255))
  rhs U32.and(v, 16383)

id BB.vfit2_1 v
  lhs U32.shrn(U32.shrn(U32.and(v, 16383), 7n), 25n)
  rhs 0

id BB.v3f v
  lhs U32.or(0, U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 14n))), 255), 127))
  rhs U32.shrn(U32.and(v, 2097151), 14n)

id BB.v3m1 v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 2097151), 14n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 7n))), 255), 127))
  rhs U32.shrn(U32.and(v, 2097151), 7n)

id BB.v3l v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 2097151), 7n), 7n), U32.and(U32.or(0, U32.and(127, U32.shrn(v, 0n))), 255))
  rhs U32.and(v, 2097151)

id BB.vfit3_1 v
  lhs U32.shrn(U32.shrn(U32.and(v, 2097151), 7n), 25n)
  rhs 0

id BB.vfit3_2 v
  lhs U32.shrn(U32.shrn(U32.and(v, 2097151), 14n), 25n)
  rhs 0

id BB.v4f v
  lhs U32.or(0, U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 21n))), 255), 127))
  rhs U32.shrn(U32.and(v, 268435455), 21n)

id BB.v4m2 v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 268435455), 21n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 14n))), 255), 127))
  rhs U32.shrn(U32.and(v, 268435455), 14n)

id BB.v4m1 v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 268435455), 14n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 7n))), 255), 127))
  rhs U32.shrn(U32.and(v, 268435455), 7n)

id BB.v4l v
  lhs U32.or(U32.shln(U32.shrn(U32.and(v, 268435455), 7n), 7n), U32.and(U32.or(0, U32.and(127, U32.shrn(v, 0n))), 255))
  rhs U32.and(v, 268435455)

id BB.vfit4_1 v
  lhs U32.shrn(U32.shrn(U32.and(v, 268435455), 7n), 25n)
  rhs 0

id BB.vfit4_2 v
  lhs U32.shrn(U32.shrn(U32.and(v, 268435455), 14n), 25n)
  rhs 0

id BB.vfit4_3 v
  lhs U32.shrn(U32.shrn(U32.and(v, 268435455), 21n), 25n)
  rhs 0

id BB.v5f v
  lhs U32.or(0, U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 28n))), 255), 127))
  rhs U32.shrn(v, 28n)

id BB.v5m3 v
  lhs U32.or(U32.shln(U32.shrn(v, 28n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 21n))), 255), 127))
  rhs U32.shrn(v, 21n)

id BB.v5m2 v
  lhs U32.or(U32.shln(U32.shrn(v, 21n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 14n))), 255), 127))
  rhs U32.shrn(v, 14n)

id BB.v5m1 v
  lhs U32.or(U32.shln(U32.shrn(v, 14n), 7n), U32.and(U32.and(U32.or(128, U32.and(127, U32.shrn(v, 7n))), 255), 127))
  rhs U32.shrn(v, 7n)

id BB.v5l v
  lhs U32.or(U32.shln(U32.shrn(v, 7n), 7n), U32.and(U32.or(0, U32.and(127, U32.shrn(v, 0n))), 255))
  rhs v

id BB.vfit5_1 v
  lhs U32.shrn(U32.shrn(v, 7n), 25n)
  rhs 0

id BB.vfit5_2 v
  lhs U32.shrn(U32.shrn(v, 14n), 25n)
  rhs 0

id BB.vfit5_3 v
  lhs U32.shrn(U32.shrn(v, 21n), 25n)
  rhs 0

id BB.vfit5_4 v
  lhs U32.shrn(U32.shrn(v, 28n), 25n)
  rhs 0

id BB.vf1 x
  lhs U32.and(128, U32.and(U32.or(128, U32.and(127, x)), 255))
  rhs 128

id BB.vf0 x
  lhs U32.and(128, U32.and(U32.or(0, U32.and(127, x)), 255))
  rhs 0

id BB.be32 v
  # A big-endian word read back.
  lhs U32.or(U32.shln(U32.or(U32.shln(U32.or(U32.shln(U32.and(U32.shrn(v, 24n), 255), 8n), U32.and(U32.and(U32.shrn(v, 16n), 255), 255)), 8n), U32.and(U32.and(U32.shrn(v, 8n), 255), 255)), 8n), U32.and(U32.and(v, 255), 255))
  rhs v

id BB.sh24 w
  # The top byte of a word, shifted down, is already a byte.
  lhs U32.shrn(w, 24n)
  rhs Y.BP.ext(w, 24n)
