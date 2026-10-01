import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./bits.bend as Z
import ./words.bend as K
import ./copy.bend as C

# The byte comparisons of bytes.bend (B.same, B.fwd1, B.fwd, B.back): each
# answers a count of bytes that agree. Every loop is mirrored by a function
# on trees, then the mirror's count is shown to agree.
#
# Source: proofs/match.bp (tools/bpp.py writes proofs/match.bend from it).

# Words compared
# ==============

# The first n of a list.
def MT.take(+n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      []
    case 1n+p Con{x, r}:
      x <> MT.take(p, r)
    case 1n+p Nil{}:
      []

# How many bytes a comparison of words x and y counts: 4, or the agreeing
# low bytes.
def MT.inc(+x: U32, +y: U32) -> U32:
  B.u32.pick(U32.is_eq(U32.xor(x, y), 0), 4, B.B.low.byte(U32.xor(x, y)))

law MT.not_f:
  for +b: Bool
  for +h: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}

def MT.not_f(b, h):
  match b:
    case True{}:
      {==}
    case False{}:
      P.Bool.true_false({False{} == True{} : Bool}, h)

law MT.ne0:
  for +a: U32
  for +h: {U32.is_ne(a, 0) == False{} : Bool}
  {a == 0 : U32}

def MT.ne0(a, h):
  V.U.is_eq(a, 0, MT.not_f(U32.is_eq(a, 0), h))

law MT.low.c2:
  for +x: U32
  for +y: U32
  for +h0: {U32.and(U32.xor(x, y), 255) == 0 : U32}
  for +h1: {U32.and(U32.xor(x, y), 65535) == 0 : U32}
  for +e0: {U32.is_ne(U32.and(U32.xor(x, y), 255), 0) == False{} : Bool}
  for +e1: {U32.is_ne(U32.and(U32.xor(x, y), 65535), 0) == False{} : Bool}
  for +c2: Bool
  for +e2: {U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0) == c2 : Bool}
  {MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(x)) == MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(y)) : List<&2, U32>}

def MT.low.c2(x, y, h0, h1, e0, e1, c2, e2):
  match c2:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 255), 0), False{}, e0) :
        {MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), False{}, e1) :
        {MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), True{}, e2) :
        {MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(False{}, 1, B.u32.pick(_, 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(False{}, 1, B.u32.pick(_, 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 0n), U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)), Z.BB.xb0(x, y)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == _ <> Y.BP.ext(y, 8n) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 8n), U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n)), Z.BB.xb1(x, y)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)) <> _ <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 0n), Y.BP.ext(U32.and(U32.xor(x, y), 65535), 0n), Z.BB.mk20(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 8n), Y.BP.ext(U32.and(U32.xor(x, y), 65535), 8n), Z.BB.mk21(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.and(U32.xor(x, y), 65535), 0n)) <> U32.xor(Y.BP.ext(x, 8n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.xor(x, y), 65535), 0, h1) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(_, 0n)) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(_, 8n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 0n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(0, 8n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 8n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == U32.xor(Y.BP.ext(x, 0n), 0) <> U32.xor(Y.BP.ext(x, 8n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 0n), 0), Y.BP.ext(x, 0n), Z.BB.xor0(Y.BP.ext(x, 0n))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == _ <> U32.xor(Y.BP.ext(x, 8n), 0) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 8n), 0), Y.BP.ext(x, 8n), Z.BB.xor0(Y.BP.ext(x, 8n))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> [] == Y.BP.ext(x, 0n) <> _ <> [] : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 255), 0), False{}, e0) :
        {MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), False{}, e1) :
        {MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), False{}, e2) :
        {MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(False{}, 1, B.u32.pick(_, 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(False{}, 1, B.u32.pick(_, 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 0n), U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)), Z.BB.xb0(x, y)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == _ <> Y.BP.ext(y, 8n) <> Y.BP.ext(y, 16n) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 8n), U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n)), Z.BB.xb1(x, y)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)) <> _ <> Y.BP.ext(y, 16n) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 16n), U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(U32.xor(x, y), 16n)), Z.BB.xb2(x, y)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n)) <> _ <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 0n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 0n), Z.BB.mk30(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.xor(x, y), 8n)) <> U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(U32.xor(x, y), 16n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 8n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 8n), Z.BB.mk31(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 0n)) <> U32.xor(Y.BP.ext(x, 8n), _) <> U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(U32.xor(x, y), 16n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 16n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 16n), Z.BB.mk32(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 0n)) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(U32.and(U32.xor(x, y), 16777215), 8n)) <> U32.xor(Y.BP.ext(x, 16n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.xor(x, y), 16777215), 0, MT.ne0(U32.and(U32.xor(x, y), 16777215), e2)) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(_, 0n)) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(_, 8n)) <> U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(_, 16n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 0n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> U32.xor(Y.BP.ext(x, 8n), Y.BP.ext(0, 8n)) <> U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(0, 16n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 8n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), 0) <> U32.xor(Y.BP.ext(x, 8n), _) <> U32.xor(Y.BP.ext(x, 16n), Y.BP.ext(0, 16n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 16n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == U32.xor(Y.BP.ext(x, 0n), 0) <> U32.xor(Y.BP.ext(x, 8n), 0) <> U32.xor(Y.BP.ext(x, 16n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 0n), 0), Y.BP.ext(x, 0n), Z.BB.xor0(Y.BP.ext(x, 0n))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == _ <> U32.xor(Y.BP.ext(x, 8n), 0) <> U32.xor(Y.BP.ext(x, 16n), 0) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 8n), 0), Y.BP.ext(x, 8n), Z.BB.xor0(Y.BP.ext(x, 8n))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == Y.BP.ext(x, 0n) <> _ <> U32.xor(Y.BP.ext(x, 16n), 0) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 16n), 0), Y.BP.ext(x, 16n), Z.BB.xor0(Y.BP.ext(x, 16n))) :
        {Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> Y.BP.ext(x, 16n) <> [] == Y.BP.ext(x, 0n) <> Y.BP.ext(x, 8n) <> _ <> [] : List<&2, U32>}
      {==}

law MT.low.c1:
  for +x: U32
  for +y: U32
  for +h0: {U32.and(U32.xor(x, y), 255) == 0 : U32}
  for +e0: {U32.is_ne(U32.and(U32.xor(x, y), 255), 0) == False{} : Bool}
  for +c1: Bool
  for +e1: {U32.is_ne(U32.and(U32.xor(x, y), 65535), 0) == c1 : Bool}
  {MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(x)) == MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(y)) : List<&2, U32>}

def MT.low.c1(x, y, h0, e0, c1, e1):
  match c1:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 255), 0), False{}, e0) :
        {MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), True{}, e1) :
        {MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(False{}, 0, B.u32.pick(_, 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(y, 0n), U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(U32.xor(x, y), 0n)), Z.BB.xb0(x, y)) :
        {Y.BP.ext(x, 0n) <> [] == _ <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(U32.xor(x, y), 0n), Y.BP.ext(U32.and(U32.xor(x, y), 255), 0n), Z.BB.mk10(U32.xor(x, y))) :
        {Y.BP.ext(x, 0n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.xor(x, y), 255), 0, h0) :
        {Y.BP.ext(x, 0n) <> [] == U32.xor(Y.BP.ext(x, 0n), Y.BP.ext(_, 0n)) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(0, 0n), 0, {==}) :
        {Y.BP.ext(x, 0n) <> [] == U32.xor(Y.BP.ext(x, 0n), _) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.xor(Y.BP.ext(x, 0n), 0), Y.BP.ext(x, 0n), Z.BB.xor0(Y.BP.ext(x, 0n))) :
        {Y.BP.ext(x, 0n) <> [] == _ <> [] : List<&2, U32>}
      {==}
    case False{}:
      MT.low.c2(x, y, h0, MT.ne0(U32.and(U32.xor(x, y), 65535), e1), e0, e1, U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), {==})

law MT.low.c0:
  for +x: U32
  for +y: U32
  for +c0: Bool
  for +e0: {U32.is_ne(U32.and(U32.xor(x, y), 255), 0) == c0 : Bool}
  {MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(x)) == MT.take(V.U.N(B.B.low.byte(U32.xor(x, y))), K.WD.w4(y)) : List<&2, U32>}

def MT.low.c0(x, y, c0, e0):
  match c0:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(U32.and(U32.xor(x, y), 255), 0), True{}, e0) :
        {MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)))), K.WD.w4(y)) : List<&2, U32>}
      {==}
    case False{}:
      MT.low.c1(x, y, MT.ne0(U32.and(U32.xor(x, y), 255), e0), e0, U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), {==})

law MT.cmp4.s:
  for +x: U32
  for +y: U32
  for +s: Bool
  for +es: {U32.is_eq(U32.xor(x, y), 0) == s : Bool}
  {MT.take(V.U.N(MT.inc(x, y)), K.WD.w4(x)) == MT.take(V.U.N(MT.inc(x, y)), K.WD.w4(y)) : List<&2, U32>}

def MT.cmp4.s(x, y, s, es):
  match s:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(U32.xor(x, y), 0), True{}, es) :
        {MT.take(V.U.N(B.u32.pick(_, 4, B.B.low.byte(U32.xor(x, y)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 4, B.B.low.byte(U32.xor(x, y)))), K.WD.w4(y)) : List<&2, U32>}
      %Equal.sym(U32, y, U32.xor(x, U32.xor(x, y)), Z.BB.xxy(x, y)) :
        {MT.take(4n, K.WD.w4(x)) == MT.take(4n, K.WD.w4(_)) : List<&2, U32>}
      %Equal.sym(U32, U32.xor(x, y), 0, V.U.is_eq(U32.xor(x, y), 0, es)) :
        {MT.take(4n, K.WD.w4(x)) == MT.take(4n, K.WD.w4(U32.xor(x, _))) : List<&2, U32>}
      %Equal.sym(U32, U32.xor(x, 0), x, Z.BB.xor0(x)) :
        {MT.take(4n, K.WD.w4(x)) == MT.take(4n, K.WD.w4(_)) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(U32.xor(x, y), 0), False{}, es) :
        {MT.take(V.U.N(B.u32.pick(_, 4, B.B.low.byte(U32.xor(x, y)))), K.WD.w4(x)) == MT.take(V.U.N(B.u32.pick(_, 4, B.B.low.byte(U32.xor(x, y)))), K.WD.w4(y)) : List<&2, U32>}
      MT.low.c0(x, y, U32.is_ne(U32.and(U32.xor(x, y), 255), 0), {==})

# The bytes a word comparison counts agree.
law MT.cmp4:
  for +x: U32
  for +y: U32
  {MT.take(V.U.N(MT.inc(x, y)), K.WD.w4(x)) == MT.take(V.U.N(MT.inc(x, y)), K.WD.w4(y)) : List<&2, U32>}

def MT.cmp4(x, y):
  MT.cmp4.s(x, y, U32.is_eq(U32.xor(x, y), 0), {==})

# Prefixes
# ========

law MT.take_sl:
  for +k: Nat
  for +n: Nat
  for +t: A.Tr
  for +p: U32
  for +h: {Cmp.is_le(Nat.cmp(k, n)) == True{} : Bool}
  {MT.take(k, S.S.sl(n, t, p)) == S.S.sl(k, t, p) : List<&2, U32>}

def MT.take_sl(k, n, t, p, h):
  match k n:
    case 0n _:
      {==}
    case 1n+a 0n:
      P.Bool.false_true({MT.take(1n+a, S.S.sl(0n, t, p)) == S.S.sl(1n+a, t, p) : List<&2, U32>}, h)
    case 1n+a 1n+b:
      %Equal.sym(List<&2, U32>, MT.take(a, S.S.sl(b, t, U32.add(p, 1))), S.S.sl(a, t, U32.add(p, 1)), MT.take_sl(a, b, t, U32.add(p, 1), h)) :
        {Y.BP.byt(t, p) <> _ == Y.BP.byt(t, p) <> S.S.sl(a, t, U32.add(p, 1)) : List<&2, U32>}
      {==}

law MT.take_rep:
  for +k: Nat
  for +n: Nat
  for +c: U32
  for +h: {Cmp.is_le(Nat.cmp(k, n)) == True{} : Bool}
  {MT.take(k, C.CP.rep(n, c)) == C.CP.rep(k, c) : List<&2, U32>}

def MT.take_rep(k, n, c, h):
  match k n:
    case 0n _:
      {==}
    case 1n+a 0n:
      P.Bool.false_true({MT.take(1n+a, C.CP.rep(0n, c)) == C.CP.rep(1n+a, c) : List<&2, U32>}, h)
    case 1n+a 1n+b:
      %Equal.sym(List<&2, U32>, MT.take(a, C.CP.rep(b, c)), C.CP.rep(a, c), MT.take_rep(a, b, c, h)) :
        {c <> _ == c <> C.CP.rep(a, c) : List<&2, U32>}
      {==}

law MT.take_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {MT.take(S.S.len(xs), K.WD.app(xs, ys)) == xs : List<&2, U32>}

def MT.take_app(xs, ys):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(List<&2, U32>, MT.take(S.S.len(r), K.WD.app(r, ys)), r, MT.take_app(r, ys)) :
        {x <> _ == x <> r : List<&2, U32>}
      {==}

# The first r bytes agree when the first n do.
law MT.pre:
  for +r: Nat
  for +n: Nat
  for +t: A.Tr
  for +i: U32
  for +ys: List<&2, U32>
  for +hr: {Cmp.is_le(Nat.cmp(r, n)) == True{} : Bool}
  for +h: {S.S.sl(n, t, i) == ys : List<&2, U32>}
  {S.S.sl(r, t, i) == MT.take(r, ys) : List<&2, U32>}

def MT.pre(r, n, t, i, ys, hr, h):
  %h :
    {S.S.sl(r, t, i) == MT.take(r, _) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MT.take(r, S.S.sl(n, t, i)), S.S.sl(r, t, i), MT.take_sl(r, n, t, i, hr)) :
    {S.S.sl(r, t, i) == _ : List<&2, U32>}
  {==}

law MT.pick_le:
  for +c: Bool
  for +a: U32
  for +b: U32
  for +n: Nat
  for +ha: {Cmp.is_le(Nat.cmp(V.U.N(a), n)) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(V.U.N(b), n)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(B.u32.pick(c, a, b)), n)) == True{} : Bool}

def MT.pick_le(c, a, b, n, ha, hb):
  match c:
    case True{}:
      ha
    case False{}:
      hb

# A comparison counts 4 bytes at most.
law MT.inc_le:
  for +x: U32
  for +y: U32
  {Cmp.is_le(Nat.cmp(V.U.N(MT.inc(x, y)), 4n)) == True{} : Bool}

def MT.inc_le(x, y):
  MT.pick_le(U32.is_eq(U32.xor(x, y), 0), 4, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 255), 0), 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3))), 4n, {==},
    MT.pick_le(U32.is_ne(U32.and(U32.xor(x, y), 255), 0), 0, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3)), 4n, {==},
      MT.pick_le(U32.is_ne(U32.and(U32.xor(x, y), 65535), 0), 1, B.u32.pick(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3), 4n, {==},
        MT.pick_le(U32.is_ne(U32.and(U32.xor(x, y), 16777215), 0), 2, 3, 4n, {==}, {==}))))

# The four bytes of a run word.
law MT.rep4w:
  for +b: U32
  {K.WD.w4(B.B.rep4(b)) == C.CP.rep(4n, U32.and(b, 255)) : List<&2, U32>}

def MT.rep4w(b):
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(b), 0n), U32.and(b, 255), Z.BB.rep4_0(b)) :
    {_ <> Y.BP.ext(B.B.rep4(b), 8n) <> Y.BP.ext(B.B.rep4(b), 16n) <> Y.BP.ext(B.B.rep4(b), 24n) <> [] == C.CP.rep(4n, U32.and(b, 255)) : List<&2, U32>}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(b), 8n), U32.and(b, 255), Z.BB.rep4_1(b)) :
    {U32.and(b, 255) <> _ <> Y.BP.ext(B.B.rep4(b), 16n) <> Y.BP.ext(B.B.rep4(b), 24n) <> [] == C.CP.rep(4n, U32.and(b, 255)) : List<&2, U32>}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(b), 16n), U32.and(b, 255), Z.BB.rep4_2(b)) :
    {U32.and(b, 255) <> U32.and(b, 255) <> _ <> Y.BP.ext(B.B.rep4(b), 24n) <> [] == C.CP.rep(4n, U32.and(b, 255)) : List<&2, U32>}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(b), 24n), U32.and(b, 255), Z.BB.rep4_3(b)) :
    {U32.and(b, 255) <> U32.and(b, 255) <> U32.and(b, 255) <> _ <> [] == C.CP.rep(4n, U32.and(b, 255)) : List<&2, U32>}
  {==}

# A comparison loop
# =================

# The bytes compared against: a tree's from j, or copies of a byte.
type MS is Data:
  MW{t: A.Tr, j: U32}
  MR{b: U32}

# The word at p, as B.word reads it.
def MT.W(+t: A.Tr, +p: U32) -> U32:
  B.B.join(A.T.word(t, U32.shrn(p, 2n)), A.T.word(t, U32.add(U32.shrn(p, 2n), 1)), B.B.sh(p))

law MT.word:
  for +t: A.Tr
  for +p: U32
  {B.B.word(A.A.from(t), p) == (A.A.from(t), MT.W(t, p)) : Array<U32> & U32}

def MT.word(t, p):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.shrn(p, 2n)), (A.A.from(t), A.T.word(t, U32.shrn(p, 2n))), A.A.get_from(t, U32.shrn(p, 2n))) :
    {B.B.word.k1(p, _) == (A.A.from(t), MT.W(t, p)) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.add(U32.shrn(p, 2n), 1)), (A.A.from(t), A.T.word(t, U32.add(U32.shrn(p, 2n), 1))), A.A.get_from(t, U32.add(U32.shrn(p, 2n), 1))) :
    {B.B.word.k2(B.B.sh(p), A.T.word(t, U32.shrn(p, 2n)), _) == (A.A.from(t), MT.W(t, p)) : Array<U32> & U32}
  {==}

# The word compared against, n bytes on.
def MT.yw(+s: MS, +n: U32) -> U32:
  match s:
    case MW{t, j}:
      MT.W(t, U32.add(j, n))
    case MR{b}:
      B.B.rep4(b)

# The k bytes compared against, n bytes on.
def MT.yo(+s: MS, +k: Nat, +n: U32) -> List<&2, U32>:
  match s:
    case MW{t, j}:
      S.S.sl(k, t, U32.add(j, n))
    case MR{b}:
      C.CP.rep(k, U32.and(b, 255))

# The first k bytes compared against.
def MT.yl(+s: MS, +k: Nat) -> List<&2, U32>:
  match s:
    case MW{t, j}:
      S.S.sl(k, t, j)
    case MR{b}:
      C.CP.rep(k, U32.and(b, 255))

# The count and the flag after comparing the words n bytes on.
def MT.cn(+ta: A.Tr, +i: U32, +s: MS, +n: U32) -> U32:
  U32.add(n, MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)))

def MT.cf(+ta: A.Tr, +i: U32, +s: MS, +max: U32, +n: U32) -> Bool:
  Bool.and(U32.is_eq(U32.xor(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), 0), U32.is_lt(U32.add(n, 4), max))

# The loop: ta's bytes from i against s, up to max.
def MT.cs(+k: Nat, +ta: A.Tr, +i: U32, +s: MS, +max: U32, +f: Bool, +n: U32) -> U32:
  match k f:
    case 0n _:
      U32.min(n, max)
    case 1n+p False{}:
      U32.min(n, max)
    case 1n+p True{}:
      MT.cs(p, ta, i, s, max, MT.cf(ta, i, s, max, n), MT.cn(ta, i, s, n))

# Runs and target matches
# =======================

law MT.same.loop:
  for +k: Nat
  for +t: A.Tr
  for +i: U32
  for +b: U32
  for +max: U32
  for +f: Bool
  for +n: U32
  {B.B.same.loop(k, i, B.B.rep4(b), max, (f, (n, A.A.from(t)))) == (A.A.from(t), MT.cs(k, t, i, MR{b}, max, f, n)) : Array<U32> & U32}

def MT.same.loop(k, t, i, b, max, f, n):
  match k f:
    case 0n _:
      {==}
    case 1n+p False{}:
      {==}
    case 1n+p True{}:
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), U32.add(i, n)), (A.A.from(t), MT.W(t, U32.add(i, n))), MT.word(t, U32.add(i, n))) :
        {B.B.same.loop(p, i, B.B.rep4(b), max, B.B.same.k(n, max, B.B.rep4(b), _)) == (A.A.from(t), MT.cs(p, t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, n), MT.cn(t, i, MR{b}, n))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.same.loop(p, i, B.B.rep4(b), max, (Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), U32.is_lt(U32.add(n, 4), max)), (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b))))), A.A.from(t)))), (A.A.from(t), MT.cs(p, t, i, MR{b}, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b))))))), MT.same.loop(p, t, i, b, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), B.B.rep4(b))))))) :
        {_ == (A.A.from(t), MT.cs(p, t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, n), MT.cn(t, i, MR{b}, n))) : Array<U32> & U32}
      {==}

law MT.fwd1.loop:
  for +k: Nat
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +max: U32
  for +f: Bool
  for +n: U32
  {B.B.fwd1.loop(k, i, j, max, (f, (n, A.A.from(t)))) == (A.A.from(t), MT.cs(k, t, i, MW{t, j}, max, f, n)) : Array<U32> & U32}

def MT.fwd1.loop(k, t, i, j, max, f, n):
  match k f:
    case 0n _:
      {==}
    case 1n+p False{}:
      {==}
    case 1n+p True{}:
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), U32.add(i, n)), (A.A.from(t), MT.W(t, U32.add(i, n))), MT.word(t, U32.add(i, n))) :
        {B.B.fwd1.loop(p, i, j, max, B.B.fwd1.k2(j, n, max, _)) == (A.A.from(t), MT.cs(p, t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, n), MT.cn(t, i, MW{t, j}, n))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), U32.add(j, n)), (A.A.from(t), MT.W(t, U32.add(j, n))), MT.word(t, U32.add(j, n))) :
        {B.B.fwd1.loop(p, i, j, max, B.B.fwd1.k3(n, max, MT.W(t, U32.add(i, n)), _)) == (A.A.from(t), MT.cs(p, t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, n), MT.cn(t, i, MW{t, j}, n))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.fwd1.loop(p, i, j, max, (Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), U32.is_lt(U32.add(n, 4), max)), (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n)))))), A.A.from(t)))), (A.A.from(t), MT.cs(p, t, i, MW{t, j}, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n)))))))), MT.fwd1.loop(p, t, i, j, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, n)), MT.W(t, U32.add(j, n)))))))) :
        {_ == (A.A.from(t), MT.cs(p, t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, n), MT.cn(t, i, MW{t, j}, n))) : Array<U32> & U32}
      {==}

# The count is right
# ==================

law MT.min_le.go:
  for +a: U32
  for +b: U32
  for +c: Bool
  for +ec: {U32.is_lt(a, b) == c : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(a, b)), V.U.N(a))) == True{} : Bool}

def MT.min_le.go(a, b, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(a))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), True{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, a, b)), V.U.N(a))) == True{} : Bool}
      C.CP.le_refl(V.U.N(a))
    case False{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(a))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), False{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, a, b)), V.U.N(a))) == True{} : Bool}
      V.U.le_N(b, a, V.U.not_lt(a, b, ec))

law MT.min_le:
  for +a: U32
  for +b: U32
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(a, b)), V.U.N(a))) == True{} : Bool}

def MT.min_le(a, b):
  MT.min_le.go(a, b, U32.is_lt(a, b), {==})

law MT.min_le_r.go:
  for +a: U32
  for +b: U32
  for +c: Bool
  for +ec: {U32.is_lt(a, b) == c : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(a, b)), V.U.N(b))) == True{} : Bool}

def MT.min_le_r.go(a, b, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(b))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), True{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, a, b)), V.U.N(b))) == True{} : Bool}
      P.Nat.lt_to_le(V.U.N(a), V.U.N(b), V.U.lt_N(a, b, ec))
    case False{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(b))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), False{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, a, b)), V.U.N(b))) == True{} : Bool}
      C.CP.le_refl(V.U.N(b))

law MT.min_le_r:
  for +a: U32
  for +b: U32
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(a, b)), V.U.N(b))) == True{} : Bool}

def MT.min_le_r(a, b):
  MT.min_le_r.go(a, b, U32.is_lt(a, b), {==})

law MT.take_yl:
  for +s: MS
  for +r: Nat
  for +n: Nat
  for +h: {Cmp.is_le(Nat.cmp(r, n)) == True{} : Bool}
  {MT.take(r, MT.yl(s, n)) == MT.yl(s, r) : List<&2, U32>}

def MT.take_yl(s, r, n, h):
  match s:
    case MW{t, j}:
      MT.take_sl(r, n, t, j, h)
    case MR{b}:
      MT.take_rep(r, n, U32.and(b, 255), h)

law MT.take_yo:
  for +s: MS
  for +r: Nat
  for +n: Nat
  for +p: U32
  for +h: {Cmp.is_le(Nat.cmp(r, n)) == True{} : Bool}
  {MT.take(r, MT.yo(s, n, p)) == MT.yo(s, r, p) : List<&2, U32>}

def MT.take_yo(s, r, n, p, h):
  match s:
    case MW{t, j}:
      MT.take_sl(r, n, t, U32.add(j, p), h)
    case MR{b}:
      MT.take_rep(r, n, U32.and(b, 255), h)

law MT.yl_app:
  for +s: MS
  for +n: U32
  for +k: Nat
  {MT.yl(s, Nat.add(V.U.N(n), k)) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, k, n)) : List<&2, U32>}

def MT.yl_app(s, n, k):
  match s:
    case MW{t, j}:
      K.WD.sl_app(V.U.N(n), k, t, j, n, {==})
    case MR{b}:
      C.CP.rep_app(V.U.N(n), k, U32.and(b, 255))

# The second source's bytes n on stay inside E.
def MT.okn(+s: MS, +n: U32, +E: U32) -> Bool:
  match s:
    case MW{t, j}:
      Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(n)), 4n), V.U.N(E)))
    case MR{b}:
      True{}

law MT.b4:
  for +j: U32
  for +n: U32
  for +E: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(n)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(U32.add(j, n))), V.U.N(E))) == True{} : Bool}

law MT.le_tail0:
  for +a: Nat
  for +b: Nat
  for +e: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(a, b), e)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(a, e)) == True{} : Bool}

def MT.le_tail0(a, b, e, h):
  P.Nat.le_trans(a, Nat.add(a, b), e, P.Nat.cmp_add_r(a, b), h)

def MT.b4(j, n, E, h):
  %Equal.sym(Nat, V.U.N(U32.add(j, n)), Nat.add(V.U.N(j), V.U.N(n)), V.U.add_N(j, n, E, MT.le_tail0(Nat.add(V.U.N(j), V.U.N(n)), 4n, V.U.N(E), h))) :
    {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(E))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(4n, Nat.add(V.U.N(j), V.U.N(n))), Nat.add(Nat.add(V.U.N(j), V.U.N(n)), 4n), P.Nat.add_comm(4n, Nat.add(V.U.N(j), V.U.N(n)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}
  h

law MT.yw4:
  for +s: MS
  for +n: U32
  for +E: U32
  for +h: {MT.okn(s, n, E) == True{} : Bool}
  {K.WD.w4(MT.yw(s, n)) == MT.yo(s, 4n, n) : List<&2, U32>}

def MT.yw4(s, n, E, h):
  match s:
    case MW{t, j}:
      K.WD.join(t, U32.add(j, n), E, MT.b4(j, n, E, h))
    case MR{b}:
      MT.rep4w(b)

law MT.cstep.b:
  for +n: U32
  for +k: U32
  for +E: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), 4n), V.U.N(E))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), 4n)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), V.U.N(E))) == True{} : Bool}

def MT.cstep.b(n, k, E, h, hk):
  P.Nat.le_trans(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), 4n), V.U.N(E),
    (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), 4n)), Nat.cmp(V.U.N(k), 4n), P.Nat.cmp_add_l(V.U.N(n), V.U.N(k), 4n)) : {Cmp.is_le(_) == True{} : Bool}; hk), h)

# One comparison: the bytes so far, then the ones it counts.
law MT.cstep:
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +n: U32
  for +E: U32
  for +hs: {S.S.sl(V.U.N(n), ta, i) == MT.yl(s, V.U.N(n)) : List<&2, U32>}
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(n)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbs: {MT.okn(s, n, E) == True{} : Bool}
  {S.S.sl(V.U.N(MT.cn(ta, i, s, n)), ta, i) == MT.yl(s, V.U.N(MT.cn(ta, i, s, n))) : List<&2, U32>}

law MT.nb:
  for +i: U32
  for +n: U32
  for +E: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(n)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), 4n), V.U.N(E))) == True{} : Bool}

def MT.nb(i, n, E, h):
  P.Nat.le_trans(Nat.add(V.U.N(n), 4n), Nat.add(Nat.add(V.U.N(i), V.U.N(n)), 4n), V.U.N(E),
    C.CP.le_add_r(V.U.N(n), Nat.add(V.U.N(i), V.U.N(n)), 4n, P.Nat.le_add_l(V.U.N(i), V.U.N(n))), h)

def MT.cstep(ta, i, s, n, E, hs, hbi, hbs):
  %Equal.sym(Nat, V.U.N(U32.add(n, MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)))), Nat.add(V.U.N(n), V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)))), V.U.add_N(n, MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), E, MT.cstep.b(n, MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), E, MT.nb(i, n, E, hbi), MT.inc_le(MT.W(ta, U32.add(i, n)), MT.yw(s, n))))) :
    {S.S.sl(_, ta, i) == MT.yl(s, _) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(Nat.add(V.U.N(n), V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)))), ta, i), K.WD.app(S.S.sl(V.U.N(n), ta, i), S.S.sl(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), ta, U32.add(i, n))), K.WD.sl_app(V.U.N(n), V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), ta, i, n, {==})) :
    {_ == MT.yl(s, Nat.add(V.U.N(n), V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MT.yl(s, Nat.add(V.U.N(n), V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))))), K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)), MT.yl_app(s, n, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))))) :
    {K.WD.app(S.S.sl(V.U.N(n), ta, i), S.S.sl(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), ta, U32.add(i, n))) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(n), ta, i), MT.yl(s, V.U.N(n)), hs) :
    {K.WD.app(_, S.S.sl(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), ta, U32.add(i, n))) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  %MT.take_sl(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), 4n, ta, U32.add(i, n), MT.inc_le(MT.W(ta, U32.add(i, n)), MT.yw(s, n))) :
    {K.WD.app(MT.yl(s, V.U.N(n)), _) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  %K.WD.join(ta, U32.add(i, n), E, MT.b4(i, n, E, hbi)) :
    {K.WD.app(MT.yl(s, V.U.N(n)), MT.take(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), _)) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MT.take(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), K.WD.w4(MT.W(ta, U32.add(i, n)))), MT.take(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), K.WD.w4(MT.yw(s, n))), MT.cmp4(MT.W(ta, U32.add(i, n)), MT.yw(s, n))) :
    {K.WD.app(MT.yl(s, V.U.N(n)), _) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, K.WD.w4(MT.yw(s, n)), MT.yo(s, 4n, n), MT.yw4(s, n, E, hbs)) :
    {K.WD.app(MT.yl(s, V.U.N(n)), MT.take(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), _)) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MT.take(V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), MT.yo(s, 4n, n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n), MT.take_yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), 4n, n, MT.inc_le(MT.W(ta, U32.add(i, n)), MT.yw(s, n)))) :
    {K.WD.app(MT.yl(s, V.U.N(n)), _) == K.WD.app(MT.yl(s, V.U.N(n)), MT.yo(s, V.U.N(MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n))), n)) : List<&2, U32>}
  {==}

law MT.flag.c:
  for +same: Bool
  for +n: U32
  for +k: U32
  for +max: U32
  for +E: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), 4n)) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), 4n), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(U32.add(n, 4), max) == c : Bool}
  {Bool.and(Bool.and(same, U32.is_lt(U32.add(n, 4), max)), Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}

law MT.flag.le:
  for +n: U32
  for +k: U32
  for +E: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), 4n)) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(U32.add(n, 4)))) == True{} : Bool}

def MT.flag.le(n, k, E, hk, hn):
  %Equal.sym(Nat, V.U.N(U32.add(n, k)), Nat.add(V.U.N(n), V.U.N(k)), V.U.add_N(n, k, E, MT.cstep.b(n, k, E, hn, hk))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(U32.add(n, 4)))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(n, 4)), Nat.add(V.U.N(n), 4n), V.U.add_N(n, 4, E, hn)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), 4n)), Nat.cmp(V.U.N(k), 4n), P.Nat.cmp_add_l(V.U.N(n), V.U.N(k), 4n)) :
    {Cmp.is_le(_) == True{} : Bool}
  hk

def MT.flag.c(same, n, k, max, E, hk, hn, c, ec):
  match c:
    case False{}:
      %Equal.sym(Bool, U32.is_lt(U32.add(n, 4), max), False{}, ec) :
        {Bool.and(Bool.and(same, _), Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, False{}), False{}, P.Bool.and_false(same)) :
        {Bool.and(_, Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}
      {==}
    case True{}:
      %Equal.sym(Cmp, Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max)), LT{}, P.Nat.le_lt_trans(V.U.N(U32.add(n, k)), V.U.N(U32.add(n, 4)), V.U.N(max), MT.flag.le(n, k, E, hk, hn), V.U.lt_N(U32.add(n, 4), max, ec))) :
        {Bool.and(Bool.and(same, U32.is_lt(U32.add(n, 4), max)), Bool.not(Cmp.is_lt(_))) == False{} : Bool}
      %Equal.sym(Bool, U32.is_lt(U32.add(n, 4), max), True{}, ec) :
        {Bool.and(Bool.and(same, _), Bool.not(Cmp.is_lt(LT{}))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, True{}), same, P.Bool.and_true(same)) :
        {Bool.and(_, Bool.not(Cmp.is_lt(LT{}))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, False{}), False{}, P.Bool.and_false(same)) :
        {_ == False{} : Bool}
      {==}

# The flag of the next comparison: on only below max.
law MT.flag:
  for +same: Bool
  for +n: U32
  for +k: U32
  for +max: U32
  for +E: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), 4n)) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), 4n), V.U.N(E))) == True{} : Bool}
  {Bool.and(Bool.and(same, U32.is_lt(U32.add(n, 4), max)), Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}

def MT.flag(same, n, k, max, E, hk, hn):
  MT.flag.c(same, n, k, max, E, hk, hn, U32.is_lt(U32.add(n, 4), max), {==})

law MT.ib:
  for +i: U32
  for +n: U32
  for +max: U32
  for +E: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(max))) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(n)), 4n), V.U.N(E))) == True{} : Bool}

def MT.ib(i, n, max, E, hn, h):
  P.Nat.le_trans(Nat.add(Nat.add(V.U.N(i), V.U.N(n)), 4n), Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E),
    C.CP.le_add_r(Nat.add(V.U.N(i), V.U.N(n)), Nat.add(V.U.N(i), V.U.N(max)), 4n,
      (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(i), V.U.N(n)), Nat.add(V.U.N(i), V.U.N(max))), Nat.cmp(V.U.N(n), V.U.N(max)), P.Nat.cmp_add_l(V.U.N(i), V.U.N(n), V.U.N(max))) : {Cmp.is_le(_) == True{} : Bool}; hn)), h)

law MT.okn_le:
  for +s: MS
  for +n: U32
  for +max: U32
  for +E: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(max))) == True{} : Bool}
  for +h: {MT.okn(s, max, E) == True{} : Bool}
  {MT.okn(s, n, E) == True{} : Bool}

def MT.okn_le(s, n, max, E, hn, h):
  match s:
    case MW{t, j}:
      MT.ib(j, n, max, E, hn, h)
    case MR{b}:
      {==}

law MT.cs_fin:
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +n: U32
  for +max: U32
  for +hs: {S.S.sl(V.U.N(n), ta, i) == MT.yl(s, V.U.N(n)) : List<&2, U32>}
  {S.S.sl(V.U.N(U32.min(n, max)), ta, i) == MT.yl(s, V.U.N(U32.min(n, max))) : List<&2, U32>}

def MT.cs_fin(ta, i, s, n, max, hs):
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(U32.min(n, max)), ta, i), MT.take(V.U.N(U32.min(n, max)), MT.yl(s, V.U.N(n))), MT.pre(V.U.N(U32.min(n, max)), V.U.N(n), ta, i, MT.yl(s, V.U.N(n)), MT.min_le(n, max), hs)) :
    {_ == MT.yl(s, V.U.N(U32.min(n, max))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MT.take(V.U.N(U32.min(n, max)), MT.yl(s, V.U.N(n))), MT.yl(s, V.U.N(U32.min(n, max))), MT.take_yl(s, V.U.N(U32.min(n, max)), V.U.N(n), MT.min_le(n, max))) :
    {_ == MT.yl(s, V.U.N(U32.min(n, max))) : List<&2, U32>}
  {==}

# The loop's count: that many bytes agree.
law MT.cs_ok:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +max: U32
  for +f: Bool
  for +n: U32
  for +E: U32
  for +hs: {S.S.sl(V.U.N(n), ta, i) == MT.yl(s, V.U.N(n)) : List<&2, U32>}
  for +hf: {Bool.and(f, Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))))) == False{} : Bool}
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbs: {MT.okn(s, max, E) == True{} : Bool}
  {S.S.sl(V.U.N(MT.cs(k, ta, i, s, max, f, n)), ta, i) == MT.yl(s, V.U.N(MT.cs(k, ta, i, s, max, f, n))) : List<&2, U32>}

law MT.lt_le:
  for +n: U32
  for +max: U32
  for +hf: {Bool.and(True{}, Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))))) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(max))) == True{} : Bool}

def MT.lt_le(n, max, hf):
  P.Nat.lt_to_le(V.U.N(n), V.U.N(max), P.Cmp.is_lt_lt(Nat.cmp(V.U.N(n), V.U.N(max)), MT.not_f(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))), hf)))

def MT.cs_ok(k, ta, i, s, max, f, n, E, hs, hf, hbi, hbs):
  match k f:
    case 0n _:
      MT.cs_fin(ta, i, s, n, max, hs)
    case 1n+p False{}:
      MT.cs_fin(ta, i, s, n, max, hs)
    case 1n+p True{}:
      MT.cs_ok(p, ta, i, s, max, MT.cf(ta, i, s, max, n), MT.cn(ta, i, s, n), E,
        MT.cstep(ta, i, s, n, E, hs, MT.ib(i, n, max, E, MT.lt_le(n, max, hf), hbi), MT.okn_le(s, n, max, E, MT.lt_le(n, max, hf), hbs)),
        MT.flag(U32.is_eq(U32.xor(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), 0), n, MT.inc(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), max, E,
          MT.inc_le(MT.W(ta, U32.add(i, n)), MT.yw(s, n)), MT.nb(i, n, E, MT.ib(i, n, max, E, MT.lt_le(n, max, hf), hbi))),
        hbi, hbs)

# The loop's count is at most max.
law MT.cs_le:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +max: U32
  for +f: Bool
  for +n: U32
  {Cmp.is_le(Nat.cmp(V.U.N(MT.cs(k, ta, i, s, max, f, n)), V.U.N(max))) == True{} : Bool}

def MT.cs_le(k, ta, i, s, max, f, n):
  match k f:
    case 0n _:
      MT.min_le_r(n, max)
    case 1n+p False{}:
      MT.min_le_r(n, max)
    case 1n+p True{}:
      MT.cs_le(p, ta, i, s, max, MT.cf(ta, i, s, max, n), MT.cn(ta, i, s, n))

law MT.W0:
  for +t: A.Tr
  for +i: U32
  {MT.W(t, i) == MT.W(t, U32.add(i, 0)) : U32}

def MT.W0(t, i):
  %Equal.sym(U32, U32.add(i, 0), i, V.U.add_zero_r(i)) :
    {MT.W(t, i) == MT.W(t, _) : U32}
  {==}

law MT.yl0:
  for +s: MS
  {S.S.sl(0n, A.TL{0}, 0) == MT.yl(s, 0n) : List<&2, U32>}

def MT.yl0(s):
  match s:
    case MW{t, j}:
      {==}
    case MR{b}:
      {==}

# A loop from 0: its count of bytes agree, and is at most max.
law MT.cs0_ok:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +max: U32
  for +E: U32
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbs: {MT.okn(s, max, E) == True{} : Bool}
  {S.S.sl(V.U.N(MT.cs(k, ta, i, s, max, MT.cf(ta, i, s, max, 0), MT.cn(ta, i, s, 0))), ta, i) == MT.yl(s, V.U.N(MT.cs(k, ta, i, s, max, MT.cf(ta, i, s, max, 0), MT.cn(ta, i, s, 0)))) : List<&2, U32>}

def MT.cs0_ok(k, ta, i, s, max, E, hbi, hbs):
  MT.cs_ok(k, ta, i, s, max, MT.cf(ta, i, s, max, 0), MT.cn(ta, i, s, 0), E,
    MT.cstep(ta, i, s, 0, E, MT.yl0(s), MT.ib(i, 0, max, E, P.Nat.le_zero(V.U.N(max)), hbi), MT.okn_le(s, 0, max, E, P.Nat.le_zero(V.U.N(max)), hbs)),
    MT.flag(U32.is_eq(U32.xor(MT.W(ta, U32.add(i, 0)), MT.yw(s, 0)), 0), 0, MT.inc(MT.W(ta, U32.add(i, 0)), MT.yw(s, 0)), max, E,
      MT.inc_le(MT.W(ta, U32.add(i, 0)), MT.yw(s, 0)), MT.nb(i, 0, E, MT.ib(i, 0, max, E, P.Nat.le_zero(V.U.N(max)), hbi))),
    hbi, hbs)

# B.same and B.fwd1 count as the loop from 0 does.
law MT.same:
  for +t: A.Tr
  for +i: U32
  for +b: U32
  for +max: U32
  {B.B.same(A.A.from(t), i, b, max) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, 0), MT.cn(t, i, MR{b}, 0))) : Array<U32> & U32}

def MT.same(t, i, b, max):
  %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), i), (A.A.from(t), MT.W(t, i)), MT.word(t, i)) :
    {B.B.same.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, B.B.rep4(b), max, B.B.same.k(0, max, B.B.rep4(b), _)) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, 0), MT.cn(t, i, MR{b}, 0))) : Array<U32> & U32}
  %Equal.sym(U32, MT.W(t, i), MT.W(t, U32.add(i, 0)), MT.W0(t, i)) :
    {B.B.same.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, B.B.rep4(b), max, B.B.same.k(0, max, B.B.rep4(b), (A.A.from(t), _))) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, 0), MT.cn(t, i, MR{b}, 0))) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, B.B.same.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, B.B.rep4(b), max, (Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), U32.is_lt(4, max)), (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b))))), A.A.from(t)))), (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MR{b}, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b))))))), MT.same.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, b, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b)), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), B.B.rep4(b))))))) :
    {_ == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MR{b}, max, MT.cf(t, i, MR{b}, max, 0), MT.cn(t, i, MR{b}, 0))) : Array<U32> & U32}
  {==}

law MT.fwd1:
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +max: U32
  {B.B.fwd1(A.A.from(t), i, j, max) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, 0), MT.cn(t, i, MW{t, j}, 0))) : Array<U32> & U32}

def MT.fwd1(t, i, j, max):
  %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), U32.add(i, 0)), (A.A.from(t), MT.W(t, U32.add(i, 0))), MT.word(t, U32.add(i, 0))) :
    {B.B.fwd1.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, j, max, B.B.fwd1.k2(j, 0, max, _)) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, 0), MT.cn(t, i, MW{t, j}, 0))) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), U32.add(j, 0)), (A.A.from(t), MT.W(t, U32.add(j, 0))), MT.word(t, U32.add(j, 0))) :
    {B.B.fwd1.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, j, max, B.B.fwd1.k3(0, max, MT.W(t, U32.add(i, 0)), _)) == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, 0), MT.cn(t, i, MW{t, j}, 0))) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, B.B.fwd1.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), i, j, max, (Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), U32.is_lt(4, max)), (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0)))))), A.A.from(t)))), (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MW{t, j}, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0)))))))), MT.fwd1.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, j, max, Bool.and(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0))), 0), 4, B.B.low.byte(U32.xor(MT.W(t, U32.add(i, 0)), MT.W(t, U32.add(j, 0)))))))) :
    {_ == (A.A.from(t), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), t, i, MW{t, j}, max, MT.cf(t, i, MW{t, j}, max, 0), MT.cn(t, i, MW{t, j}, 0))) : Array<U32> & U32}
  {==}

# Source matches
# ==============

law MT.add_le:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(c, d)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(a, c), Nat.add(b, d))) == True{} : Bool}

def MT.add_le(a, b, c, d, h1, h2):
  P.Nat.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), C.CP.le_add_r(a, b, c, h1),
    (%Equal.sym(Cmp, Nat.cmp(Nat.add(b, c), Nat.add(b, d)), Nat.cmp(c, d), P.Nat.cmp_add_l(b, c, d)) : {Cmp.is_le(_) == True{} : Bool}; h2))

# The word at i + n is read as words w and w + 1.
law MT.Wat:
  for +t: A.Tr
  for +i: U32
  for +n: U32
  for +w: U32
  for +m: Nat
  for +e: {V.U.N(U32.add(i, n)) == Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) : Nat}
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  for +hs: {B.B.sh(i) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  {MT.W(t, U32.add(i, n)) == B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), B.B.sh(i)) : U32}

def MT.Wat(t, i, n, w, m, e, hm, hs):
  %Equal.sym(U32, U32.shrn(U32.add(i, n), 2n), w, K.WD.at(U32.add(i, n), w, m, e, hm)) :
    {B.B.join(A.T.word(t, _), A.T.word(t, U32.add(_, 1)), B.B.sh(U32.add(i, n))) == B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), B.B.sh(i)) : U32}
  %Equal.sym(Nat, B.B.sh(U32.add(i, n)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), K.WD.lane(U32.add(i, n), w, m, e, hm)) :
    {B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), _) == B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), B.B.sh(i)) : U32}
  %Equal.sym(Nat, B.B.sh(i), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), hs) :
    {B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))) == B.B.join(A.T.word(t, w), A.T.word(t, U32.add(w, 1)), _) : U32}
  {==}

law MT.w1b:
  for +i: U32
  for +n: U32
  for +w: U32
  for +m: Nat
  for +E: U32
  for +e: {V.U.N(U32.add(i, n)) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(w, 1)), V.U.N(1)), V.U.N(E))) == True{} : Bool}

def MT.w1b(i, n, w, m, E, e, hb):
  P.Nat.le_trans(Nat.add(V.U.N(U32.add(w, 1)), 1n), Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E),
    MT.add_le(V.U.N(U32.add(w, 1)), V.U.N(U32.add(i, n)), 1n, 4n,
      (%Equal.sym(Nat, V.U.N(U32.add(i, n)), Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))), e) : {Cmp.is_le(Nat.cmp(V.U.N(U32.add(w, 1)), _)) == True{} : Bool}; K.WD.le_quad(m, V.U.N(U32.add(w, 1)))),
      {==}), hb)

# Four bytes on, a word on.
law MT.hia_next:
  for +i: U32
  for +n: U32
  for +w: U32
  for +m: Nat
  for +E: U32
  for +e: {V.U.N(U32.add(i, n)) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(i, U32.add(n, 4))) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(U32.add(w, 1), 1))))) : Nat}

def MT.hia_next(i, n, w, m, E, e, hb):
  %V.U.add_assoc(i, n, 4) :
    {V.U.N(_) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(U32.add(w, 1), 1))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(i, n), 4)), Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.add_N(U32.add(i, n), 4, E, hb)) :
    {_ == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(U32.add(w, 1), 1))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(w, 1), 1)), Nat.add(V.U.N(U32.add(w, 1)), 1n), V.U.add_N(U32.add(w, 1), 1, E, MT.w1b(i, n, w, m, E, e, hb))) :
    {Nat.add(V.U.N(U32.add(i, n)), 4n) == Nat.add(m, Nat.double(Nat.double(_))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(i, n)), Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))), e) :
    {Nat.add(_, 4n) == Nat.add(m, Nat.double(Nat.double(Nat.add(V.U.N(U32.add(w, 1)), 1n)))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(V.U.N(U32.add(w, 1)), 1n)), Nat.add(Nat.double(V.U.N(U32.add(w, 1))), 2n), P.Nat.double_distr(V.U.N(U32.add(w, 1)), 1n)) :
    {Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))), 4n) == Nat.add(m, Nat.double(_)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.double(V.U.N(U32.add(w, 1))), 2n)), Nat.add(Nat.double(Nat.double(V.U.N(U32.add(w, 1)))), 4n), P.Nat.double_distr(Nat.double(V.U.N(U32.add(w, 1))), 2n)) :
    {Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))), 4n) == Nat.add(m, _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))), 4n), Nat.add(m, Nat.add(Nat.double(Nat.double(V.U.N(U32.add(w, 1)))), 4n)), P.Nat.add_assoc(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1)))), 4n)) :
    {_ == Nat.add(m, Nat.add(Nat.double(Nat.double(V.U.N(U32.add(w, 1)))), 4n)) : Nat}
  {==}

law MT.fwd.F:
  for +k: Nat
  for +wa: U32
  for +wb: U32
  for +max: U32
  for +sa: Nat
  for +sb: Nat
  for +n: U32
  for +ta: A.Tr
  for +tb: A.Tr
  for +x: U32
  for +y: U32
  {B.B.fwd.loop(k, wa, wb, max, sa, sb, (False{}, (n, ((A.A.from(ta), A.A.from(tb)), (x, y))))) == ((A.A.from(ta), A.A.from(tb)), U32.min(n, max)) : (Array<U32> & Array<U32>) & U32}

def MT.fwd.F(k, wa, wb, max, sa, sb, n, ta, tb, x, y):
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

law MT.cs.F:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +s: MS
  for +max: U32
  for +n: U32
  {MT.cs(k, ta, i, s, max, False{}, n) == U32.min(n, max) : U32}

def MT.cs.F(k, ta, i, s, max, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

law MT.ainb:
  for +i: U32
  for +n: U32
  for +max: U32
  for +E: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(max))) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E))) == True{} : Bool}

def MT.ainb(i, n, max, E, hn, h):
  %Equal.sym(Nat, V.U.N(U32.add(i, n)), Nat.add(V.U.N(i), V.U.N(n)), V.U.add_N(i, n, E, MT.le_tail0(Nat.add(V.U.N(i), V.U.N(n)), 4n, V.U.N(E), MT.ib(i, n, max, E, hn, h)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, 4n), V.U.N(E))) == True{} : Bool}
  MT.ib(i, n, max, E, hn, h)

law MT.fwd.T:
  for +k: Nat
  for +ta: A.Tr
  for +tb: A.Tr
  for +i: U32
  for +j: U32
  for +wa: U32
  for +wb: U32
  for +max: U32
  for +n: U32
  for +ma: Nat
  for +mb: Nat
  for +E: U32
  for +hia: {V.U.N(U32.add(i, n)) == Nat.add(ma, Nat.double(Nat.double(V.U.N(U32.add(wa, 1))))) : Nat}
  for +hma: {Nat.cmp(ma, 4n) == LT{} : Cmp}
  for +hjb: {V.U.N(U32.add(j, n)) == Nat.add(mb, Nat.double(Nat.double(V.U.N(U32.add(wb, 1))))) : Nat}
  for +hmb: {Nat.cmp(mb, 4n) == LT{} : Cmp}
  for +hsa: {B.B.sh(i) == Y.BP.shv(P.Nat.odd(ma), P.Nat.odd(P.Nat.half(ma))) : Nat}
  for +hsb: {B.B.sh(j) == Y.BP.shv(P.Nat.odd(mb), P.Nat.odd(P.Nat.half(mb))) : Nat}
  for +hn: {Nat.cmp(V.U.N(n), V.U.N(max)) == LT{} : Cmp}
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbj: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  {B.B.fwd.loop(k, wa, wb, max, B.B.sh(i), B.B.sh(j), (True{}, (n, ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(wa, 1)), A.T.word(tb, U32.add(wb, 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(k, ta, i, MW{tb, j}, max, True{}, n)) : (Array<U32> & Array<U32>) & U32}

law MT.fwd.T.c:
  for +p: Nat
  for +ta: A.Tr
  for +tb: A.Tr
  for +i: U32
  for +j: U32
  for +wa: U32
  for +wb: U32
  for +max: U32
  for +n: U32
  for +ma: Nat
  for +mb: Nat
  for +E: U32
  for +hia: {V.U.N(U32.add(i, n)) == Nat.add(ma, Nat.double(Nat.double(V.U.N(U32.add(wa, 1))))) : Nat}
  for +hma: {Nat.cmp(ma, 4n) == LT{} : Cmp}
  for +hjb: {V.U.N(U32.add(j, n)) == Nat.add(mb, Nat.double(Nat.double(V.U.N(U32.add(wb, 1))))) : Nat}
  for +hmb: {Nat.cmp(mb, 4n) == LT{} : Cmp}
  for +hsa: {B.B.sh(i) == Y.BP.shv(P.Nat.odd(ma), P.Nat.odd(P.Nat.half(ma))) : Nat}
  for +hsb: {B.B.sh(j) == Y.BP.shv(P.Nat.odd(mb), P.Nat.odd(P.Nat.half(mb))) : Nat}
  for +hn: {Nat.cmp(V.U.N(n), V.U.N(max)) == LT{} : Cmp}
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbj: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for ih: {U32.is_lt(U32.add(n, 4), max) == True{} : Bool} -> {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (True{}, (U32.add(n, 4), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, True{}, U32.add(n, 4))) : (Array<U32> & Array<U32>) & U32}
  for +c: Bool
  for +ec: {Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)) == c : Bool}
  {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}

def MT.fwd.T.c(p, ta, tb, i, j, wa, wb, max, n, ma, mb, E, hia, hma, hjb, hmb, hsa, hsb, hn, hbi, hbj, ih, c, ec):
  match c:
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), False{}, ec) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (_, (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, _, U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (False{}, (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))), ((A.A.from(ta), A.A.from(tb)), U32.min(U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), max)), MT.fwd.F(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ta, tb, A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)))) :
        {_ == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, False{}, U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(U32, MT.cs(p, ta, i, MW{tb, j}, max, False{}, U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))))))), U32.min(U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), max), MT.cs.F(p, ta, i, MW{tb, j}, max, U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) :
        {((A.A.from(ta), A.A.from(tb)), U32.min(U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), max)) == ((A.A.from(ta), A.A.from(tb)), _) : (Array<U32> & Array<U32>) & U32}
      {==}
    case True{}:
      %Equal.sym(Bool, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), True{}, ec) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (_, (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, _, U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(Bool, U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), True{}, P.Bool.and_l(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max), ec)) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (True{}, (U32.add(n, B.u32.pick(_, 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, True{}, U32.add(n, B.u32.pick(_, 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      ih(P.Bool.and_r(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max), ec))

def MT.fwd.T(k, ta, tb, i, j, wa, wb, max, n, ma, mb, E, hia, hma, hjb, hmb, hsa, hsb, hn, hbi, hbj):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ta), U32.add(U32.add(wa, 1), 1)), (A.A.from(ta), A.T.word(ta, U32.add(U32.add(wa, 1), 1))), A.A.get_from(ta, U32.add(U32.add(wa, 1), 1))) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), B.B.fwd.k1(U32.add(wb, 1), n, max, B.B.sh(i), B.B.sh(j), A.T.word(ta, U32.add(wa, 1)), A.T.word(tb, U32.add(wb, 1)), A.A.from(tb), _)) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, n), MT.cn(ta, i, MW{tb, j}, n))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), U32.add(U32.add(wb, 1), 1)), (A.A.from(tb), A.T.word(tb, U32.add(U32.add(wb, 1), 1))), A.A.get_from(tb, U32.add(U32.add(wb, 1), 1))) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), B.B.fwd.k2(n, max, B.B.sh(i), B.B.sh(j), A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(wb, 1)), A.A.from(ta), _)) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, n), MT.cn(ta, i, MW{tb, j}, n))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(U32, MT.W(ta, U32.add(i, n)), B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), MT.Wat(ta, i, n, U32.add(wa, 1), ma, hia, hma, hsa)) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(_, MT.W(tb, U32.add(j, n))), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(_, MT.W(tb, U32.add(j, n))), 0), 4, B.B.low.byte(U32.xor(_, MT.W(tb, U32.add(j, n)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(U32, MT.W(tb, U32.add(j, n)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)), MT.Wat(tb, j, n, U32.add(wb, 1), mb, hjb, hmb, hsb)) :
        {B.B.fwd.loop(p, U32.add(wa, 1), U32.add(wb, 1), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), (U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.add(wa, 1), 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(p, ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), _), 0), U32.is_lt(U32.add(n, 4), max)), U32.add(n, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), _), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), _)))))) : (Array<U32> & Array<U32>) & U32}
      MT.fwd.T.c(p, ta, tb, i, j, wa, wb, max, n, ma, mb, E, hia, hma, hjb, hmb, hsa, hsb, hn, hbi, hbj, hl => MT.fwd.T(p, ta, tb, i, j, U32.add(wa, 1), U32.add(wb, 1), max, U32.add(n, 4), ma, mb, E, MT.hia_next(i, n, wa, ma, E, hia, MT.ainb(i, n, max, E, P.Nat.lt_to_le(V.U.N(n), V.U.N(max), hn), hbi)), hma, MT.hia_next(j, n, wb, mb, E, hjb, MT.ainb(j, n, max, E, P.Nat.lt_to_le(V.U.N(n), V.U.N(max), hn), hbj)), hmb, hsa, hsb, V.U.lt_N(U32.add(n, 4), max, hl), hbi, hbj), Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.add(wa, 1)), A.T.word(ta, U32.add(U32.add(wa, 1), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.add(wb, 1)), A.T.word(tb, U32.add(U32.add(wb, 1), 1)), B.B.sh(j))), 0), U32.is_lt(U32.add(n, 4), max)), {==})

law MT.hia_g:
  for +i: U32
  for +n: U32
  for +w: U32
  for +m: Nat
  for +E: U32
  for +e: {V.U.N(U32.add(i, n)) == Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(i, U32.add(n, 4))) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}

law MT.w0b:
  for +i: U32
  for +n: U32
  for +w: U32
  for +m: Nat
  for +E: U32
  for +e: {V.U.N(U32.add(i, n)) == Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w), V.U.N(1)), V.U.N(E))) == True{} : Bool}

def MT.w0b(i, n, w, m, E, e, hb):
  P.Nat.le_trans(Nat.add(V.U.N(w), 1n), Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.N(E),
    MT.add_le(V.U.N(w), V.U.N(U32.add(i, n)), 1n, 4n,
      (%Equal.sym(Nat, V.U.N(U32.add(i, n)), Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), e) : {Cmp.is_le(Nat.cmp(V.U.N(w), _)) == True{} : Bool}; K.WD.le_quad(m, V.U.N(w))),
      {==}), hb)

def MT.hia_g(i, n, w, m, E, e, hb):
  %V.U.add_assoc(i, n, 4) :
    {V.U.N(_) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(i, n), 4)), Nat.add(V.U.N(U32.add(i, n)), 4n), V.U.add_N(U32.add(i, n), 4, E, hb)) :
    {_ == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(w, 1)), Nat.add(V.U.N(w), 1n), V.U.add_N(w, 1, E, MT.w0b(i, n, w, m, E, e, hb))) :
    {Nat.add(V.U.N(U32.add(i, n)), 4n) == Nat.add(m, Nat.double(Nat.double(_))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(i, n)), Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), e) :
    {Nat.add(_, 4n) == Nat.add(m, Nat.double(Nat.double(Nat.add(V.U.N(w), 1n)))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(V.U.N(w), 1n)), Nat.add(Nat.double(V.U.N(w)), 2n), P.Nat.double_distr(V.U.N(w), 1n)) :
    {Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), 4n) == Nat.add(m, Nat.double(_)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.double(V.U.N(w)), 2n)), Nat.add(Nat.double(Nat.double(V.U.N(w))), 4n), P.Nat.double_distr(Nat.double(V.U.N(w)), 2n)) :
    {Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), 4n) == Nat.add(m, _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), 4n), Nat.add(m, Nat.add(Nat.double(Nat.double(V.U.N(w))), 4n)), P.Nat.add_assoc(m, Nat.double(Nat.double(V.U.N(w))), 4n)) :
    {_ == Nat.add(m, Nat.add(Nat.double(Nat.double(V.U.N(w))), 4n)) : Nat}
  {==}

# i is i + 0, read from its word.
law MT.hi0:
  for +i: U32
  {V.U.N(U32.add(i, 0)) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), Nat.double(Nat.double(V.U.N(U32.shrn(i, 2n))))) : Nat}

def MT.hi0(i):
  %Equal.sym(U32, U32.add(i, 0), i, V.U.add_zero_r(i)) :
    {V.U.N(_) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), Nat.double(Nat.double(V.U.N(U32.shrn(i, 2n))))) : Nat}
  K.WD.split_lane(i)

law MT.hs0:
  for +i: U32
  {B.B.sh(i) == Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i))))))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i))))))))) : Nat}

def MT.hs0(i):
  K.WD.lane(i, U32.shrn(i, 2n), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), K.WD.split_lane(i), K.WD.lane_lt(P.Nat.odd(V.U.N(i)), P.Nat.odd(P.Nat.half(V.U.N(i)))))

law MT.fwd.c:
  for +ta: A.Tr
  for +tb: A.Tr
  for +i: U32
  for +j: U32
  for +max: U32
  for +E: U32
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbj: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)) == c : Bool}
  {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}

def MT.fwd.c(ta, tb, i, j, max, E, hbi, hbj, c, ec):
  match c:
    case False{}:
      %Equal.sym(Bool, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), False{}, ec) :
        {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (_, (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, _, U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (False{}, (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))), ((A.A.from(ta), A.A.from(tb)), U32.min(U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), max)), MT.fwd.F(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ta, tb, A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)))) :
        {_ == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, False{}, U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(U32, MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, False{}, U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))))))), U32.min(U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), max), MT.cs.F(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) :
        {((A.A.from(ta), A.A.from(tb)), U32.min(U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), max)) == ((A.A.from(ta), A.A.from(tb)), _) : (Array<U32> & Array<U32>) & U32}
      {==}
    case True{}:
      %Equal.sym(Bool, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), True{}, ec) :
        {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (_, (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, _, U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(Bool, U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), True{}, P.Bool.and_l(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max), ec)) :
        {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (True{}, (U32.add(0, B.u32.pick(_, 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, True{}, U32.add(0, B.u32.pick(_, 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))))) : (Array<U32> & Array<U32>) & U32}
      MT.fwd.T(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, tb, i, j, U32.shrn(i, 2n), U32.shrn(j, 2n), max, 4, Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(j))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(j)))))), E,
        MT.hia_g(i, 0, U32.shrn(i, 2n), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), E, MT.hi0(i), MT.ainb(i, 0, max, E, P.Nat.le_zero(V.U.N(max)), hbi)), K.WD.lane_lt(P.Nat.odd(V.U.N(i)), P.Nat.odd(P.Nat.half(V.U.N(i)))),
        MT.hia_g(j, 0, U32.shrn(j, 2n), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(j))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(j)))))), E, MT.hi0(j), MT.ainb(j, 0, max, E, P.Nat.le_zero(V.U.N(max)), hbj)), K.WD.lane_lt(P.Nat.odd(V.U.N(j)), P.Nat.odd(P.Nat.half(V.U.N(j)))),
        MT.hs0(i), MT.hs0(j), V.U.lt_N(4, max, P.Bool.and_r(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max), ec)), hbi, hbj)

# B.fwd counts as the loop from 0 does.
law MT.fwd:
  for +ta: A.Tr
  for +tb: A.Tr
  for +i: U32
  for +j: U32
  for +max: U32
  for +E: U32
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  for +hbj: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(j), V.U.N(max)), 4n), V.U.N(E))) == True{} : Bool}
  {B.B.fwd(A.A.from(ta), i, A.A.from(tb), j, max) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, 0), MT.cn(ta, i, MW{tb, j}, 0))) : (Array<U32> & Array<U32>) & U32}

def MT.fwd(ta, tb, i, j, max, E, hbi, hbj):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ta), U32.shrn(i, 2n)), (A.A.from(ta), A.T.word(ta, U32.shrn(i, 2n))), A.A.get_from(ta, U32.shrn(i, 2n))) :
    {B.B.fwd.s1(U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), A.A.from(tb), _) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, 0), MT.cn(ta, i, MW{tb, j}, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), U32.shrn(j, 2n)), (A.A.from(tb), A.T.word(tb, U32.shrn(j, 2n))), A.A.get_from(tb, U32.shrn(j, 2n))) :
    {B.B.fwd.s2(U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), A.T.word(ta, U32.shrn(i, 2n)), A.A.from(ta), _) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, 0), MT.cn(ta, i, MW{tb, j}, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ta), U32.add(U32.shrn(i, 2n), 1)), (A.A.from(ta), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1))), A.A.get_from(ta, U32.add(U32.shrn(i, 2n), 1))) :
    {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), B.B.fwd.k1(U32.shrn(j, 2n), 0, max, B.B.sh(i), B.B.sh(j), A.T.word(ta, U32.shrn(i, 2n)), A.T.word(tb, U32.shrn(j, 2n)), A.A.from(tb), _)) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, 0), MT.cn(ta, i, MW{tb, j}, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), U32.add(U32.shrn(j, 2n), 1)), (A.A.from(tb), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))), A.A.get_from(tb, U32.add(U32.shrn(j, 2n), 1))) :
    {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), B.B.fwd.k2(0, max, B.B.sh(i), B.B.sh(j), A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.shrn(j, 2n)), A.A.from(ta), _)) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, MT.cf(ta, i, MW{tb, j}, max, 0), MT.cn(ta, i, MW{tb, j}, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(U32, MT.W(ta, U32.add(i, 0)), B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), MT.Wat(ta, i, 0, U32.shrn(i, 2n), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(i))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(i)))))), MT.hi0(i), K.WD.lane_lt(P.Nat.odd(V.U.N(i)), P.Nat.odd(P.Nat.half(V.U.N(i)))), MT.hs0(i))) :
    {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(_, MT.W(tb, U32.add(j, 0))), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(_, MT.W(tb, U32.add(j, 0))), 0), 4, B.B.low.byte(U32.xor(_, MT.W(tb, U32.add(j, 0)))))))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(U32, MT.W(tb, U32.add(j, 0)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)), MT.Wat(tb, j, 0, U32.shrn(j, 2n), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(j))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(j)))))), MT.hi0(j), K.WD.lane_lt(P.Nat.odd(V.U.N(j)), P.Nat.odd(P.Nat.half(V.U.N(j)))), MT.hs0(j))) :
    {B.B.fwd.loop(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), U32.shrn(i, 2n), U32.shrn(j, 2n), max, B.B.sh(i), B.B.sh(j), (Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), (U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j)))))), ((A.A.from(ta), A.A.from(tb)), (A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1))))))) == ((A.A.from(ta), A.A.from(tb)), MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ta, i, MW{tb, j}, max, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), _), 0), U32.is_lt(4, max)), U32.add(0, B.u32.pick(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), _), 0), 4, B.B.low.byte(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), _)))))) : (Array<U32> & Array<U32>) & U32}
  MT.fwd.c(ta, tb, i, j, max, E, hbi, hbj, Bool.and(U32.is_eq(U32.xor(B.B.join(A.T.word(ta, U32.shrn(i, 2n)), A.T.word(ta, U32.add(U32.shrn(i, 2n), 1)), B.B.sh(i)), B.B.join(A.T.word(tb, U32.shrn(j, 2n)), A.T.word(tb, U32.add(U32.shrn(j, 2n), 1)), B.B.sh(j))), 0), U32.is_lt(4, max)), {==})

# Backward matches
# ================

law MT.ss:
  for +i: U32
  for +a: U32
  for +b: U32
  {U32.sub(U32.sub(i, a), b) == U32.sub(i, U32.add(b, a)) : U32}

def MT.ss(i, a, b):
  %V.U.add_sub(i, U32.add(b, a)) :
    {U32.sub(U32.sub(_, a), b) == U32.sub(i, U32.add(b, a)) : U32}
  %V.U.add_assoc(U32.sub(i, U32.add(b, a)), b, a) :
    {U32.sub(U32.sub(_, a), b) == U32.sub(i, U32.add(b, a)) : U32}
  %Equal.sym(U32, U32.sub(U32.add(U32.add(U32.sub(i, U32.add(b, a)), b), a), a), U32.add(U32.sub(i, U32.add(b, a)), b), V.U.sub_add(U32.add(U32.sub(i, U32.add(b, a)), b), a)) :
    {U32.sub(_, b) == U32.sub(i, U32.add(b, a)) : U32}
  %Equal.sym(U32, U32.sub(U32.add(U32.sub(i, U32.add(b, a)), b), b), U32.sub(i, U32.add(b, a)), V.U.sub_add(U32.sub(i, U32.add(b, a)), b)) :
    {_ == U32.sub(i, U32.add(b, a)) : U32}
  {==}

law MT.sa:
  for +i: U32
  for +n: U32
  {U32.add(U32.sub(i, U32.add(n, 1)), 1) == U32.sub(i, n) : U32}

def MT.sa(i, n):
  %V.U.add_sub(i, U32.add(n, 1)) :
    {U32.add(U32.sub(i, U32.add(n, 1)), 1) == U32.sub(_, n) : U32}
  %Equal.sym(U32, U32.add(n, 1), U32.add(1, n), V.U.add_comm(n, 1)) :
    {U32.add(U32.sub(i, _), 1) == U32.sub(U32.add(U32.sub(i, _), _), n) : U32}
  %V.U.add_assoc(U32.sub(i, U32.add(1, n)), 1, n) :
    {U32.add(U32.sub(i, U32.add(1, n)), 1) == U32.sub(_, n) : U32}
  %Equal.sym(U32, U32.sub(U32.add(U32.add(U32.sub(i, U32.add(1, n)), 1), n), n), U32.add(U32.sub(i, U32.add(1, n)), 1), V.U.sub_add(U32.add(U32.sub(i, U32.add(1, n)), 1), n)) :
    {U32.add(U32.sub(i, U32.add(1, n)), 1) == _ : U32}
  {==}

# The byte before i, n back.
def MT.bb(+t: A.Tr, +i: U32, +n: U32) -> U32:
  Y.BP.byt(t, U32.sub(U32.sub(i, 1), n))

def MT.bf(+ta: A.Tr, +i: U32, +tb: A.Tr, +j: U32, +max: U32, +n: U32) -> Bool:
  Bool.and(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), U32.is_lt(U32.add(n, 1), max))

def MT.bn(+ta: A.Tr, +i: U32, +tb: A.Tr, +j: U32, +n: U32) -> U32:
  U32.add(n, B.u32.pick(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), 1, 0))

def MT.bs(+k: Nat, +ta: A.Tr, +i: U32, +tb: A.Tr, +j: U32, +max: U32, +f: Bool, +n: U32) -> U32:
  match k f:
    case 0n _:
      U32.min(n, max)
    case 1n+p False{}:
      U32.min(n, max)
    case 1n+p True{}:
      MT.bs(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n))

law MT.back.loop:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +f: Bool
  for +n: U32
  {B.B.back.loop(k, i, j, max, (f, (n, (A.A.from(ta), A.A.from(tb))))) == ((A.A.from(ta), A.A.from(tb)), MT.bs(k, ta, i, tb, j, max, f, n)) : (Array<U32> & Array<U32>) & U32}

def MT.back.loop(k, ta, i, tb, j, max, f, n):
  match k f:
    case 0n _:
      {==}
    case 1n+p False{}:
      {==}
    case 1n+p True{}:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(ta), U32.sub(U32.sub(i, 1), n)), (A.A.from(ta), Y.BP.byt(ta, U32.sub(U32.sub(i, 1), n))), Y.BP.get_from(ta, U32.sub(U32.sub(i, 1), n))) :
        {B.B.back.loop(p, i, j, max, B.B.back.k1(j, n, max, A.A.from(tb), _)) == ((A.A.from(ta), A.A.from(tb)), MT.bs(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tb), U32.sub(U32.sub(j, 1), n)), (A.A.from(tb), Y.BP.byt(tb, U32.sub(U32.sub(j, 1), n))), Y.BP.get_from(tb, U32.sub(U32.sub(j, 1), n))) :
        {B.B.back.loop(p, i, j, max, B.B.back.k2(n, max, A.A.from(ta), Y.BP.byt(ta, U32.sub(U32.sub(i, 1), n)), _)) == ((A.A.from(ta), A.A.from(tb)), MT.bs(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n))) : (Array<U32> & Array<U32>) & U32}
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.back.loop(p, i, j, max, (Bool.and(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), U32.is_lt(U32.add(n, 1), max)), (U32.add(n, B.u32.pick(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), 1, 0)), (A.A.from(ta), A.A.from(tb))))), ((A.A.from(ta), A.A.from(tb)), MT.bs(p, ta, i, tb, j, max, Bool.and(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), U32.is_lt(U32.add(n, 1), max)), U32.add(n, B.u32.pick(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), 1, 0)))), MT.back.loop(p, ta, i, tb, j, max, Bool.and(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), U32.is_lt(U32.add(n, 1), max)), U32.add(n, B.u32.pick(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), 1, 0)))) :
        {_ == ((A.A.from(ta), A.A.from(tb)), MT.bs(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n))) : (Array<U32> & Array<U32>) & U32}
      {==}

# B.back counts as the loop from 0 does.
law MT.back:
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  {B.B.back(A.A.from(ta), i, A.A.from(tb), j, max) == ((A.A.from(ta), A.A.from(tb)), MT.bs(U32.to_nat(max), ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))) : (Array<U32> & Array<U32>) & U32}

def MT.back(ta, i, tb, j, max):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(ta), U32.sub(U32.sub(i, 1), 0)), (A.A.from(ta), Y.BP.byt(ta, U32.sub(U32.sub(i, 1), 0))), Y.BP.get_from(ta, U32.sub(U32.sub(i, 1), 0))) :
    {B.B.back.loop(U32.to_nat(max), i, j, max, B.B.back.k1(j, 0, max, A.A.from(tb), _)) == ((A.A.from(ta), A.A.from(tb)), MT.bs(U32.to_nat(max), ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tb), U32.sub(U32.sub(j, 1), 0)), (A.A.from(tb), Y.BP.byt(tb, U32.sub(U32.sub(j, 1), 0))), Y.BP.get_from(tb, U32.sub(U32.sub(j, 1), 0))) :
    {B.B.back.loop(U32.to_nat(max), i, j, max, B.B.back.k2(0, max, A.A.from(ta), Y.BP.byt(ta, U32.sub(U32.sub(i, 1), 0)), _)) == ((A.A.from(ta), A.A.from(tb)), MT.bs(U32.to_nat(max), ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))) : (Array<U32> & Array<U32>) & U32}
  %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.back.loop(U32.to_nat(max), i, j, max, (Bool.and(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), U32.is_lt(1, max)), (U32.add(0, B.u32.pick(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), 1, 0)), (A.A.from(ta), A.A.from(tb))))), ((A.A.from(ta), A.A.from(tb)), MT.bs(U32.to_nat(max), ta, i, tb, j, max, Bool.and(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), U32.is_lt(1, max)), U32.add(0, B.u32.pick(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), 1, 0)))), MT.back.loop(U32.to_nat(max), ta, i, tb, j, max, Bool.and(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), U32.is_lt(U32.add(0, 1), max)), U32.add(0, B.u32.pick(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), 1, 0)))) :
    {_ == ((A.A.from(ta), A.A.from(tb)), MT.bs(U32.to_nat(max), ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))) : (Array<U32> & Array<U32>) & U32}
  {==}

law MT.app_inj:
  for +xs1: List<&2, U32>
  for +xs2: List<&2, U32>
  for +ys1: List<&2, U32>
  for +ys2: List<&2, U32>
  for +hl: {S.S.len(xs1) == S.S.len(xs2) : Nat}
  for +h: {K.WD.app(xs1, ys1) == K.WD.app(xs2, ys2) : List<&2, U32>}
  {ys1 == ys2 : List<&2, U32>}

def MT.app_inj(xs1, xs2, ys1, ys2, hl, h):
  match xs1 xs2:
    case Nil{} Nil{}:
      h
    case Nil{} Con{y, r}:
      P.Bool.false_true({ys1 == ys2 : List<&2, U32>}, (%hl : {Cmp.is_eq(Nat.cmp(_, 0n)) == True{} : Bool}; {==}))
    case Con{x, r} Nil{}:
      P.Bool.false_true({ys1 == ys2 : List<&2, U32>}, (%Equal.sym(Nat, S.S.len(Con{x, r}), 0n, hl) : {Cmp.is_eq(Nat.cmp(_, 0n)) == True{} : Bool}; {==}))
    case Con{x, r} Con{y, q}:
      MT.app_inj(r, q, ys1, ys2, P.Nat.succ_inj(S.S.len(r), S.S.len(q), hl), K.WD.cons_inj_t(x, K.WD.app(r, ys1), y, K.WD.app(q, ys2), h))

# The last m of k + m bytes agree when they all do.
law MT.suf:
  for +k: Nat
  for +m: Nat
  for +t1: A.Tr
  for +t2: A.Tr
  for +p1: U32
  for +p2: U32
  for +x: U32
  for +ex: {V.U.N(x) == k : Nat}
  for +e: {S.S.sl(Nat.add(k, m), t1, p1) == S.S.sl(Nat.add(k, m), t2, p2) : List<&2, U32>}
  {S.S.sl(m, t1, U32.add(p1, x)) == S.S.sl(m, t2, U32.add(p2, x)) : List<&2, U32>}

def MT.suf(k, m, t1, t2, p1, p2, x, ex, e):
  MT.app_inj(S.S.sl(k, t1, p1), S.S.sl(k, t2, p2), S.S.sl(m, t1, U32.add(p1, x)), S.S.sl(m, t2, U32.add(p2, x)),
    (%Equal.sym(Nat, S.S.len(S.S.sl(k, t2, p2)), k, S.S.len_sl(k, t2, p2)) : {S.S.len(S.S.sl(k, t1, p1)) == _ : Nat}; S.S.len_sl(k, t1, p1)),
    (%K.WD.sl_app(k, m, t1, p1, x, ex) : {_ == K.WD.app(S.S.sl(k, t2, p2), S.S.sl(m, t2, U32.add(p2, x))) : List<&2, U32>};
      (%K.WD.sl_app(k, m, t2, p2, x, ex) : {S.S.sl(Nat.add(k, m), t1, p1) == _ : List<&2, U32>}; e)))

law MT.as:
  for +a: U32
  for +n: U32
  for +r: U32
  {U32.add(a, U32.sub(n, r)) == U32.sub(U32.add(a, n), r) : U32}

def MT.as(a, n, r):
  %V.U.add_sub(n, r) :
    {U32.add(a, U32.sub(n, r)) == U32.sub(U32.add(a, _), r) : U32}
  %V.U.add_assoc(a, U32.sub(n, r), r) :
    {U32.add(a, U32.sub(n, r)) == U32.sub(_, r) : U32}
  %Equal.sym(U32, U32.sub(U32.add(U32.add(a, U32.sub(n, r)), r), r), U32.add(a, U32.sub(n, r)), V.U.sub_add(U32.add(a, U32.sub(n, r)), r)) :
    {U32.add(a, U32.sub(n, r)) == _ : U32}
  {==}

law MT.asub:
  for +i: U32
  for +n: U32
  for +r: U32
  {U32.add(U32.sub(i, n), U32.sub(n, r)) == U32.sub(i, r) : U32}

def MT.asub(i, n, r):
  %Equal.sym(U32, U32.add(U32.sub(i, n), U32.sub(n, r)), U32.sub(U32.add(U32.sub(i, n), n), r), MT.as(U32.sub(i, n), n, r)) :
    {_ == U32.sub(i, r) : U32}
  %Equal.sym(U32, U32.add(U32.sub(i, n), n), i, V.U.add_sub(i, n)) :
    {U32.sub(_, r) == U32.sub(i, r) : U32}
  {==}

law MT.bs_fin:
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +n: U32
  for +max: U32
  for +hs: {S.S.sl(V.U.N(n), ta, U32.sub(i, n)) == S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
  {S.S.sl(V.U.N(U32.min(n, max)), ta, U32.sub(i, U32.min(n, max))) == S.S.sl(V.U.N(U32.min(n, max)), tb, U32.sub(j, U32.min(n, max))) : List<&2, U32>}

def MT.bs_fin(ta, i, tb, j, n, max, hs):
  %MT.asub(i, n, U32.min(n, max)) :
    {S.S.sl(V.U.N(U32.min(n, max)), ta, _) == S.S.sl(V.U.N(U32.min(n, max)), tb, U32.sub(j, U32.min(n, max))) : List<&2, U32>}
  %MT.asub(j, n, U32.min(n, max)) :
    {S.S.sl(V.U.N(U32.min(n, max)), ta, U32.add(U32.sub(i, n), U32.sub(n, U32.min(n, max)))) == S.S.sl(V.U.N(U32.min(n, max)), tb, _) : List<&2, U32>}
  MT.suf(V.U.N(U32.sub(n, U32.min(n, max))), V.U.N(U32.min(n, max)), ta, tb, U32.sub(i, n), U32.sub(j, n), U32.sub(n, U32.min(n, max)), {==},
    (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(n, U32.min(n, max))), V.U.N(U32.min(n, max))), V.U.N(n), V.U.sub_nat(n, U32.min(n, max), V.U.N_le(U32.min(n, max), n, MT.min_le(n, max)))) : {S.S.sl(_, ta, U32.sub(i, n)) == S.S.sl(_, tb, U32.sub(j, n)) : List<&2, U32>}; hs))

law MT.bstep.c:
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +n: U32
  for +max: U32
  for +hs: {S.S.sl(V.U.N(n), ta, U32.sub(i, n)) == S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
  for +hl: {Nat.cmp(V.U.N(n), V.U.N(max)) == LT{} : Cmp}
  for +c: Bool
  for +ec: {U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)) == c : Bool}
  {S.S.sl(V.U.N(MT.bn(ta, i, tb, j, n)), ta, U32.sub(i, MT.bn(ta, i, tb, j, n))) == S.S.sl(V.U.N(MT.bn(ta, i, tb, j, n)), tb, U32.sub(j, MT.bn(ta, i, tb, j, n))) : List<&2, U32>}

law MT.lt_s1:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(a, b) == LT{} : Cmp}
  {Cmp.is_le(Nat.cmp(Nat.add(a, 1n), b)) == True{} : Bool}

def MT.lt_s1(a, b, h):
  match a b:
    case 0n 0n:
      P.Bool.false_true({Cmp.is_le(Nat.cmp(Nat.add(0n, 1n), 0n)) == True{} : Bool}, (%Equal.sym(Cmp, EQ{}, LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}; {==}))
    case 0n 1n+q:
      P.Nat.le_zero(q)
    case 1n+p 0n:
      P.Bool.false_true({Cmp.is_le(Nat.cmp(Nat.add(1n+p, 1n), 0n)) == True{} : Bool}, (%Equal.sym(Cmp, GT{}, LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}; {==}))
    case 1n+p 1n+q:
      MT.lt_s1(p, q, h)

def MT.bstep.c(ta, i, tb, j, n, max, hs, hl, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), True{}, ec) :
        {S.S.sl(V.U.N(U32.add(n, B.u32.pick(_, 1, 0))), ta, U32.sub(i, U32.add(n, B.u32.pick(_, 1, 0)))) == S.S.sl(V.U.N(U32.add(n, B.u32.pick(_, 1, 0))), tb, U32.sub(j, U32.add(n, B.u32.pick(_, 1, 0)))) : List<&2, U32>}
      %Equal.sym(Nat, V.U.N(U32.add(n, 1)), Nat.add(V.U.N(n), 1n), V.U.add_N(n, 1, max, MT.lt_s1(V.U.N(n), V.U.N(max), hl))) :
        {S.S.sl(_, ta, U32.sub(i, U32.add(n, 1))) == S.S.sl(_, tb, U32.sub(j, U32.add(n, 1))) : List<&2, U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(n), 1n), Nat.add(1n, V.U.N(n)), P.Nat.add_comm(V.U.N(n), 1n)) :
        {S.S.sl(_, ta, U32.sub(i, U32.add(n, 1))) == S.S.sl(_, tb, U32.sub(j, U32.add(n, 1))) : List<&2, U32>}
      %Equal.sym(U32, U32.add(U32.sub(i, U32.add(n, 1)), 1), U32.sub(i, n), MT.sa(i, n)) :
        {Y.BP.byt(ta, U32.sub(i, U32.add(n, 1))) <> S.S.sl(V.U.N(n), ta, _) == Y.BP.byt(tb, U32.sub(j, U32.add(n, 1))) <> S.S.sl(V.U.N(n), tb, U32.add(U32.sub(j, U32.add(n, 1)), 1)) : List<&2, U32>}
      %Equal.sym(U32, U32.add(U32.sub(j, U32.add(n, 1)), 1), U32.sub(j, n), MT.sa(j, n)) :
        {Y.BP.byt(ta, U32.sub(i, U32.add(n, 1))) <> S.S.sl(V.U.N(n), ta, U32.sub(i, n)) == Y.BP.byt(tb, U32.sub(j, U32.add(n, 1))) <> S.S.sl(V.U.N(n), tb, _) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(n), ta, U32.sub(i, n)), S.S.sl(V.U.N(n), tb, U32.sub(j, n)), hs) :
        {Y.BP.byt(ta, U32.sub(i, U32.add(n, 1))) <> _ == Y.BP.byt(tb, U32.sub(j, U32.add(n, 1))) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
      %MT.ss(i, 1, n) :
        {Y.BP.byt(ta, _) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) == Y.BP.byt(tb, U32.sub(j, U32.add(n, 1))) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
      %MT.ss(j, 1, n) :
        {Y.BP.byt(ta, U32.sub(U32.sub(i, 1), n)) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) == Y.BP.byt(tb, _) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
      %Equal.sym(U32, MT.bb(ta, i, n), MT.bb(tb, j, n), V.U.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n), ec)) :
        {_ <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) == MT.bb(tb, j, n) <> S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), False{}, ec) :
        {S.S.sl(V.U.N(U32.add(n, B.u32.pick(_, 1, 0))), ta, U32.sub(i, U32.add(n, B.u32.pick(_, 1, 0)))) == S.S.sl(V.U.N(U32.add(n, B.u32.pick(_, 1, 0))), tb, U32.sub(j, U32.add(n, B.u32.pick(_, 1, 0)))) : List<&2, U32>}
      %Equal.sym(U32, U32.add(n, 0), n, V.U.add_zero_r(n)) :
        {S.S.sl(V.U.N(_), ta, U32.sub(i, _)) == S.S.sl(V.U.N(_), tb, U32.sub(j, _)) : List<&2, U32>}
      hs

law MT.bstep:
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +n: U32
  for +max: U32
  for +hs: {S.S.sl(V.U.N(n), ta, U32.sub(i, n)) == S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
  for +hl: {Nat.cmp(V.U.N(n), V.U.N(max)) == LT{} : Cmp}
  {S.S.sl(V.U.N(MT.bn(ta, i, tb, j, n)), ta, U32.sub(i, MT.bn(ta, i, tb, j, n))) == S.S.sl(V.U.N(MT.bn(ta, i, tb, j, n)), tb, U32.sub(j, MT.bn(ta, i, tb, j, n))) : List<&2, U32>}

def MT.bstep(ta, i, tb, j, n, max, hs, hl):
  MT.bstep.c(ta, i, tb, j, n, max, hs, hl, U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), {==})

law MT.flagd.le:
  for +n: U32
  for +k: U32
  for +d: U32
  for +E: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), V.U.N(d))) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(U32.add(n, d)))) == True{} : Bool}

def MT.flagd.le(n, k, d, E, hk, hn):
  %Equal.sym(Nat, V.U.N(U32.add(n, k)), Nat.add(V.U.N(n), V.U.N(k)), V.U.add_N(n, k, E, P.Nat.le_trans(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), V.U.N(d))), Nat.cmp(V.U.N(k), V.U.N(d)), P.Nat.cmp_add_l(V.U.N(n), V.U.N(k), V.U.N(d))) : {Cmp.is_le(_) == True{} : Bool}; hk), hn))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(U32.add(n, d)))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(n, d)), Nat.add(V.U.N(n), V.U.N(d)), V.U.add_N(n, d, E, hn)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(n), V.U.N(k)), Nat.add(V.U.N(n), V.U.N(d))), Nat.cmp(V.U.N(k), V.U.N(d)), P.Nat.cmp_add_l(V.U.N(n), V.U.N(k), V.U.N(d))) :
    {Cmp.is_le(_) == True{} : Bool}
  hk

law MT.flagd.c:
  for +same: Bool
  for +n: U32
  for +k: U32
  for +d: U32
  for +max: U32
  for +E: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), V.U.N(d))) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(U32.add(n, d), max) == c : Bool}
  {Bool.and(Bool.and(same, U32.is_lt(U32.add(n, d), max)), Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}

def MT.flagd.c(same, n, k, d, max, E, hk, hn, c, ec):
  match c:
    case False{}:
      %Equal.sym(Bool, U32.is_lt(U32.add(n, d), max), False{}, ec) :
        {Bool.and(Bool.and(same, _), Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, False{}), False{}, P.Bool.and_false(same)) :
        {Bool.and(_, Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max))))) == False{} : Bool}
      {==}
    case True{}:
      %Equal.sym(Cmp, Nat.cmp(V.U.N(U32.add(n, k)), V.U.N(max)), LT{}, P.Nat.le_lt_trans(V.U.N(U32.add(n, k)), V.U.N(U32.add(n, d)), V.U.N(max), MT.flagd.le(n, k, d, E, hk, hn), V.U.lt_N(U32.add(n, d), max, ec))) :
        {Bool.and(Bool.and(same, U32.is_lt(U32.add(n, d), max)), Bool.not(Cmp.is_lt(_))) == False{} : Bool}
      %Equal.sym(Bool, U32.is_lt(U32.add(n, d), max), True{}, ec) :
        {Bool.and(Bool.and(same, _), Bool.not(Cmp.is_lt(LT{}))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, True{}), same, P.Bool.and_true(same)) :
        {Bool.and(_, Bool.not(Cmp.is_lt(LT{}))) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(same, False{}), False{}, P.Bool.and_false(same)) :
        {_ == False{} : Bool}
      {==}

law MT.bk_le:
  for +c: Bool
  {Cmp.is_le(Nat.cmp(V.U.N(B.u32.pick(c, 1, 0)), V.U.N(1))) == True{} : Bool}

def MT.bk_le(c):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# The backward loop's count: that many bytes before i and j agree.
law MT.bs_ok:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +f: Bool
  for +n: U32
  for +hs: {S.S.sl(V.U.N(n), ta, U32.sub(i, n)) == S.S.sl(V.U.N(n), tb, U32.sub(j, n)) : List<&2, U32>}
  for +hf: {Bool.and(f, Bool.not(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))))) == False{} : Bool}
  {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, f, n)), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, max, f, n))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, f, n)), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, max, f, n))) : List<&2, U32>}

def MT.bs_ok(k, ta, i, tb, j, max, f, n, hs, hf):
  match k f:
    case 0n _:
      MT.bs_fin(ta, i, tb, j, n, max, hs)
    case 1n+p False{}:
      MT.bs_fin(ta, i, tb, j, n, max, hs)
    case 1n+p True{}:
      MT.bs_ok(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n),
        MT.bstep(ta, i, tb, j, n, max, hs, P.Cmp.is_lt_lt(Nat.cmp(V.U.N(n), V.U.N(max)), MT.not_f(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))), hf))),
        MT.flagd.c(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), n, B.u32.pick(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n)), 1, 0), 1, max, max,
          MT.bk_le(U32.is_eq(MT.bb(ta, i, n), MT.bb(tb, j, n))), MT.lt_s1(V.U.N(n), V.U.N(max), P.Cmp.is_lt_lt(Nat.cmp(V.U.N(n), V.U.N(max)), MT.not_f(Cmp.is_lt(Nat.cmp(V.U.N(n), V.U.N(max))), hf))),
          U32.is_lt(U32.add(n, 1), max), {==}))

law MT.bs_le:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +f: Bool
  for +n: U32
  {Cmp.is_le(Nat.cmp(V.U.N(MT.bs(k, ta, i, tb, j, max, f, n)), V.U.N(max))) == True{} : Bool}

def MT.bs_le(k, ta, i, tb, j, max, f, n):
  match k f:
    case 0n _:
      MT.min_le_r(n, max)
    case 1n+p False{}:
      MT.min_le_r(n, max)
    case 1n+p True{}:
      MT.bs_le(p, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, n), MT.bn(ta, i, tb, j, n))

# A backward loop from 0.
law MT.bs0_ok:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}

law MT.bs0_ok.c:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +c: Cmp
  for +ec: {Nat.cmp(V.U.N(0), V.U.N(max)) == c : Cmp}
  {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}

law MT.bs.F:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +n: U32
  {MT.bs(k, ta, i, tb, j, max, False{}, n) == U32.min(n, max) : U32}

def MT.bs.F(k, ta, i, tb, j, max, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

law MT.nat0:
  for +n: Nat
  for +h: {Cmp.is_le(Nat.cmp(n, 0n)) == True{} : Bool}
  {n == 0n : Nat}

def MT.nat0(n, h):
  match n:
    case 0n:
      {==}
    case 1n+p:
      P.Bool.false_true({1n+p == 0n : Nat}, h)

law MT.bs0_ok.z:
  for +k: Nat
  for +ta: A.Tr
  for +i: U32
  for +tb: A.Tr
  for +j: U32
  for +max: U32
  for +ec: {Nat.cmp(V.U.N(0), V.U.N(max)) == EQ{} : Cmp}
  {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}

def MT.bs0_ok.z(k, ta, i, tb, j, max, ec):
  %Equal.sym(U32, max, 0, V.U.eq_N(max, 0, Equal.sym(Nat, V.U.N(0), V.U.N(max), P.Nat.cmp_eq(V.U.N(0), V.U.N(max), ec)))) :
    {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, _, MT.bf(ta, i, tb, j, _, 0), MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, _, MT.bf(ta, i, tb, j, _, 0), MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, _, MT.bf(ta, i, tb, j, _, 0), MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, _, MT.bf(ta, i, tb, j, _, 0), MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), False{}), False{}, P.Bool.and_false(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)))) :
    {S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, 0, _, MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, 0, _, MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, 0, _, MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, 0, _, MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}
  %Equal.sym(U32, MT.bs(k, ta, i, tb, j, 0, False{}, MT.bn(ta, i, tb, j, 0)), U32.min(MT.bn(ta, i, tb, j, 0), 0), MT.bs.F(k, ta, i, tb, j, 0, MT.bn(ta, i, tb, j, 0))) :
    {S.S.sl(V.U.N(_), ta, U32.sub(i, _)) == S.S.sl(V.U.N(_), tb, U32.sub(j, _)) : List<&2, U32>}
  %Equal.sym(Nat, V.U.N(U32.min(MT.bn(ta, i, tb, j, 0), 0)), 0n, MT.nat0(V.U.N(U32.min(MT.bn(ta, i, tb, j, 0), 0)), MT.min_le_r(MT.bn(ta, i, tb, j, 0), 0))) :
    {S.S.sl(_, ta, U32.sub(i, U32.min(MT.bn(ta, i, tb, j, 0), 0))) == S.S.sl(_, tb, U32.sub(j, U32.min(MT.bn(ta, i, tb, j, 0), 0))) : List<&2, U32>}
  {==}

def MT.bs0_ok.c(k, ta, i, tb, j, max, c, ec):
  match c:
    case LT{}:
      MT.bs_ok(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0),
        MT.bstep(ta, i, tb, j, 0, max, {==}, ec),
        MT.flagd.c(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), 0, B.u32.pick(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0)), 1, 0), 1, max, max,
          MT.bk_le(U32.is_eq(MT.bb(ta, i, 0), MT.bb(tb, j, 0))), MT.lt_s1(V.U.N(0), V.U.N(max), ec), U32.is_lt(U32.add(0, 1), max), {==}))
    case EQ{}:
      MT.bs0_ok.z(k, ta, i, tb, j, max, ec)
    case GT{}:
      P.Bool.false_true({S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), ta, U32.sub(i, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) == S.S.sl(V.U.N(MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0))), tb, U32.sub(j, MT.bs(k, ta, i, tb, j, max, MT.bf(ta, i, tb, j, max, 0), MT.bn(ta, i, tb, j, 0)))) : List<&2, U32>}, (%ec : {Cmp.is_le(_) == True{} : Bool}; P.Nat.le_zero(V.U.N(max))))

def MT.bs0_ok(k, ta, i, tb, j, max):
  MT.bs0_ok.c(k, ta, i, tb, j, max, Nat.cmp(V.U.N(0), V.U.N(max)), {==})
