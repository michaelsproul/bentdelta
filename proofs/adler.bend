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

# Adler-32 (bytes.bend) reads only the bytes in its range: B.adler32 is a
# function of them, so two trees agreeing there have the same checksum.
#
# Source: proofs/adler.bp (tools/bpp.py writes proofs/adler.bend from it).

# The sums as functions of the bytes
# ==================================

type AB is Data:
  AB{a: U32, b: U32}

def AD.pr(+s: AB) -> U32 & U32:
  match s:
    case AB{a, b}:
      (a, b)

def AD.by(+xs: List<&2, U32>, +s: AB) -> AB:
  match xs s:
    case [] s:
      s
    case Con{x, r} AB{a, b}:
      AD.by(r, AB{(a + x : U32), (b + (a + x : U32) : U32)})

def AD.wo4(+x0: U32, +x1: U32, +x2: U32, +x3: U32, +s: AB) -> AB:
  match s:
    case AB{a, b}:
      AB{((a + (x0 + x1 : U32) : U32) + (x2 + x3 : U32) : U32),
        ((((b + (a << 2n : U32) : U32) + (x0 << 2n : U32) : U32) + (x1 * 3 : U32) : U32) + ((x2 << 1n : U32) + x3 : U32) : U32)}

def AD.wo(+k: Nat, +xs: List<&2, U32>, +s: AB) -> AB:
  match k xs:
    case 0n _:
      s
    case 1n+p Con{x0, Con{x1, Con{x2, Con{x3, r}}}}:
      AD.wo(p, r, AD.wo4(x0, x1, x2, x3, s))
    case 1n+p _:
      s

def AD.red(+s: AB) -> AB:
  match s:
    case AB{a, b}:
      AB{(a % 65521 : U32), (b % 65521 : U32)}

def AD.fin(+s: AB) -> U32:
  match s:
    case AB{a, b}:
      ((b << 16n : U32) .|. a : U32)

def AD.go(+k: Nat, +t: A.Tr, +i: U32, +nw: U32, +s: AB) -> AB:
  match k:
    case 0n:
      s
    case 1n+p:
      +m = U32.min(nw, 1388)
      AD.go(p, t, (i + (m << 2n : U32) : U32), (nw - m : U32),
        AD.red(AD.wo(U32.to_nat(m), S.S.sl(Nat.double(Nat.double(U32.to_nat(m))), t, i), s)))

# The checksum of t's bytes [i, i + n), as B.adler32 computes it.
def AD.T(+t: A.Tr, +i: U32, +n: U32) -> U32:
  +h = U32.min(n, ((4 - (i .&. 3 : U32) : U32) .&. 3 : U32))
  +n1 = (n - h : U32)
  +nw = (n1 >> 2n : U32)
  AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat((n1 .&. 3 : U32)), t, ((i + h : U32) + (nw << 2n : U32) : U32)),
    AD.go(U32.to_nat(((nw + 1387 : U32) / 1388 : U32)), t, (i + h : U32), nw,
      AD.red(AD.by(S.S.sl(U32.to_nat(h), t, i), AB{1, 0}))))))

# The code's loops
# ================

law AD.bytes:
  for +k: Nat
  for +a: U32
  for +b: U32
  for +i: U32
  for +t: A.Tr
  {B.B.adler.bytes(k, a, b, i, (A.A.from(t), Y.BP.byt(t, i))) == (A.A.from(t), AD.pr(AD.by(S.S.sl(k, t, i), AB{a, b}))) : Array<U32> & (U32 & U32)}

def AD.bytes(k, a, b, i, t):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), U32.add(i, 1)), (A.A.from(t), Y.BP.byt(t, U32.add(i, 1))), Y.BP.get_from(t, U32.add(i, 1))) :
        {B.B.adler.bytes(p, U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i))), U32.add(i, 1), _) == (A.A.from(t), AD.pr(AD.by(S.S.sl(p, t, U32.add(i, 1)), AB{U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i)))}))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.bytes(p, U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i))), U32.add(i, 1), (A.A.from(t), Y.BP.byt(t, U32.add(i, 1)))), (A.A.from(t), AD.pr(AD.by(S.S.sl(p, t, U32.add(i, 1)), AB{U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i)))}))), AD.bytes(p, U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i))), U32.add(i, 1), t)) :
        {_ == (A.A.from(t), AD.pr(AD.by(S.S.sl(p, t, U32.add(i, 1)), AB{U32.add(a, Y.BP.byt(t, i)), U32.add(b, U32.add(a, Y.BP.byt(t, i)))}))) : Array<U32> & U32 & U32}
      {==}

# The bytes of the word at an aligned position.
law AD.w4word:
  for +t: A.Tr
  for +i: U32
  for +wi: U32
  for +E: U32
  for +ed: {V.U.N(i) == Nat.double(Nat.double(V.U.N(wi))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {K.WD.w4(A.T.word(t, wi)) == S.S.sl(4n, t, i) : List<&2, U32>}

def AD.w4word(t, i, wi, E, ed, hb):
  %Z.BB.join00(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1))) :
    {_ <> Y.BP.ext(A.T.word(t, wi), 8n) <> Y.BP.ext(A.T.word(t, wi), 16n) <> Y.BP.ext(A.T.word(t, wi), 24n) <> [] == S.S.sl(4n, t, i) : List<&2, U32>}
  %Z.BB.join01(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1))) :
    {Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 0n) <> _ <> Y.BP.ext(A.T.word(t, wi), 16n) <> Y.BP.ext(A.T.word(t, wi), 24n) <> [] == S.S.sl(4n, t, i) : List<&2, U32>}
  %Z.BB.join02(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1))) :
    {Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 0n) <> Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 8n) <> _ <> Y.BP.ext(A.T.word(t, wi), 24n) <> [] == S.S.sl(4n, t, i) : List<&2, U32>}
  %Z.BB.join03(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1))) :
    {Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 0n) <> Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 8n) <> Y.BP.ext(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), 0n), 16n) <> _ <> [] == S.S.sl(4n, t, i) : List<&2, U32>}
  %K.WD.lane(i, wi, 0n, ed, {==}) :
    {K.WD.w4(B.B.join(A.T.word(t, wi), A.T.word(t, U32.add(wi, 1)), _)) == S.S.sl(4n, t, i) : List<&2, U32>}
  %K.WD.at(i, wi, 0n, ed, {==}) :
    {K.WD.w4(B.B.join(A.T.word(t, _), A.T.word(t, U32.add(_, 1)), B.B.sh(i))) == S.S.sl(4n, t, i) : List<&2, U32>}
  K.WD.join(t, i, E, hb)

law AD.words:
  for +k: Nat
  for +a: U32
  for +b: U32
  for +wi: U32
  for +i: U32
  for +t: A.Tr
  for +E: U32
  for +ed: {V.U.N(i) == Nat.double(Nat.double(V.U.N(wi))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(k)), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {B.B.adler.words(k, a, b, wi, (A.A.from(t), A.T.word(t, wi))) == (A.A.from(t), AD.pr(AD.wo(k, S.S.sl(Nat.double(Nat.double(k)), t, i), AB{a, b}))) : Array<U32> & (U32 & U32)}

def AD.words(k, a, b, wi, i, t, E, ed, hb):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.add(wi, 1)), (A.A.from(t), A.T.word(t, U32.add(wi, 1))), A.A.get_from(t, U32.add(wi, 1))) :
        {B.B.adler.words(p, U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n))), U32.add(wi, 1), _) == (A.A.from(t), AD.pr(AD.wo(1n+p, S.S.sl(4n+Nat.double(Nat.double(p)), t, i), AB{a, b}))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.words(p, U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n))), U32.add(wi, 1), (A.A.from(t), A.T.word(t, U32.add(wi, 1)))), (A.A.from(t), AD.pr(AD.wo(p, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4)), AB{U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n)))}))), AD.words(p, U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n))), U32.add(wi, 1), U32.add(i, 4), t, E, (%K.WD.step4(i) : {V.U.N(_) == Nat.add(0n, Nat.double(Nat.double(V.U.N(U32.add(wi, 1))))) : Nat}; C.CP.next(i, wi, E, 0n, ed, C.CP.le4(Nat.double(Nat.double(p)), V.U.N(i), V.U.N(E), hb))), (%Equal.sym(Nat, V.U.N(U32.add(i, 4)), 4n+V.U.N(i), (%K.WD.step4(i) : {V.U.N(_) == 4n+V.U.N(i) : Nat}; K.WD.pos_4(i, E, C.CP.le4(Nat.double(Nat.double(p)), V.U.N(i), V.U.N(E), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(p)), _), V.U.N(E))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.double(Nat.double(p)), 4n+V.U.N(i)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(i)), K.WD.add4r(Nat.double(Nat.double(p)), V.U.N(i))) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb)))) :
        {_ == (A.A.from(t), AD.pr(AD.wo(1n+p, S.S.sl(4n+Nat.double(Nat.double(p)), t, i), AB{a, b}))) : Array<U32> & U32 & U32}
      %Equal.sym(List<&2, U32>, S.S.sl(4n+Nat.double(Nat.double(p)), t, i), K.WD.app(S.S.sl(4n, t, i), S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4))), K.WD.sl_app(4n, Nat.double(Nat.double(p)), t, i, 4, {==})) :
        {(A.A.from(t), AD.pr(AD.wo(p, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4)), AB{U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n)))}))) == (A.A.from(t), AD.pr(AD.wo(1n+p, _, AB{a, b}))) : Array<U32> & U32 & U32}
      %AD.w4word(t, i, wi, E, ed, C.CP.le4(Nat.double(Nat.double(p)), V.U.N(i), V.U.N(E), hb)) :
        {(A.A.from(t), AD.pr(AD.wo(p, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4)), AB{U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), U32.shrn(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), U32.shrn(A.T.word(t, wi), 24n)))}))) == (A.A.from(t), AD.pr(AD.wo(1n+p, K.WD.app(_, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4))), AB{a, b}))) : Array<U32> & U32 & U32}
      %Equal.sym(U32, U32.shrn(A.T.word(t, wi), 24n), Y.BP.ext(A.T.word(t, wi), 24n), Z.BB.sh24(A.T.word(t, wi))) :
        {(A.A.from(t), AD.pr(AD.wo(p, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4)), AB{U32.add(U32.add(a, U32.add(U32.and(A.T.word(t, wi), 255), U32.and(U32.shrn(A.T.word(t, wi), 8n), 255))), U32.add(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), _)), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(U32.and(A.T.word(t, wi), 255), 2n)), U32.mul(U32.and(U32.shrn(A.T.word(t, wi), 8n), 255), 3)), U32.add(U32.shln(U32.and(U32.shrn(A.T.word(t, wi), 16n), 255), 1n), _))}))) == (A.A.from(t), AD.pr(AD.wo(p, S.S.sl(Nat.double(Nat.double(p)), t, U32.add(i, 4)), AB{U32.add(U32.add(a, U32.add(Y.BP.ext(A.T.word(t, wi), 0n), Y.BP.ext(A.T.word(t, wi), 8n))), U32.add(Y.BP.ext(A.T.word(t, wi), 16n), Y.BP.ext(A.T.word(t, wi), 24n))), U32.add(U32.add(U32.add(U32.add(b, U32.shln(a, 2n)), U32.shln(Y.BP.ext(A.T.word(t, wi), 0n), 2n)), U32.mul(Y.BP.ext(A.T.word(t, wi), 8n), 3)), U32.add(U32.shln(Y.BP.ext(A.T.word(t, wi), 16n), 1n), Y.BP.ext(A.T.word(t, wi), 24n)))}))) : Array<U32> & U32 & U32}
      {==}

# Chunks
# ======

law AD.m_le.go:
  for +nw: U32
  for +c: Bool
  for +ec: {U32.is_lt(nw, 1388) == c : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(nw, 1388)), V.U.N(1388))) == True{} : Bool}

def AD.m_le.go(nw, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(nw, 1388), Bool.pick(U32, U32.is_lt(nw, 1388), nw, 1388), K.WD.min(nw, 1388)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(1388))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(nw, 1388), True{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, nw, 1388)), V.U.N(1388))) == True{} : Bool}
      P.Nat.lt_to_le(V.U.N(nw), V.U.N(1388), V.U.lt_N(nw, 1388, ec))
    case False{}:
      %Equal.sym(U32, U32.min(nw, 1388), Bool.pick(U32, U32.is_lt(nw, 1388), nw, 1388), K.WD.min(nw, 1388)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(1388))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(nw, 1388), False{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, nw, 1388)), V.U.N(1388))) == True{} : Bool}
      C.CP.le_refl(V.U.N(1388))

# A chunk has at most 1388 words.
law AD.m_le:
  for +nw: U32
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(nw, 1388)), V.U.N(1388))) == True{} : Bool}

def AD.m_le(nw):
  AD.m_le.go(nw, U32.is_lt(nw, 1388), {==})

# Four times a small value.
law AD.shl4:
  for +m: U32
  for +h: {Cmp.is_le(Nat.cmp(V.U.N(m), V.U.N(1388))) == True{} : Bool}
  {V.U.N(U32.shln(m, 2n)) == Nat.double(Nat.double(V.U.N(m))) : Nat}

def AD.shl4(m, h):
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shl(m))), Nat.double(V.U.N(U32.shl(m))), V.U.N_shl(U32.shl(m), (%Equal.sym(Bool, V.U.bit(U32.shl(m), 31n), V.U.bit(m, 30n), V.U.bit_shl(m, 30n, {==})) : {_ == False{} : Bool}; V.U.bit_high(m, 11n, 30n, P.Nat.le_lt_trans(V.U.N(m), V.U.N(1388), P.Nat.pow2(11n), h, {==}), {==})))) :
    {_ == Nat.double(Nat.double(V.U.N(m))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(m)), Nat.double(V.U.N(m)), V.U.N_shl(m, V.U.bit_high(m, 11n, 31n, P.Nat.le_lt_trans(V.U.N(m), V.U.N(1388), P.Nat.pow2(11n), h, {==}), {==}))) :
    {Nat.double(_) == Nat.double(Nat.double(V.U.N(m))) : Nat}
  {==}

law AD.min_le_l.go:
  for +nw: U32
  for +b: U32
  for +c: Bool
  for +ec: {U32.is_lt(nw, b) == c : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(nw, b)), V.U.N(nw))) == True{} : Bool}

def AD.min_le_l.go(nw, b, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(nw, b), Bool.pick(U32, U32.is_lt(nw, b), nw, b), K.WD.min(nw, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(nw))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(nw, b), True{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, nw, b)), V.U.N(nw))) == True{} : Bool}
      C.CP.le_refl(V.U.N(nw))
    case False{}:
      %Equal.sym(U32, U32.min(nw, b), Bool.pick(U32, U32.is_lt(nw, b), nw, b), K.WD.min(nw, b)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(nw))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(nw, b), False{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(Bool.pick(U32, _, nw, b)), V.U.N(nw))) == True{} : Bool}
      V.U.le_N(b, nw, V.U.not_lt(nw, b, ec))

# min(a, b) <= a.
law AD.min_le_l:
  for +nw: U32
  for +b: U32
  {Cmp.is_le(Nat.cmp(V.U.N(U32.min(nw, b)), V.U.N(nw))) == True{} : Bool}

def AD.min_le_l(nw, b):
  AD.min_le_l.go(nw, b, U32.is_lt(nw, b), {==})

law AD.red_ok:
  for +t: A.Tr
  for +w: AB
  {B.B.adler.red((A.A.from(t), AD.pr(w))) == (A.A.from(t), AD.pr(AD.red(w))) : Array<U32> & (U32 & U32)}

def AD.red_ok(t, w):
  match w:
    case AB{a, b}:
      {==}

# Four times the word count of a chunk, below the bound.
law AD.hbm:
  for +nw: U32
  for +i: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), V.U.N(i)), V.U.N(E))) == True{} : Bool}

law AD.dd_le:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(a)), Nat.double(Nat.double(b)))) == True{} : Bool}

def AD.dd_le(a, b, h):
  match a b:
    case 0n _:
      P.Nat.le_zero(Nat.double(Nat.double(b)))
    case 1n+p 0n:
      P.Bool.false_true({Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+p)), Nat.double(Nat.double(0n)))) == True{} : Bool}, h)
    case 1n+p 1n+q:
      AD.dd_le(p, q, h)

def AD.hbm(nw, i, E, hb):
  P.Nat.le_trans(Nat.add(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), V.U.N(i)), Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E),
    C.CP.le_add_r(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(nw))), V.U.N(i), AD.dd_le(V.U.N(U32.min(nw, 1388)), V.U.N(nw), AD.min_le_l(nw, 1388))),
    hb)

law AD.h1:
  for +i: U32
  for +nw: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), V.U.N(U32.shln(U32.min(nw, 1388), 2n))), V.U.N(E))) == True{} : Bool}

def AD.h1(i, nw, E, hb):
  %Equal.sym(Nat, V.U.N(U32.shln(U32.min(nw, 1388), 2n)), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), AD.shl4(U32.min(nw, 1388), AD.m_le(nw))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), _), V.U.N(E))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(i), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))), Nat.add(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), V.U.N(i)), P.Nat.add_comm(V.U.N(i), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}
  AD.hbm(nw, i, E, hb)

law AD.h2:
  for +i: U32
  for +wi: U32
  for +nw: U32
  for +E: U32
  for +ed: {V.U.N(i) == Nat.double(Nat.double(V.U.N(wi))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(wi), V.U.N(U32.min(nw, 1388))), V.U.N(E))) == True{} : Bool}

law AD.add_le:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(c, d)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(a, c), Nat.add(b, d))) == True{} : Bool}

def AD.add_le(a, b, c, d, h1, h2):
  P.Nat.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), C.CP.le_add_r(a, b, c, h1),
    (%Equal.sym(Cmp, Nat.cmp(Nat.add(b, c), Nat.add(b, d)), Nat.cmp(c, d), P.Nat.cmp_add_l(b, c, d)) : {Cmp.is_le(_) == True{} : Bool}; h2))

def AD.h2(i, wi, nw, E, ed, hb):
  P.Nat.le_trans(Nat.add(V.U.N(wi), V.U.N(U32.min(nw, 1388))), Nat.add(V.U.N(i), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))), V.U.N(E),
    AD.add_le(V.U.N(wi), V.U.N(i), V.U.N(U32.min(nw, 1388)), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))),
      (%Equal.sym(Nat, V.U.N(i), Nat.double(Nat.double(V.U.N(wi))), ed) : {Cmp.is_le(Nat.cmp(V.U.N(wi), _)) == True{} : Bool}; K.WD.le_quad(0n, V.U.N(wi))),
      K.WD.le_quad(0n, V.U.N(U32.min(nw, 1388)))),
    (%AD.shl4(U32.min(nw, 1388), AD.m_le(nw)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), _), V.U.N(E))) == True{} : Bool}; AD.h1(i, nw, E, hb)))

# The next chunk's position is aligned to its word.
law AD.ed2:
  for +i: U32
  for +wi: U32
  for +nw: U32
  for +E: U32
  for +ed: {V.U.N(i) == Nat.double(Nat.double(V.U.N(wi))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(i, U32.shln(U32.min(nw, 1388), 2n))) == Nat.double(Nat.double(V.U.N(U32.add(wi, U32.min(nw, 1388))))) : Nat}

def AD.ed2(i, wi, nw, E, ed, hb):
  %Equal.sym(Nat, V.U.N(U32.add(i, U32.shln(U32.min(nw, 1388), 2n))), Nat.add(V.U.N(i), V.U.N(U32.shln(U32.min(nw, 1388), 2n))), V.U.add_N(i, U32.shln(U32.min(nw, 1388), 2n), E, AD.h1(i, nw, E, hb))) :
    {_ == Nat.double(Nat.double(V.U.N(U32.add(wi, U32.min(nw, 1388))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shln(U32.min(nw, 1388), 2n)), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), AD.shl4(U32.min(nw, 1388), AD.m_le(nw))) :
    {Nat.add(V.U.N(i), _) == Nat.double(Nat.double(V.U.N(U32.add(wi, U32.min(nw, 1388))))) : Nat}
  %Equal.sym(Nat, V.U.N(i), Nat.double(Nat.double(V.U.N(wi))), ed) :
    {Nat.add(_, Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))) == Nat.double(Nat.double(V.U.N(U32.add(wi, U32.min(nw, 1388))))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(wi, U32.min(nw, 1388))), Nat.add(V.U.N(wi), V.U.N(U32.min(nw, 1388))), V.U.add_N(wi, U32.min(nw, 1388), E, AD.h2(i, wi, nw, E, ed, hb))) :
    {Nat.add(Nat.double(Nat.double(V.U.N(wi))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))) == Nat.double(Nat.double(_)) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(V.U.N(wi), V.U.N(U32.min(nw, 1388)))), Nat.add(Nat.double(V.U.N(wi)), Nat.double(V.U.N(U32.min(nw, 1388)))), P.Nat.double_distr(V.U.N(wi), V.U.N(U32.min(nw, 1388)))) :
    {Nat.add(Nat.double(Nat.double(V.U.N(wi))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))) == Nat.double(_) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.double(V.U.N(wi)), Nat.double(V.U.N(U32.min(nw, 1388))))), Nat.add(Nat.double(Nat.double(V.U.N(wi))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))), P.Nat.double_distr(Nat.double(V.U.N(wi)), Nat.double(V.U.N(U32.min(nw, 1388))))) :
    {Nat.add(Nat.double(Nat.double(V.U.N(wi))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))) == _ : Nat}
  {==}

# The rest of the words, from the next chunk.
law AD.hb2:
  for +i: U32
  for +nw: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), V.U.N(U32.add(i, U32.shln(U32.min(nw, 1388), 2n)))), V.U.N(E))) == True{} : Bool}

def AD.hb2(i, nw, E, hb):
  %Equal.sym(Nat, V.U.N(U32.add(i, U32.shln(U32.min(nw, 1388), 2n))), Nat.add(V.U.N(i), V.U.N(U32.shln(U32.min(nw, 1388), 2n))), V.U.add_N(i, U32.shln(U32.min(nw, 1388), 2n), E, AD.h1(i, nw, E, hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), _), V.U.N(E))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.shln(U32.min(nw, 1388), 2n)), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), AD.shl4(U32.min(nw, 1388), AD.m_le(nw))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), Nat.add(V.U.N(i), _)), V.U.N(E))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(i), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388))))), Nat.add(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), V.U.N(i)), P.Nat.add_comm(V.U.N(i), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), _), V.U.N(E))) == True{} : Bool}
  %P.Nat.add_assoc(Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), V.U.N(i)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}
  %P.Nat.double_distr(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388)))), Nat.double(V.U.N(U32.min(nw, 1388)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(i)), V.U.N(E))) == True{} : Bool}
  %P.Nat.double_distr(V.U.N(U32.sub(nw, U32.min(nw, 1388))), V.U.N(U32.min(nw, 1388))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(_), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(nw, U32.min(nw, 1388))), V.U.N(U32.min(nw, 1388))), V.U.N(nw), V.U.sub_nat(nw, U32.min(nw, 1388), V.U.N_le(U32.min(nw, 1388), nw, AD.min_le_l(nw, 1388)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(_)), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  hb

# The chunked word loop.
law AD.go_ok:
  for +k: Nat
  for +wi: U32
  for +nw: U32
  for +i: U32
  for +t: A.Tr
  for +w: AB
  for +E: U32
  for +ed: {V.U.N(i) == Nat.double(Nat.double(V.U.N(wi))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {B.B.adler.go(k, wi, nw, (A.A.from(t), AD.pr(w))) == (A.A.from(t), AD.pr(AD.go(k, t, i, nw, w))) : Array<U32> & (U32 & U32)}

def AD.go_ok(k, wi, nw, i, t, w, E, ed, hb):
  match k w:
    case 0n _:
      {==}
    case 1n+p AB{a, b}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), wi), (A.A.from(t), A.T.word(t, wi)), A.A.get_from(t, wi)) :
        {B.B.adler.go(p, U32.add(wi, U32.min(nw, 1388)), U32.sub(nw, U32.min(nw, 1388)), B.B.adler.red(B.B.adler.words(U32.to_nat(U32.min(nw, 1388)), a, b, wi, _))) == (A.A.from(t), AD.pr(AD.go(p, t, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.words(U32.to_nat(U32.min(nw, 1388)), a, b, wi, (A.A.from(t), A.T.word(t, wi))), (A.A.from(t), AD.pr(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))), AD.words(U32.to_nat(U32.min(nw, 1388)), a, b, wi, i, t, E, ed, AD.hbm(nw, i, E, hb))) :
        {B.B.adler.go(p, U32.add(wi, U32.min(nw, 1388)), U32.sub(nw, U32.min(nw, 1388)), B.B.adler.red(_)) == (A.A.from(t), AD.pr(AD.go(p, t, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.red((A.A.from(t), AD.pr(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b})))), (A.A.from(t), AD.pr(AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b})))), AD.red_ok(t, AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))) :
        {B.B.adler.go(p, U32.add(wi, U32.min(nw, 1388)), U32.sub(nw, U32.min(nw, 1388)), _) == (A.A.from(t), AD.pr(AD.go(p, t, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.go(p, U32.add(wi, U32.min(nw, 1388)), U32.sub(nw, U32.min(nw, 1388)), (A.A.from(t), AD.pr(AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))), (A.A.from(t), AD.pr(AD.go(p, t, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))), AD.go_ok(p, U32.add(wi, U32.min(nw, 1388)), U32.sub(nw, U32.min(nw, 1388)), U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), t, AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b})), E, AD.ed2(i, wi, nw, E, ed, hb), AD.hb2(i, nw, E, hb))) :
        {_ == (A.A.from(t), AD.pr(AD.go(p, t, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(U32.to_nat(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(U32.to_nat(U32.min(nw, 1388)))), t, i), AB{a, b}))))) : Array<U32> & U32 & U32}
      {==}

law AD.fin_ok:
  for +t: A.Tr
  for +w: AB
  {B.B.adler.fin((A.A.from(t), AD.pr(w))) == (A.A.from(t), AD.fin(w)) : Array<U32> & U32}

def AD.fin_ok(t, w):
  match w:
    case AB{a, b}:
      {==}

# The trailing bytes.
law AD.tail_ok:
  for +i: U32
  for +n: U32
  for +t: A.Tr
  for +w: AB
  {B.B.adler.tail(i, n, (A.A.from(t), AD.pr(w))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), w)))) : Array<U32> & U32}

def AD.tail_ok(i, n, t, w):
  match w:
    case AB{a, b}:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), i), (A.A.from(t), Y.BP.byt(t, i)), Y.BP.get_from(t, i)) :
        {B.B.adler.fin(B.B.adler.red(B.B.adler.bytes(U32.to_nat(n), a, b, i, _))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.bytes(U32.to_nat(n), a, b, i, (A.A.from(t), Y.BP.byt(t, i))), (A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b}))), AD.bytes(U32.to_nat(n), a, b, i, t)) :
        {B.B.adler.fin(B.B.adler.red(_)) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.red((A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))), (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))), AD.red_ok(t, AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b}))) :
        {B.B.adler.fin(_) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.adler.fin((A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b}))))), (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))), AD.fin_ok(t, AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))) :
        {_ == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{a, b})))) : Array<U32> & U32}
      {==}

# The words after the head, inside the bound.
law AD.hbw:
  for +i: U32
  for +n: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  for +ec: {U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n)))), V.U.N(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), V.U.N(E))) == True{} : Bool}

def AD.hbw(i, n, E, hb, ec):
  %Equal.sym(Nat, V.U.N(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3))), Nat.add(V.U.N(i), V.U.N(U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.add_N(i, U32.and(U32.sub(4, U32.and(i, 3)), 3), E, C.CP.le_part(V.U.N(i), V.U.N(U32.and(U32.sub(4, U32.and(i, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(i, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3), ec)), hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n)))), _), V.U.N(E))) == True{} : Bool}
  C.CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n)))), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(i, 3)), 3)), V.U.N(n), V.U.N(i), V.U.N(E),
    (%Equal.sym(Nat, V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n))))), K.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n)))), _)) == True{} : Bool};
      P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n)))))),
    V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(i, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3), ec)), hb)

law AD.ok.go:
  for +t: A.Tr
  for +i: U32
  for +n: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)) == c : Bool}
  {B.B.adler32(A.A.from(t), i, n) == (A.A.from(t), AD.T(t, i, n)) : Array<U32> & U32}

def AD.ok.go(t, i, n, E, hb, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), K.WD.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))) :
        {B.B.adler.body(U32.add(i, _), U32.sub(n, _), B.B.adler.red(B.B.adler.bytes(U32.to_nat(_), 1, 0, i, B.B.get(A.A.from(t), i)))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, _), 3)), t, U32.add(U32.add(i, _), U32.shln(U32.shrn(U32.sub(n, _), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, _), 2n), 1387), 1388)), t, U32.add(i, _), U32.shrn(U32.sub(n, _), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(_), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), True{}, ec) :
        {B.B.adler.body(U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), B.B.adler.red(B.B.adler.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 1, 0, i, B.B.get(A.A.from(t), i)))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t, U32.add(U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t, U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), i), (A.A.from(t), Y.BP.byt(t, i)), Y.BP.get_from(t, i)) :
        {B.B.adler.body(U32.add(i, n), U32.sub(n, n), B.B.adler.red(B.B.adler.bytes(U32.to_nat(n), 1, 0, i, _))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, n), 3)), t, U32.add(U32.add(i, n), U32.shln(U32.shrn(U32.sub(n, n), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, n), 2n), 1387), 1388)), t, U32.add(i, n), U32.shrn(U32.sub(n, n), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.bytes(U32.to_nat(n), 1, 0, i, (A.A.from(t), Y.BP.byt(t, i))), (A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))), AD.bytes(U32.to_nat(n), 1, 0, i, t)) :
        {B.B.adler.body(U32.add(i, n), U32.sub(n, n), B.B.adler.red(_)) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, n), 3)), t, U32.add(U32.add(i, n), U32.shln(U32.shrn(U32.sub(n, n), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, n), 2n), 1387), 1388)), t, U32.add(i, n), U32.shrn(U32.sub(n, n), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.red((A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0})))), (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0})))), AD.red_ok(t, AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))) :
        {B.B.adler.body(U32.add(i, n), U32.sub(n, n), _) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, n), 3)), t, U32.add(U32.add(i, n), U32.shln(U32.shrn(U32.sub(n, n), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, n), 2n), 1387), 1388)), t, U32.add(i, n), U32.shrn(U32.sub(n, n), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(U32, U32.sub(n, n), 0, K.WD.sub_self(n)) :
        {B.B.adler.body(U32.add(i, n), _, (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(_, 3)), t, U32.add(U32.add(i, n), U32.shln(U32.shrn(_, 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(_, 2n), 1387), 1388)), t, U32.add(i, n), U32.shrn(_, 2n), AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.adler.tail(U32.add(U32.add(i, n), 0), 0, (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))), (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(0n, t, U32.add(U32.add(i, n), 0)), AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0})))))), AD.tail_ok(U32.add(U32.add(i, n), 0), 0, t, AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0})))) :
        {_ == (A.A.from(t), AD.fin(AD.red(AD.red(AD.by(S.S.sl(U32.to_nat(n), t, i), AB{1, 0}))))) : Array<U32> & U32}
      {==}
    case False{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), K.WD.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))) :
        {B.B.adler.body(U32.add(i, _), U32.sub(n, _), B.B.adler.red(B.B.adler.bytes(U32.to_nat(_), 1, 0, i, B.B.get(A.A.from(t), i)))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, _), 3)), t, U32.add(U32.add(i, _), U32.shln(U32.shrn(U32.sub(n, _), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, _), 2n), 1387), 1388)), t, U32.add(i, _), U32.shrn(U32.sub(n, _), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(_), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), False{}, ec) :
        {B.B.adler.body(U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), B.B.adler.red(B.B.adler.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 1, 0, i, B.B.get(A.A.from(t), i)))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t, U32.add(U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t, U32.add(i, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), i), (A.A.from(t), Y.BP.byt(t, i)), Y.BP.get_from(t, i)) :
        {B.B.adler.body(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), B.B.adler.red(B.B.adler.bytes(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), 1, 0, i, _))) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.bytes(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), 1, 0, i, (A.A.from(t), Y.BP.byt(t, i))), (A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))), AD.bytes(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), 1, 0, i, t)) :
        {B.B.adler.body(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), B.B.adler.red(_)) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.red((A.A.from(t), AD.pr(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0})))), (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0})))), AD.red_ok(t, AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))) :
        {B.B.adler.body(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), _) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32 & U32, B.B.adler.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), U32.shrn(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), (A.A.from(t), AD.pr(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))), (A.A.from(t), AD.pr(AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))), AD.go_ok(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), U32.shrn(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0})), E, C.CP.align(i, E, C.CP.le_part(V.U.N(i), V.U.N(U32.and(U32.sub(4, U32.and(i, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(i, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3), ec)), hb)), AD.hbw(i, n, E, hb, ec))) :
        {B.B.adler.tail(U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n)), U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3), _) == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      %Equal.sym(Array<U32> & U32, B.B.adler.tail(U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n)), U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3), (A.A.from(t), AD.pr(AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0})))))), (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))), AD.tail_ok(U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n)), U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3), t, AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))) :
        {_ == (A.A.from(t), AD.fin(AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 3)), t, U32.add(U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 2n))), AD.go(U32.to_nat(U32.div(U32.add(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), 1387), 1388)), t, U32.add(i, U32.and(U32.sub(4, U32.and(i, 3)), 3)), U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), 2n), AD.red(AD.by(S.S.sl(U32.to_nat(U32.and(U32.sub(4, U32.and(i, 3)), 3)), t, i), AB{1, 0}))))))) : Array<U32> & U32}
      {==}

# Adler-32 of [i, i + n) in an array.
law AD.ok:
  for +t: A.Tr
  for +i: U32
  for +n: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {B.B.adler32(A.A.from(t), i, n) == (A.A.from(t), AD.T(t, i, n)) : Array<U32> & U32}

def AD.ok(t, i, n, E, hb):
  AD.ok.go(t, i, n, E, hb, U32.is_lt(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), {==})

# Equal bytes, equal sums
# =======================

# x = y + (x - y) when y <= x.
law AD.split:
  for +x: U32
  for +y: U32
  for +h: {Cmp.is_le(Nat.cmp(V.U.N(y), V.U.N(x))) == True{} : Bool}
  {V.U.N(x) == Nat.add(V.U.N(y), V.U.N(U32.sub(x, y))) : Nat}

def AD.split(x, y, h):
  %Equal.sym(Nat, Nat.add(V.U.N(y), V.U.N(U32.sub(x, y))), Nat.add(V.U.N(U32.sub(x, y)), V.U.N(y)), P.Nat.add_comm(V.U.N(y), V.U.N(U32.sub(x, y)))) :
    {V.U.N(x) == _ : Nat}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(x, y)), V.U.N(y)), V.U.N(x), V.U.sub_nat(x, y, V.U.N_le(y, x, h))) :
    {V.U.N(x) == _ : Nat}
  {==}

law AD.dd_split:
  for +nw: U32
  {Nat.double(Nat.double(V.U.N(nw))) == Nat.add(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388)))))) : Nat}

def AD.dd_split(nw):
  %P.Nat.double_distr(Nat.double(V.U.N(U32.min(nw, 1388))), Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))) :
    {Nat.double(Nat.double(V.U.N(nw))) == _ : Nat}
  %P.Nat.double_distr(V.U.N(U32.min(nw, 1388)), V.U.N(U32.sub(nw, U32.min(nw, 1388)))) :
    {Nat.double(Nat.double(V.U.N(nw))) == Nat.double(_) : Nat}
  %AD.split(nw, U32.min(nw, 1388), AD.min_le_l(nw, 1388)) :
    {Nat.double(Nat.double(V.U.N(nw))) == Nat.double(Nat.double(_)) : Nat}
  {==}

# Equal slices, cut in two.
law AD.sl_cut:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +t1: A.Tr
  for +t2: A.Tr
  for +i: U32
  for +ea: {a == Nat.add(b, c) : Nat}
  for +e: {S.S.sl(a, t1, i) == S.S.sl(a, t2, i) : List<&2, U32>}
  {S.S.sl(Nat.add(b, c), t1, i) == S.S.sl(Nat.add(b, c), t2, i) : List<&2, U32>}

def AD.sl_cut(a, b, c, t1, t2, i, ea, e):
  %ea :
    {S.S.sl(_, t1, i) == S.S.sl(_, t2, i) : List<&2, U32>}
  e

# The chunks read only the words' bytes.
law AD.go_eq:
  for +k: Nat
  for +t1: A.Tr
  for +t2: A.Tr
  for +i: U32
  for +nw: U32
  for +s: AB
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(nw))), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  for +e: {S.S.sl(Nat.double(Nat.double(V.U.N(nw))), t1, i) == S.S.sl(Nat.double(Nat.double(V.U.N(nw))), t2, i) : List<&2, U32>}
  {AD.go(k, t1, i, nw, s) == AD.go(k, t2, i, nw, s) : AB}

def AD.go_eq(k, t1, t2, i, nw, s, E, hb, e):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, U32>, S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t1, i), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), K.WD.sl_pre(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), t1, t2, i, AD.sl_cut(Nat.double(Nat.double(V.U.N(nw))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), t1, t2, i, AD.dd_split(nw), e))) :
        {AD.go(p, t1, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), _, s))) == AD.go(p, t2, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), s))) : AB}
      %Equal.sym(AB, AD.go(p, t1, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), s))), AD.go(p, t2, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), s))), AD.go_eq(p, t1, t2, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), s)), E, AD.hb2(i, nw, E, hb), K.WD.sl_suf(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), t1, t2, i, U32.shln(U32.min(nw, 1388), 2n), AD.shl4(U32.min(nw, 1388), AD.m_le(nw)), AD.sl_cut(Nat.double(Nat.double(V.U.N(nw))), Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), Nat.double(Nat.double(V.U.N(U32.sub(nw, U32.min(nw, 1388))))), t1, t2, i, AD.dd_split(nw), e)))) :
        {_ == AD.go(p, t2, U32.add(i, U32.shln(U32.min(nw, 1388), 2n)), U32.sub(nw, U32.min(nw, 1388)), AD.red(AD.wo(V.U.N(U32.min(nw, 1388)), S.S.sl(Nat.double(Nat.double(V.U.N(U32.min(nw, 1388)))), t2, i), s))) : AB}
      {==}

# x is 4 (x >> 2) + (x & 3).
law AD.mod4c:
  for +x: U32
  {V.U.N(x) == Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))), V.U.N(U32.and(x, 3))) : Nat}

def AD.mod4c(x):
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))), V.U.N(U32.and(x, 3))), Nat.add(V.U.N(U32.and(x, 3)), Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n))))), P.Nat.add_comm(Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))), V.U.N(U32.and(x, 3)))) :
    {V.U.N(x) == _ : Nat}
  K.WD.mod4(x)

# The words after h bytes of n, inside the bound.
law AD.hbg:
  for +i: U32
  for +n: U32
  for +h: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  for +hle: {Cmp.is_le(Nat.cmp(V.U.N(h), V.U.N(n))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n)))), V.U.N(U32.add(i, h))), V.U.N(E))) == True{} : Bool}

def AD.hbg(i, n, h, E, hb, hle):
  %Equal.sym(Nat, V.U.N(U32.add(i, h)), Nat.add(V.U.N(i), V.U.N(h)), V.U.add_N(i, h, E, C.CP.le_part(V.U.N(i), V.U.N(h), V.U.N(n), V.U.N(E), hle, hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n)))), _), V.U.N(E))) == True{} : Bool}
  C.CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n)))), V.U.N(U32.sub(n, h)), V.U.N(h), V.U.N(n), V.U.N(i), V.U.N(E),
    (%Equal.sym(Nat, V.U.N(U32.sub(n, h)), Nat.add(V.U.N(U32.and(U32.sub(n, h), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n))))), K.WD.mod4(U32.sub(n, h))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n)))), _)) == True{} : Bool};
      P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, h), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, h), 2n)))))),
    V.U.sub_nat(n, h, V.U.N_le(h, n, hle)), hb)

# Two arrays with the same bytes in [i, i + n) have the same checksum there.
law AD.eq:
  for +t1: A.Tr
  for +t2: A.Tr
  for +i: U32
  for +n: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(i)), V.U.N(E))) == True{} : Bool}
  for +e: {S.S.sl(V.U.N(n), t1, i) == S.S.sl(V.U.N(n), t2, i) : List<&2, U32>}
  {AD.T(t1, i, n) == AD.T(t2, i, n) : U32}

def AD.eq(t1, t2, i, n, E, hb, e):
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t1, i), S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), K.WD.sl_pre(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, AD.sl_cut(V.U.N(n), V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, AD.split(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), AD.min_le_l(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), e))) :
    {AD.fin(AD.red(AD.by(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t1, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(_, AB{1, 0})))))) == AD.fin(AD.red(AD.by(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t2, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0})))))) : U32}
  %Equal.sym(AB, AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t1, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0}))), AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0}))), AD.go_eq(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t1, t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0})), E, AD.hbg(i, n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), E, hb, AD.min_le_l(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), K.WD.sl_pre(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n)))), V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), AD.sl_cut(V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n)))), V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), AD.mod4c(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), K.WD.sl_suf(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), {==}, AD.sl_cut(V.U.N(n), V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, AD.split(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), AD.min_le_l(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), e)))))) :
    {AD.fin(AD.red(AD.by(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), _))) == AD.fin(AD.red(AD.by(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t2, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0})))))) : U32}
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t2, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), K.WD.sl_suf(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n)))), V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n), K.WD.shl2(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), AD.sl_cut(V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n)))), V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t1, t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), AD.mod4c(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), K.WD.sl_suf(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), {==}, AD.sl_cut(V.U.N(n), V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), V.U.N(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)))), t1, t2, i, AD.split(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3)), AD.min_le_l(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), e))))) :
    {AD.fin(AD.red(AD.by(_, AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0})))))) == AD.fin(AD.red(AD.by(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 3)), t2, U32.add(U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shln(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 2n))), AD.go(V.U.N(U32.div(U32.add(U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), 1387), 1388)), t2, U32.add(i, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), U32.shrn(U32.sub(n, U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), 2n), AD.red(AD.by(S.S.sl(V.U.N(U32.min(n, U32.and(U32.sub(4, U32.and(i, 3)), 3))), t2, i), AB{1, 0})))))) : U32}
  {==}
