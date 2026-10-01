import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./fallback.bend as F

# Decoding the plain encoding (proofs/fallback.bend): the decoder reads the
# header, then each window, and copies each window's byte to the target.

# Reads
# =====

# A read of a byte the tree holds.
law R.rd:
  for +td: A.Tr
  for +q: U32
  for +v: U32
  for +rest: List<&2, U32>
  for +h: {S.S.has(v <> rest, td, q) == True{} : Bool}
  {B.B.get(A.A.from(td), q) == (A.A.from(td), U32.and(v, 255)) : Array<U32> & U32}

def R.rd(td, q, v, rest, h):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), q), (A.A.from(td), Y.BP.byt(td, q)), Y.BP.get_from(td, q)) :
    {_ == (A.A.from(td), U32.and(v, 255)) : Array<U32> & U32}
  %Equal.sym(U32, Y.BP.byt(td, q), U32.and(v, 255),
    V.U.is_eq(Y.BP.byt(td, q), U32.and(v, 255),
      P.Bool.and_l(U32.is_eq(Y.BP.byt(td, q), U32.and(v, 255)), S.S.has(rest, td, (q + 1 : U32)), h))) :
    {(A.A.from(td), _) == (A.A.from(td), U32.and(v, 255)) : Array<U32> & U32}
  {==}

# The rest of a list held.
law R.tl:
  for +td: A.Tr
  for +q: U32
  for +v: U32
  for +rest: List<&2, U32>
  for +h: {S.S.has(v <> rest, td, q) == True{} : Bool}
  {S.S.has(rest, td, (q + 1 : U32)) == True{} : Bool}

def R.tl(td, q, v, rest, h):
  P.Bool.and_r(U32.is_eq(Y.BP.byt(td, q), U32.and(v, 255)), S.S.has(rest, td, (q + 1 : U32)), h)

# The file header
# ===============

law H.parse:
  for +td: A.Tr
  for +dlen: U32
  for +rest: List<&2, U32>
  for +h: {S.S.has(F.F.hdr(rest), td, 0) == True{} : Bool}
  for +hl: {Nat.cmp(4n, V.U.N(dlen)) == LT{} : Cmp}
  {D.hdr.parse(A.A.from(td), dlen) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}

def H.parse(td, dlen, rest, h, hl):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), 0), (A.A.from(td), 214),
    R.rd(td, 0, 214, 195 <> 196 <> 0 <> 0 <> rest, h)) :
    {D.hdr.magic(dlen, D.be32.k0(0, dlen, _)) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), 1), (A.A.from(td), 195),
    R.rd(td, 1, 195, 196 <> 0 <> 0 <> rest, R.tl(td, 0, 214, 195 <> 196 <> 0 <> 0 <> rest, h))) :
    {D.hdr.magic(dlen, D.be32.k1(214, 1, dlen, _)) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), 2), (A.A.from(td), 196),
    R.rd(td, 2, 196, 0 <> 0 <> rest, R.tl(td, 1, 195, 196 <> 0 <> 0 <> rest, R.tl(td, 0, 214, 195 <> 196 <> 0 <> 0 <> rest, h)))) :
    {D.hdr.magic(dlen, D.be32.k2(54979, 2, dlen, _)) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), 3), (A.A.from(td), 0),
    R.rd(td, 3, 0, 0 <> rest, R.tl(td, 2, 196, 0 <> 0 <> rest, R.tl(td, 1, 195, 196 <> 0 <> 0 <> rest, R.tl(td, 0, 214, 195 <> 196 <> 0 <> 0 <> rest, h))))) :
    {D.hdr.magic(dlen, D.be32.k3(14074820, 3, dlen, _)) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Bool, U32.is_lt(3, dlen), True{}, V.U.N_lt(3, dlen, P.Nat.lt_succ_l(3n, V.U.N(dlen), hl))) :
    {D.hdr.magic(dlen, B.VR{A.A.from(td), 3603153920, 4, _}) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), 4), (A.A.from(td), 0),
    R.rd(td, 4, 0, rest, R.tl(td, 3, 0, 0 <> rest, R.tl(td, 2, 196, 0 <> 0 <> rest, R.tl(td, 1, 195, 196 <> 0 <> 0 <> rest, R.tl(td, 0, 214, 195 <> 196 <> 0 <> 0 <> rest, h)))))) :
    {D.hdr.ind(0, dlen, B.B.byte.k(4, dlen, _)) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  %Equal.sym(Bool, U32.is_lt(4, dlen), True{}, V.U.N_lt(4, dlen, hl)) :
    {D.hdr.ind(0, dlen, B.VR{A.A.from(td), 0, 5, _}) == (A.A.from(td), (5, 0)) : Array<U32> & (U32 & U32)}
  {==}

# A window's header
# =================

law W.parse:
  for +td: A.Tr
  for +p: U32
  for +dlen: U32
  for +x: U32
  for +rest: List<&2, U32>
  for +h: {S.S.has(F.F.win(x, rest), td, p) == True{} : Bool}
  for +l0: {U32.is_lt(p, dlen) == True{} : Bool}
  for +l1: {U32.is_lt((p + 1 : U32), dlen) == True{} : Bool}
  for +l2: {U32.is_lt(((p + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l3: {U32.is_lt((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l4: {U32.is_lt(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l5: {U32.is_lt((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l6: {U32.is_lt(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +le7: {U32.is_le(7, U32.sub(dlen, ((p + 1 : U32) + 1 : U32))) == True{} : Bool}
  for +hw: {(((p + 1 : U32) + 1 : U32) + 7 : U32) == (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  for +hs: {U32.sub((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == 2 : U32}
  for +hb: {U32.is_le((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == True{} : Bool}
  {D.win.parse(A.A.from(td), p, dlen) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}

def W.parse(td, p, dlen, x, rest, h, l0, l1, l2, l3, l4, l5, l6, le7, hw, hs, hb):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), p), (A.A.from(td), 0),
    R.rd(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)) :
    {D.wp.ind(dlen, B.B.byte.k(p, dlen, _)) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(p, dlen), True{}, l0) :
    {D.wp.ind(dlen, B.VR{A.A.from(td), 0, (p + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), (p + 1 : U32)), (A.A.from(td), 7),
    R.rd(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h))) :
    {D.wp.enc(0, 0, 0, 0, dlen, B.B.var.go(5n, dlen, 0, (p + 1 : U32), True{}, B.B.var.cont(_))) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt((p + 1 : U32), dlen), True{}, l1) :
    {D.wp.enc(0, 0, 0, 0, dlen, B.VR{A.A.from(td), 7, ((p + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_le(7, U32.sub(dlen, ((p + 1 : U32) + 1 : U32))), True{}, le7) :
    {D.wp.tlen(0, 0, 0, (((p + 1 : U32) + 1 : U32) + 7 : U32), D.err.set(0, Bool.not(_), D.E.TRUNCATED()), dlen, B.B.var.get(A.A.from(td), ((p + 1 : U32) + 1 : U32), dlen)) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(U32, (((p + 1 : U32) + 1 : U32) + 7 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), hw) :
    {D.wp.tlen(0, 0, 0, _, 0, dlen, B.B.var.get(A.A.from(td), ((p + 1 : U32) + 1 : U32), dlen)) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ((p + 1 : U32) + 1 : U32)), (A.A.from(td), 1),
    R.rd(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)))) :
    {D.wp.tlen(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, dlen, B.B.var.go(5n, dlen, 0, ((p + 1 : U32) + 1 : U32), True{}, B.B.var.cont(_))) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(((p + 1 : U32) + 1 : U32), dlen), True{}, l2) :
    {D.wp.tlen(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, dlen, B.VR{A.A.from(td), 1, (((p + 1 : U32) + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), (((p + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 0),
    R.rd(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h))))) :
    {D.wp.dli(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, dlen, B.B.byte.k((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, _)) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, l3) :
    {D.wp.dli(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, dlen, B.VR{A.A.from(td), 0, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 1),
    R.rd(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)))))) :
    {D.wp.dl(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 0, dlen, B.B.var.go(5n, dlen, 0, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), True{}, B.B.var.cont(_))) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, l4) :
    {D.wp.dl(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 0, dlen, B.VR{A.A.from(td), 1, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 1),
    R.rd(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> x <> 2 <> rest, R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h))))))) :
    {D.wp.il(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 1, 0, dlen, B.B.var.go(5n, dlen, 0, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), True{}, B.B.var.cont(_))) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, l5) :
    {D.wp.il(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 1, 0, dlen, B.VR{A.A.from(td), 1, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 0),
    R.rd(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, x <> 2 <> rest, R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> x <> 2 <> rest, R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)))))))) :
    {D.wp.al(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 1, 1, 0, dlen, B.B.var.go(5n, dlen, 0, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), True{}, B.B.var.cont(_))) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, l6) :
    {D.wp.al(0, 0, 0, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0, 1, 1, 0, dlen, B.VR{A.A.from(td), 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(U32, U32.sub((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), 2, hs) :
    {(A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32),
      Bool.pick(U32, Bool.not(Bool.and(U32.is_le((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), Bool.and(Bool.and(U32.is_le(1, _),
        U32.is_le(1, U32.sub(_, 1))), Cmp.is_eq(U32.cmp(0, U32.sub(U32.sub(_, 1), 1)))))), 6, 0)}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_le((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), True{}, hb) :
    {(A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32),
      Bool.pick(U32, Bool.not(Bool.and(_, True{})), 6, 0)}) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}
  {==}


# A window
# ========

# The table's entry for opcode 2: ADD of size 1.
law R.tab:
  for +tb: A.Tr
  for +ht: {A.T.word(tb, 2) == 5 : U32}
  {Array.get(U32, A.A.from(tb), 2) == (A.A.from(tb), 5) : Array<U32> & U32}

def R.tab(tb, ht):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), 2), (A.A.from(tb), A.T.word(tb, 2)), A.A.get_from(tb, 2)) :
    {_ == (A.A.from(tb), 5) : Array<U32> & U32}
  %Equal.sym(U32, A.T.word(tb, 2), 5, ht) :
    {(A.A.from(tb), _) == (A.A.from(tb), 5) : Array<U32> & U32}
  {==}

law W.step:
  for -src: Array<U32>
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for -ca: Array<U32>
  for +slen: U32
  for +dlen: U32
  for +p: U32
  for +opos: U32
  for +x: U32
  for +rest: List<&2, U32>
  for +h: {S.S.has(F.F.win(x, rest), td, p) == True{} : Bool}
  for +l0: {U32.is_lt(p, dlen) == True{} : Bool}
  for +l1: {U32.is_lt((p + 1 : U32), dlen) == True{} : Bool}
  for +l2: {U32.is_lt(((p + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l3: {U32.is_lt((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l4: {U32.is_lt(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l5: {U32.is_lt((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +l6: {U32.is_lt(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen) == True{} : Bool}
  for +le7: {U32.is_le(7, U32.sub(dlen, ((p + 1 : U32) + 1 : U32))) == True{} : Bool}
  for +hw: {(((p + 1 : U32) + 1 : U32) + 7 : U32) == (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  for +hs: {U32.sub((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == 2 : U32}
  for +hb: {U32.is_le((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == True{} : Bool}
  for +hd1: {U32.sub(((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == 1 : U32}
  for +ho1: {U32.sub((opos + 1 : U32), opos) == 1 : U32}
  for +hbig: {U32.is_gt(1, U32.sub(2147483648, opos)) == False{} : Bool}
  for +ht: {A.T.word(tb, 2) == 5 : U32}
  {D.win.more(D.win.dec(D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}

def W.step(src, td, to, tb, ca, slen, dlen, p, opos, x, rest, h, l0, l1, l2, l3, l4, l5, l6, le7, hw, hs, hb, hd1, ho1, hbig, ht):
  %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), p, dlen), (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}), W.parse(td, p, dlen, x, rest, h, l0, l1, l2, l3, l4, l5, l6, le7, hw, hs, hb)) :
    {D.win.more(D.win.go(src, A.A.from(to), A.A.from(tb), ca, slen, dlen, opos, 0, _)) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Bool, U32.is_gt(1, U32.sub(2147483648, opos)), False{}, hbig) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(1n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, (U32.is_eq(D.err.set(0, _, 14), 0), D.Dec{src, A.A.from(td), A.A.from(to), A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, D.err.set(0, _, 14)})))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 2),
    R.rd(td, ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2, rest, R.tl(td, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), x, 2 <> rest, R.tl(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, x <> 2 <> rest, R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> x <> 2 <> rest, R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)))))))))) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.opcode(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, src, A.A.from(to), A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, _)))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), 2), (A.A.from(tb), 5), R.tab(tb, ht)) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.op(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, src, A.A.from(td), A.A.from(to), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, _)))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(U32, U32.sub(((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), 1, hd1) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.more(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.half(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, 0, D.dec.add.k(src, A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, D.u32.pick(Bool.and(U32.is_le(1, _), U32.is_le(1, U32.sub((opos + 1 : U32), opos))), 1, 0), Bool.and(U32.is_le(1, _), U32.is_le(1, U32.sub((opos + 1 : U32), opos))), B.B.copy.bytes(U32.to_nat(D.u32.pick(Bool.and(U32.is_le(1, _), U32.is_le(1, U32.sub((opos + 1 : U32), opos))), 1, 0)), A.A.from(to), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), B.B.get(A.A.from(td), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32))))))))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(U32, U32.sub((opos + 1 : U32), opos), 1, ho1) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.more(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.half(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, 0, D.dec.add.k(src, A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, D.u32.pick(U32.is_le(1, _), 1, 0), U32.is_le(1, _), B.B.copy.bytes(U32.to_nat(D.u32.pick(U32.is_le(1, _), 1, 0)), A.A.from(to), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), B.B.get(A.A.from(td), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32))))))))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), U32.and(x, 255)),
    R.rd(td, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), x, 2 <> rest, R.tl(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, x <> 2 <> rest, R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> x <> 2 <> rest, R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h))))))))) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.more(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.half(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, 0, D.dec.add.k(src, A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, 1, True{}, B.B.copy.bytes(1n, A.A.from(to), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _))))))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)), (A.A.from(td), 2),
    R.rd(td, ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2, rest, R.tl(td, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), x, 2 <> rest, R.tl(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, x <> 2 <> rest, R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> x <> 2 <> rest, R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> x <> 2 <> rest, R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> rest, h)))))))))) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.more(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.half(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, 0, D.dec.add.k(src, A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, 1, True{}, B.B.copy.bytes(0n, B.B.put(A.A.from(to), opos, U32.and(x, 255)), (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), _))))))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Array<U32>, B.B.put(A.A.from(to), opos, U32.and(x, 255)), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), Y.BP.put_from(to, opos, U32.and(x, 255))) :
    {D.win.more(D.win.fin(slen, dlen, 0, 0, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.loop(0n, D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.more(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, D.dec.half(D.WinC{0, 0, False{}, opos, (opos + 1 : U32), ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)}, 0, D.dec.add.k(src, A.A.from(tb), D.cache.clear(ca), opos, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, 0, 1, True{}, (A.A.from(td), _))))))) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Cmp, U32.cmp((opos + 1 : U32), (opos + 1 : U32)), EQ{}, V.U.cmp_refl((opos + 1 : U32))) :
    {D.win.more(D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), D.err.set(0, Bool.not(Cmp.is_eq(_)), D.E.LENGTH())}) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  %Equal.sym(Bool, Bool.and(U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}), U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), P.Bool.and_true(U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen))) :
    {(_, D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}
  {==}


# Positions
# =========

# d = q + 1 + j (as values) puts q below d.
law Q.ltN:
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == 1n+Nat.add(j, V.U.N(q)) : Nat}
  {Nat.cmp(V.U.N(q), V.U.N(d)) == LT{} : Cmp}

def Q.ltN(q, d, j, e):
  (%Equal.sym(Nat, V.U.N(d), 1n+Nat.add(j, V.U.N(q)), e) : {Nat.cmp(V.U.N(q), _) == LT{} : Cmp}
    P.Nat.lt_succ_add(V.U.N(q), j))

law Q.lt:
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == 1n+Nat.add(j, V.U.N(q)) : Nat}
  {U32.is_lt(q, d) == True{} : Bool}

def Q.lt(q, d, j, e):
  V.U.N_lt(q, d, Q.ltN(q, d, j, e))

law Q.succ:
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == 1n+Nat.add(j, V.U.N(q)) : Nat}
  {V.U.N((q + 1 : U32)) == 1n+V.U.N(q) : Nat}

def Q.succ(q, d, j, e):
  V.U.succ_N(q, d, Q.ltN(q, d, j, e))

law Q.adv:
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == 1n+Nat.add(j, V.U.N(q)) : Nat}
  {V.U.N(d) == Nat.add(j, V.U.N((q + 1 : U32))) : Nat}

def Q.adv(q, d, j, e):
  %Equal.sym(Nat, V.U.N((q + 1 : U32)), 1n+V.U.N(q), Q.succ(q, d, j, e)) : {V.U.N(d) == Nat.add(j, _) : Nat}
  %Equal.sym(Nat, Nat.add(j, 1n+V.U.N(q)), 1n+Nat.add(j, V.U.N(q)), P.Nat.add_succ_r(j, V.U.N(q))) :
    {V.U.N(d) == _ : Nat}
  e

law Q.le_of:
  for +q: U32
  for +d: U32
  for +k: Nat
  for +e: {V.U.N(d) == Nat.add(k, V.U.N(q)) : Nat}
  {U32.is_le(q, d) == True{} : Bool}

def Q.le_of(q, d, k, e):
  (%Equal.sym(Cmp, U32.cmp(q, d), Nat.cmp(V.U.N(q), V.U.N(d)), V.U.cmp_nat(q, d)) : {Cmp.is_le(_) == True{} : Bool}
    (%Equal.sym(Nat, V.U.N(d), Nat.add(k, V.U.N(q)), e) : {Cmp.is_le(Nat.cmp(V.U.N(q), _)) == True{} : Bool}
      P.Nat.le_add_l(k, V.U.N(q))))

# c <= d - q when d = c + j + q.
law Q.lesub:
  for +c: U32
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == Nat.add(Nat.add(V.U.N(c), j), V.U.N(q)) : Nat}
  {U32.is_le(c, U32.sub(d, q)) == True{} : Bool}

def Q.lesub(c, q, d, j, e):
  %Equal.sym(Cmp, U32.cmp(c, U32.sub(d, q)), Nat.cmp(V.U.N(c), V.U.N(U32.sub(d, q))), V.U.cmp_nat(c, U32.sub(d, q))) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.sub(d, q)), Nat.add(V.U.N(c), j),
    P.Nat.add_cancel_r(V.U.N(U32.sub(d, q)), Nat.add(V.U.N(c), j), V.U.N(q),
      (%e : {Nat.add(V.U.N(U32.sub(d, q)), V.U.N(q)) == _ : Nat}
        V.U.sub_nat(d, q, Q.le_of(q, d, Nat.add(V.U.N(c), j), e))))) :
    {Cmp.is_le(Nat.cmp(V.U.N(c), _)) == True{} : Bool}
  P.Nat.cmp_add_r(V.U.N(c), j)

# q <= q + 2 when that does not wrap.
law Q.le2:
  for +q: U32
  for +d: U32
  for +j: Nat
  for +e: {V.U.N(d) == 1n+1n+Nat.add(j, V.U.N(q)) : Nat}
  {U32.is_le(q, ((q + 1 : U32) + 1 : U32)) == True{} : Bool}

def Q.le2(q, d, j, e):
  %Equal.sym(Cmp, U32.cmp(q, ((q + 1 : U32) + 1 : U32)), Nat.cmp(V.U.N(q), V.U.N(((q + 1 : U32) + 1 : U32))),
    V.U.cmp_nat(q, ((q + 1 : U32) + 1 : U32))) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(((q + 1 : U32) + 1 : U32)), 1n+V.U.N((q + 1 : U32)),
    Q.succ((q + 1 : U32), d, j, Q.adv(q, d, 1n+j, e))) :
    {Cmp.is_le(Nat.cmp(V.U.N(q), _)) == True{} : Bool}
  %Equal.sym(Nat, V.U.N((q + 1 : U32)), 1n+V.U.N(q), Q.succ(q, d, 1n+j, e)) :
    {Cmp.is_le(Nat.cmp(V.U.N(q), 1n+_)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(q), 1n+1n+V.U.N(q)), LT{}, P.Nat.lt_succ_add(V.U.N(q), 1n)) :
    {Cmp.is_le(_) == True{} : Bool}
  {==}

law Q.add7:
  for +q: U32
  {(q + 7 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}

def Q.add7(q):
  %V.U.add_assoc(q, 6, 1) :
    {_ == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  %V.U.add_assoc(q, 5, 1) :
    {(_ + 1 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  %V.U.add_assoc(q, 4, 1) :
    {((_ + 1 : U32) + 1 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  %V.U.add_assoc(q, 3, 1) :
    {(((_ + 1 : U32) + 1 : U32) + 1 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  %V.U.add_assoc(q, 2, 1) :
    {((((_ + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  %V.U.add_assoc(q, 1, 1) :
    {(((((_ + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) == (((((((q + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) : U32}
  {==}

# A window, its side conditions discharged.
law W.step2:
  for -src: Array<U32>
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for -ca: Array<U32>
  for +slen: U32
  for +dlen: U32
  for +p: U32
  for +opos: U32
  for +x: U32
  for +rest: List<&2, U32>
  for +L: Nat
  for +h: {S.S.has(F.F.win(x, rest), td, p) == True{} : Bool}
  for +e: {V.U.N(dlen) == Nat.add(Nat.add(9n, L), V.U.N(p)) : Nat}
  for +hsm: {U32.is_lt(opos, 134217728) == True{} : Bool}
  for +ht: {A.T.word(tb, 2) == 5 : U32}
  {D.win.more(D.win.dec(D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})) == (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(x, 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}) : Bool & D.DS}

def W.step2(src, td, to, tb, ca, slen, dlen, p, opos, x, rest, L, h, e, hsm, ht):
  W.step(src, td, to, tb, ca, slen, dlen, p, opos, x, rest, h, Q.lt(p, dlen, Nat.add(8n, L), e), Q.lt((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)), Q.lt(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))), Q.lt((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))), Q.lt(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))))), Q.lt((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))))), Q.lt(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(2n, L), Q.adv((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))))))), Q.lesub(7, ((p + 1 : U32) + 1 : U32), dlen, L, Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))), Q.add7(((p + 1 : U32) + 1 : U32)), (%Equal.sym(U32, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), U32.add((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2), V.U.add_assoc((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1)) : {U32.sub(_, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == 2 : U32}
      V.U.sub_add_l((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2)), Q.le2((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, L, Q.adv(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(2n, L), Q.adv((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))))))), V.U.sub_add_l((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1), V.U.sub_add_l(opos, 1), V.U.big(opos, hsm), ht)

# After a window, the rest of the delta.
law W.next:
  for +p: U32
  for +dlen: U32
  for +L: Nat
  for +e: {V.U.N(dlen) == Nat.add(Nat.add(9n, L), V.U.N(p)) : Nat}
  {V.U.N(dlen) == Nat.add(L, V.U.N((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32))) : Nat}

def W.next(p, dlen, L, e):
  Q.adv(((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(0n, L), Q.adv((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(1n, L), Q.adv(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(2n, L), Q.adv((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))))))))


# A window's header, its side conditions discharged.
law W.parse2:
  for +td: A.Tr
  for +p: U32
  for +dlen: U32
  for +x: U32
  for +rest: List<&2, U32>
  for +L: Nat
  for +h: {S.S.has(F.F.win(x, rest), td, p) == True{} : Bool}
  for +e: {V.U.N(dlen) == Nat.add(Nat.add(9n, L), V.U.N(p)) : Nat}
  {D.win.parse(A.A.from(td), p, dlen) == (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}) : Array<U32> & D.WH}

def W.parse2(td, p, dlen, x, rest, L, h, e):
  W.parse(td, p, dlen, x, rest, h, Q.lt(p, dlen, Nat.add(8n, L), e), Q.lt((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)), Q.lt(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))), Q.lt((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))), Q.lt(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))))), Q.lt((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))))), Q.lt(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(2n, L), Q.adv((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))))))), Q.lesub(7, ((p + 1 : U32) + 1 : U32), dlen, L, Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e))), Q.add7(((p + 1 : U32) + 1 : U32)), (%Equal.sym(U32, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), U32.add((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2), V.U.add_assoc((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1)) : {U32.sub(_, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32)) == 2 : U32}
      V.U.sub_add_l((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2)), Q.le2((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, L, Q.adv(((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(2n, L), Q.adv((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(3n, L), Q.adv(((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(4n, L), Q.adv((((p + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(5n, L), Q.adv(((p + 1 : U32) + 1 : U32), dlen, Nat.add(6n, L), Q.adv((p + 1 : U32), dlen, Nat.add(7n, L), Q.adv(p, dlen, Nat.add(8n, L), e)))))))))

# The flag after the last window.
law Q.flag0:
  for +q: U32
  for +d: U32
  for +e: {V.U.N(d) == Nat.add(0n, V.U.N(q)) : Nat}
  {U32.is_lt(q, d) == False{} : Bool}

def Q.flag0(q, d, e):
  %Equal.sym(U32, d, q, V.U.eq_N(d, q, e)) : {U32.is_lt(q, _) == False{} : Bool}
  %Equal.sym(Cmp, U32.cmp(q, q), EQ{}, V.U.cmp_refl(q)) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

# Decoding windows
# ================

law L.dec:
  for +k: Nat
  for +f: Nat
  for +tt: A.Tr
  for +w: U32
  for src: Array<U32>
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for ca: Array<U32>
  for +slen: U32
  for +dlen: U32
  for +p: U32
  for +opos: U32
  for +total: U32
  for +lenU: U32
  for +h: {S.S.has(F.F.wins(S.S.sl(1n+k, tt, w)), td, p) == True{} : Bool}
  for +e: {V.U.N(dlen) == Nat.add(S.S.len(F.F.wins(S.S.sl(1n+k, tt, w))), V.U.N(p)) : Nat}
  for +hf: {Cmp.is_le(Nat.cmp(k, f)) == True{} : Bool}
  for +hlo: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n+k), V.U.N(lenU))) == True{} : Bool}
  for +hlen: {U32.is_lt(lenU, 134217728) == True{} : Bool}
  for +ht: {A.T.word(tb, 2) == 5 : U32}
  {D.dec.done(total, D.win.loop(1n+f, (True{}, D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})))
    == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+k, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}

def L.dec(k, f, tt, w, src, td, to, tb, ca, slen, dlen, p, opos, total, lenU, h, e, hf, hlo, hlen, ht):
  match k f:
    case 0n 0n:
      %Equal.sym(Bool & D.DS, D.win.more(D.win.dec(D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})),
        (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(Y.BP.byt(tt, w), 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}),
        W.step2(src, td, to, tb, ca, slen, dlen, p, opos, Y.BP.byt(tt, w), F.F.wins(S.S.sl(0n, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), h, e, V.U.lt_trans(opos, lenU, 134217728, V.U.N_lt(opos, lenU, S.S.lt_of_bound(opos, 0n, lenU, hlo)), hlen), ht)) :
        {D.dec.done(total, D.win.loop(0n, _)) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(U32, U32.and(Y.BP.byt(tt, w), 255), Y.BP.byt(tt, w), Y.BP.byt_255(tt, w)) :
        {D.dec.done(total, (D.win.loop(0n, (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, _)), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), False{}, Q.flag0((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), e))) :
        {D.dec.done(total, (D.win.loop(0n, (_, D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, Y.BP.byt(tt, w))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      {==}
    case 0n 1n+g:
      %Equal.sym(Bool & D.DS, D.win.more(D.win.dec(D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})),
        (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(Y.BP.byt(tt, w), 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}),
        W.step2(src, td, to, tb, ca, slen, dlen, p, opos, Y.BP.byt(tt, w), F.F.wins(S.S.sl(0n, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), h, e, V.U.lt_trans(opos, lenU, 134217728, V.U.N_lt(opos, lenU, S.S.lt_of_bound(opos, 0n, lenU, hlo)), hlen), ht)) :
        {D.dec.done(total, D.win.loop(1n+g, _)) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(U32, U32.and(Y.BP.byt(tt, w), 255), Y.BP.byt(tt, w), Y.BP.byt_255(tt, w)) :
        {D.dec.done(total, (D.win.loop(1n+g, (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, _)), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), False{}, Q.flag0((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), e))) :
        {D.dec.done(total, (D.win.loop(1n+g, (_, D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, Y.BP.byt(tt, w))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+0n, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      {==}
    case 1n+j 0n:
      P.Bool.false_true({D.dec.done(total, D.win.loop(1n, (True{}, D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})))
        == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+1n+j, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}, hf)
    case 1n+j 1n+g:
      %Equal.sym(Bool & D.DS, D.win.more(D.win.dec(D.DS{src, A.A.from(td), A.A.from(to), A.A.from(tb), ca, slen, dlen, p, opos, 0})),
        (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, U32.and(Y.BP.byt(tt, w), 255))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0}),
        W.step2(src, td, to, tb, ca, slen, dlen, p, opos, Y.BP.byt(tt, w), F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), h, e, V.U.lt_trans(opos, lenU, 134217728, V.U.N_lt(opos, lenU, S.S.lt_of_bound(opos, 1n+j, lenU, hlo)), hlen), ht)) :
        {D.dec.done(total, D.win.loop(1n+g, _)) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+1n+j, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(U32, U32.and(Y.BP.byt(tt, w), 255), Y.BP.byt(tt, w), Y.BP.byt_255(tt, w)) :
        {D.dec.done(total, (D.win.loop(1n+g, (U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, _)), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+1n+j, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, Q.lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(8n, S.S.len(F.F.wins(S.S.sl(j, tt, ((w + 1 : U32) + 1 : U32))))), W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), e))) :
        {D.dec.done(total, (D.win.loop(1n+g, (_, D.DS{src, A.A.from(td), A.A.from(Y.BP.put(to, opos, Y.BP.byt(tt, w))), A.A.from(tb), D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), 0})))) == (B.Bytes{slen, src}, (B.Bytes{dlen, A.A.from(td)}, Done{B.Bytes{total, A.A.from(S.S.puts(S.S.sl(1n+1n+j, tt, w), to, opos))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
      L.dec(j, g, tt, (w + 1 : U32), src, td, Y.BP.put(to, opos, Y.BP.byt(tt, w)), tb, D.cache.clear(ca), slen, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (opos + 1 : U32), total, lenU,
        R.tl(td, ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2, F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), Y.BP.byt(tt, w), 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), h))))))))),
        W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), e), hf, S.S.bound_succ(opos, 1n+j, lenU, hlo), hlen, ht)


# The prescan
# ===========

law L.pre:
  for +k: Nat
  for +f: Nat
  for +tt: A.Tr
  for +w: U32
  for +td: A.Tr
  for +dlen: U32
  for +p: U32
  for +total: U32
  for +lenU: U32
  for +h: {S.S.has(F.F.wins(S.S.sl(1n+k, tt, w)), td, p) == True{} : Bool}
  for +e: {V.U.N(dlen) == Nat.add(S.S.len(F.F.wins(S.S.sl(1n+k, tt, w))), V.U.N(p)) : Nat}
  for +hf: {Cmp.is_le(Nat.cmp(k, f)) == True{} : Bool}
  for +hlo: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(total), 1n+k), V.U.N(lenU))) == True{} : Bool}
  for +hlen: {U32.is_lt(lenU, 134217728) == True{} : Bool}
  {D.pre.loop(1n+f, (True{}, D.PS{A.A.from(td), dlen, p, total, 0})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+k, tt, w)), p), S.S.adv(S.S.sl(1n+k, tt, w), total), 0} : D.PS}

def L.pre(k, f, tt, w, td, dlen, p, total, lenU, h, e, hf, hlo, hlen):
  match k f:
    case 0n 0n:
      %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), p, dlen), (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}),
        W.parse2(td, p, dlen, Y.BP.byt(tt, w), F.F.wins(S.S.sl(0n, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), h, e)) :
        {D.pre.loop(0n, D.pre.k(dlen, total, 0, _)) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_gt(1, U32.sub(2147483648, total)), False{}, V.U.big(total, V.U.lt_trans(total, lenU, 134217728, V.U.N_lt(total, lenU, S.S.lt_of_bound(total, 0n, lenU, hlo)), hlen))) :
        {D.pre.loop(0n, (Bool.and(U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), U32.is_eq(D.err.set(0, _, 14), 0)),
          D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), D.err.set(0, _, 14)})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), False{}, Q.flag0((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), e))) :
        {D.pre.loop(0n, (Bool.and(_, True{}), D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), 0})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      {==}
    case 0n 1n+g:
      %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), p, dlen), (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}),
        W.parse2(td, p, dlen, Y.BP.byt(tt, w), F.F.wins(S.S.sl(0n, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), h, e)) :
        {D.pre.loop(1n+g, D.pre.k(dlen, total, 0, _)) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_gt(1, U32.sub(2147483648, total)), False{}, V.U.big(total, V.U.lt_trans(total, lenU, 134217728, V.U.N_lt(total, lenU, S.S.lt_of_bound(total, 0n, lenU, hlo)), hlen))) :
        {D.pre.loop(1n+g, (Bool.and(U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), U32.is_eq(D.err.set(0, _, 14), 0)),
          D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), D.err.set(0, _, 14)})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), False{}, Q.flag0((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(0n, tt, (w + 1 : U32)))), e))) :
        {D.pre.loop(1n+g, (Bool.and(_, True{}), D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), 0})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+0n, tt, w)), p), S.S.adv(S.S.sl(1n+0n, tt, w), total), 0} : D.PS}
      {==}
    case 1n+j 0n:
      P.Bool.false_true({D.pre.loop(1n, (True{}, D.PS{A.A.from(td), dlen, p, total, 0})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+1n+j, tt, w)), p), S.S.adv(S.S.sl(1n+1n+j, tt, w), total), 0} : D.PS}, hf)
    case 1n+j 1n+g:
      %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), p, dlen), (A.A.from(td), D.WH{0, 0, 0, 1, 1, 1, 0, 0, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0}),
        W.parse2(td, p, dlen, Y.BP.byt(tt, w), F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), h, e)) :
        {D.pre.loop(1n+g, D.pre.k(dlen, total, 0, _)) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+1n+j, tt, w)), p), S.S.adv(S.S.sl(1n+1n+j, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_gt(1, U32.sub(2147483648, total)), False{}, V.U.big(total, V.U.lt_trans(total, lenU, 134217728, V.U.N_lt(total, lenU, S.S.lt_of_bound(total, 1n+j, lenU, hlo)), hlen))) :
        {D.pre.loop(1n+g, (Bool.and(U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), U32.is_eq(D.err.set(0, _, 14), 0)),
          D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), D.err.set(0, _, 14)})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+1n+j, tt, w)), p), S.S.adv(S.S.sl(1n+1n+j, tt, w), total), 0} : D.PS}
      %Equal.sym(Bool, U32.is_lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen), True{}, Q.lt((((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), dlen, Nat.add(8n, S.S.len(F.F.wins(S.S.sl(j, tt, ((w + 1 : U32) + 1 : U32))))), W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), e))) :
        {D.pre.loop(1n+g, (Bool.and(_, True{}), D.PS{A.A.from(td), dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), 0})) == D.PS{A.A.from(td), dlen, S.S.adv(F.F.wins(S.S.sl(1n+1n+j, tt, w)), p), S.S.adv(S.S.sl(1n+1n+j, tt, w), total), 0} : D.PS}
      L.pre(j, g, tt, (w + 1 : U32), td, dlen, (((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), (total + 1 : U32), lenU,
        R.tl(td, ((((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 2, F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), Y.BP.byt(tt, w), 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 0, Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((((p + 1 : U32) + 1 : U32) + 1 : U32) + 1 : U32), 1, 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (((p + 1 : U32) + 1 : U32) + 1 : U32), 0, 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, ((p + 1 : U32) + 1 : U32), 1, 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, (p + 1 : U32), 7, 1 <> 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), R.tl(td, p, 0, 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> Y.BP.byt(tt, w) <> 2 <> F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32))), h))))))))),
        W.next(p, dlen, S.S.len(F.F.wins(S.S.sl(1n+j, tt, (w + 1 : U32)))), e), hf, S.S.bound_succ(total, 1n+j, lenU, hlo), hlen)

