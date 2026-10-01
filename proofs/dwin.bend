import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./bits.bend as Z
import ./words.bend as K
import ./copy.bend as C
import ./varint.bend as R
import ./spec.bend as Q
import ./sem.bend as M
import ./dec.bend as X
import ./adler.bend as H

# The decoder on a window: its header, its instructions (proofs/dec), then
# the length and checksum checks.
#
# Source: proofs/dwin.bp (tools/bpp.py writes proofs/dwin.bend from it).

# Arithmetic
# ==========

# x <= x + y when the sum does not wrap.
law DW.le_add:
  for +x: U32
  for +y: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(x), V.U.N(y)), V.U.N(e))) == True{} : Bool}
  {U32.is_le(x, U32.add(x, y)) == True{} : Bool}

law DW.le_add.go:
  for +x: U32
  for +y: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(x), V.U.N(y)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(x), V.U.N(U32.add(x, y)))) == True{} : Bool}

def DW.le_add.go(x, y, e, h):
  %Equal.sym(Nat, V.U.N(U32.add(x, y)), Nat.add(V.U.N(x), V.U.N(y)), V.U.add_N(x, y, e, h)) :
    {Cmp.is_le(Nat.cmp(V.U.N(x), _)) == True{} : Bool}
  P.Nat.cmp_add_r(V.U.N(x), V.U.N(y))

def DW.le_add(x, y, e, h):
  V.U.N_le(x, U32.add(x, y), DW.le_add.go(x, y, e, h))

# a + (b + c) <= e gives b + c <= e.
law DW.le_tail:
  for +a: Nat
  for +b: Nat
  for +e: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(a, b), e)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(b, e)) == True{} : Bool}

def DW.le_tail(a, b, e, h):
  P.Nat.le_trans(b, Nat.add(a, b), e, P.Nat.le_add_l(a, b), h)

# The section lengths fill the window exactly: the decoder's checks pass.
law DW.secs:
  for +body: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(e))) == True{} : Bool}
  {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.sub(U32.add(body, U32.add(dl, U32.add(il, al))), body)), U32.is_le(il, U32.sub(U32.sub(U32.add(body, U32.add(dl, U32.add(il, al))), body), dl))), U32.is_eq(al, U32.sub(U32.sub(U32.sub(U32.add(body, U32.add(dl, U32.add(il, al))), body), dl), il)))) == True{} : Bool}

law DW.secs.b2:
  for +body: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(dl), V.U.N(U32.add(il, al))), V.U.N(e))) == True{} : Bool}

def DW.secs.b2(body, dl, il, al, e, hb):
  %Equal.sym(Nat, V.U.N(U32.add(il, al)), Nat.add(V.U.N(il), V.U.N(al)), V.U.add_N(il, al, e, DW.le_tail(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)), V.U.N(e), DW.le_tail(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), V.U.N(e), hb)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(dl), _), V.U.N(e))) == True{} : Bool}
  DW.le_tail(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), V.U.N(e), hb)

law DW.secs.b1:
  for +body: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), V.U.N(U32.add(dl, U32.add(il, al)))), V.U.N(e))) == True{} : Bool}

def DW.secs.b1(body, dl, il, al, e, hb):
  %Equal.sym(Nat, V.U.N(U32.add(dl, U32.add(il, al))), Nat.add(V.U.N(dl), V.U.N(U32.add(il, al))), V.U.add_N(dl, U32.add(il, al), e, DW.secs.b2(body, dl, il, al, e, hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), _), V.U.N(e))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(il, al)), Nat.add(V.U.N(il), V.U.N(al)), V.U.add_N(il, al, e, DW.le_tail(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)), V.U.N(e), DW.le_tail(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), V.U.N(e), hb)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(body), Nat.add(V.U.N(dl), _)), V.U.N(e))) == True{} : Bool}
  hb

def DW.secs(body, dl, il, al, e, hb):
  %Equal.sym(U32, U32.sub(U32.add(body, U32.add(dl, U32.add(il, al))), body), U32.add(dl, U32.add(il, al)), V.U.sub_add_l(body, U32.add(dl, U32.add(il, al)))) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, _), U32.is_le(il, U32.sub(_, dl))), U32.is_eq(al, U32.sub(U32.sub(_, dl), il)))) == True{} : Bool}
  %Equal.sym(U32, U32.sub(U32.add(dl, U32.add(il, al)), dl), U32.add(il, al), V.U.sub_add_l(dl, U32.add(il, al))) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.add(dl, U32.add(il, al))), U32.is_le(il, _)), U32.is_eq(al, U32.sub(_, il)))) == True{} : Bool}
  %Equal.sym(U32, U32.sub(U32.add(il, al), il), al, V.U.sub_add_l(il, al)) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.add(dl, U32.add(il, al))), U32.is_le(il, U32.add(il, al))), U32.is_eq(al, _))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(al, al), True{}, V.U.is_eq_refl(al)) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.add(dl, U32.add(il, al))), U32.is_le(il, U32.add(il, al))), _)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(il, U32.add(il, al)), True{}, DW.le_add(il, al, e, DW.le_tail(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)), V.U.N(e), DW.le_tail(V.U.N(body), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), V.U.N(e), hb)))) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.add(dl, U32.add(il, al))), _), True{})) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(dl, U32.add(dl, U32.add(il, al))), True{}, DW.le_add(dl, U32.add(il, al), e, DW.secs.b2(body, dl, il, al, e, hb))) :
    {Bool.and(U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(_, True{}), True{})) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(body, U32.add(body, U32.add(dl, U32.add(il, al)))), True{}, DW.le_add(body, U32.add(dl, U32.add(il, al)), e, DW.secs.b1(body, dl, il, al, e, hb))) :
    {Bool.and(_, Bool.and(Bool.and(True{}, True{}), True{})) == True{} : Bool}
  {==}

# The header
# ==========

# The checksum's bytes, ahead of the rest.
law DW.be_app:
  for +sum: U32
  for +R: List<&2, U32>
  {K.WD.app(Q.SP.be(sum), R) == U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R : List<&2, U32>}

def DW.be_app(sum, R):
  {==}

# A held byte before the end: its position is below the end.
law DW.at_lt:
  for +x: U32
  for +rest: List<&2, U32>
  for +td: A.Tr
  for +p: U32
  for +end: U32
  for +h: {Q.SP.at(x <> rest, td, p, end) == True{} : Bool}
  {U32.is_lt(p, end) == True{} : Bool}

def DW.at_lt(x, rest, td, p, end, h):
  V.U.N_lt(p, end, K.WD.lt_of_succ_le(V.U.N(p), V.U.N(end), X.DX.at_pre(x <> [], rest, td, p, end, h)))

# The header from the target length on.
law DW.tail:
  for +td: A.Tr
  for +p3: U32
  for +end: U32
  for +ind: U32
  for +cpl: U32
  for +cpo: U32
  for +wend: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +R: List<&2, U32>
  for +h: {Q.SP.at(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))))), td, p3, end) == True{} : Bool}
  for +hind: {U32.is_ne(U32.and(ind, 4), 0) == True{} : Bool}
  for +hw: {wend == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  for +hwb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(end))) == True{} : Bool}
  {D.wp.tlen(ind, cpl, cpo, wend, 0, end, B.B.var.get(A.A.from(td), p3, end)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}

def DW.tail(td, p3, end, ind, cpl, cpo, wend, tlen, dl, il, al, sum, R, h, hind, hw, hwb):
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), p3, end), B.VR{A.A.from(td), tlen, U32.add(p3, B.B.var.len(tlen)), True{}}, R.VI.get(td, p3, end, tlen, 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), X.DX.at_has(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))))), td, p3, end, h), (%R.VI.len_var(tlen) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(p3)), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, h)))) :
    {D.wp.tlen(ind, cpl, cpo, wend, 0, end, _) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), U32.add(p3, B.B.var.len(tlen))), (A.A.from(td), 0), R.VI.rd(td, U32.add(p3, B.B.var.len(tlen)), 0, K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), X.DX.at_has(0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))) :
    {D.wp.dli(ind, cpl, cpo, wend, tlen, D.err.set(0, False{}, D.E.TRUNCATED()), end, B.B.byte.k(U32.add(p3, B.B.var.len(tlen)), end, _)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(U32.add(p3, B.B.var.len(tlen)), end), True{}, DW.at_lt(0, K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))) :
    {D.wp.dli(ind, cpl, cpo, wend, tlen, D.err.set(0, False{}, D.E.TRUNCATED()), end, B.VR{A.A.from(td), 0, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), _}) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end), B.VR{A.A.from(td), dl, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), True{}}, R.VI.get(td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, dl, K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), X.DX.at_has(K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))), (%R.VI.len_var(dl) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(U32.add(p3, B.B.var.len(tlen)), 1))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))))) :
    {D.wp.dl(ind, cpl, cpo, wend, tlen, 0, D.err.set(0, False{}, D.E.TRUNCATED()), end, _) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end), B.VR{A.A.from(td), il, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), True{}}, R.VI.get(td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, il, K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), X.DX.at_has(K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))), (%R.VI.len_var(il) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))))))) :
    {D.wp.il(ind, cpl, cpo, wend, tlen, 0, dl, D.err.set(0, False{}, D.E.TRUNCATED()), end, _) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end), B.VR{A.A.from(td), al, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), True{}}, R.VI.get(td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, al, K.WD.app(Q.SP.be(sum), R), X.DX.at_has(K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))))), (%R.VI.len_var(al) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))))))) :
    {D.wp.al(ind, cpl, cpo, wend, tlen, 0, dl, il, D.err.set(0, False{}, D.E.TRUNCATED()), end, _) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_ne(U32.and(ind, 4), 0), True{}, hind) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), D.wp.sum.if(_, A.A.from(td), U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al))), (A.A.from(td), U32.and(U32.shrn(sum, 24n), 255)), R.VI.rd(td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.shrn(sum, 24n), U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, X.DX.at_has(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, (%DW.be_app(sum, R) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end) == True{} : Bool}; X.DX.at_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))))))))) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), D.be32.k0(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, _)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1)), (A.A.from(td), U32.and(U32.and(U32.shrn(sum, 16n), 255), 255)), R.VI.rd(td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), U32.and(U32.shrn(sum, 16n), 255), U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, X.DX.at_has(U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, X.DX.at_next(U32.shrn(sum, 24n) <> [], U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, 1, {==}, (%DW.be_app(sum, R) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end) == True{} : Bool}; X.DX.at_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))))))))) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), D.be32.k1(U32.and(U32.shrn(sum, 24n), 255), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, _)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1)), (A.A.from(td), U32.and(U32.and(U32.shrn(sum, 8n), 255), 255)), R.VI.rd(td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), U32.and(U32.shrn(sum, 8n), 255), U32.and(sum, 255) <> R, X.DX.at_has(U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), end, X.DX.at_next(U32.and(U32.shrn(sum, 16n), 255) <> [], U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, 1, {==}, X.DX.at_next(U32.shrn(sum, 24n) <> [], U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, 1, {==}, (%DW.be_app(sum, R) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end) == True{} : Bool}; X.DX.at_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))))))))))) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), D.be32.k2(U32.or(U32.shln(U32.and(U32.shrn(sum, 24n), 255), 8n), U32.and(U32.and(U32.shrn(sum, 16n), 255), 255)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), end, _)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1)), (A.A.from(td), U32.and(U32.and(sum, 255), 255)), R.VI.rd(td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), U32.and(sum, 255), R, X.DX.at_has(U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end, X.DX.at_next(U32.and(U32.shrn(sum, 8n), 255) <> [], U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), end, 1, {==}, X.DX.at_next(U32.and(U32.shrn(sum, 16n), 255) <> [], U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, 1, {==}, X.DX.at_next(U32.shrn(sum, 24n) <> [], U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, 1, {==}, (%DW.be_app(sum, R) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end) == True{} : Bool}; X.DX.at_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h)))))))))))) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), D.be32.k3(U32.or(U32.shln(U32.or(U32.shln(U32.and(U32.shrn(sum, 24n), 255), 8n), U32.and(U32.and(U32.shrn(sum, 16n), 255), 255)), 8n), U32.and(U32.and(U32.shrn(sum, 8n), 255), 255)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end, _)) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(U32, U32.or(U32.shln(U32.or(U32.shln(U32.or(U32.shln(U32.and(U32.shrn(sum, 24n), 255), 8n), U32.and(U32.and(U32.shrn(sum, 16n), 255), 255)), 8n), U32.and(U32.and(U32.shrn(sum, 8n), 255), 255)), 8n), U32.and(U32.and(sum, 255), 255)), sum, Z.BB.be32(sum)) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), B.VR{A.A.from(td), _, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.is_lt(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end)}) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end), True{}, DW.at_lt(U32.and(sum, 255), R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end, X.DX.at_next(U32.and(U32.shrn(sum, 8n), 255) <> [], U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), end, 1, {==}, X.DX.at_next(U32.and(U32.shrn(sum, 16n), 255) <> [], U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, 1, {==}, X.DX.at_next(U32.shrn(sum, 24n) <> [], U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, 1, {==}, (%DW.be_app(sum, R) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end) == True{} : Bool}; X.DX.at_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), X.DX.at_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), X.DX.at_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), X.DX.at_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, {==}, X.DX.at_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), h))))))))))) :
    {D.wp.sum(ind, cpl, cpo, wend, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), B.VR{A.A.from(td), sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), _}) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), wend, 0}) : Array<U32> & D.WH}
  %Equal.sym(U32, wend, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), hw) :
    {D.wp.sum(ind, cpl, cpo, _, tlen, 0, dl, il, al, D.err.set(0, False{}, D.E.TRUNCATED()), B.VR{A.A.from(td), sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), True{}}) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), _, 0}) : Array<U32> & D.WH}
  %Equal.sym(Bool, Bool.and(U32.is_le(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al)))), Bool.and(Bool.and(U32.is_le(dl, U32.sub(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1))), U32.is_le(il, U32.sub(U32.sub(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), dl))), U32.is_eq(al, U32.sub(U32.sub(U32.sub(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), dl), il)))), True{}, DW.secs(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl, il, al, end, hwb)) :
    {(A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), D.err.set(D.err.set(D.err.set(0, False{}, D.E.TRUNCATED()), False{}, D.E.SECONDARY()), Bool.not(_), D.E.TRUNCATED())}) == (A.A.from(td), D.WH{ind, cpl, cpo, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), 0}) : Array<U32> & D.WH}
  {==}

# The header to the delta encoding length, with a source segment.
law DW.head1:
  for +td: A.Tr
  for +pos: U32
  for +end: U32
  for +cpl: U32
  for +off: U32
  for +enc: U32
  for +REST: List<&2, U32>
  for +h: {Q.SP.at(5 <> K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end) == True{} : Bool}
  for +hf: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc))), V.U.N(enc)), V.U.N(end))) == True{} : Bool}
  {D.win.parse(A.A.from(td), pos, end) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}

def DW.head1(td, pos, end, cpl, off, enc, REST, h, hf):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), pos), (A.A.from(td), 5), R.VI.rd(td, pos, 5, K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), X.DX.at_has(5 <> K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, h))) :
    {D.wp.ind(end, B.B.byte.k(pos, end, _)) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(pos, end), True{}, DW.at_lt(5, K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, h)) :
    {D.wp.ind(end, B.VR{A.A.from(td), 5, U32.add(pos, 1), _}) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(pos, 1), end), B.VR{A.A.from(td), cpl, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), True{}}, R.VI.get(td, U32.add(pos, 1), end, cpl, K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), X.DX.at_has(K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, U32.add(pos, 1), end, X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h)), (%R.VI.len_var(cpl) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(pos, 1))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(pos, 1), end, X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h))))) :
    {D.wp.cpl(5, D.err.set(D.err.set(0, False{}, D.E.TRUNCATED()), False{}, D.E.WININD()), end, _) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end), B.VR{A.A.from(td), off, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), True{}}, R.VI.get(td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, off, K.WD.app(R.VI.var(enc), REST), X.DX.at_has(K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h))), (%R.VI.len_var(off) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(U32.add(pos, 1), B.B.var.len(cpl)))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(off), K.WD.app(R.VI.var(enc), REST), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h)))))) :
    {D.wp.cpo(5, cpl, D.err.set(0, False{}, D.E.TRUNCATED()), end, _) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end), B.VR{A.A.from(td), enc, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), True{}}, R.VI.get(td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, enc, REST, X.DX.at_has(K.WD.app(R.VI.var(enc), REST), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(enc), REST), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h)))), (%R.VI.len_var(enc) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(enc), REST, td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(enc), REST), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST)), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(enc), REST))), td, pos, end, 1, {==}, h))))))) :
    {D.wp.enc(5, cpl, off, D.err.set(0, False{}, D.E.TRUNCATED()), end, _) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_le(enc, U32.sub(end, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)))), True{}, X.DX.le_sub(enc, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end, (%P.Nat.add_comm(V.U.N(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc))), V.U.N(enc)) : {Cmp.is_le(Nat.cmp(_, V.U.N(end))) == True{} : Bool}; hf))) :
    {D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), D.err.set(0, Bool.not(_), D.E.TRUNCATED()), end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) == D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  {==}

# The same, with no source segment.
law DW.head0:
  for +td: A.Tr
  for +pos: U32
  for +end: U32
  for +enc: U32
  for +REST: List<&2, U32>
  for +h: {Q.SP.at(4 <> K.WD.app(R.VI.var(enc), REST), td, pos, end) == True{} : Bool}
  for +hf: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(U32.add(pos, 1), B.B.var.len(enc))), V.U.N(enc)), V.U.N(end))) == True{} : Bool}
  {D.win.parse(A.A.from(td), pos, end) == D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) : Array<U32> & D.WH}

def DW.head0(td, pos, end, enc, REST, h, hf):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), pos), (A.A.from(td), 4), R.VI.rd(td, pos, 4, K.WD.app(R.VI.var(enc), REST), X.DX.at_has(4 <> K.WD.app(R.VI.var(enc), REST), td, pos, end, h))) :
    {D.wp.ind(end, B.B.byte.k(pos, end, _)) == D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_lt(pos, end), True{}, DW.at_lt(4, K.WD.app(R.VI.var(enc), REST), td, pos, end, h)) :
    {D.wp.ind(end, B.VR{A.A.from(td), 4, U32.add(pos, 1), _}) == D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), U32.add(pos, 1), end), B.VR{A.A.from(td), enc, U32.add(U32.add(pos, 1), B.B.var.len(enc)), True{}}, R.VI.get(td, U32.add(pos, 1), end, enc, REST, X.DX.at_has(K.WD.app(R.VI.var(enc), REST), td, U32.add(pos, 1), end, X.DX.at_next(4 <> [], K.WD.app(R.VI.var(enc), REST), td, pos, end, 1, {==}, h)), (%R.VI.len_var(enc) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(pos, 1))), V.U.N(end))) == True{} : Bool}; X.DX.at_pre(R.VI.var(enc), REST, td, U32.add(pos, 1), end, X.DX.at_next(4 <> [], K.WD.app(R.VI.var(enc), REST), td, pos, end, 1, {==}, h))))) :
    {D.wp.enc(4, 0, 0, D.err.set(D.err.set(0, False{}, D.E.TRUNCATED()), False{}, D.E.WININD()), end, _) == D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  %Equal.sym(Bool, U32.is_le(enc, U32.sub(end, U32.add(U32.add(pos, 1), B.B.var.len(enc)))), True{}, X.DX.le_sub(enc, U32.add(U32.add(pos, 1), B.B.var.len(enc)), end, (%P.Nat.add_comm(V.U.N(U32.add(U32.add(pos, 1), B.B.var.len(enc))), V.U.N(enc)) : {Cmp.is_le(Nat.cmp(_, V.U.N(end))) == True{} : Bool}; hf))) :
    {D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), D.err.set(0, Bool.not(_), D.E.TRUNCATED()), end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) == D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(enc)), enc), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(enc)), end)) : Array<U32> & D.WH}
  {==}

# The window's end, from its header fields.
law DW.wend:
  for +p3: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  {U32.add(p3, Q.SP.enc(tlen, dl, il, al)) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}

def DW.wend(p3, tlen, dl, il, al):
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), U32.add(il, al)), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il, al)) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), U32.add(il, al)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), U32.add(dl, U32.add(il, al))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl, U32.add(il, al))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(4, U32.add(dl, U32.add(il, al)))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4, U32.add(dl, U32.add(il, al)))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(4, U32.add(dl, U32.add(il, al)))), U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))), V.U.add_assoc(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))), U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), V.U.add_assoc(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(U32.add(1, B.B.var.len(tlen)), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), V.U.add_assoc(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(1, B.B.var.len(tlen)), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), V.U.add_assoc(1, B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(p3, _) == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), U32.add(1, U32.add(dl, U32.add(il, al)))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1, U32.add(dl, U32.add(il, al)))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), U32.add(1, U32.add(dl, U32.add(il, al)))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1, U32.add(1, U32.add(dl, U32.add(il, al))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))), U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))), U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))), V.U.add_assoc(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))), U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))), V.U.add_assoc(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))), U32.add(U32.add(p3, B.B.var.len(tlen)), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))), V.U.add_assoc(U32.add(p3, B.B.var.len(tlen)), 1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(p3, B.B.var.len(tlen)), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))), U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))))), V.U.add_assoc(p3, B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == _ : U32}
  %V.U.add_assoc(1, 1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %V.U.add_assoc(2, 1, U32.add(1, U32.add(dl, U32.add(il, al)))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %V.U.add_assoc(3, 1, U32.add(dl, U32.add(il, al))) :
    {U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), U32.add(1, U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), K.WD.add_lc(p3, 1, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) :
    {_ == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(p3, B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(p3, B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(tlen), _)) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(p3, B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), _))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), _)) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(p3, B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _)))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(il), B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), _)) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(dl), B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al)))), K.WD.add_lc(p3, 4, U32.add(dl, U32.add(il, al)))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al))))), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(B.B.var.len(tlen), 4, U32.add(p3, U32.add(dl, U32.add(il, al))))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _)))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(il), 4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), _))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(dl), 4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(al), _)) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(al), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), U32.add(4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(al), 4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %V.U.add_assoc(1, 4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {_ == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(dl, U32.add(il, al))), U32.add(dl, U32.add(p3, U32.add(il, al))), K.WD.add_lc(p3, dl, U32.add(il, al))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(il, al)), U32.add(il, U32.add(p3, al)), K.WD.add_lc(p3, il, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, al), U32.add(al, p3), V.U.add_comm(p3, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, U32.add(il, _))))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(il, U32.add(al, p3)), U32.add(al, U32.add(il, p3)), K.WD.add_lc(il, al, p3)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(dl, U32.add(al, U32.add(il, p3))), U32.add(al, U32.add(dl, U32.add(il, p3))), K.WD.add_lc(dl, al, U32.add(il, p3))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), K.WD.add_lc(p3, B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(p3, 1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(B.B.var.len(tlen), _) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), U32.add(1, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), K.WD.add_lc(B.B.var.len(tlen), 1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(p3, B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(tlen), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, _) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(p3, B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(dl), _)) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(p3, B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _)))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(il), B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(dl), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(dl), B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, _) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al)))), K.WD.add_lc(p3, 4, U32.add(dl, U32.add(il, al)))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al))))), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(B.B.var.len(tlen), 4, U32.add(p3, U32.add(dl, U32.add(il, al))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _)))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(il), 4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(dl), 4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, U32.add(B.B.var.len(al), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(al), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), U32.add(4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(al), 4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(1, _) : U32}
  %V.U.add_assoc(1, 4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(dl, U32.add(il, al))), U32.add(dl, U32.add(p3, U32.add(il, al))), K.WD.add_lc(p3, dl, U32.add(il, al))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(il, al)), U32.add(il, U32.add(p3, al)), K.WD.add_lc(p3, il, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) : U32}
  %Equal.sym(U32, U32.add(p3, al), U32.add(al, p3), V.U.add_comm(p3, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, U32.add(il, _))))))) : U32}
  %Equal.sym(U32, U32.add(il, U32.add(al, p3)), U32.add(al, U32.add(il, p3)), K.WD.add_lc(il, al, p3)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) : U32}
  %Equal.sym(U32, U32.add(dl, U32.add(al, U32.add(il, p3))), U32.add(al, U32.add(dl, U32.add(il, p3))), K.WD.add_lc(dl, al, U32.add(il, p3))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(al, U32.add(dl, U32.add(il, p3)))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  {==}

# Positions along held bytes
# ==========================

# xs is held at q, inside e, and q is at least lo.
def DW.atl(+xs: List<&2, U32>, +t: A.Tr, +q: U32, +e: U32, +lo: U32) -> Bool:
  Q.SP.at(xs, t, q, e) && Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(q)))

law DW.atl_mk:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +h: {Q.SP.at(xs, t, q, e) == True{} : Bool}
  {DW.atl(xs, t, q, e, q) == True{} : Bool}

def DW.atl_mk(xs, t, q, e, h):
  %Equal.sym(Bool, Q.SP.at(xs, t, q, e), True{}, h) :
    {Bool.and(_, Cmp.is_le(Nat.cmp(V.U.N(q), V.U.N(q)))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(V.U.N(q), V.U.N(q))), True{}, C.CP.le_refl(V.U.N(q))) :
    {Bool.and(True{}, _) == True{} : Bool}
  {==}

law DW.atl_at:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +lo: U32
  for +h: {DW.atl(xs, t, q, e, lo) == True{} : Bool}
  {Q.SP.at(xs, t, q, e) == True{} : Bool}

def DW.atl_at(xs, t, q, e, lo, h):
  P.Bool.and_l(Q.SP.at(xs, t, q, e), Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(q))), h)

law DW.atl_lo:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +lo: U32
  for +h: {DW.atl(xs, t, q, e, lo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(q))) == True{} : Bool}

def DW.atl_lo(xs, t, q, e, lo, h):
  P.Bool.and_r(Q.SP.at(xs, t, q, e), Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(q))), h)

# Past the held xs.
law DW.atl_next:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +lo: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {DW.atl(K.WD.app(xs, ys), t, q, e, lo) == True{} : Bool}
  {DW.atl(ys, t, U32.add(q, x), e, lo) == True{} : Bool}

def DW.atl_next(xs, ys, t, q, e, x, lo, ex, h):
  %Equal.sym(Bool, Q.SP.at(ys, t, U32.add(q, x), e), True{}, X.DX.at_next(xs, ys, t, q, e, x, ex, DW.atl_at(K.WD.app(xs, ys), t, q, e, lo, h))) :
    {Bool.and(_, Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(U32.add(q, x))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(V.U.N(lo), V.U.N(U32.add(q, x)))), True{}, P.Nat.le_trans(V.U.N(lo), V.U.N(q), V.U.N(U32.add(q, x)), DW.atl_lo(K.WD.app(xs, ys), t, q, e, lo, h), DW.le_add.go(q, x, e, X.DX.at_next.qx(xs, ys, q, e, x, ex, X.DX.at_le(K.WD.app(xs, ys), t, q, e, DW.atl_at(K.WD.app(xs, ys), t, q, e, lo, h)))))) :
    {Bool.and(True{}, _) == True{} : Bool}
  {==}

# Through the header fields after the delta encoding length.
law DW.hdr:
  for +td: A.Tr
  for +p3: U32
  for +end: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +R: List<&2, U32>
  for +h: {Q.SP.at(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))))), td, p3, end) == True{} : Bool}
  {DW.atl(R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, p3) == True{} : Bool}

def DW.hdr(td, p3, end, tlen, dl, il, al, sum, R, h):
  DW.atl_next(U32.and(sum, 255) <> [], R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), end, 1, p3, {==}, DW.atl_next(U32.and(U32.shrn(sum, 8n), 255) <> [], U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), end, 1, p3, {==}, DW.atl_next(U32.and(U32.shrn(sum, 16n), 255) <> [], U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), end, 1, p3, {==}, DW.atl_next(U32.shrn(sum, 24n) <> [], U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> R, td, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), end, 1, p3, {==}, DW.atl_next(R.VI.var(al), K.WD.app(Q.SP.be(sum), R), td, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), end, B.B.var.len(al), p3, Equal.sym(Nat, S.S.len(R.VI.var(al)), V.U.N(B.B.var.len(al)), R.VI.len_var(al)), DW.atl_next(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)), td, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), end, B.B.var.len(il), p3, Equal.sym(Nat, S.S.len(R.VI.var(il)), V.U.N(B.B.var.len(il)), R.VI.len_var(il)), DW.atl_next(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))), td, U32.add(U32.add(p3, B.B.var.len(tlen)), 1), end, B.B.var.len(dl), p3, Equal.sym(Nat, S.S.len(R.VI.var(dl)), V.U.N(B.B.var.len(dl)), R.VI.len_var(dl)), DW.atl_next(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, U32.add(p3, B.B.var.len(tlen)), end, 1, p3, {==}, DW.atl_next(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R)))), td, p3, end, B.B.var.len(tlen), p3, Equal.sym(Nat, S.S.len(R.VI.var(tlen)), V.U.N(B.B.var.len(tlen)), R.VI.len_var(tlen)), DW.atl_mk(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), R))))), td, p3, end, h))))))))))

law DW.len_le:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {Cmp.is_le(Nat.cmp(S.S.len(xs), S.S.len(K.WD.app(xs, ys)))) == True{} : Bool}

def DW.len_le(xs, ys):
  %Equal.sym(Nat, S.S.len(K.WD.app(xs, ys)), Nat.add(S.S.len(xs), S.S.len(ys)), K.WD.len_app(xs, ys)) :
    {Cmp.is_le(Nat.cmp(S.S.len(xs), _)) == True{} : Bool}
  P.Nat.cmp_add_r(S.S.len(xs), S.S.len(ys))

# The sections end inside the delta.
law DW.hwb:
  for +b: U32
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +end: U32
  for +n: Nat
  for +hl: {n == S.S.len(xs) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(b)), V.U.N(end))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(b), n), V.U.N(end))) == True{} : Bool}

def DW.hwb(b, xs, ys, end, n, hl, hb):
  %Equal.sym(Nat, n, S.S.len(xs), hl) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(b), _), V.U.N(end))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(b), S.S.len(xs)), Nat.add(S.S.len(xs), V.U.N(b)), P.Nat.add_comm(V.U.N(b), S.S.len(xs))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(end))) == True{} : Bool}
  P.Nat.le_trans(Nat.add(S.S.len(xs), V.U.N(b)), Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(b)), V.U.N(end), C.CP.le_add_r(S.S.len(xs), S.S.len(K.WD.app(xs, ys)), V.U.N(b), DW.len_le(xs, ys)), hb)

law DW.hf.le:
  for +p3: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +end: U32
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(p3), V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)))) == True{} : Bool}
  for +hwb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(end))) == True{} : Bool}
  {U32.is_le(p3, U32.add(p3, Q.SP.enc(tlen, dl, il, al))) == True{} : Bool}

def DW.hf.le(p3, tlen, dl, il, al, end, hp, hwb):
  %Equal.sym(U32, U32.add(p3, Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), DW.wend(p3, tlen, dl, il, al)) :
    {U32.is_le(p3, _) == True{} : Bool}
  V.U.N_le(p3, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), P.Nat.le_trans(V.U.N(p3), V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al)))), hp, DW.le_add.go(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al)), end, DW.secs.b1(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl, il, al, end, hwb))))

# The delta encoding length fits in the delta.
law DW.hf:
  for +p3: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +end: U32
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(p3), V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)))) == True{} : Bool}
  for +hwb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), V.U.N(end))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p3), V.U.N(Q.SP.enc(tlen, dl, il, al))), V.U.N(end))) == True{} : Bool}

def DW.hf(p3, tlen, dl, il, al, end, hp, hwb):
  %V.U.add_nowrap(p3, Q.SP.enc(tlen, dl, il, al), DW.hf.le(p3, tlen, dl, il, al, end, hp, hwb)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(end))) == True{} : Bool}
  %Equal.sym(U32, U32.add(p3, Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), DW.wend(p3, tlen, dl, il, al)) :
    {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(end))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al)))), Nat.add(V.U.N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), V.U.N(U32.add(dl, U32.add(il, al)))), V.U.add_N(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al)), end, DW.secs.b1(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl, il, al, end, hwb))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(end))) == True{} : Bool}
  DW.secs.b1(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl, il, al, end, hwb)

# A window header with a source segment.
law DW.parse1:
  for +td: A.Tr
  for +pos: U32
  for +end: U32
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +SECS: List<&2, U32>
  for +REST: List<&2, U32>
  for +hl: {Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))) == S.S.len(SECS) : Nat}
  for +h: {Q.SP.at(5 <> K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))))), td, pos, end) == True{} : Bool}
  {D.win.parse(A.A.from(td), pos, end) == (A.A.from(td), D.WH{5, cpl, off, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}

def DW.parse1(td, pos, end, cpl, off, tlen, dl, il, al, sum, SECS, REST, hl, h):
  %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), pos, end), D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end)), DW.head1(td, pos, end, cpl, off, Q.SP.enc(tlen, dl, il, al), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), h, DW.hf(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al, end, DW.atl_lo(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))))), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))))), td, pos, end, 1, {==}, h)))))), DW.hwb(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), SECS, REST, end, Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), hl, X.DX.at_le(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, DW.atl_at(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))))), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))))), td, pos, end, 1, {==}, h))))))))))) :
    {_ == (A.A.from(td), D.WH{5, cpl, off, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & D.WH, D.wp.tlen(5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end)), (A.A.from(td), D.WH{5, cpl, off, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}), DW.tail(td, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, 5, cpl, off, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))))), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))))), td, pos, end, 1, {==}, h)))), {==}, DW.wend(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al), DW.hwb(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), SECS, REST, end, Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), hl, X.DX.at_le(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, DW.atl_at(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), end, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))))), td, U32.add(pos, 1), end, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))))), td, pos, end, 1, {==}, h)))))))))) :
    {_ == (A.A.from(td), D.WH{5, cpl, off, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}
  {==}

# A window header.
law DW.parse0:
  for +td: A.Tr
  for +pos: U32
  for +end: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +SECS: List<&2, U32>
  for +REST: List<&2, U32>
  for +hl: {Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))) == S.S.len(SECS) : Nat}
  for +h: {Q.SP.at(4 <> K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, pos, end) == True{} : Bool}
  {D.win.parse(A.A.from(td), pos, end) == (A.A.from(td), D.WH{4, 0, 0, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}

def DW.parse0(td, pos, end, tlen, dl, il, al, sum, SECS, REST, hl, h):
  %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), pos, end), D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end)), DW.head0(td, pos, end, Q.SP.enc(tlen, dl, il, al), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), h, DW.hf(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al, end, DW.atl_lo(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(pos, 1), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(4 <> [], K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, pos, end, 1, {==}, h)))), DW.hwb(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), SECS, REST, end, Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), hl, X.DX.at_le(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, DW.atl_at(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(pos, 1), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(4 <> [], K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, pos, end, 1, {==}, h))))))))) :
    {_ == (A.A.from(td), D.WH{4, 0, 0, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}
  %Equal.sym(Array<U32> & D.WH, D.wp.tlen(4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0, end, B.B.var.get(A.A.from(td), U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end)), (A.A.from(td), D.WH{4, 0, 0, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}), DW.tail(td, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, 4, 0, 0, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(pos, 1), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(4 <> [], K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, pos, end, 1, {==}, h)), {==}, DW.wend(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al), DW.hwb(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), SECS, REST, end, Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), hl, X.DX.at_le(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, DW.atl_at(K.WD.app(SECS, REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), end, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), end, tlen, dl, il, al, sum, K.WD.app(SECS, REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST)))))), td, U32.add(pos, 1), end, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(4 <> [], K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(SECS, REST))))))), td, pos, end, 1, {==}, h)))))))) :
    {_ == (A.A.from(td), D.WH{4, 0, 0, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}) : Array<U32> & D.WH}
  {==}

# The window's checks
# ===================

# Clearing a cache of depth d.
law DW.clr:
  for +d: Nat
  for +t: A.Tr
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {D.cache.clear(A.A.from(t)) == A.A.from(A.T.new(d, 0)) : Array<U32>}

def DW.clr(d, t, hp):
  match d t:
    case 0n A.TL{v}:
      {==}
    case 0n A.TN{l, r}:
      P.Bool.false_true({D.cache.clear(A.A.from(A.TN{l, r})) == A.A.from(A.T.new(0n, 0)) : Array<U32>}, hp)
    case 1n+p A.TL{v}:
      P.Bool.false_true({D.cache.clear(A.A.from(A.TL{v})) == A.A.from(A.T.new(1n+p, 0)) : Array<U32>}, hp)
    case 1n+p A.TN{l, r}:
      %Equal.sym(Array<U32>, D.cache.clear(A.A.from(l)), A.A.from(A.T.new(p, 0)), DW.clr(p, l, P.Bool.and_l(A.T.pf(p, l), A.T.pf(p, r), hp))) :
        {ANode{_, D.cache.clear(A.A.from(r))} == ANode{A.A.from(A.T.new(p, 0)), A.A.from(A.T.new(p, 0))} : Array<U32>}
      %Equal.sym(Array<U32>, D.cache.clear(A.A.from(r)), A.A.from(A.T.new(p, 0)), DW.clr(p, r, P.Bool.and_r(A.T.pf(p, l), A.T.pf(p, r), hp))) :
        {ANode{A.A.from(A.T.new(p, 0)), _} == ANode{A.A.from(A.T.new(p, 0)), A.A.from(A.T.new(p, 0))} : Array<U32>}
      {==}

# The first instruction check: some instruction bytes.
law DW.flag:
  for +dend: U32
  for +il: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(dend), V.U.N(il)), V.U.N(e))) == True{} : Bool}
  {U32.is_lt(dend, U32.add(dend, il)) == U32.is_lt(0, il) : Bool}

def DW.flag(dend, il, e, h):
  %Equal.sym(Cmp, U32.cmp(dend, U32.add(dend, il)), Nat.cmp(V.U.N(dend), V.U.N(U32.add(dend, il))), V.U.cmp_nat(dend, U32.add(dend, il))) :
    {Cmp.is_lt(_) == Cmp.is_lt(U32.cmp(0, il)) : Bool}
  %Equal.sym(Cmp, U32.cmp(0, il), Nat.cmp(0n, V.U.N(il)), V.U.cmp_nat(0, il)) :
    {Cmp.is_lt(Nat.cmp(V.U.N(dend), V.U.N(U32.add(dend, il)))) == Cmp.is_lt(_) : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(dend, il)), Nat.add(V.U.N(dend), V.U.N(il)), V.U.add_N(dend, il, e, h)) :
    {Cmp.is_lt(Nat.cmp(V.U.N(dend), _)) == Cmp.is_lt(Nat.cmp(0n, V.U.N(il))) : Bool}
  %P.Nat.cmp_add_l(V.U.N(dend), 0n, V.U.N(il)) :
    {Cmp.is_lt(Nat.cmp(V.U.N(dend), Nat.add(V.U.N(dend), V.U.N(il)))) == Cmp.is_lt(_) : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(dend), 0n), V.U.N(dend), P.Nat.add_zero_r(V.U.N(dend))) :
    {Cmp.is_lt(Nat.cmp(V.U.N(dend), Nat.add(V.U.N(dend), V.U.N(il)))) == Cmp.is_lt(Nat.cmp(_, Nat.add(V.U.N(dend), V.U.N(il)))) : Bool}
  {==}

law DW.ne_self:
  for +x: U32
  {U32.is_ne(x, x) == False{} : Bool}

def DW.ne_self(x):
  %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, V.U.cmp_refl(x)) :
    {Bool.not(Cmp.is_eq(_)) == False{} : Bool}
  {==}

law DW.held.h:
  for +tt: A.Tr
  for +t: A.Tr
  for +opos: U32
  for +tlen: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(E))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(U32.add(opos, tlen)), tt, 0), t, 0) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(tlen), tt, opos), t, opos) == True{} : Bool}

def DW.held.h(tt, t, opos, tlen, E, hb, h):
  %V.U.add_zero_r(opos) :
    {S.S.has(S.S.sl(V.U.N(tlen), tt, _), t, _) == True{} : Bool}
  %Equal.sym(U32, U32.add(opos, 0), U32.add(0, opos), V.U.add_comm(opos, 0)) :
    {S.S.has(S.S.sl(V.U.N(tlen), tt, _), t, _) == True{} : Bool}
  P.Bool.and_r(S.S.has(S.S.sl(V.U.N(opos), tt, 0), t, 0), S.S.has(S.S.sl(V.U.N(tlen), tt, U32.add(0, opos)), t, U32.add(0, opos)),
    (%K.WD.has_app(S.S.sl(V.U.N(opos), tt, 0), S.S.sl(V.U.N(tlen), tt, U32.add(0, opos)), t, 0, opos, Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(opos), tt, 0)), V.U.N(opos), S.S.len_sl(V.U.N(opos), tt, 0))) : {_ == True{} : Bool};
      (%K.WD.sl_app(V.U.N(opos), V.U.N(tlen), tt, 0, opos, {==}) : {S.S.has(_, t, 0) == True{} : Bool};
        (%V.U.add_N(opos, tlen, E, hb) : {S.S.has(S.S.sl(_, tt, 0), t, 0) == True{} : Bool};
          h))))

# The target window, held from the target's start, is in place.
law DW.held:
  for +tt: A.Tr
  for +t: A.Tr
  for +opos: U32
  for +tlen: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(E))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(U32.add(opos, tlen)), tt, 0), t, 0) == True{} : Bool}
  {S.S.sl(V.U.N(tlen), t, opos) == S.S.sl(V.U.N(tlen), tt, opos) : List<&2, U32>}

def DW.held(tt, t, opos, tlen, E, hb, h):
  S.S.sl_has(V.U.N(tlen), t, opos, tt, opos, DW.held.h(tt, t, opos, tlen, E, hb, h))

# The length and checksum checks pass.
law DW.fin:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +c2: A.Tr
  for +o2: U32
  for +d2: U32
  for +i2: U32
  for +a2: U32
  for +s2: U32
  for +slen: U32
  for +dlen: U32
  for +ind: U32
  for +sum: U32
  for +seg: U32
  for +cpl: U32
  for +opos: U32
  for +tlen: U32
  for +dend: U32
  for +iend: U32
  for +wend: U32
  for +tt: A.Tr
  for +E: U32
  for +hind: {U32.is_ne(U32.and(ind, 4), 0) == True{} : Bool}
  for +ho: {o2 == U32.add(opos, tlen) : U32}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(E))) == True{} : Bool}
  for +hs: {sum == H.AD.T(tt, opos, tlen) : U32}
  for +h: {S.S.has(S.S.sl(V.U.N(U32.add(opos, tlen)), tt, 0), to, 0) == True{} : Bool}
  {D.win.fin(slen, dlen, ind, sum, D.WinC{seg, cpl, False{}, opos, U32.add(opos, tlen), dend, iend, wend}, X.DX.st(ts, td, to, tb, c2, o2, d2, i2, a2, s2)) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}

def DW.fin(ts, td, to, tb, c2, o2, d2, i2, a2, s2, slen, dlen, ind, sum, seg, cpl, opos, tlen, dend, iend, wend, tt, E, hind, ho, hb, hs, h):
  %Equal.sym(U32, o2, U32.add(opos, tlen), ho) :
    {D.win.sum(Bool.and(U32.is_ne(U32.and(ind, 4), 0), U32.is_eq(D.err.set(0, U32.is_ne(_, U32.add(opos, tlen)), D.E.LENGTH()), 0)), A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), sum, D.err.set(0, U32.is_ne(_, U32.add(opos, tlen)), D.E.LENGTH()), opos) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, U32.is_ne(U32.add(opos, tlen), U32.add(opos, tlen)), False{}, DW.ne_self(U32.add(opos, tlen))) :
    {D.win.sum(Bool.and(U32.is_ne(U32.and(ind, 4), 0), U32.is_eq(D.err.set(0, _, D.E.LENGTH()), 0)), A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), sum, D.err.set(0, _, D.E.LENGTH()), opos) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, U32.is_ne(U32.and(ind, 4), 0), True{}, hind) :
    {D.win.sum(Bool.and(_, True{}), A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), sum, 0, opos) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(U32, U32.sub(U32.add(opos, tlen), opos), tlen, V.U.sub_add_l(opos, tlen)) :
    {D.win.sum.k(A.A.from(ts), A.A.from(td), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), sum, 0, B.B.adler32(A.A.from(to), opos, _)) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Array<U32> & U32, B.B.adler32(A.A.from(to), opos, tlen), (A.A.from(to), H.AD.T(to, opos, tlen)), H.AD.ok(to, opos, tlen, E, (%P.Nat.add_comm(V.U.N(opos), V.U.N(tlen)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb))) :
    {D.win.sum.k(A.A.from(ts), A.A.from(td), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), sum, 0, _) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(U32, H.AD.T(to, opos, tlen), H.AD.T(tt, opos, tlen), H.AD.eq(to, tt, opos, tlen, E, (%P.Nat.add_comm(V.U.N(opos), V.U.N(tlen)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb), DW.held(tt, to, opos, tlen, E, hb, h))) :
    {D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), D.err.set(0, U32.is_ne(_, sum), D.E.CHECKSUM())} == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %hs :
    {D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), D.err.set(0, U32.is_ne(_, sum), D.E.CHECKSUM())} == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, U32.is_ne(sum, sum), False{}, DW.ne_self(sum)) :
    {D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), D.err.set(0, _, D.E.CHECKSUM())} == D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(c2), slen, dlen, wend, U32.add(opos, tlen), 0} : D.DS}
  {==}

# Sections
# ========

law DW.has_pre:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {S.S.has(K.WD.app(xs, []), t, q) == True{} : Bool}

def DW.has_pre(xs, ys, t, q, e, x, ex, h):
  %Equal.sym(List<&2, U32>, K.WD.app(xs, []), xs, K.WD.app_nil(xs)) :
    {S.S.has(_, t, q) == True{} : Bool}
  P.Bool.and_l(S.S.has(xs, t, q), S.S.has(ys, t, U32.add(q, x)), (%K.WD.has_app(xs, ys, t, q, x, ex) : {_ == True{} : Bool}; X.DX.at_has(K.WD.app(xs, ys), t, q, e, h)))

law DW.sect.le:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(K.WD.app(xs, [])), V.U.N(q)), V.U.N(U32.add(q, x)))) == True{} : Bool}

def DW.sect.le(xs, ys, t, q, e, x, ex, h):
  %Equal.sym(List<&2, U32>, K.WD.app(xs, []), xs, K.WD.app_nil(xs)) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(_), V.U.N(q)), V.U.N(U32.add(q, x)))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(q, x)), Nat.add(V.U.N(q), V.U.N(x)), V.U.add_N(q, x, e, X.DX.at_next.qx(xs, ys, q, e, x, ex, X.DX.at_le(K.WD.app(xs, ys), t, q, e, h)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), _)) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(x), S.S.len(xs), ex) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), Nat.add(V.U.N(q), _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(S.S.len(xs), V.U.N(q)), Nat.add(V.U.N(q), S.S.len(xs)), P.Nat.add_comm(S.S.len(xs), V.U.N(q))) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(q), S.S.len(xs)))) == True{} : Bool}
  C.CP.le_refl(Nat.add(V.U.N(q), S.S.len(xs)))

# A section, held up to its end.
law DW.sect:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {Q.SP.at(K.WD.app(xs, []), t, q, U32.add(q, x)) == True{} : Bool}

def DW.sect(xs, ys, t, q, e, x, ex, h):
  X.DX.at_mk(K.WD.app(xs, []), t, q, U32.add(q, x), DW.has_pre(xs, ys, t, q, e, x, ex, h), DW.sect.le(xs, ys, t, q, e, x, ex, h))

# The instruction count bounds the instructions.
law DW.hk:
  for +xs: List<&2, U32>
  for +il: U32
  for +ex: {V.U.N(il) == S.S.len(xs) : Nat}
  {Cmp.is_le(Nat.cmp(S.S.len(xs), U32.to_nat(il))) == True{} : Bool}

def DW.hk(xs, il, ex):
  %Equal.sym(Nat, V.U.N(il), S.S.len(xs), ex) :
    {Cmp.is_le(Nat.cmp(S.S.len(xs), _)) == True{} : Bool}
  C.CP.le_refl(S.S.len(xs))

law DW.heq:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {Nat.add(S.S.len(xs), V.U.N(q)) == V.U.N(U32.add(q, x)) : Nat}

def DW.heq(xs, ys, t, q, e, x, ex, h):
  %Equal.sym(Nat, V.U.N(U32.add(q, x)), Nat.add(V.U.N(q), V.U.N(x)), V.U.add_N(q, x, e, X.DX.at_next.qx(xs, ys, q, e, x, ex, X.DX.at_le(K.WD.app(xs, ys), t, q, e, h)))) :
    {Nat.add(S.S.len(xs), V.U.N(q)) == _ : Nat}
  %Equal.sym(Nat, V.U.N(x), S.S.len(xs), ex) :
    {Nat.add(S.S.len(xs), V.U.N(q)) == Nat.add(V.U.N(q), _) : Nat}
  %Equal.sym(Nat, Nat.add(S.S.len(xs), V.U.N(q)), Nat.add(V.U.N(q), S.S.len(xs)), P.Nat.add_comm(S.S.len(xs), V.U.N(q))) :
    {_ == Nat.add(V.U.N(q), S.S.len(xs)) : Nat}
  {==}

# The section lengths add up.
law DW.slen:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hd: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hi: {V.U.N(il) == S.S.len(ys) : Nat}
  for +ha: {V.U.N(al) == S.S.len(zs) : Nat}
  {Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))) == S.S.len(K.WD.app(xs, K.WD.app(ys, zs))) : Nat}

def DW.slen(xs, ys, zs, dl, il, al, hd, hi, ha):
  %Equal.sym(Nat, S.S.len(K.WD.app(xs, K.WD.app(ys, zs))), Nat.add(S.S.len(xs), S.S.len(K.WD.app(ys, zs))), K.WD.len_app(xs, K.WD.app(ys, zs))) :
    {Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))) == _ : Nat}
  %Equal.sym(Nat, S.S.len(K.WD.app(ys, zs)), Nat.add(S.S.len(ys), S.S.len(zs)), K.WD.len_app(ys, zs)) :
    {Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))) == Nat.add(S.S.len(xs), _) : Nat}
  %Equal.sym(Nat, V.U.N(dl), S.S.len(xs), hd) :
    {Nat.add(_, Nat.add(V.U.N(il), V.U.N(al))) == Nat.add(S.S.len(xs), Nat.add(S.S.len(ys), S.S.len(zs))) : Nat}
  %Equal.sym(Nat, V.U.N(il), S.S.len(ys), hi) :
    {Nat.add(S.S.len(xs), Nat.add(_, V.U.N(al))) == Nat.add(S.S.len(xs), Nat.add(S.S.len(ys), S.S.len(zs))) : Nat}
  %Equal.sym(Nat, V.U.N(al), S.S.len(zs), ha) :
    {Nat.add(S.S.len(xs), Nat.add(S.S.len(ys), _)) == Nat.add(S.S.len(xs), Nat.add(S.S.len(ys), S.S.len(zs))) : Nat}
  {==}

# The address section ends where the window does.
law DW.aend:
  for +p3: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  {U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), al) == U32.add(p3, Q.SP.enc(tlen, dl, il, al)) : U32}

def DW.aend(p3, tlen, dl, il, al):
  %Equal.sym(U32, U32.add(p3, Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), DW.wend(p3, tlen, dl, il, al)) :
    {U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), al) == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), al), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(il, al)), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il, al)) :
    {_ == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(il, al)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl, U32.add(il, al))) :
    {_ == U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))) : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(dl, U32.add(il, al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), U32.add(1, U32.add(dl, U32.add(il, al)))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1, U32.add(dl, U32.add(il, al)))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), U32.add(1, U32.add(dl, U32.add(il, al)))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1, U32.add(1, U32.add(dl, U32.add(il, al))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))), U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))), V.U.add_assoc(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))), U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))), V.U.add_assoc(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl)), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))), U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))), V.U.add_assoc(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(U32.add(p3, B.B.var.len(tlen)), 1), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))), U32.add(U32.add(p3, B.B.var.len(tlen)), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))), V.U.add_assoc(U32.add(p3, B.B.var.len(tlen)), 1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(U32.add(p3, B.B.var.len(tlen)), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))))))))), U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))))), V.U.add_assoc(p3, B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(1, U32.add(1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al)))))))))))) :
    {_ == _ : U32}
  %V.U.add_assoc(1, 1, U32.add(1, U32.add(1, U32.add(dl, U32.add(il, al))))) :
    {U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %V.U.add_assoc(2, 1, U32.add(1, U32.add(dl, U32.add(il, al)))) :
    {U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %V.U.add_assoc(3, 1, U32.add(dl, U32.add(il, al))) :
    {U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) == U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), _)))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), K.WD.add_lc(p3, B.B.var.len(tlen), U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(p3, 1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(B.B.var.len(tlen), _) == U32.add(B.B.var.len(tlen), _) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), U32.add(1, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))), K.WD.add_lc(B.B.var.len(tlen), 1, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(p3, B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(tlen), _)) == U32.add(1, U32.add(B.B.var.len(tlen), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(dl), U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(1, _) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(p3, B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), _))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(tlen), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(il), U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), _)) == U32.add(1, U32.add(B.B.var.len(dl), _)) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(p3, B.B.var.len(al), U32.add(4, U32.add(dl, U32.add(il, al))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _)))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _)))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(tlen), B.B.var.len(al), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _))) == U32.add(1, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(il), B.B.var.len(al), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(dl), _)) == U32.add(1, U32.add(B.B.var.len(dl), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(dl), B.B.var.len(al), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(1, _) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(4, U32.add(dl, U32.add(il, al)))), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al)))), K.WD.add_lc(p3, 4, U32.add(dl, U32.add(il, al)))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(tlen), U32.add(4, U32.add(p3, U32.add(dl, U32.add(il, al))))), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))), K.WD.add_lc(B.B.var.len(tlen), 4, U32.add(p3, U32.add(dl, U32.add(il, al))))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _)))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), _)))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(il), U32.add(4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))), K.WD.add_lc(B.B.var.len(il), 4, U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))) :
    {U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), _))) == U32.add(1, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), _))) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(dl), U32.add(4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))), K.WD.add_lc(B.B.var.len(dl), 4, U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al))))))) :
    {U32.add(1, U32.add(B.B.var.len(al), _)) == U32.add(1, U32.add(B.B.var.len(al), _)) : U32}
  %Equal.sym(U32, U32.add(B.B.var.len(al), U32.add(4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), U32.add(4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))), K.WD.add_lc(B.B.var.len(al), 4, U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {U32.add(1, _) == U32.add(1, _) : U32}
  %V.U.add_assoc(1, 4, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(p3, U32.add(dl, U32.add(il, al)))))))) :
    {_ == _ : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(dl, U32.add(il, al))), U32.add(dl, U32.add(p3, U32.add(il, al))), K.WD.add_lc(p3, dl, U32.add(il, al))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  %Equal.sym(U32, U32.add(p3, U32.add(il, al)), U32.add(il, U32.add(p3, al)), K.WD.add_lc(p3, il, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) : U32}
  %Equal.sym(U32, U32.add(p3, al), U32.add(al, p3), V.U.add_comm(p3, al)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, U32.add(il, _))))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, U32.add(il, _))))))) : U32}
  %Equal.sym(U32, U32.add(il, U32.add(al, p3)), U32.add(al, U32.add(il, p3)), K.WD.add_lc(il, al, p3)) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), U32.add(dl, _)))))) : U32}
  %Equal.sym(U32, U32.add(dl, U32.add(al, U32.add(il, p3))), U32.add(al, U32.add(dl, U32.add(il, p3))), K.WD.add_lc(dl, al, U32.add(il, p3))) :
    {U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) == U32.add(5, U32.add(B.B.var.len(al), U32.add(B.B.var.len(dl), U32.add(B.B.var.len(il), U32.add(B.B.var.len(tlen), _))))) : U32}
  {==}

law DW.gt_false:
  for +x: U32
  for +y: U32
  for +h: {U32.is_le(x, y) == True{} : Bool}
  {U32.is_gt(x, y) == False{} : Bool}

law DW.gt_false.go:
  for +c: Cmp
  for +h: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_gt(c) == False{} : Bool}

def DW.gt_false.go(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.false_true({Cmp.is_gt(GT{}) == False{} : Bool}, h)

def DW.gt_false(x, y, h):
  DW.gt_false.go(U32.cmp(x, y), h)

# The target length check passes.
law DW.big:
  for +opos: U32
  for +tlen: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(2147483648))) == True{} : Bool}
  {U32.is_gt(tlen, U32.sub(2147483648, opos)) == False{} : Bool}

def DW.big(opos, tlen, hb):
  DW.gt_false(tlen, U32.sub(2147483648, opos), X.DX.le_sub(tlen, opos, 2147483648, (%P.Nat.add_comm(V.U.N(opos), V.U.N(tlen)) : {Cmp.is_le(Nat.cmp(_, V.U.N(2147483648))) == True{} : Bool}; hb)))

# The three sections, each held up to its end.
law DW.s_d:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +R: List<&2, U32>
  for +t: A.Tr
  for +b: U32
  for +e: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hdl: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hil: {V.U.N(il) == S.S.len(ys) : Nat}
  for +hal: {V.U.N(al) == S.S.len(zs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, R))), t, b, e) == True{} : Bool}
  {Q.SP.at(K.WD.app(xs, []), t, b, U32.add(b, dl)) == True{} : Bool}

def DW.s_d(xs, ys, zs, R, t, b, e, dl, il, al, hdl, hil, hal, h):
  DW.sect(xs, K.WD.app(ys, K.WD.app(zs, R)), t, b, e, dl, hdl, h)

law DW.s_i:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +R: List<&2, U32>
  for +t: A.Tr
  for +b: U32
  for +e: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hdl: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hil: {V.U.N(il) == S.S.len(ys) : Nat}
  for +hal: {V.U.N(al) == S.S.len(zs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, R))), t, b, e) == True{} : Bool}
  {Q.SP.at(K.WD.app(ys, []), t, U32.add(b, dl), U32.add(U32.add(b, dl), il)) == True{} : Bool}

def DW.s_i(xs, ys, zs, R, t, b, e, dl, il, al, hdl, hil, hal, h):
  DW.sect(ys, K.WD.app(zs, R), t, U32.add(b, dl), e, il, hil, X.DX.at_next(xs, K.WD.app(ys, K.WD.app(zs, R)), t, b, e, dl, hdl, h))

law DW.s_q:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +R: List<&2, U32>
  for +t: A.Tr
  for +b: U32
  for +e: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hdl: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hil: {V.U.N(il) == S.S.len(ys) : Nat}
  for +hal: {V.U.N(al) == S.S.len(zs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, R))), t, b, e) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(b, dl)), V.U.N(il)), V.U.N(e))) == True{} : Bool}

def DW.s_q(xs, ys, zs, R, t, b, e, dl, il, al, hdl, hil, hal, h):
  X.DX.at_next.qx(ys, K.WD.app(zs, R), U32.add(b, dl), e, il, hil, X.DX.at_le(K.WD.app(ys, K.WD.app(zs, R)), t, U32.add(b, dl), e, X.DX.at_next(xs, K.WD.app(ys, K.WD.app(zs, R)), t, b, e, dl, hdl, h)))

law DW.s_e:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +R: List<&2, U32>
  for +t: A.Tr
  for +b: U32
  for +e: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hdl: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hil: {V.U.N(il) == S.S.len(ys) : Nat}
  for +hal: {V.U.N(al) == S.S.len(zs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, R))), t, b, e) == True{} : Bool}
  {Nat.add(S.S.len(ys), V.U.N(U32.add(b, dl))) == V.U.N(U32.add(U32.add(b, dl), il)) : Nat}

def DW.s_e(xs, ys, zs, R, t, b, e, dl, il, al, hdl, hil, hal, h):
  DW.heq(ys, K.WD.app(zs, R), t, U32.add(b, dl), e, il, hil, X.DX.at_next(xs, K.WD.app(ys, K.WD.app(zs, R)), t, b, e, dl, hdl, h))

law DW.s_a:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +R: List<&2, U32>
  for +t: A.Tr
  for +b: U32
  for +e: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +hdl: {V.U.N(dl) == S.S.len(xs) : Nat}
  for +hil: {V.U.N(il) == S.S.len(ys) : Nat}
  for +hal: {V.U.N(al) == S.S.len(zs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, R))), t, b, e) == True{} : Bool}
  for +w: U32
  for +hw: {U32.add(U32.add(U32.add(b, dl), il), al) == w : U32}
  {Q.SP.at(K.WD.app(zs, []), t, U32.add(U32.add(b, dl), il), w) == True{} : Bool}

def DW.s_a(xs, ys, zs, R, t, b, e, dl, il, al, hdl, hil, hal, h, w, hw):
  %hw :
    {Q.SP.at(K.WD.app(zs, []), t, U32.add(U32.add(b, dl), il), _) == True{} : Bool}
  DW.sect(zs, R, t, U32.add(U32.add(b, dl), il), e, al, hal, X.DX.at_next(ys, K.WD.app(zs, R), t, U32.add(b, dl), e, il, hil, X.DX.at_next(xs, K.WD.app(ys, K.WD.app(zs, R)), t, b, e, dl, hdl, h)))

# The instruction loop from a window's first state.
law DW.loop0:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +opos: U32
  for +tlen: U32
  for +il: U32
  for +ops: List<&2, Q.OP>
  for +tt: A.Tr
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +b: U32
  for +dend: U32
  for +iend: U32
  for +wend: U32
  for +off: U32
  for +cpl: U32
  for +hk: {Cmp.is_le(Nat.cmp(S.S.len(Q.SP.insl(ops)), U32.to_nat(il))) == True{} : Bool}
  for +hc: {Q.SP.coks(ops, tb) == True{} : Bool}
  for +hi: {Q.SP.at(K.WD.app(Q.SP.insl(ops), []), td, dend, iend) == True{} : Bool}
  for +heq: {Nat.add(S.S.len(Q.SP.insl(ops)), V.U.N(dend)) == V.U.N(iend) : Nat}
  for +hd: {Q.SP.at(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), []), td, b, dend) == True{} : Bool}
  for +ha: {Q.SP.at(K.WD.app(Q.SP.adrl(Q.SP.halves(ops)), []), td, iend, wend) == True{} : Bool}
  for +hv: {Q.SP.vhs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}) == True{} : Bool}
  for +hdk: {Q.SP.doks(Q.SP.halves(ops)) == True{} : Bool}
  for +hb: {Q.SP.bnds(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}, E, Es) == True{} : Bool}
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  {D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), dend, iend, wend}, (U32.is_lt(dend, iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, b, dend, iend, 0, 0})) == X.DX.st(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), b), iend, Q.SP.anexts(Q.SP.halves(ops), iend), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))) : D.Dec}

def DW.loop0(ts, td, to, tb, opos, tlen, il, ops, tt, dp, E, Es, b, dend, iend, wend, off, cpl, hk, hc, hi, heq, hd, ha, hv, hdk, hb, hp, hdp, he):
  X.DX.loop(U32.to_nat(il), ops, ts, td, to, tb, Q.ST{opos, A.T.new(10n, 0), 0}, b, dend, iend, off, cpl, opos, U32.add(opos, tlen), dend, iend, wend, tt, [], [], [], hk, hc, hi, heq, hd, ha, hv, hdk, dp, E, Es, hp, hdp, he, hb)

# The sections of a window with a source segment.
law DW.sat1:
  for +td: A.Tr
  for +pos: U32
  for +dlen: U32
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +REST: List<&2, U32>
  for +h: {Q.SP.at(5 <> K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST))))))))), td, pos, dlen) == True{} : Bool}
  {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, REST))), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}

def DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, xs, ys, zs, REST, h):
  (%K.WD.app_assoc(ys, zs, REST) : {Q.SP.at(K.WD.app(xs, _), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}; (%K.WD.app_assoc(xs, K.WD.app(ys, zs), REST) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}; DW.atl_at(K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), dlen, tlen, dl, il, al, sum, K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST)))))), td, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), dlen, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST))))))), td, U32.add(U32.add(pos, 1), B.B.var.len(cpl)), dlen, B.B.var.len(off), Equal.sym(Nat, S.S.len(R.VI.var(off)), V.U.N(B.B.var.len(off)), R.VI.len_var(off)), X.DX.at_next(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST)))))))), td, U32.add(pos, 1), dlen, B.B.var.len(cpl), Equal.sym(Nat, S.S.len(R.VI.var(cpl)), V.U.N(B.B.var.len(cpl)), R.VI.len_var(cpl)), X.DX.at_next(5 <> [], K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST))))))))), td, pos, dlen, 1, {==}, h))))))))

# A window with a source segment, decoded.
law DW.win1:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +slen: U32
  for +dlen: U32
  for +pos: U32
  for +opos: U32
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +ops: List<&2, Q.OP>
  for +sum: U32
  for +REST: List<&2, U32>
  for +tt: A.Tr
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +h: {Q.SP.at(5 <> K.WD.app(R.VI.var(cpl), K.WD.app(R.VI.var(off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))), REST))))))))), td, pos, dlen) == True{} : Bool}
  for +hdl: {V.U.N(dl) == S.S.len(Q.SP.datl(Q.SP.halves(ops))) : Nat}
  for +hil: {V.U.N(il) == S.S.len(Q.SP.insl(ops)) : Nat}
  for +hal: {V.U.N(al) == S.S.len(Q.SP.adrl(Q.SP.halves(ops))) : Nat}
  for +hseg: {Bool.and(U32.is_le(cpl, slen), U32.is_le(off, U32.sub(slen, cpl))) == True{} : Bool}
  for +hbig: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(2147483648))) == True{} : Bool}
  for +hc: {Q.SP.coks(ops, tb) == True{} : Bool}
  for +hv: {Q.SP.vhs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}) == True{} : Bool}
  for +hdk: {Q.SP.doks(Q.SP.halves(ops)) == True{} : Bool}
  for +hb: {Q.SP.bnds(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}, E, Es) == True{} : Bool}
  for +hend: {Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})) == U32.add(opos, tlen) : U32}
  for +hs: {sum == H.AD.T(tt, opos, tlen) : U32}
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hca: {A.T.pf(10n, ca) == True{} : Bool}
  for +hto: {S.S.has(S.S.sl(V.U.N(opos), tt, 0), to, 0) == True{} : Bool}
  {D.win.dec(D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), slen, dlen, pos, opos, 0}) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}

def DW.win1(ts, td, to, tb, ca, slen, dlen, pos, opos, cpl, off, tlen, dl, il, al, ops, sum, REST, tt, dp, E, Es, h, hdl, hil, hal, hseg, hbig, hc, hv, hdk, hb, hend, hs, hp, hdp, he, hca, hto):
  %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), pos, dlen), (A.A.from(td), D.WH{5, cpl, off, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}), DW.parse1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))), REST, DW.slen(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), dl, il, al, hdl, hil, hal), h)) :
    {D.win.go(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), slen, dlen, opos, 0, _) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, Bool.and(U32.is_le(cpl, slen), U32.is_le(off, U32.sub(slen, cpl))), True{}, hseg) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (Bool.and(U32.is_lt(0, il), U32.is_eq(Bool.pick(U32, Bool.and(U32.is_eq(Bool.pick(U32, Bool.not(_), D.E.SOURCE(), 0), 0), U32.is_gt(tlen, U32.sub(2147483648, opos))), D.E.TOOBIG(), Bool.pick(U32, Bool.not(_), D.E.SOURCE(), 0)), 0)), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), D.cache.clear(A.A.from(ca)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, Bool.pick(U32, Bool.and(U32.is_eq(Bool.pick(U32, Bool.not(_), D.E.SOURCE(), 0), 0), U32.is_gt(tlen, U32.sub(2147483648, opos))), D.E.TOOBIG(), Bool.pick(U32, Bool.not(_), D.E.SOURCE(), 0))}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, U32.is_gt(tlen, U32.sub(2147483648, opos)), False{}, DW.big(opos, tlen, hbig)) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (Bool.and(U32.is_lt(0, il), U32.is_eq(Bool.pick(U32, Bool.and(U32.is_eq(Bool.pick(U32, Bool.not(True{}), D.E.SOURCE(), 0), 0), _), D.E.TOOBIG(), Bool.pick(U32, Bool.not(True{}), D.E.SOURCE(), 0)), 0)), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), D.cache.clear(A.A.from(ca)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, Bool.pick(U32, Bool.and(U32.is_eq(Bool.pick(U32, Bool.not(True{}), D.E.SOURCE(), 0), 0), _), D.E.TOOBIG(), Bool.pick(U32, Bool.not(True{}), D.E.SOURCE(), 0))}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Array<U32>, D.cache.clear(A.A.from(ca)), A.A.from(A.T.new(10n, 0)), DW.clr(10n, ca, hca)) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (Bool.and(U32.is_lt(0, il), True{}), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), _, opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, Bool.and(U32.is_lt(0, il), True{}), U32.is_lt(0, il), P.Bool.and_true(U32.is_lt(0, il))) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (_, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %DW.flag(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il, dlen, DW.s_q(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h))) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (_, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(D.Dec, D.dec.loop(U32.to_nat(il), D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (U32.is_lt(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0})), X.DX.st(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), DW.loop0(ts, td, to, tb, opos, tlen, il, ops, tt, dp, E, Es, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), off, cpl, DW.hk(Q.SP.insl(ops), il, hil), hc, DW.s_i(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_e(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_d(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_a(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat1(td, pos, dlen, cpl, off, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), DW.aend(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al)), hv, hdk, hb, hp, hdp, he)) :
    {D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, _) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(D.DS, D.win.fin(slen, dlen, 5, sum, D.WinC{off, cpl, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, X.DX.st(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})))), D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0}, DW.fin(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), slen, dlen, 5, sum, off, cpl, opos, tlen, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), tt, 2147483648, {==}, hend, hbig, hs, (%hend : {S.S.has(S.S.sl(V.U.N(_), tt, 0), Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), 0) == True{} : Bool}; M.SM.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}, dp, E, Es, hp, hdp, he, hv, hb, hto)))) :
    {_ == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, off, cpl, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  {==}

# The sections of a window.
law DW.sat0:
  for +td: A.Tr
  for +pos: U32
  for +dlen: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +sum: U32
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  for +REST: List<&2, U32>
  for +h: {Q.SP.at(4 <> K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST))))))), td, pos, dlen) == True{} : Bool}
  {Q.SP.at(K.WD.app(xs, K.WD.app(ys, K.WD.app(zs, REST))), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}

def DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, xs, ys, zs, REST, h):
  (%K.WD.app_assoc(ys, zs, REST) : {Q.SP.at(K.WD.app(xs, _), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}; (%K.WD.app_assoc(xs, K.WD.app(ys, zs), REST) : {Q.SP.at(_, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen) == True{} : Bool}; DW.atl_at(K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST), td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), DW.hdr(td, U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), dlen, tlen, dl, il, al, sum, K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST), X.DX.at_next(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST)))))), td, U32.add(pos, 1), dlen, B.B.var.len(Q.SP.enc(tlen, dl, il, al)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), V.U.N(B.B.var.len(Q.SP.enc(tlen, dl, il, al))), R.VI.len_var(Q.SP.enc(tlen, dl, il, al))), X.DX.at_next(4 <> [], K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(xs, K.WD.app(ys, zs)), REST))))))), td, pos, dlen, 1, {==}, h))))))

# A window, decoded.
law DW.win0:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +slen: U32
  for +dlen: U32
  for +pos: U32
  for +opos: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +ops: List<&2, Q.OP>
  for +sum: U32
  for +REST: List<&2, U32>
  for +tt: A.Tr
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +h: {Q.SP.at(4 <> K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(Q.SP.be(sum), K.WD.app(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))), REST))))))), td, pos, dlen) == True{} : Bool}
  for +hdl: {V.U.N(dl) == S.S.len(Q.SP.datl(Q.SP.halves(ops))) : Nat}
  for +hil: {V.U.N(il) == S.S.len(Q.SP.insl(ops)) : Nat}
  for +hal: {V.U.N(al) == S.S.len(Q.SP.adrl(Q.SP.halves(ops))) : Nat}
  for +hbig: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), V.U.N(tlen)), V.U.N(2147483648))) == True{} : Bool}
  for +hc: {Q.SP.coks(ops, tb) == True{} : Bool}
  for +hv: {Q.SP.vhs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}) == True{} : Bool}
  for +hdk: {Q.SP.doks(Q.SP.halves(ops)) == True{} : Bool}
  for +hb: {Q.SP.bnds(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}, E, Es) == True{} : Bool}
  for +hend: {Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})) == U32.add(opos, tlen) : U32}
  for +hs: {sum == H.AD.T(tt, opos, tlen) : U32}
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hca: {A.T.pf(10n, ca) == True{} : Bool}
  for +hto: {S.S.has(S.S.sl(V.U.N(opos), tt, 0), to, 0) == True{} : Bool}
  {D.win.dec(D.DS{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), slen, dlen, pos, opos, 0}) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}

def DW.win0(ts, td, to, tb, ca, slen, dlen, pos, opos, tlen, dl, il, al, ops, sum, REST, tt, dp, E, Es, h, hdl, hil, hal, hbig, hc, hv, hdk, hb, hend, hs, hp, hdp, he, hca, hto):
  %Equal.sym(Array<U32> & D.WH, D.win.parse(A.A.from(td), pos, dlen), (A.A.from(td), D.WH{4, 0, 0, tlen, dl, il, al, sum, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0}), DW.parse0(td, pos, dlen, tlen, dl, il, al, sum, K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))), REST, DW.slen(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), dl, il, al, hdl, hil, hal), h)) :
    {D.win.go(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), slen, dlen, opos, 0, _) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, U32.is_gt(tlen, U32.sub(2147483648, opos)), False{}, DW.big(opos, tlen, hbig)) :
    {D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (Bool.and(U32.is_lt(0, il), U32.is_eq(Bool.pick(U32, _, D.E.TOOBIG(), 0), 0)), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), D.cache.clear(A.A.from(ca)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, Bool.pick(U32, _, D.E.TOOBIG(), 0)}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Array<U32>, D.cache.clear(A.A.from(ca)), A.A.from(A.T.new(10n, 0)), DW.clr(10n, ca, hca)) :
    {D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (Bool.and(U32.is_lt(0, il), True{}), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), _, opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(Bool, Bool.and(U32.is_lt(0, il), True{}), U32.is_lt(0, il), P.Bool.and_true(U32.is_lt(0, il))) :
    {D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (_, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %DW.flag(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il, dlen, DW.s_q(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h))) :
    {D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, D.dec.loop(U32.to_nat(il), D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (_, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0}))) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(D.Dec, D.dec.loop(U32.to_nat(il), D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, (U32.is_lt(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(A.T.new(10n, 0)), opos, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), 0, 0})), X.DX.st(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), DW.loop0(ts, td, to, tb, opos, tlen, il, ops, tt, dp, E, Es, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), 0, 0, DW.hk(Q.SP.insl(ops), il, hil), hc, DW.s_i(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_e(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_d(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h)), DW.s_a(Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, td, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dlen, dl, il, al, hdl, hil, hal, DW.sat0(td, pos, dlen, tlen, dl, il, al, sum, Q.SP.datl(Q.SP.halves(ops)), Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)), REST, h), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), DW.aend(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), tlen, dl, il, al)), hv, hdk, hb, hp, hdp, he)) :
    {D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, _) == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  %Equal.sym(D.DS, D.win.fin(slen, dlen, 4, sum, D.WinC{0, 0, False{}, opos, U32.add(opos, tlen), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))}, X.DX.st(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})))), D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0}, DW.fin(ts, td, Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), tb, Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.so(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), Q.SP.dnexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1)), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), Q.SP.anexts(Q.SP.halves(ops), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il)), Q.SP.ss(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0})), slen, dlen, 4, sum, 0, 0, opos, tlen, U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), tt, 2147483648, {==}, hend, hbig, hs, (%hend : {S.S.has(S.S.sl(V.U.N(_), tt, 0), Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}), 0) == True{} : Bool}; M.SM.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0}, dp, E, Es, hp, hdp, he, hv, hb, hto)))) :
    {_ == D.DS{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.outs(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, to, Q.ST{opos, A.T.new(10n, 0), 0})), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.run(Q.SP.halves(ops), Q.XC{ts, tt, 0, 0, opos, U32.add(opos, tlen)}, Q.ST{opos, A.T.new(10n, 0), 0}))), slen, dlen, U32.add(U32.add(U32.add(pos, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(opos, tlen), 0} : D.DS}
  {==}
