import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ../encode.bend as N
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./words.bend as K
import ./copy.bend as C
import ./varint.bend as R
import ./spec.bend as Q
import ./sem.bend as M
import ./bits.bend as Z
import ./emit.bend as EM_
import ./einst.bend as EI_
import ./settle.bend as SE_

# The source segment
# ==================
#
# The scan buffers matches with source positions (below slen) or, past
# slen, offsets into the target window. seg.choose picks the window's copy
# segment [off, off + cpl) and seg.map moves the addresses to it.

# A match as the scan buffers it.
def SG.k0(+ts: A.Tr, +tt: A.Tr, +slen: U32, +w0: U32, +run: Bool, +pos: U32, +len: U32, +val: U32) -> Bool:
  match run:
    case True{}:
      S.S.has(C.CP.rep(V.U.N(len), val), tt, pos)
    case False{}:
      Bool.pick(Bool, U32.is_lt(val, slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos)))

def SG.ok0(+ts: A.Tr, +tt: A.Tr, +slen: U32, +w0: U32, +w1: U32, +e: N.Ent) -> Bool:
  match e:
    case N.Ent{pos, len, val, run}:
      Bool.and(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))))

# Its source bytes lie in [off, off + cpl).
def SG.inr(+slen: U32, +off: U32, +cpl: U32, +e: N.Ent) -> Bool:
  match e:
    case N.Ent{pos, len, val, run}:
      Bool.or(run, Bool.or(Bool.not(U32.is_lt(val, slen)), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl))))))))

# The match with its address in the window: past the segment's start, or
# past the segment for the target.
def SG.mv(+slen: U32, +off: U32, +cpl: U32, +e: N.Ent) -> N.Ent:
  match e:
    case N.Ent{pos, len, val, run}:
      N.Ent{pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))), run}

law SG.one_le:
  for +n: U32
  for +h: {U32.is_eq(n, 0) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(1n, V.U.N(n))) == True{} : Bool}

def SG.one_le(n, h):
  P.Nat.lt_le_succ(0n, V.U.N(n), P.Cmp.is_lt_lt(Nat.cmp(0n, V.U.N(n)), (%V.U.cmp_nat(0, n) : {Cmp.is_lt(_) == True{} : Bool}; SE_.SE.pos_ne(n, h))))

law SG.pw:
  for +pos: U32
  for +w0: U32
  for +w1: U32
  for +len: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(pos, w0)), V.U.N(U32.sub(w1, w0)))) == True{} : Bool}

def SG.pw(pos, w0, w1, len, hlo, hpos):
  EM_.EM.k_le(pos, w1, w0, hlo, V.U.N_le(pos, w1, P.Nat.le_trans(V.U.N(pos), Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(pos), V.U.N(len)), hpos)))

law SG.here_N:
  for +cpl: U32
  for +pos: U32
  for +w0: U32
  for +w1: U32
  for +len: U32
  for +HB: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  {V.U.N(U32.add(cpl, U32.sub(pos, w0))) == Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))) : Nat}

def SG.here_N(cpl, pos, w0, w1, len, HB, hlo, hpos, hH):
  V.U.add_N(cpl, U32.sub(pos, w0), HB, P.Nat.le_trans(Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB), EI_.EI.lea(V.U.N(cpl), V.U.N(U32.sub(pos, w0)), V.U.N(U32.sub(w1, w0)), SG.pw(pos, w0, w1, len, hlo, hpos)), hH))

law SG.s.vN:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {Nat.add(V.U.N(U32.sub(val, off)), V.U.N(off)) == V.U.N(val) : Nat}

def SG.s.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  V.U.sub_nat(val, off, hv)

law SG.s.lt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {Nat.cmp(V.U.N(U32.sub(val, off)), V.U.N(cpl)) == LT{} : Cmp}

def SG.s.lt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  %P.Nat.cmp_add_rr(V.U.N(U32.sub(val, off)), V.U.N(cpl), V.U.N(off)) : {_ == LT{} : Cmp}
  %P.Nat.add_comm(V.U.N(off), V.U.N(cpl)) : {Nat.cmp(Nat.add(V.U.N(U32.sub(val, off)), V.U.N(off)), _) == LT{} : Cmp}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(val, off)), V.U.N(off)), V.U.N(val), SG.s.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) : {Nat.cmp(_, Nat.add(V.U.N(off), V.U.N(cpl))) == LT{} : Cmp}
  P.Nat.lt_le_trans(V.U.N(val), Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)), (%P.Nat.add_zero_r(V.U.N(val)) : {Nat.cmp(_, Nat.add(V.U.N(val), V.U.N(len))) == LT{} : Cmp}; (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(val), 0n), Nat.add(V.U.N(val), V.U.N(len))), Nat.cmp(0n, V.U.N(len)), P.Nat.cmp_add_l(V.U.N(val), 0n, V.U.N(len))) : {_ == LT{} : Cmp}; P.Nat.lt_le_trans(0n, 1n, V.U.N(len), {==}, SG.one_le(len, hz)))), hvl)

law SG.s.cpos:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {U32.is_lt(0, cpl) == True{} : Bool}

def SG.s.cpos(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  V.U.N_lt(0, cpl, P.Nat.le_lt_trans(0n, V.U.N(U32.sub(val, off)), V.U.N(cpl), SE_.SE.le0(V.U.N(U32.sub(val, off))), SG.s.lt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)))

law SG.s.seg:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {Q.SP.wseg(cpl, off) == off : U32}

def SG.s.seg(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  %Equal.sym(Bool, U32.is_lt(0, cpl), True{}, SG.s.cpos(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) :
    {Bool.pick(U32, _, off, 0) == off : U32}
  {==}

law SG.s.here:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {U32.is_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}

def SG.s.here(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  V.U.N_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0)), (%Equal.sym(Nat, V.U.N(U32.add(cpl, U32.sub(pos, w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), SG.here_N(cpl, pos, w0, w1, len, HB, hlo, hpos, hH)) : {Nat.cmp(V.U.N(U32.sub(val, off)), _) == LT{} : Cmp};
    P.Nat.lt_le_trans(V.U.N(U32.sub(val, off)), V.U.N(cpl), Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), SG.s.lt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas), P.Nat.cmp_add_r(V.U.N(cpl), V.U.N(U32.sub(pos, w0))))))

law SG.s.sz:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {U32.is_le(len, U32.sub(cpl, U32.sub(val, off))) == True{} : Bool}

law SG.s.sz2:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(U32.sub(val, off))), V.U.N(cpl))) == True{} : Bool}

def SG.s.sz2(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  %Equal.sym(Nat, Nat.add(V.U.N(len), V.U.N(U32.sub(val, off))), Nat.add(V.U.N(U32.sub(val, off)), V.U.N(len)), P.Nat.add_comm(V.U.N(len), V.U.N(U32.sub(val, off)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(cpl))) == True{} : Bool}
  %P.Nat.cmp_add_rr(Nat.add(V.U.N(U32.sub(val, off)), V.U.N(len)), V.U.N(cpl), V.U.N(off)) : {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V.U.N(U32.sub(val, off)), V.U.N(len)), V.U.N(off)), Nat.add(V.U.N(U32.sub(val, off)), Nat.add(V.U.N(len), V.U.N(off))), P.Nat.add_assoc(V.U.N(U32.sub(val, off)), V.U.N(len), V.U.N(off))) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(cpl), V.U.N(off)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(len), V.U.N(off)), Nat.add(V.U.N(off), V.U.N(len)), P.Nat.add_comm(V.U.N(len), V.U.N(off))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(val, off)), _), Nat.add(V.U.N(cpl), V.U.N(off)))) == True{} : Bool}
  %P.Nat.add_assoc(V.U.N(U32.sub(val, off)), V.U.N(off), V.U.N(len)) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(cpl), V.U.N(off)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(val, off)), V.U.N(off)), V.U.N(val), SG.s.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(len)), Nat.add(V.U.N(cpl), V.U.N(off)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(cpl), V.U.N(off)), Nat.add(V.U.N(off), V.U.N(cpl)), P.Nat.add_comm(V.U.N(cpl), V.U.N(off))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), _)) == True{} : Bool}
  hvl

def SG.s.sz(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  V.U.N_le(len, U32.sub(cpl, U32.sub(val, off)), (%P.Nat.cmp_add_rr(V.U.N(len), V.U.N(U32.sub(cpl, U32.sub(val, off))), V.U.N(U32.sub(val, off))) : {Cmp.is_le(_) == True{} : Bool};
    (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(cpl, U32.sub(val, off))), V.U.N(U32.sub(val, off))), V.U.N(cpl), V.U.sub_nat(cpl, U32.sub(val, off), V.U.lt_to_le(U32.sub(val, off), cpl, V.U.N_lt(U32.sub(val, off), cpl, SG.s.lt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas))))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(U32.sub(val, off))), _)) == True{} : Bool};
      SG.s.sz2(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas))))

law SG.t.b:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), V.U.N(HB))) == True{} : Bool}

def SG.t.b(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  P.Nat.le_trans(Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB),
    (%P.Nat.add_comm(V.U.N(U32.sub(w1, w0)), V.U.N(cpl)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), _)) == True{} : Bool};
      SE_.SE.lear(V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(w1, w0)), V.U.N(cpl), P.Nat.lt_to_le(V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(w1, w0)), P.Nat.lt_le_trans(V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(pos, w0)), V.U.N(U32.sub(w1, w0)), V.U.lt_N(U32.sub(val, slen), U32.sub(pos, w0), hlt), SG.pw(pos, w0, w1, len, hlo, hpos))))),
    hH)

law SG.t.vN:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {V.U.N(U32.add(U32.sub(val, slen), cpl)) == Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)) : Nat}

def SG.t.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  V.U.add_N(U32.sub(val, slen), cpl, HB, SG.t.b(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt))

law SG.t.nlt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {U32.is_lt(U32.add(U32.sub(val, slen), cpl), cpl) == False{} : Bool}

def SG.t.nlt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  EI_.EI.le_nlt(cpl, U32.add(U32.sub(val, slen), cpl), (%Equal.sym(Nat, V.U.N(U32.add(U32.sub(val, slen), cpl)), Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), SG.t.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) : {Cmp.is_le(Nat.cmp(V.U.N(cpl), _)) == True{} : Bool}; P.Nat.le_add_l(V.U.N(U32.sub(val, slen)), V.U.N(cpl))))

law SG.t.here:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {U32.is_lt(U32.add(U32.sub(val, slen), cpl), U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}

def SG.t.here(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  V.U.N_lt(U32.add(U32.sub(val, slen), cpl), U32.add(cpl, U32.sub(pos, w0)), (%Equal.sym(Nat, V.U.N(U32.add(U32.sub(val, slen), cpl)), Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), SG.t.vN(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) : {Nat.cmp(_, V.U.N(U32.add(cpl, U32.sub(pos, w0)))) == LT{} : Cmp};
    (%Equal.sym(Nat, V.U.N(U32.add(cpl, U32.sub(pos, w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), SG.here_N(cpl, pos, w0, w1, len, HB, hlo, hpos, hH)) : {Nat.cmp(Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), _) == LT{} : Cmp};
      (%P.Nat.add_comm(V.U.N(U32.sub(pos, w0)), V.U.N(cpl)) : {Nat.cmp(Nat.add(V.U.N(U32.sub(val, slen)), V.U.N(cpl)), _) == LT{} : Cmp};
        P.Nat.add_lt_r(V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(pos, w0)), V.U.N(cpl), V.U.lt_N(U32.sub(val, slen), U32.sub(pos, w0), hlt))))))

law SG.t.idx:
  for +d: U32
  for +cpl: U32
  for +w0: U32
  {U32.add(w0, U32.sub(U32.add(d, cpl), cpl)) == U32.add(w0, d) : U32}

def SG.t.idx(d, cpl, w0):
  %Equal.sym(U32, U32.sub(U32.add(d, cpl), cpl), d, V.U.sub_add(d, cpl)) :
    {U32.add(w0, _) == U32.add(w0, d) : U32}
  {==}

law SG.t.cb:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, slen))), V.U.N(pos))) == True{} : Bool}

law SG.t.cb2:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  {Nat.cmp(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), V.U.N(pos)) == LT{} : Cmp}

def SG.t.cb2(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  %V.U.sub_nat(pos, w0, hlo) : {Nat.cmp(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), _) == LT{} : Cmp}
  %P.Nat.add_comm(V.U.N(w0), V.U.N(U32.sub(pos, w0))) : {Nat.cmp(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), _) == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), Nat.add(V.U.N(w0), V.U.N(U32.sub(pos, w0)))), Nat.cmp(V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(pos, w0))), P.Nat.cmp_add_l(V.U.N(w0), V.U.N(U32.sub(val, slen)), V.U.N(U32.sub(pos, w0)))) : {_ == LT{} : Cmp}
  V.U.lt_N(U32.sub(val, slen), U32.sub(pos, w0), hlt)

def SG.t.cb(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt):
  %Equal.sym(Nat, V.U.N(U32.add(w0, U32.sub(val, slen))), Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), V.U.add_N(w0, U32.sub(val, slen), pos, P.Nat.lt_to_le(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), V.U.N(pos), SG.t.cb2(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)))) :
    {Cmp.is_lt(Nat.cmp(_, V.U.N(pos))) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w0), V.U.N(U32.sub(val, slen))), V.U.N(pos)), LT{}, SG.t.cb2(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) :
    {Cmp.is_lt(_) == True{} : Bool}
  {==}

# A source copy, at its window address.
law SG.src:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hv: {U32.is_le(off, val) == True{} : Bool}
  for +hvl: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos) == True{} : Bool}
  {EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, False{}, pos, len, U32.sub(val, off)) == True{} : Bool}

def SG.src(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas):
  %Equal.sym(U32, Q.SP.wseg(cpl, off), off, SG.s.seg(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) :
    {Bool.and(U32.is_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0))), Bool.and(Bool.pick(Bool, U32.is_lt(U32.sub(val, off), cpl), Bool.and(U32.is_le(len, U32.sub(cpl, U32.sub(val, off))), S.S.has(S.S.sl(V.U.N(len), ts, U32.add(_, U32.sub(val, off))), tt, pos)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(U32.sub(val, off), cpl))), tt, pos)), Bool.pick(Bool, U32.is_lt(U32.sub(val, off), cpl), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(U32.add(_, U32.sub(val, off)))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.sub(val, off), cpl))), V.U.N(pos)))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.sub(val, off), cpl), True{}, V.U.N_lt(U32.sub(val, off), cpl, SG.s.lt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas))) :
    {Bool.and(U32.is_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0))), Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(len, U32.sub(cpl, U32.sub(val, off))), S.S.has(S.S.sl(V.U.N(len), ts, U32.add(off, U32.sub(val, off))), tt, pos)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(U32.sub(val, off), cpl))), tt, pos)), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(U32.add(off, U32.sub(val, off)))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.sub(val, off), cpl))), V.U.N(pos)))))) == True{} : Bool}
  %Equal.sym(U32, U32.add(off, U32.sub(val, off)), val, EM_.EM.addsub(off, val)) :
    {Bool.and(U32.is_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0))), Bool.and(Bool.and(U32.is_le(len, U32.sub(cpl, U32.sub(val, off))), S.S.has(S.S.sl(V.U.N(len), ts, _), tt, pos)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(_)), V.U.N(Es))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.sub(val, off), U32.add(cpl, U32.sub(pos, w0))), True{}, SG.s.here(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) :
    {Bool.and(_, Bool.and(Bool.and(U32.is_le(len, U32.sub(cpl, U32.sub(val, off))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(val)), V.U.N(Es))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(len, U32.sub(cpl, U32.sub(val, off))), True{}, SG.s.sz(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hv, hvl, hs, hhas)) :
    {Bool.and(True{}, Bool.and(Bool.and(_, S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(val)), V.U.N(Es))))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), True{}, hhas) :
    {Bool.and(True{}, Bool.and(Bool.and(True{}, _), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(val)), V.U.N(Es))))) == True{} : Bool}
  P.Nat.le_trans(Nat.add(V.U.N(len), V.U.N(val)), V.U.N(slen), V.U.N(Es), (%P.Nat.add_comm(V.U.N(val), V.U.N(len)) : {Cmp.is_le(Nat.cmp(_, V.U.N(slen))) == True{} : Bool}; hs), hEs)

# A target copy, at its window address.
law SG.tgt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlt: {U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos) == True{} : Bool}
  {EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, False{}, pos, len, U32.add(U32.sub(val, slen), cpl)) == True{} : Bool}

def SG.tgt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt, hhas):
  %Equal.sym(Bool, U32.is_lt(U32.add(U32.sub(val, slen), cpl), cpl), False{}, SG.t.nlt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) :
    {Bool.and(U32.is_lt(U32.add(U32.sub(val, slen), cpl), U32.add(cpl, U32.sub(pos, w0))), Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(len, U32.sub(cpl, U32.add(U32.sub(val, slen), cpl))), S.S.has(S.S.sl(V.U.N(len), ts, U32.add(Q.SP.wseg(cpl, off), U32.add(U32.sub(val, slen), cpl))), tt, pos)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(U32.add(U32.sub(val, slen), cpl), cpl))), tt, pos)), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(len), V.U.N(U32.add(Q.SP.wseg(cpl, off), U32.add(U32.sub(val, slen), cpl)))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.add(U32.sub(val, slen), cpl), cpl))), V.U.N(pos)))))) == True{} : Bool}
  %Equal.sym(U32, U32.add(w0, U32.sub(U32.add(U32.sub(val, slen), cpl), cpl)), U32.add(w0, U32.sub(val, slen)), SG.t.idx(U32.sub(val, slen), cpl, w0)) :
    {Bool.and(U32.is_lt(U32.add(U32.sub(val, slen), cpl), U32.add(cpl, U32.sub(pos, w0))), Bool.and(S.S.has(S.S.sl(V.U.N(len), tt, _), tt, pos), Cmp.is_lt(Nat.cmp(V.U.N(_), V.U.N(pos))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.add(U32.sub(val, slen), cpl), U32.add(cpl, U32.sub(pos, w0))), True{}, SG.t.here(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) :
    {Bool.and(_, Bool.and(S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, slen))), V.U.N(pos))))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos), True{}, hhas) :
    {Bool.and(True{}, Bool.and(_, Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, slen))), V.U.N(pos))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, slen))), V.U.N(pos))), True{}, SG.t.cb(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hlt)) :
    {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

# The address part, a copy: source or target.
law SG.cp.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hz: {U32.is_eq(len, 0) == False{} : Bool}
  for +hk: {SG.k0(ts, tt, slen, w0, False{}, pos, len, val) == True{} : Bool}
  for +hinr: {Bool.or(Bool.not(U32.is_lt(val, slen)), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl))))))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(val, slen) == c : Bool}
  {EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, False{}, pos, len, N.u32.pick(c, U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))) == True{} : Bool}

def SG.cp.c(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz, hk, hinr, c, ec):
  match c:
    case True{}:
      SG.src(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, hz,
        P.Bool.and_l(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))), (%hz : {Bool.or(_, Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))))) == True{} : Bool}; (%ec : {Bool.or(Bool.not(_), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl))))))) == True{} : Bool}; hinr))),
        P.Bool.and_r(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))), (%hz : {Bool.or(_, Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl)))))) == True{} : Bool}; (%ec : {Bool.or(Bool.not(_), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(off, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(off), V.U.N(cpl))))))) == True{} : Bool}; hinr))),
        P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), (%ec : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; hk)),
        P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), (%ec : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; hk)))
    case False{}:
      SG.tgt(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH,
        P.Bool.and_l(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos), (%ec : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; hk)),
        P.Bool.and_r(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos), (%ec : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; hk)))

law SG.ek.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +run: Bool
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)) == True{} : Bool}
  for +hinr: {SG.inr(slen, off, cpl, N.Ent{pos, len, val, run}) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(len, 0) == z : Bool}
  {Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, run, pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))) == True{} : Bool}

def SG.ek.c(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, run, hor, hinr, z, ez):
  match run z:
    case True{} True{}:
      %Equal.sym(Bool, U32.is_eq(len, 0), True{}, ez) :
        {Bool.or(_, EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, True{}, pos, len, N.u32.pick(True{}, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, U32.is_eq(len, 0), True{}, ez) :
        {Bool.or(_, EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, False{}, pos, len, N.u32.pick(False{}, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))) == True{} : Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, U32.is_eq(len, 0), False{}, ez) :
        {Bool.or(_, EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, True{}, pos, len, N.u32.pick(True{}, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))) == True{} : Bool}
      (%ez : {Bool.or(_, SG.k0(ts, tt, slen, w0, True{}, pos, len, val)) == True{} : Bool}; hor)
    case False{} False{}:
      %Equal.sym(Bool, U32.is_eq(len, 0), False{}, ez) :
        {Bool.or(_, EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, False{}, pos, len, N.u32.pick(False{}, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))) == True{} : Bool}
      SG.cp.c(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, hlo, hpos, hH, hEs, ez, (%ez : {Bool.or(_, SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}; hor), hinr, U32.is_lt(val, slen), {==})

# A buffered match the scan found, its address moved into the window, is
# fit to write.
law SG.mv_ok:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hok: {SG.ok0(ts, tt, slen, w0, w1, N.Ent{pos, len, val, run}) == True{} : Bool}
  for +hinr: {SG.inr(slen, off, cpl, N.Ent{pos, len, val, run}) == True{} : Bool}
  {SE_.SE.ok(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.mv(slen, off, cpl, N.Ent{pos, len, val, run})) == True{} : Bool}

def SG.mv_ok(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, run, hH, hEs, hok, hinr):
  EM_.EM.and2(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, run, pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl)))))),
    P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok),
    EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, run, pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, off), U32.add(U32.sub(val, slen), cpl))))),
      P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)),
      SG.ek.c(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)), hH, hEs, run,
        P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)), hinr, U32.is_eq(len, 0), {==})))

# Where the buffered matches lie
# ------------------------------

def SG.tri(+a: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      1n+1n+1n+SG.tri(p)

law SG.tri_eq:
  for +a: Nat
  {Nat.add(Nat.double(a), a) == SG.tri(a) : Nat}

def SG.tri_eq(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(Nat.double(p), 1n+p), 1n+Nat.add(Nat.double(p), p), P.Nat.add_succ_r(Nat.double(p), p)) : {1n+1n+_ == 1n+1n+1n+SG.tri(p) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.double(p), p), SG.tri(p), SG.tri_eq(p)) : {1n+1n+1n+_ == 1n+1n+1n+SG.tri(p) : Nat}
      {==}

law SG.tri_ge:
  for +a: Nat
  {Cmp.is_le(Nat.cmp(a, SG.tri(a))) == True{} : Bool}

def SG.tri_ge(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      P.Nat.le_trans(p, SG.tri(p), 1n+1n+SG.tri(p), SG.tri_ge(p), P.Nat.le_trans(SG.tri(p), 1n+SG.tri(p), 1n+1n+SG.tri(p), P.Nat.le_succ_l(SG.tri(p), 1n+SG.tri(p), C.CP.le_refl(1n+SG.tri(p))), P.Nat.le_succ_l(1n+SG.tri(p), 1n+1n+SG.tri(p), C.CP.le_refl(1n+1n+SG.tri(p)))))

# Words of two different matches differ.
law SG.lt3:
  for +r: Nat
  for +x: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, 2n)) == True{} : Bool}
  {Nat.cmp(r, 1n+1n+1n+x) == LT{} : Cmp}

law SG.lt3.a:
  for +r: Nat
  for +x: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, 1n)) == True{} : Bool}
  {Nat.cmp(r, 1n+1n+x) == LT{} : Cmp}

law SG.lt3.b:
  for +r: Nat
  for +x: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, 0n)) == True{} : Bool}
  {Nat.cmp(r, 1n+x) == LT{} : Cmp}

def SG.lt3.b(r, x, hr):
  match r:
    case 0n:
      {==}
    case 1n+r1:
      P.Bool.false_true({Nat.cmp(1n+r1, 1n+x) == LT{} : Cmp}, hr)

def SG.lt3.a(r, x, hr):
  match r:
    case 0n:
      {==}
    case 1n+r1:
      SG.lt3.b(r1, x, hr)

def SG.lt3(r, x, hr):
  match r:
    case 0n:
      {==}
    case 1n+r1:
      SG.lt3.a(r1, x, hr)

law SG.tri_ne:
  for +a: Nat
  for +b: Nat
  for +r: Nat
  for +s: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, 2n)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(s, 2n)) == True{} : Bool}
  for +hne: {Cmp.is_eq(Nat.cmp(a, b)) == False{} : Bool}
  {Cmp.is_eq(Nat.cmp(Nat.add(SG.tri(a), r), Nat.add(SG.tri(b), s))) == False{} : Bool}

def SG.tri_ne(a, b, r, s, hr, hs, hne):
  match a b:
    case 0n 0n:
      P.Bool.false_true({Cmp.is_eq(Nat.cmp(Nat.add(SG.tri(0n), r), Nat.add(SG.tri(0n), s))) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, hne))
    case 0n 1n+q:
      %Equal.sym(Cmp, Nat.cmp(r, 1n+1n+1n+Nat.add(SG.tri(q), s)), LT{}, SG.lt3(r, Nat.add(SG.tri(q), s), hr)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case 1n+p 0n:
      %Equal.sym(Cmp, Nat.cmp(Nat.add(SG.tri(1n+p), r), s), P.Cmp.flip(Nat.cmp(s, Nat.add(SG.tri(1n+p), r))), P.Nat.cmp_swap(s, Nat.add(SG.tri(1n+p), r))) : {Cmp.is_eq(_) == False{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(s, 1n+1n+1n+Nat.add(SG.tri(p), r)), LT{}, SG.lt3(s, Nat.add(SG.tri(p), r), hs)) : {Cmp.is_eq(P.Cmp.flip(_)) == False{} : Bool}
      {==}
    case 1n+p 1n+q:
      SG.tri_ne(p, q, r, s, hr, hs, hne)

law SG.lt_add3:
  for +x: Nat
  {Nat.cmp(x, Nat.add(x, 3n)) == LT{} : Cmp}

def SG.lt_add3(x):
  %P.Nat.add_zero_r(x) : {Nat.cmp(_, Nat.add(x, 3n)) == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(x, 0n), Nat.add(x, 3n)), Nat.cmp(0n, 3n), P.Nat.cmp_add_l(x, 0n, 3n)) : {_ == LT{} : Cmp}
  {==}

law SG.jlt:
  for +j: U32
  for +d: Nat
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {Nat.cmp(V.U.N(j), P.Nat.pow2(d)) == LT{} : Cmp}

def SG.jlt(j, d, hcap):
  P.Nat.lt_le_trans(V.U.N(j), Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d), P.Nat.le_lt_trans(V.U.N(j), SG.tri(V.U.N(j)), Nat.add(SG.tri(V.U.N(j)), 3n), SG.tri_ge(V.U.N(j)), SG.lt_add3(SG.tri(V.U.N(j)))), hcap)

# Where the j-th match starts, as a number.
law SG.atN:
  for +j: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {V.U.N(N.io.at(j)) == SG.tri(V.U.N(j)) : Nat}

law SG.atN.b:
  for +j: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.shl(j)), V.U.N(j)), V.U.N(U32.shln(1, d)))) == True{} : Bool}

def SG.atN.b(j, d, hd, hcap):
  (%Equal.sym(Nat, V.U.N(U32.shl(j)), Nat.double(V.U.N(j)), V.U.N_shl(j, V.U.bit_high(j, d, 31n, SG.jlt(j, d, hcap), P.Nat.lt_succ_le(d, 31n, hd)))) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(j)), V.U.N(U32.shln(1, d)))) == True{} : Bool};
    (%Equal.sym(Nat, V.U.N(U32.shln(1, d)), P.Nat.pow2(d), V.U.N_pow(d, hd)) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(V.U.N(j)), V.U.N(j)), _)) == True{} : Bool};
      (%Equal.sym(Nat, Nat.add(Nat.double(V.U.N(j)), V.U.N(j)), SG.tri(V.U.N(j)), SG.tri_eq(V.U.N(j))) : {Cmp.is_le(Nat.cmp(_, P.Nat.pow2(d))) == True{} : Bool};
        P.Nat.le_trans(SG.tri(V.U.N(j)), Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d), P.Nat.cmp_add_r(SG.tri(V.U.N(j)), 3n), hcap))))

def SG.atN(j, d, hd, hcap):
  %Equal.sym(Nat, V.U.N(U32.add(U32.shl(j), j)), Nat.add(V.U.N(U32.shl(j)), V.U.N(j)), V.U.add_N(U32.shl(j), j, U32.shln(1, d), SG.atN.b(j, d, hd, hcap))) :
    {_ == SG.tri(V.U.N(j)) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(j)), Nat.double(V.U.N(j)), V.U.N_shl(j, V.U.bit_high(j, d, 31n, SG.jlt(j, d, hcap), P.Nat.lt_succ_le(d, 31n, hd)))) :
    {Nat.add(_, V.U.N(j)) == SG.tri(V.U.N(j)) : Nat}
  SG.tri_eq(V.U.N(j))

# The words of the j-th match, as numbers.
law SG.ixN:
  for +j: U32
  for +r: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(V.U.N(r), 2n)) == True{} : Bool}
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {V.U.N(U32.add(N.io.at(j), r)) == Nat.add(SG.tri(V.U.N(j)), V.U.N(r)) : Nat}

law SG.ixN.b:
  for +j: U32
  for +r: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(V.U.N(r), 2n)) == True{} : Bool}
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(N.io.at(j)), V.U.N(r)), V.U.N(U32.shln(1, d)))) == True{} : Bool}

def SG.ixN.b(j, r, d, hd, hr, hcap):
  %Equal.sym(Nat, V.U.N(N.io.at(j)), SG.tri(V.U.N(j)), SG.atN(j, d, hd, hcap)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(r)), V.U.N(U32.shln(1, d)))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.shln(1, d)), P.Nat.pow2(d), V.U.N_pow(d, hd)) :
    {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), _)) == True{} : Bool}
  P.Nat.le_trans(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d), EI_.EI.lea(SG.tri(V.U.N(j)), V.U.N(r), 3n, P.Nat.le_trans(V.U.N(r), 2n, 3n, hr, {==})), hcap)

def SG.ixN(j, r, d, hd, hr, hcap):
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(j), r)), Nat.add(V.U.N(N.io.at(j)), V.U.N(r)), V.U.add_N(N.io.at(j), r, U32.shln(1, d), SG.ixN.b(j, r, d, hd, hr, hcap))) :
    {_ == Nat.add(SG.tri(V.U.N(j)), V.U.N(r)) : Nat}
  %Equal.sym(Nat, V.U.N(N.io.at(j)), SG.tri(V.U.N(j)), SG.atN(j, d, hd, hcap)) :
    {Nat.add(_, V.U.N(r)) == Nat.add(SG.tri(V.U.N(j)), V.U.N(r)) : Nat}
  {==}

# They lie inside the buffer...
law SG.ix_lt:
  for +j: U32
  for +r: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(V.U.N(r), 2n)) == True{} : Bool}
  for +hcap: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {U32.is_lt(U32.add(N.io.at(j), r), U32.shln(1, d)) == True{} : Bool}

def SG.ix_lt(j, r, d, hd, hr, hcap):
  V.U.N_lt(U32.add(N.io.at(j), r), U32.shln(1, d),
    (%Equal.sym(Nat, V.U.N(U32.add(N.io.at(j), r)), Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), SG.ixN(j, r, d, hd, hr, hcap)) : {Nat.cmp(_, V.U.N(U32.shln(1, d))) == LT{} : Cmp};
      (%Equal.sym(Nat, V.U.N(U32.shln(1, d)), P.Nat.pow2(d), V.U.N_pow(d, hd)) : {Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), _) == LT{} : Cmp};
        P.Nat.lt_le_trans(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d), (%Equal.sym(Cmp, Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), Nat.add(SG.tri(V.U.N(j)), 3n)), Nat.cmp(V.U.N(r), 3n), P.Nat.cmp_add_l(SG.tri(V.U.N(j)), V.U.N(r), 3n)) : {_ == LT{} : Cmp}; P.Nat.le_lt_succ(V.U.N(r), 2n, hr)), hcap))))

# ... and differ between matches...
law SG.ix_ne:
  for +j: U32
  for +n: U32
  for +r: U32
  for +s: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(V.U.N(r), 2n)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(V.U.N(s), 2n)) == True{} : Bool}
  for +hcj: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hcn: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(n)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hne: {U32.is_eq(j, n) == False{} : Bool}
  {U32.is_eq(U32.add(N.io.at(j), r), U32.add(N.io.at(n), s)) == False{} : Bool}

def SG.ix_ne(j, n, r, s, d, hd, hr, hs, hcj, hcn, hne):
  %Equal.sym(Cmp, U32.cmp(U32.add(N.io.at(j), r), U32.add(N.io.at(n), s)), Nat.cmp(V.U.N(U32.add(N.io.at(j), r)), V.U.N(U32.add(N.io.at(n), s))), V.U.cmp_nat(U32.add(N.io.at(j), r), U32.add(N.io.at(n), s))) :
    {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(j), r)), Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), SG.ixN(j, r, d, hd, hr, hcj)) :
    {Cmp.is_eq(Nat.cmp(_, V.U.N(U32.add(N.io.at(n), s)))) == False{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(n), s)), Nat.add(SG.tri(V.U.N(n)), V.U.N(s)), SG.ixN(n, s, d, hd, hs, hcn)) :
    {Cmp.is_eq(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), _)) == False{} : Bool}
  SG.tri_ne(V.U.N(j), V.U.N(n), V.U.N(r), V.U.N(s), hr, hs, (%V.U.cmp_nat(j, n) : {Cmp.is_eq(_) == False{} : Bool}; hne))

# ... and within one.
law SG.ix_ne1:
  for +j: U32
  for +r: U32
  for +s: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(V.U.N(r), 2n)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(V.U.N(s), 2n)) == True{} : Bool}
  for +hcj: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hne: {U32.is_eq(r, s) == False{} : Bool}
  {U32.is_eq(U32.add(N.io.at(j), r), U32.add(N.io.at(j), s)) == False{} : Bool}

def SG.ix_ne1(j, r, s, d, hd, hr, hs, hcj, hne):
  %Equal.sym(Cmp, U32.cmp(U32.add(N.io.at(j), r), U32.add(N.io.at(j), s)), Nat.cmp(V.U.N(U32.add(N.io.at(j), r)), V.U.N(U32.add(N.io.at(j), s))), V.U.cmp_nat(U32.add(N.io.at(j), r), U32.add(N.io.at(j), s))) :
    {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(j), r)), Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), SG.ixN(j, r, d, hd, hr, hcj)) :
    {Cmp.is_eq(Nat.cmp(_, V.U.N(U32.add(N.io.at(j), s)))) == False{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(j), s)), Nat.add(SG.tri(V.U.N(j)), V.U.N(s)), SG.ixN(j, s, d, hd, hs, hcj)) :
    {Cmp.is_eq(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), _)) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(SG.tri(V.U.N(j)), V.U.N(r)), Nat.add(SG.tri(V.U.N(j)), V.U.N(s))), Nat.cmp(V.U.N(r), V.U.N(s)), P.Nat.cmp_add_l(SG.tri(V.U.N(j)), V.U.N(r), V.U.N(s))) :
    {Cmp.is_eq(_) == False{} : Bool}
  %V.U.cmp_nat(r, s) : {Cmp.is_eq(_) == False{} : Bool}
  hne

# Writing a match
# ---------------

def SG.put(+t: A.Tr, +n: U32, +pos: U32, +len: U32, +val: U32) -> A.Tr:
  A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)

law SG.put_code:
  for +t: A.Tr
  for +n: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  {N.io.put(A.A.from(t), n, pos, len, val) == A.A.from(SG.put(t, n, pos, len, val)) : Array<U32>}

def SG.put_code(t, n, pos, len, val):
  %Equal.sym(Array<U32>, Array.set(U32, A.A.from(t), N.io.at(n), pos), A.A.from(A.T.set(t, N.io.at(n), pos)), A.A.set_from(t, N.io.at(n), pos)) :
    {Array.set(U32, Array.set(U32, _, U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val) == A.A.from(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, A.A.from(A.T.set(t, N.io.at(n), pos)), U32.add(N.io.at(n), 1), len), A.A.from(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len)), A.A.set_from(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len)) :
    {Array.set(U32, _, U32.add(N.io.at(n), 2), val) == A.A.from(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, A.A.from(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len)), U32.add(N.io.at(n), 2), val), A.A.from(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)), A.A.set_from(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)) :
    {_ == A.A.from(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)) : Array<U32>}
  {==}

law SG.get_same:
  for +t: A.Tr
  for +n: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(n)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {SE_.SE.ent(SG.put(t, n, pos, len, val), n) == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}

def SG.get_same(t, n, pos, len, val, d, hp, hd, hcn):
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(n), 2)), val, A.T.word_set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val)) :
    {N.Ent{A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), N.io.at(n)), U32.and(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(n), 1)), 2147483647), _, N.ent.run(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(n), 1)))} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(n), 1)), A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 1)), A.T.word_other(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), U32.add(N.io.at(n), 1), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)), hd, SG.ix_lt(n, 2, d, hd, {==}, hcn), SG.ix_lt(n, 1, d, hd, {==}, hcn), SG.ix_ne1(n, 2, 1, d, hd, {==}, {==}, hcn, {==}))) :
    {N.Ent{A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), N.io.at(n)), U32.and(_, 2147483647), val, N.ent.run(_)} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 1)), len, A.T.word_set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len)) :
    {N.Ent{A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), N.io.at(n)), U32.and(_, 2147483647), val, N.ent.run(_)} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), N.io.at(n)), A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), N.io.at(n)), A.T.word_other(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), N.io.at(n), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)), hd, SG.ix_lt(n, 2, d, hd, {==}, hcn), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(n, 0, d, hd, {==}, hcn)), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_eq(U32.add(N.io.at(n), 2), _) == False{} : Bool}; SG.ix_ne1(n, 2, 0, d, hd, {==}, {==}, hcn, {==})))) :
    {N.Ent{_, U32.and(len, 2147483647), val, N.ent.run(len)} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), N.io.at(n)), A.T.word(A.T.set(t, N.io.at(n), pos), N.io.at(n)), A.T.word_other(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), N.io.at(n), len, A.T.pf_set(d, t, N.io.at(n), pos, hp), hd, SG.ix_lt(n, 1, d, hd, {==}, hcn), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(n, 0, d, hd, {==}, hcn)), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_eq(U32.add(N.io.at(n), 1), _) == False{} : Bool}; SG.ix_ne1(n, 1, 0, d, hd, {==}, {==}, hcn, {==})))) :
    {N.Ent{_, U32.and(len, 2147483647), val, N.ent.run(len)} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(t, N.io.at(n), pos), N.io.at(n)), pos, A.T.word_set(t, N.io.at(n), pos)) :
    {N.Ent{_, U32.and(len, 2147483647), val, N.ent.run(len)} == N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)} : N.Ent}
  {==}

law SG.get_other:
  for +t: A.Tr
  for +n: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +j: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(n)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hcj: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hne: {U32.is_eq(n, j) == False{} : Bool}
  {SE_.SE.ent(SG.put(t, n, pos, len, val), j) == SE_.SE.ent(t, j) : N.Ent}

def SG.get_other(t, n, pos, len, val, j, d, hp, hd, hcn, hcj, hne):
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), N.io.at(j)), A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), N.io.at(j)), A.T.word_other(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), N.io.at(j), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)), hd, SG.ix_lt(n, 2, d, hd, {==}, hcn), (%V.U.add_zero_r(N.io.at(j)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(j, 0, d, hd, {==}, hcj)), (%V.U.add_zero_r(N.io.at(j)) : {U32.is_eq(U32.add(N.io.at(n), 2), _) == False{} : Bool}; SG.ix_ne(n, j, 2, 0, d, hd, {==}, {==}, hcn, hcj, hne)))) :
    {N.Ent{_, U32.and(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)), 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), N.io.at(j)), A.T.word(A.T.set(t, N.io.at(n), pos), N.io.at(j)), A.T.word_other(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), N.io.at(j), len, A.T.pf_set(d, t, N.io.at(n), pos, hp), hd, SG.ix_lt(n, 1, d, hd, {==}, hcn), (%V.U.add_zero_r(N.io.at(j)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(j, 0, d, hd, {==}, hcj)), (%V.U.add_zero_r(N.io.at(j)) : {U32.is_eq(U32.add(N.io.at(n), 1), _) == False{} : Bool}; SG.ix_ne(n, j, 1, 0, d, hd, {==}, {==}, hcn, hcj, hne)))) :
    {N.Ent{_, U32.and(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)), 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(t, N.io.at(n), pos), N.io.at(j)), A.T.word(t, N.io.at(j)), A.T.word_other(d, t, N.io.at(n), N.io.at(j), pos, hp, hd, (%V.U.add_zero_r(N.io.at(n)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(n, 0, d, hd, {==}, hcn)), (%V.U.add_zero_r(N.io.at(j)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(j, 0, d, hd, {==}, hcj)), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_eq(_, N.io.at(j)) == False{} : Bool}; (%V.U.add_zero_r(N.io.at(j)) : {U32.is_eq(U32.add(N.io.at(n), 0), _) == False{} : Bool}; SG.ix_ne(n, j, 0, 0, d, hd, {==}, {==}, hcn, hcj, hne))))) :
    {N.Ent{_, U32.and(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)), 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 1)), A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(j), 1)), A.T.word_other(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), U32.add(N.io.at(j), 1), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)), hd, SG.ix_lt(n, 2, d, hd, {==}, hcn), SG.ix_lt(j, 1, d, hd, {==}, hcj), SG.ix_ne(n, j, 2, 1, d, hd, {==}, {==}, hcn, hcj, hne))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(_, 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(_)} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(j), 1)), A.T.word(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(j), 1)), A.T.word_other(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), U32.add(N.io.at(j), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp), hd, SG.ix_lt(n, 1, d, hd, {==}, hcn), SG.ix_lt(j, 1, d, hd, {==}, hcj), SG.ix_ne(n, j, 1, 1, d, hd, {==}, {==}, hcn, hcj, hne))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(_, 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(_)} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(j), 1)), A.T.word(t, U32.add(N.io.at(j), 1)), A.T.word_other(d, t, N.io.at(n), U32.add(N.io.at(j), 1), pos, hp, hd, (%V.U.add_zero_r(N.io.at(n)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(n, 0, d, hd, {==}, hcn)), SG.ix_lt(j, 1, d, hd, {==}, hcj), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_eq(_, U32.add(N.io.at(j), 1)) == False{} : Bool}; SG.ix_ne(n, j, 0, 1, d, hd, {==}, {==}, hcn, hcj, hne)))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(_, 2147483647), A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), N.ent.run(_)} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val), U32.add(N.io.at(j), 2)), A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(j), 2)), A.T.word_other(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), U32.add(N.io.at(j), 2), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)), hd, SG.ix_lt(n, 2, d, hd, {==}, hcn), SG.ix_lt(j, 2, d, hd, {==}, hcj), SG.ix_ne(n, j, 2, 2, d, hd, {==}, {==}, hcn, hcj, hne))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), _, N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(j), 2)), A.T.word(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(j), 2)), A.T.word_other(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), U32.add(N.io.at(j), 2), len, A.T.pf_set(d, t, N.io.at(n), pos, hp), hd, SG.ix_lt(n, 1, d, hd, {==}, hcn), SG.ix_lt(j, 2, d, hd, {==}, hcj), SG.ix_ne(n, j, 1, 2, d, hd, {==}, {==}, hcn, hcj, hne))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), _, N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(j), 2)), A.T.word(t, U32.add(N.io.at(j), 2)), A.T.word_other(d, t, N.io.at(n), U32.add(N.io.at(j), 2), pos, hp, hd, (%V.U.add_zero_r(N.io.at(n)) : {U32.is_lt(_, U32.shln(1, d)) == True{} : Bool}; SG.ix_lt(n, 0, d, hd, {==}, hcn)), SG.ix_lt(j, 2, d, hd, {==}, hcj), (%V.U.add_zero_r(N.io.at(n)) : {U32.is_eq(_, U32.add(N.io.at(j), 2)) == False{} : Bool}; SG.ix_ne(n, j, 0, 2, d, hd, {==}, {==}, hcn, hcj, hne)))) :
    {N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), _, N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} == N.Ent{A.T.word(t, N.io.at(j)), U32.and(A.T.word(t, U32.add(N.io.at(j), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(j), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(j), 1)))} : N.Ent}
  {==}

# Moving the addresses
# --------------------

def SG.mput(+slen: U32, +lo: U32, +cpl: U32, +i: U32, +e: N.Ent, +t: A.Tr) -> A.Tr:
  match e:
    case N.Ent{pos, len, val, run}:
      SG.put(t, i, pos, N.u32.pick(run, U32.or(len, 2147483648), len), N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, lo), U32.add(U32.sub(val, slen), cpl))))

def SG.map(k: Nat, +i: U32, +slen: U32, +lo: U32, +cpl: U32, +t: A.Tr) -> A.Tr:
  match k:
    case 0n:
      t
    case 1n+p:
      SG.map(p, U32.add(i, 1), slen, lo, cpl, SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t))

law SG.map_code:
  for +k: Nat
  for +i: U32
  for +slen: U32
  for +lo: U32
  for +cpl: U32
  for +t: A.Tr
  {N.seg.map(k, i, slen, lo, cpl, A.A.from(t)) == A.A.from(SG.map(k, i, slen, lo, cpl, t)) : Array<U32>}

def SG.map_code(k, i, slen, lo, cpl, t):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & N.Ent, N.io.get(A.A.from(t), i), (A.A.from(t), SE_.SE.ent(t, i)), SE_.SE.get(t, i)) :
        {N.seg.map(p, U32.add(i, 1), slen, lo, cpl, N.seg.map.k(slen, lo, cpl, i, _)) == A.A.from(SG.map(p, U32.add(i, 1), slen, lo, cpl, SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t))) : Array<U32>}
      %Equal.sym(Array<U32>, N.io.put(A.A.from(t), i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl)))), A.A.from(SG.put(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))))), SG.put_code(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))))) :
        {N.seg.map(p, U32.add(i, 1), slen, lo, cpl, _) == A.A.from(SG.map(p, U32.add(i, 1), slen, lo, cpl, SG.put(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl)))))) : Array<U32>}
      SG.map_code(p, U32.add(i, 1), slen, lo, cpl, SG.put(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl)))))

law SG.rl.c:
  for +w: U32
  for +b: Bool
  {U32.and(N.u32.pick(b, U32.or(U32.and(w, 2147483647), 2147483648), U32.and(w, 2147483647)), 2147483647) == U32.and(w, 2147483647) : U32}

def SG.rl.c(w, b):
  match b:
    case True{}:
      Z.BB.runl1(w)
    case False{}:
      Z.BB.runl0(w)

law SG.rf.c:
  for +w: U32
  for +b: Bool
  for +eb: {N.ent.run(w) == b : Bool}
  {N.ent.run(N.u32.pick(b, U32.or(U32.and(w, 2147483647), 2147483648), U32.and(w, 2147483647))) == b : Bool}

def SG.rf.c(w, b, eb):
  match b:
    case True{}:
      %Equal.sym(U32, U32.and(U32.or(U32.and(w, 2147483647), 2147483648), 2147483648), 2147483648, Z.BB.runf1(w)) :
        {U32.is_ne(_, 0) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(U32, U32.and(U32.and(w, 2147483647), 2147483648), 0, Z.BB.runf0(w)) :
        {U32.is_ne(_, 0) == False{} : Bool}
      {==}

law SG.ent_def:
  for +t: A.Tr
  for +i: U32
  {SE_.SE.ent(t, i) == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}

def SG.ent_def(t, i):
  {==}

# A moved match reads back moved.
law SG.mput_same:
  for +slen: U32
  for +lo: U32
  for +cpl: U32
  for +i: U32
  for +t: A.Tr
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hci: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(i)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  {SE_.SE.ent(SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t), i) == SG.mv(slen, lo, cpl, SE_.SE.ent(t, i)) : N.Ent}

def SG.mput_same(slen, lo, cpl, i, t, d, hp, hd, hci):
  %Equal.sym(N.Ent, SE_.SE.ent(t, i), N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))}, SG.ent_def(t, i)) :
    {SE_.SE.ent(SG.mput(slen, lo, cpl, i, _, t), i) == SG.mv(slen, lo, cpl, _) : N.Ent}
  %Equal.sym(N.Ent, SE_.SE.ent(SG.put(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl)))), i), N.Ent{A.T.word(t, N.io.at(i)), U32.and(N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), 2147483647), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), N.ent.run(N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)))}, SG.get_same(t, i, A.T.word(t, N.io.at(i)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), d, hp, hd, hci)) :
    {_ == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  %Equal.sym(U32, U32.and(N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), 2147483647), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), SG.rl.c(A.T.word(t, U32.add(N.io.at(i), 1)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))))) :
    {N.Ent{A.T.word(t, N.io.at(i)), _, N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), N.ent.run(N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)))} == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  %Equal.sym(Bool, N.ent.run(N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), U32.or(U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), 2147483648), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647))), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), SG.rf.c(A.T.word(t, U32.add(N.io.at(i), 1)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), {==})) :
    {N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), _} == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), N.u32.pick(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1))), A.T.word(t, U32.add(N.io.at(i), 2)), N.u32.pick(U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen), U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), lo), U32.add(U32.sub(A.T.word(t, U32.add(N.io.at(i), 2)), slen), cpl))), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  {==}

law SG.pf_put:
  for +t: A.Tr
  for +n: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {A.T.pf(d, SG.put(t, n, pos, len, val)) == True{} : Bool}

def SG.pf_put(t, n, pos, len, val, d, hp):
  A.T.pf_set(d, A.T.set(A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len), U32.add(N.io.at(n), 2), val, A.T.pf_set(d, A.T.set(t, N.io.at(n), pos), U32.add(N.io.at(n), 1), len, A.T.pf_set(d, t, N.io.at(n), pos, hp)))

law SG.pf_mput:
  for +slen: U32
  for +lo: U32
  for +cpl: U32
  for +i: U32
  for +e: N.Ent
  for +t: A.Tr
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {A.T.pf(d, SG.mput(slen, lo, cpl, i, e, t)) == True{} : Bool}

def SG.pf_mput(slen, lo, cpl, i, e, t, d, hp):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.pf_put(t, i, pos, N.u32.pick(run, U32.or(len, 2147483648), len), N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, lo), U32.add(U32.sub(val, slen), cpl))), d, hp)

law SG.mput_other:
  for +slen: U32
  for +lo: U32
  for +cpl: U32
  for +i: U32
  for +e: N.Ent
  for +t: A.Tr
  for +j: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hci: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(i)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hcj: {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hne: {U32.is_eq(i, j) == False{} : Bool}
  {SE_.SE.ent(SG.mput(slen, lo, cpl, i, e, t), j) == SE_.SE.ent(t, j) : N.Ent}

def SG.mput_other(slen, lo, cpl, i, e, t, j, d, hp, hd, hci, hcj, hne):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.get_other(t, i, pos, N.u32.pick(run, U32.or(len, 2147483648), len), N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), U32.sub(val, lo), U32.add(U32.sub(val, slen), cpl))), j, d, hp, hd, hci, hcj, hne)

law SG.tri_mono:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(SG.tri(a), SG.tri(b))) == True{} : Bool}

def SG.tri_mono(a, b, h):
  match a b:
    case 0n b:
      SE_.SE.le0(SG.tri(b))
    case 1n+p 0n:
      P.Bool.false_true({Cmp.is_le(Nat.cmp(SG.tri(1n+p), SG.tri(0n))) == True{} : Bool}, h)
    case 1n+p 1n+q:
      SG.tri_mono(p, q, h)

# The capacity of the buffer for nio matches covers each of them.
law SG.cap_of:
  for +j: U32
  for +nio: U32
  for +d: Nat
  for +hj: {Nat.cmp(V.U.N(j), V.U.N(nio)) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(SG.tri(V.U.N(j)), 3n), P.Nat.pow2(d))) == True{} : Bool}

def SG.cap_of(j, nio, d, hj, hcn):
  %P.Nat.add_comm(3n, SG.tri(V.U.N(j))) : {Cmp.is_le(Nat.cmp(_, P.Nat.pow2(d))) == True{} : Bool}
  P.Nat.le_trans(SG.tri(1n+V.U.N(j)), SG.tri(V.U.N(nio)), P.Nat.pow2(d), SG.tri_mono(1n+V.U.N(j), V.U.N(nio), P.Nat.lt_le_succ(V.U.N(j), V.U.N(nio), hj)), hcn)

# The k matches from i, as the scan buffers them.
def SG.oks0(k: Nat, +ts: A.Tr, +tt: A.Tr, +slen: U32, +w0: U32, +w1: U32, +t: A.Tr, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)))

def SG.inrs(k: Nat, +slen: U32, +off: U32, +cpl: U32, +t: A.Tr, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(SG.inr(slen, off, cpl, SE_.SE.ent(t, i)), SG.inrs(p, slen, off, cpl, t, U32.add(i, 1)))

law SG.lt_succ:
  for +i: U32
  for +nio: U32
  for +p: Nat
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  {V.U.N(U32.add(i, 1)) == 1n+V.U.N(i) : Nat}

def SG.lt_succ(i, nio, p, hr):
  V.U.succ_N(i, nio, P.Nat.lt_le_trans(V.U.N(i), Nat.add(V.U.N(i), 1n+p), V.U.N(nio), (%Equal.sym(Nat, Nat.add(V.U.N(i), 1n+p), 1n+Nat.add(V.U.N(i), p), P.Nat.add_succ_r(V.U.N(i), p)) : {Nat.cmp(V.U.N(i), _) == LT{} : Cmp}; P.Nat.le_lt_succ(V.U.N(i), Nat.add(V.U.N(i), p), P.Nat.cmp_add_r(V.U.N(i), p))), hr))

law SG.i_lt:
  for +i: U32
  for +nio: U32
  for +p: Nat
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  {Nat.cmp(V.U.N(i), V.U.N(nio)) == LT{} : Cmp}

def SG.i_lt(i, nio, p, hr):
  P.Nat.lt_le_trans(V.U.N(i), Nat.add(V.U.N(i), 1n+p), V.U.N(nio), (%Equal.sym(Nat, Nat.add(V.U.N(i), 1n+p), 1n+Nat.add(V.U.N(i), p), P.Nat.add_succ_r(V.U.N(i), p)) : {Nat.cmp(V.U.N(i), _) == LT{} : Cmp}; P.Nat.le_lt_succ(V.U.N(i), Nat.add(V.U.N(i), p), P.Nat.cmp_add_r(V.U.N(i), p))), hr)

law SG.r_next:
  for +i: U32
  for +nio: U32
  for +p: Nat
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, 1)), p), V.U.N(nio))) == True{} : Bool}

def SG.r_next(i, nio, p, hr):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), SG.lt_succ(i, nio, p, hr)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, p), V.U.N(nio))) == True{} : Bool}
  %P.Nat.add_succ_r(V.U.N(i), p) : {Cmp.is_le(Nat.cmp(_, V.U.N(nio))) == True{} : Bool}
  hr

law SG.ne_lt:
  for +a: U32
  for +b: U32
  for +h: {Nat.cmp(V.U.N(a), V.U.N(b)) == LT{} : Cmp}
  {U32.is_eq(a, b) == False{} : Bool}

def SG.ne_lt(a, b, h):
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(V.U.N(a), V.U.N(b)), V.U.cmp_nat(a, b)) :
    {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(a), V.U.N(b)), LT{}, h) :
    {Cmp.is_eq(_) == False{} : Bool}
  {==}

law SG.lt_next:
  for +j: U32
  for +i: U32
  for +nio: U32
  for +p: Nat
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(V.U.N(j), V.U.N(i))) == True{} : Bool}
  {Nat.cmp(V.U.N(j), V.U.N(U32.add(i, 1))) == LT{} : Cmp}

def SG.lt_next(j, i, nio, p, hr, h):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), SG.lt_succ(i, nio, p, hr)) :
    {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
  P.Nat.le_lt_succ(V.U.N(j), V.U.N(i), h)

# A match moved before the range leaves the range as it was.
law SG.oks0_mput:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +lo: U32
  for +cpl: U32
  for +n: U32
  for +e: N.Ent
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hn: {Nat.cmp(V.U.N(n), V.U.N(nio)) == LT{} : Cmp}
  for +hlt: {Nat.cmp(V.U.N(n), V.U.N(i)) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(nio))) == True{} : Bool}
  {SG.oks0(k, ts, tt, slen, w0, w1, SG.mput(slen, lo, cpl, n, e, t), i) == SG.oks0(k, ts, tt, slen, w0, w1, t, i) : Bool}

def SG.oks0_mput(k, ts, tt, slen, w0, w1, lo, cpl, n, e, t, i, d, nio, hp, hd, hcn, hn, hlt, hr):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(N.Ent, SE_.SE.ent(SG.mput(slen, lo, cpl, n, e, t), i), SE_.SE.ent(t, i), SG.mput_other(slen, lo, cpl, n, e, t, i, d, hp, hd, SG.cap_of(n, nio, d, hn, hcn), SG.cap_of(i, nio, d, SG.i_lt(i, nio, p, hr), hcn), SG.ne_lt(n, i, hlt))) :
        {Bool.and(SG.ok0(ts, tt, slen, w0, w1, _), SG.oks0(p, ts, tt, slen, w0, w1, SG.mput(slen, lo, cpl, n, e, t), U32.add(i, 1))) == Bool.and(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      %Equal.sym(Bool, SG.oks0(p, ts, tt, slen, w0, w1, SG.mput(slen, lo, cpl, n, e, t), U32.add(i, 1)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), SG.oks0_mput(p, ts, tt, slen, w0, w1, lo, cpl, n, e, t, U32.add(i, 1), d, nio, hp, hd, hcn, hn, P.Nat.lt_trans(V.U.N(n), V.U.N(i), V.U.N(U32.add(i, 1)), hlt, SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i)))), SG.r_next(i, nio, p, hr))) :
        {Bool.and(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), _) == Bool.and(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      {==}

law SG.inrs_mput:
  for +k: Nat
  for +slen: U32
  for +off: U32
  for +cpw: U32
  for +lo: U32
  for +cpl: U32
  for +n: U32
  for +e: N.Ent
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hn: {Nat.cmp(V.U.N(n), V.U.N(nio)) == LT{} : Cmp}
  for +hlt: {Nat.cmp(V.U.N(n), V.U.N(i)) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(nio))) == True{} : Bool}
  {SG.inrs(k, slen, off, cpw, SG.mput(slen, lo, cpl, n, e, t), i) == SG.inrs(k, slen, off, cpw, t, i) : Bool}

def SG.inrs_mput(k, slen, off, cpw, lo, cpl, n, e, t, i, d, nio, hp, hd, hcn, hn, hlt, hr):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(N.Ent, SE_.SE.ent(SG.mput(slen, lo, cpl, n, e, t), i), SE_.SE.ent(t, i), SG.mput_other(slen, lo, cpl, n, e, t, i, d, hp, hd, SG.cap_of(n, nio, d, hn, hcn), SG.cap_of(i, nio, d, SG.i_lt(i, nio, p, hr), hcn), SG.ne_lt(n, i, hlt))) :
        {Bool.and(SG.inr(slen, off, cpw, _), SG.inrs(p, slen, off, cpw, SG.mput(slen, lo, cpl, n, e, t), U32.add(i, 1))) == Bool.and(SG.inr(slen, off, cpw, SE_.SE.ent(t, i)), SG.inrs(p, slen, off, cpw, t, U32.add(i, 1))) : Bool}
      %Equal.sym(Bool, SG.inrs(p, slen, off, cpw, SG.mput(slen, lo, cpl, n, e, t), U32.add(i, 1)), SG.inrs(p, slen, off, cpw, t, U32.add(i, 1)), SG.inrs_mput(p, slen, off, cpw, lo, cpl, n, e, t, U32.add(i, 1), d, nio, hp, hd, hcn, hn, P.Nat.lt_trans(V.U.N(n), V.U.N(i), V.U.N(U32.add(i, 1)), hlt, SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i)))), SG.r_next(i, nio, p, hr))) :
        {Bool.and(SG.inr(slen, off, cpw, SE_.SE.ent(t, i)), _) == Bool.and(SG.inr(slen, off, cpw, SE_.SE.ent(t, i)), SG.inrs(p, slen, off, cpw, t, U32.add(i, 1))) : Bool}
      {==}

# Moving the matches from i on leaves those before i.
law SG.map_below:
  for +k: Nat
  for +slen: U32
  for +lo: U32
  for +cpl: U32
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hj: {Nat.cmp(V.U.N(j), V.U.N(i)) == LT{} : Cmp}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(nio))) == True{} : Bool}
  {SE_.SE.ent(SG.map(k, i, slen, lo, cpl, t), j) == SE_.SE.ent(t, j) : N.Ent}

law SG.ne_gt:
  for +a: U32
  for +b: U32
  for +h: {Nat.cmp(V.U.N(b), V.U.N(a)) == LT{} : Cmp}
  {U32.is_eq(a, b) == False{} : Bool}

def SG.ne_gt(a, b, h):
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(V.U.N(a), V.U.N(b)), V.U.cmp_nat(a, b)) :
    {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(a), V.U.N(b)), P.Cmp.flip(Nat.cmp(V.U.N(b), V.U.N(a))), P.Nat.cmp_swap(V.U.N(b), V.U.N(a))) :
    {Cmp.is_eq(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(b), V.U.N(a)), LT{}, h) :
    {Cmp.is_eq(P.Cmp.flip(_)) == False{} : Bool}
  {==}

def SG.map_below(k, slen, lo, cpl, t, i, j, d, nio, hp, hd, hcn, hj, hr):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(N.Ent, SE_.SE.ent(SG.map(p, U32.add(i, 1), slen, lo, cpl, SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t)), j), SE_.SE.ent(SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t), j), SG.map_below(p, slen, lo, cpl, SG.mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1), j, d, nio, SG.pf_mput(slen, lo, cpl, i, SE_.SE.ent(t, i), t, d, hp), hd, hcn, P.Nat.lt_trans(V.U.N(j), V.U.N(i), V.U.N(U32.add(i, 1)), hj, SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i)))), SG.r_next(i, nio, p, hr))) :
        {_ == SE_.SE.ent(t, j) : N.Ent}
      SG.mput_other(slen, lo, cpl, i, SE_.SE.ent(t, i), t, j, d, hp, hd, SG.cap_of(i, nio, d, SG.i_lt(i, nio, p, hr), hcn), SG.cap_of(j, nio, d, P.Nat.lt_trans(V.U.N(j), V.U.N(i), V.U.N(nio), hj, SG.i_lt(i, nio, p, hr)), hcn), SG.ne_gt(i, j, hj))

law SG.mv_ok_e:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +e: N.Ent
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +hok: {SG.ok0(ts, tt, slen, w0, w1, e) == True{} : Bool}
  for +hinr: {SG.inr(slen, off, cpl, e) == True{} : Bool}
  {SE_.SE.ok(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.mv(slen, off, cpl, e)) == True{} : Bool}

def SG.mv_ok_e(ts, tt, slen, w0, w1, Es, HB, off, cpl, e, hH, hEs, hok, hinr):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.mv_ok(ts, tt, slen, w0, w1, Es, HB, off, cpl, pos, len, val, run, hH, hEs, hok, hinr)

law SG.ho_next:
  for +p: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +off: U32
  for +cpl: U32
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  for +ho: {SG.oks0(1n+p, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  {SG.oks0(p, ts, tt, slen, w0, w1, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1)) == True{} : Bool}

def SG.ho_next(p, ts, tt, slen, w0, w1, off, cpl, t, i, d, nio, hp, hd, hcn, hr, ho):
  %Equal.sym(Bool, SG.oks0(p, ts, tt, slen, w0, w1, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), SG.oks0_mput(p, ts, tt, slen, w0, w1, off, cpl, i, SE_.SE.ent(t, i), t, U32.add(i, 1), d, nio, hp, hd, hcn, SG.i_lt(i, nio, p, hr), SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i))), SG.r_next(i, nio, p, hr))) :
    {_ == True{} : Bool}
  P.Bool.and_r(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho)

law SG.hn_next:
  for +p: Nat
  for +slen: U32
  for +off: U32
  for +cpl: U32
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(nio))) == True{} : Bool}
  for +hn: {SG.inrs(1n+p, slen, off, cpl, t, i) == True{} : Bool}
  {SG.inrs(p, slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1)) == True{} : Bool}

def SG.hn_next(p, slen, off, cpl, t, i, d, nio, hp, hd, hcn, hr, hn):
  %Equal.sym(Bool, SG.inrs(p, slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1)), SG.inrs(p, slen, off, cpl, t, U32.add(i, 1)), SG.inrs_mput(p, slen, off, cpl, off, cpl, i, SE_.SE.ent(t, i), t, U32.add(i, 1), d, nio, hp, hd, hcn, SG.i_lt(i, nio, p, hr), SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i))), SG.r_next(i, nio, p, hr))) :
    {_ == True{} : Bool}
  P.Bool.and_r(SG.inr(slen, off, cpl, SE_.SE.ent(t, i)), SG.inrs(p, slen, off, cpl, t, U32.add(i, 1)), hn)

# The moved matches are fit to write.
law SG.map_oks:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +off: U32
  for +cpl: U32
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +nio: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(nio))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +ho: {SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  for +hn: {SG.inrs(k, slen, off, cpl, t, i) == True{} : Bool}
  {SE_.SE.oks(k, ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.map(k, i, slen, off, cpl, t), i) == True{} : Bool}

def SG.map_oks(k, ts, tt, slen, w0, w1, Es, HB, off, cpl, t, i, d, nio, hp, hd, hcn, hr, hH, hEs, ho, hn):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(N.Ent, SE_.SE.ent(SG.map(p, U32.add(i, 1), slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t)), i), SE_.SE.ent(SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), i), SG.map_below(p, slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1), i, d, nio, SG.pf_mput(slen, off, cpl, i, SE_.SE.ent(t, i), t, d, hp), hd, hcn, SG.lt_next(i, i, nio, p, hr, C.CP.le_refl(V.U.N(i))), SG.r_next(i, nio, p, hr))) :
        {Bool.and(SE_.SE.ok(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, _), SE_.SE.oks(p, ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.map(p, U32.add(i, 1), slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t)), U32.add(i, 1))) == True{} : Bool}
      %Equal.sym(N.Ent, SE_.SE.ent(SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), i), SG.mv(slen, off, cpl, SE_.SE.ent(t, i)), SG.mput_same(slen, off, cpl, i, t, d, hp, hd, SG.cap_of(i, nio, d, SG.i_lt(i, nio, p, hr), hcn))) :
        {Bool.and(SE_.SE.ok(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, _), SE_.SE.oks(p, ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.map(p, U32.add(i, 1), slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t)), U32.add(i, 1))) == True{} : Bool}
      EM_.EM.and2(SE_.SE.ok(ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.mv(slen, off, cpl, SE_.SE.ent(t, i))), SE_.SE.oks(p, ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1, Es, SG.map(p, U32.add(i, 1), slen, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t)), U32.add(i, 1)),
        SG.mv_ok_e(ts, tt, slen, w0, w1, Es, HB, off, cpl, SE_.SE.ent(t, i), hH, hEs, P.Bool.and_l(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho), P.Bool.and_l(SG.inr(slen, off, cpl, SE_.SE.ent(t, i)), SG.inrs(p, slen, off, cpl, t, U32.add(i, 1)), hn)),
        SG.map_oks(p, ts, tt, slen, w0, w1, Es, HB, off, cpl, SG.mput(slen, off, cpl, i, SE_.SE.ent(t, i), t), U32.add(i, 1), d, nio, SG.pf_mput(slen, off, cpl, i, SE_.SE.ent(t, i), t, d, hp), hd, hcn, SG.r_next(i, nio, p, hr), hH, hEs,
          SG.ho_next(p, ts, tt, slen, w0, w1, off, cpl, t, i, d, nio, hp, hd, hcn, hr, ho),
          SG.hn_next(p, slen, off, cpl, t, i, d, nio, hp, hd, hcn, hr, hn)))

# The source range
# ----------------

def SG.lo1(+slen: U32, +lo: U32, +e: N.Ent) -> U32:
  match e:
    case N.Ent{pos, len, val, run}:
      N.u32.pick(Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(val, lo)), val, lo)

def SG.hi1(+slen: U32, +hi: U32, +e: N.Ent) -> U32:
  match e:
    case N.Ent{pos, len, val, run}:
      N.u32.pick(Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(hi, U32.add(val, len))), U32.add(val, len), hi)

def SG.slo(k: Nat, +i: U32, +slen: U32, +t: A.Tr, +lo: U32) -> U32:
  match k:
    case 0n:
      lo
    case 1n+p:
      SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i)))

def SG.shi(k: Nat, +i: U32, +slen: U32, +t: A.Tr, +hi: U32) -> U32:
  match k:
    case 0n:
      hi
    case 1n+p:
      SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i)))

law SG.scan_code:
  for +k: Nat
  for +i: U32
  for +slen: U32
  for +t: A.Tr
  for +lo: U32
  for +hi: U32
  {N.seg.scan(k, i, slen, (A.A.from(t), (lo, hi))) == (A.A.from(t), (SG.slo(k, i, slen, t, lo), SG.shi(k, i, slen, t, hi))) : Array<U32> & (U32 & U32)}

def SG.scan_code(k, i, slen, t, lo, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & N.Ent, N.io.get(A.A.from(t), i), (A.A.from(t), SE_.SE.ent(t, i)), SE_.SE.get(t, i)) :
        {N.seg.scan(p, U32.add(i, 1), slen, N.seg.scan.k(slen, lo, hi, _)) == (A.A.from(t), (SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))))) : Array<U32> & U32 & U32}
      SG.scan_code(p, U32.add(i, 1), slen, t, N.u32.pick(Bool.and(Bool.and(Bool.not(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))), U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen)), U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), lo)), A.T.word(t, U32.add(N.io.at(i), 2)), lo), N.u32.pick(Bool.and(Bool.and(Bool.not(N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))), U32.is_lt(A.T.word(t, U32.add(N.io.at(i), 2)), slen)), U32.is_lt(hi, U32.add(A.T.word(t, U32.add(N.io.at(i), 2)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)))), U32.add(A.T.word(t, U32.add(N.io.at(i), 2)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647)), hi))

# A match's source bytes lie in [lo, hi).
def SG.inlh(+slen: U32, +lo: U32, +hi: U32, +e: N.Ent) -> Bool:
  match e:
    case N.Ent{pos, len, val, run}:
      Bool.or(run, Bool.or(Bool.not(U32.is_lt(val, slen)), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))))))

def SG.inlhs(k: Nat, +slen: U32, +lo: U32, +hi: U32, +t: A.Tr, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(SG.inlh(slen, lo, hi, SE_.SE.ent(t, i)), SG.inlhs(p, slen, lo, hi, t, U32.add(i, 1)))

law SG.ule_refl:
  for +a: U32
  {U32.is_le(a, a) == True{} : Bool}

def SG.ule_refl(a):
  V.U.N_le(a, a, C.CP.le_refl(V.U.N(a)))

law SG.ule_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for +h1: {U32.is_le(a, b) == True{} : Bool}
  for +h2: {U32.is_le(b, c) == True{} : Bool}
  {U32.is_le(a, c) == True{} : Bool}

def SG.ule_trans(a, b, c, h1, h2):
  V.U.N_le(a, c, P.Nat.le_trans(V.U.N(a), V.U.N(b), V.U.N(c), V.U.le_N(a, b, h1), V.U.le_N(b, c, h2)))

law SG.lo1_le.c:
  for +val: U32
  for +lo: U32
  for +x: Bool
  for +b: Bool
  for +eb: {Bool.and(x, U32.is_lt(val, lo)) == b : Bool}
  {U32.is_le(N.u32.pick(b, val, lo), lo) == True{} : Bool}

def SG.lo1_le.c(val, lo, x, b, eb):
  match b:
    case True{}:
      V.U.lt_to_le(val, lo, P.Bool.and_r(x, U32.is_lt(val, lo), eb))
    case False{}:
      SG.ule_refl(lo)

law SG.lo1_le:
  for +slen: U32
  for +lo: U32
  for +e: N.Ent
  {U32.is_le(SG.lo1(slen, lo, e), lo) == True{} : Bool}

def SG.lo1_le(slen, lo, e):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.lo1_le.c(val, lo, Bool.and(Bool.not(run), U32.is_lt(val, slen)), Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(val, lo)), {==})

law SG.hi1_ge.c:
  for +v: U32
  for +hi: U32
  for +x: Bool
  for +b: Bool
  for +eb: {Bool.and(x, U32.is_lt(hi, v)) == b : Bool}
  {U32.is_le(hi, N.u32.pick(b, v, hi)) == True{} : Bool}

def SG.hi1_ge.c(v, hi, x, b, eb):
  match b:
    case True{}:
      V.U.lt_to_le(hi, v, P.Bool.and_r(x, U32.is_lt(hi, v), eb))
    case False{}:
      SG.ule_refl(hi)

law SG.hi1_ge:
  for +slen: U32
  for +hi: U32
  for +e: N.Ent
  {U32.is_le(hi, SG.hi1(slen, hi, e)) == True{} : Bool}

def SG.hi1_ge(slen, hi, e):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.hi1_ge.c(U32.add(val, len), hi, Bool.and(Bool.not(run), U32.is_lt(val, slen)), Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(hi, U32.add(val, len))), {==})

law SG.slo_le:
  for +k: Nat
  for +i: U32
  for +slen: U32
  for +t: A.Tr
  for +lo: U32
  {U32.is_le(SG.slo(k, i, slen, t, lo), lo) == True{} : Bool}

def SG.slo_le(k, i, slen, t, lo):
  match k:
    case 0n:
      SG.ule_refl(lo)
    case 1n+p:
      SG.ule_trans(SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.lo1(slen, lo, SE_.SE.ent(t, i)), lo, SG.slo_le(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.lo1_le(slen, lo, SE_.SE.ent(t, i)))

law SG.shi_ge:
  for +k: Nat
  for +i: U32
  for +slen: U32
  for +t: A.Tr
  for +hi: U32
  {U32.is_le(hi, SG.shi(k, i, slen, t, hi)) == True{} : Bool}

def SG.shi_ge(k, i, slen, t, hi):
  match k:
    case 0n:
      SG.ule_refl(hi)
    case 1n+p:
      SG.ule_trans(hi, SG.hi1(slen, hi, SE_.SE.ent(t, i)), SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))), SG.hi1_ge(slen, hi, SE_.SE.ent(t, i)), SG.shi_ge(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))))

law SG.or3:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +x: Bool
  for +y: Bool
  for +h: {Bool.or(a, Bool.or(b, Bool.or(c, x))) == True{} : Bool}
  for f: {x == True{} : Bool} -> {y == True{} : Bool}
  {Bool.or(a, Bool.or(b, Bool.or(c, y))) == True{} : Bool}

def SG.or3(a, b, c, x, y, h, f):
  match a b c:
    case True{} b c:
      {==}
    case False{} True{} c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      f(h)

law SG.inl4:
  for +lo: U32
  for +hi: U32
  for +lo2: U32
  for +hi2: U32
  for +len: U32
  for +val: U32
  for +hl: {U32.is_le(lo2, lo) == True{} : Bool}
  for +hh: {U32.is_le(hi, hi2) == True{} : Bool}
  for +hx: {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))) == True{} : Bool}
  {Bool.and(U32.is_le(lo2, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi2)))) == True{} : Bool}

def SG.inl4(lo, hi, lo2, hi2, len, val, hl, hh, hx):
  EM_.EM.and2(U32.is_le(lo2, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi2))),
    SG.ule_trans(lo2, lo, val, hl, P.Bool.and_l(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi))), hx)),
    P.Nat.le_trans(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi), V.U.N(hi2), P.Bool.and_r(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi))), hx), V.U.le_N(hi, hi2, hh)))

law SG.inlh_mono:
  for +slen: U32
  for +lo: U32
  for +hi: U32
  for +lo2: U32
  for +hi2: U32
  for +e: N.Ent
  for +h: {SG.inlh(slen, lo, hi, e) == True{} : Bool}
  for +hl: {U32.is_le(lo2, lo) == True{} : Bool}
  for +hh: {U32.is_le(hi, hi2) == True{} : Bool}
  {SG.inlh(slen, lo2, hi2, e) == True{} : Bool}

def SG.inlh_mono(slen, lo, hi, lo2, hi2, e, h, hl, hh):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.or3(run, Bool.not(U32.is_lt(val, slen)), U32.is_eq(len, 0), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))), Bool.and(U32.is_le(lo2, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi2)))), h, hx => SG.inl4(lo, hi, lo2, hi2, len, val, hl, hh, hx))

law SG.lo_v.c:
  for +val: U32
  for +lo: U32
  for +b: Bool
  for +eb: {U32.is_lt(val, lo) == b : Bool}
  {U32.is_le(N.u32.pick(b, val, lo), val) == True{} : Bool}

def SG.lo_v.c(val, lo, b, eb):
  match b:
    case True{}:
      SG.ule_refl(val)
    case False{}:
      V.U.not_lt(val, lo, eb)

law SG.hi_v.c:
  for +val: U32
  for +len: U32
  for +hi: U32
  for +slen: U32
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}
  for +b: Bool
  for +eb: {U32.is_lt(hi, U32.add(val, len)) == b : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(N.u32.pick(b, U32.add(val, len), hi)))) == True{} : Bool}

def SG.hi_v.c(val, len, hi, slen, hs, b, eb):
  match b:
    case True{}:
      %Equal.sym(Nat, V.U.N(U32.add(val, len)), Nat.add(V.U.N(val), V.U.N(len)), V.U.add_N(val, len, slen, hs)) :
        {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), _)) == True{} : Bool}
      C.CP.le_refl(Nat.add(V.U.N(val), V.U.N(len)))
    case False{}:
      %V.U.add_N(val, len, slen, hs) : {Cmp.is_le(Nat.cmp(_, V.U.N(hi))) == True{} : Bool}
      V.U.le_N(U32.add(val, len), hi, V.U.not_lt(hi, U32.add(val, len), eb))

law SG.inlh1.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +lo: U32
  for +hi: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)) == True{} : Bool}
  for +z1: Bool
  for +z2: Bool
  for +e1: {U32.is_lt(val, slen) == z1 : Bool}
  for +e2: {U32.is_eq(len, 0) == z2 : Bool}
  {Bool.or(run, Bool.or(Bool.not(z1), Bool.or(z2, Bool.and(U32.is_le(N.u32.pick(Bool.and(Bool.and(Bool.not(run), z1), U32.is_lt(val, lo)), val, lo), val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(N.u32.pick(Bool.and(Bool.and(Bool.not(run), z1), U32.is_lt(hi, U32.add(val, len))), U32.add(val, len), hi)))))))) == True{} : Bool}

def SG.inlh1.c(ts, tt, slen, w0, w1, lo, hi, pos, len, val, run, hor, z1, z2, e1, e2):
  match run z1 z2:
    case True{} z1 z2:
      {==}
    case False{} False{} z2:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      EM_.EM.and2(U32.is_le(N.u32.pick(U32.is_lt(val, lo), val, lo), val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(N.u32.pick(U32.is_lt(hi, U32.add(val, len)), U32.add(val, len), hi)))),
        SG.lo_v.c(val, lo, U32.is_lt(val, lo), {==}),
        SG.hi_v.c(val, len, hi, slen, P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), (%e1 : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; (%e2 : {Bool.or(_, SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}; hor))), U32.is_lt(hi, U32.add(val, len)), {==}))

# Scanning a match puts its source bytes in the range.
law SG.inlh1:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +lo: U32
  for +hi: U32
  for +e: N.Ent
  for +hok: {SG.ok0(ts, tt, slen, w0, w1, e) == True{} : Bool}
  {SG.inlh(slen, SG.lo1(slen, lo, e), SG.hi1(slen, hi, e), e) == True{} : Bool}

def SG.inlh1(ts, tt, slen, w0, w1, lo, hi, e, hok):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.inlh1.c(ts, tt, slen, w0, w1, lo, hi, pos, len, val, run, P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)), U32.is_lt(val, slen), U32.is_eq(len, 0), {==}, {==})

# After the scan, every match's source bytes lie in the range.
law SG.scan_inl:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +i: U32
  for +lo: U32
  for +hi: U32
  for +ho: {SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  {SG.inlhs(k, slen, SG.slo(k, i, slen, t, lo), SG.shi(k, i, slen, t, hi), t, i) == True{} : Bool}

def SG.scan_inl(k, ts, tt, slen, w0, w1, t, i, lo, hi, ho):
  match k:
    case 0n:
      {==}
    case 1n+p:
      EM_.EM.and2(SG.inlh(slen, SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))), SE_.SE.ent(t, i)), SG.inlhs(p, slen, SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))), t, U32.add(i, 1)),
        SG.inlh_mono(slen, SG.lo1(slen, lo, SE_.SE.ent(t, i)), SG.hi1(slen, hi, SE_.SE.ent(t, i)), SG.slo(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.shi(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i))), SE_.SE.ent(t, i), SG.inlh1(ts, tt, slen, w0, w1, lo, hi, SE_.SE.ent(t, i), P.Bool.and_l(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho)), SG.slo_le(p, U32.add(i, 1), slen, t, SG.lo1(slen, lo, SE_.SE.ent(t, i))), SG.shi_ge(p, U32.add(i, 1), slen, t, SG.hi1(slen, hi, SE_.SE.ent(t, i)))),
        SG.scan_inl(p, ts, tt, slen, w0, w1, t, U32.add(i, 1), SG.lo1(slen, lo, SE_.SE.ent(t, i)), SG.hi1(slen, hi, SE_.SE.ent(t, i)), P.Bool.and_r(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho)))

law SG.or3z:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +x: Bool
  for +y: Bool
  for +h: {Bool.or(a, Bool.or(b, Bool.or(c, x))) == True{} : Bool}
  for f: {x == True{} : Bool} -> {c == True{} : Bool}
  {Bool.or(a, Bool.or(b, Bool.or(c, y))) == True{} : Bool}

def SG.or3z(a, b, c, x, y, h, f):
  match a b c:
    case True{} b c:
      {==}
    case False{} True{} c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      P.Bool.false_true({Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, y))) == True{} : Bool}, f(h))

law SG.len0:
  for +lo: U32
  for +hi: U32
  for +len: U32
  for +val: U32
  for +hnl: {U32.is_lt(lo, hi) == False{} : Bool}
  for +hx: {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))) == True{} : Bool}
  {U32.is_eq(len, 0) == True{} : Bool}

def SG.len0(lo, hi, len, val, hnl, hx):
  %Equal.sym(Cmp, U32.cmp(len, 0), Nat.cmp(V.U.N(len), 0n), V.U.cmp_nat(len, 0)) :
    {Cmp.is_eq(_) == True{} : Bool}
  SE_.SE.nle0(V.U.N(len), (%P.Nat.cmp_add_l(V.U.N(val), V.U.N(len), 0n) : {Cmp.is_le(_) == True{} : Bool};
    (%Equal.sym(Nat, Nat.add(V.U.N(val), 0n), V.U.N(val), P.Nat.add_zero_r(V.U.N(val))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), _)) == True{} : Bool};
      P.Nat.le_trans(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi), V.U.N(val), P.Bool.and_r(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi))), hx),
        P.Nat.le_trans(V.U.N(hi), V.U.N(lo), V.U.N(val), V.U.le_N(hi, lo, V.U.not_lt(lo, hi, hnl)), V.U.le_N(lo, val, P.Bool.and_l(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi))), hx)))))))

law SG.inr4:
  for +lo: U32
  for +hi: U32
  for +len: U32
  for +val: U32
  for +hl: {U32.is_lt(lo, hi) == True{} : Bool}
  for +hx: {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))) == True{} : Bool}
  {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(lo), V.U.N(U32.sub(hi, lo)))))) == True{} : Bool}

def SG.inr4(lo, hi, len, val, hl, hx):
  %Equal.sym(Nat, Nat.add(V.U.N(lo), V.U.N(U32.sub(hi, lo))), Nat.add(V.U.N(U32.sub(hi, lo)), V.U.N(lo)), P.Nat.add_comm(V.U.N(lo), V.U.N(U32.sub(hi, lo)))) :
    {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(hi, lo)), V.U.N(lo)), V.U.N(hi), V.U.sub_nat(hi, lo, V.U.lt_to_le(lo, hi, hl))) :
    {Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), _))) == True{} : Bool}
  hx

law SG.inr_of.c:
  for +slen: U32
  for +lo: U32
  for +hi: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +h: {Bool.or(run, Bool.or(Bool.not(U32.is_lt(val, slen)), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi))))))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(lo, hi) == c : Bool}
  {Bool.or(run, Bool.or(Bool.not(U32.is_lt(val, slen)), Bool.or(U32.is_eq(len, 0), Bool.and(U32.is_le(N.u32.pick(c, lo, 0), val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(N.u32.pick(c, lo, 0)), V.U.N(N.u32.pick(c, U32.sub(hi, lo), 0))))))))) == True{} : Bool}

def SG.inr_of.c(slen, lo, hi, pos, len, val, run, h, c, ec):
  match c:
    case True{}:
      SG.or3(run, Bool.not(U32.is_lt(val, slen)), U32.is_eq(len, 0), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(lo), V.U.N(U32.sub(hi, lo)))))), h, hx => SG.inr4(lo, hi, len, val, ec, hx))
    case False{}:
      SG.or3z(run, Bool.not(U32.is_lt(val, slen)), U32.is_eq(len, 0), Bool.and(U32.is_le(lo, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(hi)))), Bool.and(U32.is_le(0, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), Nat.add(V.U.N(0), V.U.N(0))))), h, hx => SG.len0(lo, hi, len, val, ec, hx))

law SG.inr_of:
  for +slen: U32
  for +lo: U32
  for +hi: U32
  for +e: N.Ent
  for +h: {SG.inlh(slen, lo, hi, e) == True{} : Bool}
  {SG.inr(slen, N.u32.pick(U32.is_lt(lo, hi), lo, 0), N.u32.pick(U32.is_lt(lo, hi), U32.sub(hi, lo), 0), e) == True{} : Bool}

def SG.inr_of(slen, lo, hi, e, h):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.inr_of.c(slen, lo, hi, pos, len, val, run, h, U32.is_lt(lo, hi), {==})

law SG.inrs_of:
  for +k: Nat
  for +slen: U32
  for +lo: U32
  for +hi: U32
  for +t: A.Tr
  for +i: U32
  for +h: {SG.inlhs(k, slen, lo, hi, t, i) == True{} : Bool}
  {SG.inrs(k, slen, N.u32.pick(U32.is_lt(lo, hi), lo, 0), N.u32.pick(U32.is_lt(lo, hi), U32.sub(hi, lo), 0), t, i) == True{} : Bool}

def SG.inrs_of(k, slen, lo, hi, t, i, h):
  match k:
    case 0n:
      {==}
    case 1n+p:
      EM_.EM.and2(SG.inr(slen, N.u32.pick(U32.is_lt(lo, hi), lo, 0), N.u32.pick(U32.is_lt(lo, hi), U32.sub(hi, lo), 0), SE_.SE.ent(t, i)), SG.inrs(p, slen, N.u32.pick(U32.is_lt(lo, hi), lo, 0), N.u32.pick(U32.is_lt(lo, hi), U32.sub(hi, lo), 0), t, U32.add(i, 1)),
        SG.inr_of(slen, lo, hi, SE_.SE.ent(t, i), P.Bool.and_l(SG.inlh(slen, lo, hi, SE_.SE.ent(t, i)), SG.inlhs(p, slen, lo, hi, t, U32.add(i, 1)), h)),
        SG.inrs_of(p, slen, lo, hi, t, U32.add(i, 1), P.Bool.and_r(SG.inlh(slen, lo, hi, SE_.SE.ent(t, i)), SG.inlhs(p, slen, lo, hi, t, U32.add(i, 1)), h)))

law SG.vl_le.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}
  for +hv: {U32.is_lt(val, slen) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(len, 0) == z : Bool}
  {U32.is_le(U32.add(val, len), slen) == True{} : Bool}

law SG.vl_le.s:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}
  for +hv: {U32.is_lt(val, slen) == True{} : Bool}
  for +ez: {U32.is_eq(len, 0) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))) == True{} : Bool}

def SG.vl_le.s(ts, tt, slen, w0, pos, len, val, hor, hv, ez):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), (%hv : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; (%ez : {Bool.or(_, SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}; hor)))

def SG.vl_le.c(ts, tt, slen, w0, pos, len, val, hor, hv, z, ez):
  match z:
    case True{}:
      %Equal.sym(U32, len, 0, V.U.is_eq(len, 0, ez)) : {U32.is_le(U32.add(val, _), slen) == True{} : Bool}
      %Equal.sym(U32, U32.add(val, 0), val, V.U.add_zero_r(val)) :
        {U32.is_le(_, slen) == True{} : Bool}
      V.U.lt_to_le(val, slen, hv)
    case False{}:
      V.U.N_le(U32.add(val, len), slen, (%Equal.sym(Nat, V.U.N(U32.add(val, len)), Nat.add(V.U.N(val), V.U.N(len)), V.U.add_N(val, len, slen, SG.vl_le.s(ts, tt, slen, w0, pos, len, val, hor, hv, ez))) : {Cmp.is_le(Nat.cmp(_, V.U.N(slen))) == True{} : Bool}; SG.vl_le.s(ts, tt, slen, w0, pos, len, val, hor, hv, ez)))

law SG.hi1_le.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +hi: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)) == True{} : Bool}
  for +hh: {U32.is_le(hi, slen) == True{} : Bool}
  for +b: Bool
  for +eb: {Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(hi, U32.add(val, len))) == b : Bool}
  {U32.is_le(N.u32.pick(b, U32.add(val, len), hi), slen) == True{} : Bool}

def SG.hi1_le.c(ts, tt, slen, w0, hi, pos, len, val, run, hor, hh, b, eb):
  match run b:
    case True{} False{}:
      hh
    case False{} False{}:
      hh
    case True{} True{}:
      P.Bool.false_true({U32.is_le(N.u32.pick(True{}, U32.add(val, len), hi), slen) == True{} : Bool}, eb)
    case False{} True{}:
      SG.vl_le.c(ts, tt, slen, w0, pos, len, val, hor, P.Bool.and_l(U32.is_lt(val, slen), U32.is_lt(hi, U32.add(val, len)), eb), U32.is_eq(len, 0), {==})

law SG.hi1_le:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +hi: U32
  for +e: N.Ent
  for +hok: {SG.ok0(ts, tt, slen, w0, w1, e) == True{} : Bool}
  for +hh: {U32.is_le(hi, slen) == True{} : Bool}
  {U32.is_le(SG.hi1(slen, hi, e), slen) == True{} : Bool}

def SG.hi1_le(ts, tt, slen, w0, w1, hi, e, hok, hh):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.hi1_le.c(ts, tt, slen, w0, hi, pos, len, val, run, P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)), hh, Bool.and(Bool.and(Bool.not(run), U32.is_lt(val, slen)), U32.is_lt(hi, U32.add(val, len))), {==})

# The range ends inside the source.
law SG.shi_le:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +i: U32
  for +hi: U32
  for +ho: {SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  for +hh: {U32.is_le(hi, slen) == True{} : Bool}
  {U32.is_le(SG.shi(k, i, slen, t, hi), slen) == True{} : Bool}

def SG.shi_le(k, ts, tt, slen, w0, w1, t, i, hi, ho, hh):
  match k:
    case 0n:
      hh
    case 1n+p:
      SG.shi_le(p, ts, tt, slen, w0, w1, t, U32.add(i, 1), SG.hi1(slen, hi, SE_.SE.ent(t, i)), P.Bool.and_r(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho), SG.hi1_le(ts, tt, slen, w0, w1, hi, SE_.SE.ent(t, i), P.Bool.and_l(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho), hh))

law SG.sub0:
  for +x: U32
  {U32.sub(x, 0) == x : U32}

def SG.sub0(x):
  %V.U.add_zero_r(U32.sub(x, 0)) : {_ == x : U32}
  V.U.add_sub(x, 0)

law SG.mv_id:
  for +slen: U32
  for +e: N.Ent
  {SG.mv(slen, 0, slen, e) == e : N.Ent}

law SG.mv_id.c:
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +c: Bool
  {N.Ent{pos, len, N.u32.pick(run, val, N.u32.pick(c, val, val)), run} == N.Ent{pos, len, val, run} : N.Ent}

def SG.mv_id.c(pos, len, val, run, c):
  match run c:
    case True{} c:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def SG.mv_id(slen, e):
  match e:
    case N.Ent{pos, len, val, run}:
      %Equal.sym(U32, U32.sub(val, 0), val, SG.sub0(val)) :
        {N.Ent{pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), _, U32.add(U32.sub(val, slen), slen))), run} == N.Ent{pos, len, val, run} : N.Ent}
      %Equal.sym(U32, U32.add(U32.sub(val, slen), slen), val, V.U.add_sub(val, slen)) :
        {N.Ent{pos, len, N.u32.pick(run, val, N.u32.pick(U32.is_lt(val, slen), val, _)), run} == N.Ent{pos, len, val, run} : N.Ent}
      SG.mv_id.c(pos, len, val, run, U32.is_lt(val, slen))

law SG.inlh0.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +run: Bool
  for +hor: {Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)) == True{} : Bool}
  for +z1: Bool
  for +z2: Bool
  for +e1: {U32.is_lt(val, slen) == z1 : Bool}
  for +e2: {U32.is_eq(len, 0) == z2 : Bool}
  {Bool.or(run, Bool.or(Bool.not(z1), Bool.or(z2, Bool.and(U32.is_le(0, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))))))) == True{} : Bool}

def SG.inlh0.c(ts, tt, slen, w0, pos, len, val, run, hor, z1, z2, e1, e2):
  match run z1 z2:
    case True{} z1 z2:
      {==}
    case False{} False{} z2:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      EM_.EM.and2(U32.is_le(0, val), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), V.U.N_le(0, val, SE_.SE.le0(V.U.N(val))),
        P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos), (%e1 : {Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(len)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(len), ts, val), tt, pos)), Bool.and(U32.is_lt(U32.sub(val, slen), U32.sub(pos, w0)), S.S.has(S.S.sl(V.U.N(len), tt, U32.add(w0, U32.sub(val, slen))), tt, pos))) == True{} : Bool}; (%e2 : {Bool.or(_, SG.k0(ts, tt, slen, w0, False{}, pos, len, val)) == True{} : Bool}; hor))))

law SG.inr0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +e: N.Ent
  for +hok: {SG.ok0(ts, tt, slen, w0, w1, e) == True{} : Bool}
  {SG.inr(slen, 0, slen, e) == True{} : Bool}

def SG.inr0(ts, tt, slen, w0, w1, e, hok):
  match e:
    case N.Ent{pos, len, val, run}:
      SG.inlh0.c(ts, tt, slen, w0, pos, len, val, run, P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG.k0(ts, tt, slen, w0, run, pos, len, val))), hok)), U32.is_lt(val, slen), U32.is_eq(len, 0), {==}, {==})

# Without a segment (the whole source), the matches are fit to write as
# they are.
law SG.id_oks:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +t: A.Tr
  for +i: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +ho: {SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  {SE_.SE.oks(k, ts, tt, Q.SP.wseg(slen, 0), slen, w0, w1, Es, t, i) == True{} : Bool}

def SG.id_oks(k, ts, tt, slen, w0, w1, Es, HB, t, i, hH, hEs, ho):
  match k:
    case 0n:
      {==}
    case 1n+p:
      EM_.EM.and2(SE_.SE.ok(ts, tt, Q.SP.wseg(slen, 0), slen, w0, w1, Es, SE_.SE.ent(t, i)), SE_.SE.oks(p, ts, tt, Q.SP.wseg(slen, 0), slen, w0, w1, Es, t, U32.add(i, 1)),
        (%SG.mv_id(slen, SE_.SE.ent(t, i)) : {SE_.SE.ok(ts, tt, Q.SP.wseg(slen, 0), slen, w0, w1, Es, _) == True{} : Bool};
          SG.mv_ok_e(ts, tt, slen, w0, w1, Es, HB, 0, slen, SE_.SE.ent(t, i), hH, hEs, P.Bool.and_l(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho), SG.inr0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i), P.Bool.and_l(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho)))),
        SG.id_oks(p, ts, tt, slen, w0, w1, Es, HB, t, U32.add(i, 1), hH, hEs, P.Bool.and_r(SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG.oks0(p, ts, tt, slen, w0, w1, t, U32.add(i, 1)), ho)))

# The choice
# ----------

def SG.cC(+idle: Bool, +slen: U32, +nio: U32, +t: A.Tr) -> U32:
  match idle:
    case True{}:
      N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0)
    case False{}:
      slen

def SG.cO(+idle: Bool, +slen: U32, +nio: U32, +t: A.Tr) -> U32:
  match idle:
    case True{}:
      N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0)
    case False{}:
      0

def SG.cT(+idle: Bool, +slen: U32, +nio: U32, +t: A.Tr) -> A.Tr:
  match idle:
    case True{}:
      SG.map(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t)
    case False{}:
      t

law SG.choose_code:
  for +idle: Bool
  for +slen: U32
  for +nio: U32
  for +t: A.Tr
  {N.seg.choose(idle, slen, nio, A.A.from(t)) == (A.A.from(SG.cT(idle, slen, nio, t)), (SG.cC(idle, slen, nio, t), SG.cO(idle, slen, nio, t))) : Array<U32> & (U32 & U32)}

def SG.choose_code(idle, slen, nio, t):
  match idle:
    case True{}:
      %Equal.sym(Array<U32> & U32 & U32, N.seg.scan(V.U.N(nio), 0, slen, (A.A.from(t), (slen, 0))), (A.A.from(t), (SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0))), SG.scan_code(V.U.N(nio), 0, slen, t, slen, 0)) :
        {N.seg.fit(slen, nio, _) == (A.A.from(SG.map(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t)), (N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0))) : Array<U32> & U32 & U32}
      %Equal.sym(Array<U32>, N.seg.map(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), A.A.from(t)), A.A.from(SG.map(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t)), SG.map_code(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t)) :
        {(_, (N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0))) == (A.A.from(SG.map(V.U.N(nio), 0, slen, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t)), (N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0))) : Array<U32> & U32 & U32}
      {==}
    case False{}:
      {==}

law SG.cpl_le.c:
  for +lo: U32
  for +hi: U32
  for +slen: U32
  for +hh: {U32.is_le(hi, slen) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(lo, hi) == c : Bool}
  {U32.is_le(N.u32.pick(c, U32.sub(hi, lo), 0), slen) == True{} : Bool}

def SG.cpl_le.c(lo, hi, slen, hh, c, ec):
  match c:
    case True{}:
      V.U.N_le(U32.sub(hi, lo), slen, P.Nat.le_trans(V.U.N(U32.sub(hi, lo)), V.U.N(hi), V.U.N(slen), EM_.EM.sub_le(hi, lo, V.U.lt_to_le(lo, hi, ec)), V.U.le_N(hi, slen, hh)))
    case False{}:
      V.U.N_le(0, slen, SE_.SE.le0(V.U.N(slen)))

# The segment's length is at most the source's.
law SG.cC_le:
  for +idle: Bool
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +nio: U32
  for +t: A.Tr
  for +ho: {SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0) == True{} : Bool}
  {U32.is_le(SG.cC(idle, slen, nio, t), slen) == True{} : Bool}

def SG.cC_le(idle, ts, tt, slen, w0, w1, nio, t, ho):
  match idle:
    case True{}:
      SG.cpl_le.c(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0), slen, SG.shi_le(V.U.N(nio), ts, tt, slen, w0, w1, t, 0, 0, ho, V.U.N_le(0, slen, SE_.SE.le0(V.U.N(slen)))), U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), {==})
    case False{}:
      SG.ule_refl(slen)

# The window's buffered matches, moved to the segment chosen, are fit to
# write.
law SG.choose_oks:
  for +idle: Bool
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +nio: U32
  for +t: A.Tr
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}
  for +ho: {SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0) == True{} : Bool}
  {SE_.SE.oks(V.U.N(nio), ts, tt, Q.SP.wseg(SG.cC(idle, slen, nio, t), SG.cO(idle, slen, nio, t)), SG.cC(idle, slen, nio, t), w0, w1, Es, SG.cT(idle, slen, nio, t), 0) == True{} : Bool}

def SG.choose_oks(idle, ts, tt, slen, w0, w1, Es, HB, nio, t, d, hp, hd, hcn, hH, hEs, ho):
  match idle:
    case True{}:
      SG.map_oks(V.U.N(nio), ts, tt, slen, w0, w1, Es, HB, N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), SG.slo(V.U.N(nio), 0, slen, t, slen), 0), N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), t, 0, d, nio, hp, hd, hcn, C.CP.le_refl(V.U.N(nio)),
        P.Nat.le_trans(Nat.add(V.U.N(N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0)), V.U.N(U32.sub(w1, w0))), Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(HB), SE_.SE.lear(V.U.N(N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0)), V.U.N(slen), V.U.N(U32.sub(w1, w0)), V.U.le_N(N.u32.pick(U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), U32.sub(SG.shi(V.U.N(nio), 0, slen, t, 0), SG.slo(V.U.N(nio), 0, slen, t, slen)), 0), slen, SG.cC_le(True{}, ts, tt, slen, w0, w1, nio, t, ho))), hH),
        hEs, ho, SG.inrs_of(V.U.N(nio), slen, SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0), t, 0, SG.scan_inl(V.U.N(nio), ts, tt, slen, w0, w1, t, 0, slen, 0, ho)))
    case False{}:
      SG.id_oks(V.U.N(nio), ts, tt, slen, w0, w1, Es, HB, t, 0, hH, hEs, ho)

law SG.aw4:
  for +lo: U32
  for +hi: U32
  for +S: U32
  for +hl: {U32.is_lt(lo, hi) == True{} : Bool}
  for +hh: {U32.is_le(hi, S) == True{} : Bool}
  {U32.is_le(lo, U32.sub(S, U32.sub(hi, lo))) == True{} : Bool}

def SG.aw4(lo, hi, S, hl, hh):
  V.U.N_le(lo, U32.sub(S, U32.sub(hi, lo)), (%P.Nat.cmp_add_rr(V.U.N(lo), V.U.N(U32.sub(S, U32.sub(hi, lo))), V.U.N(U32.sub(hi, lo))) : {Cmp.is_le(_) == True{} : Bool};
    (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(S, U32.sub(hi, lo))), V.U.N(U32.sub(hi, lo))), V.U.N(S), V.U.sub_nat(S, U32.sub(hi, lo), SG.ule_trans(U32.sub(hi, lo), hi, S, V.U.N_le(U32.sub(hi, lo), hi, EM_.EM.sub_le(hi, lo, V.U.lt_to_le(lo, hi, hl))), hh))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(lo), V.U.N(U32.sub(hi, lo))), _)) == True{} : Bool};
      (%P.Nat.add_comm(V.U.N(U32.sub(hi, lo)), V.U.N(lo)) : {Cmp.is_le(Nat.cmp(_, V.U.N(S))) == True{} : Bool};
        (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(hi, lo)), V.U.N(lo)), V.U.N(hi), V.U.sub_nat(hi, lo, V.U.lt_to_le(lo, hi, hl))) : {Cmp.is_le(Nat.cmp(_, V.U.N(S))) == True{} : Bool};
          V.U.le_N(hi, S, hh))))))

law SG.aw.c:
  for +lo: U32
  for +hi: U32
  for +S: U32
  for +hh: {U32.is_le(hi, S) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(lo, hi) == c : Bool}
  {Bool.or(Bool.not(U32.is_lt(0, N.u32.pick(c, U32.sub(hi, lo), 0))), Bool.and(U32.is_le(N.u32.pick(c, U32.sub(hi, lo), 0), S), U32.is_le(N.u32.pick(c, lo, 0), U32.sub(S, N.u32.pick(c, U32.sub(hi, lo), 0))))) == True{} : Bool}

def SG.aw.c(lo, hi, S, hh, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(U32.sub(hi, lo), S), True{}, SG.ule_trans(U32.sub(hi, lo), hi, S, V.U.N_le(U32.sub(hi, lo), hi, EM_.EM.sub_le(hi, lo, V.U.lt_to_le(lo, hi, ec))), hh)) :
        {Bool.or(Bool.not(U32.is_lt(0, U32.sub(hi, lo))), Bool.and(_, U32.is_le(lo, U32.sub(S, U32.sub(hi, lo))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_le(lo, U32.sub(S, U32.sub(hi, lo))), True{}, SG.aw4(lo, hi, S, ec, hh)) :
        {Bool.or(Bool.not(U32.is_lt(0, U32.sub(hi, lo))), Bool.and(True{}, _)) == True{} : Bool}
      P.Bool.or_true(Bool.not(U32.is_lt(0, U32.sub(hi, lo))))
    case False{}:
      {==}

# The segment lies in the source (of S bytes, at least the slen matched).
law SG.choose_aw:
  for +idle: Bool
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +nio: U32
  for +t: A.Tr
  for +S: U32
  for +hS: {U32.is_le(slen, S) == True{} : Bool}
  for +ho: {SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0) == True{} : Bool}
  {Bool.or(Bool.not(U32.is_lt(0, SG.cC(idle, slen, nio, t))), Bool.and(U32.is_le(SG.cC(idle, slen, nio, t), S), U32.is_le(SG.cO(idle, slen, nio, t), U32.sub(S, SG.cC(idle, slen, nio, t))))) == True{} : Bool}

def SG.choose_aw(idle, ts, tt, slen, w0, w1, nio, t, S, hS, ho):
  match idle:
    case True{}:
      SG.aw.c(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0), S, SG.ule_trans(SG.shi(V.U.N(nio), 0, slen, t, 0), slen, S, SG.shi_le(V.U.N(nio), ts, tt, slen, w0, w1, t, 0, 0, ho, V.U.N_le(0, slen, SE_.SE.le0(V.U.N(slen)))), hS), U32.is_lt(SG.slo(V.U.N(nio), 0, slen, t, slen), SG.shi(V.U.N(nio), 0, slen, t, 0)), {==})
    case False{}:
      %Equal.sym(Bool, U32.is_le(slen, S), True{}, hS) :
        {Bool.or(Bool.not(U32.is_lt(0, slen)), Bool.and(_, U32.is_le(0, U32.sub(S, slen)))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_le(0, U32.sub(S, slen)), True{}, V.U.N_le(0, U32.sub(S, slen), SE_.SE.le0(V.U.N(U32.sub(S, slen))))) :
        {Bool.or(Bool.not(U32.is_lt(0, slen)), Bool.and(True{}, _)) == True{} : Bool}
      P.Bool.or_true(Bool.not(U32.is_lt(0, slen)))
