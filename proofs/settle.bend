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
import ./emit.bend as EM_
import ./einst.bend as EI_

# Settling the matches
# ====================
#
# io.flush walks the window's buffered matches, trimming overlapping ones
# and writing each with em.inst. Every match it writes is one of those
# buffered, or a part of one, so each keeps the emitter's invariant.

# The n-th buffered match.
def SE.ent(+tio: A.Tr, +n: U32) -> N.Ent:
  N.Ent{A.T.word(tio, N.io.at(n)), U32.and(A.T.word(tio, U32.add(N.io.at(n), 1)), 2147483647), A.T.word(tio, U32.add(N.io.at(n), 2)), N.ent.run(A.T.word(tio, U32.add(N.io.at(n), 1)))}

law SE.get:
  for +tio: A.Tr
  for +n: U32
  {N.io.get(A.A.from(tio), n) == (A.A.from(tio), SE.ent(tio, n)) : Array<U32> & N.Ent}

def SE.get(tio, n):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), N.io.at(n)), (A.A.from(tio), A.T.word(tio, N.io.at(n))), A.A.get_from(tio, N.io.at(n))) :
    {N.ent.k0(N.io.at(n), _) == (A.A.from(tio), SE.ent(tio, n)) : Array<U32> & N.Ent}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), U32.add(N.io.at(n), 1)), (A.A.from(tio), A.T.word(tio, U32.add(N.io.at(n), 1))), A.A.get_from(tio, U32.add(N.io.at(n), 1))) :
    {N.ent.k1(N.io.at(n), A.T.word(tio, N.io.at(n)), _) == (A.A.from(tio), SE.ent(tio, n)) : Array<U32> & N.Ent}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), U32.add(N.io.at(n), 2)), (A.A.from(tio), A.T.word(tio, U32.add(N.io.at(n), 2))), A.A.get_from(tio, U32.add(N.io.at(n), 2))) :
    {N.ent.k2(A.T.word(tio, N.io.at(n)), A.T.word(tio, U32.add(N.io.at(n), 1)), _) == (A.A.from(tio), SE.ent(tio, n)) : Array<U32> & N.Ent}
  {==}

# A buffered match fit to write: inside the window, and, unless it is
# empty, a RUN of its byte or a COPY from an earlier address.
def SE.ok(+ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +Es: U32, +e: N.Ent) -> Bool:
  match e:
    case N.Ent{pos, len, val, run}:
      Bool.and(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))))

law SE.min_le:
  for +a: U32
  for +b: U32
  {U32.is_le(U32.min(a, b), a) == True{} : Bool}

law SE.min_le.c:
  for +a: U32
  for +b: U32
  for +c: Bool
  for +ec: {U32.is_lt(a, b) == c : Bool}
  {U32.is_le(Bool.pick(U32, U32.is_lt(a, b), a, b), a) == True{} : Bool}

def SE.min_le.c(a, b, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(a, b), True{}, ec) :
        {U32.is_le(Bool.pick(U32, _, a, b), a) == True{} : Bool}
      V.U.N_le(a, a, C.CP.le_refl(V.U.N(a)))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(a, b), False{}, ec) :
        {U32.is_le(Bool.pick(U32, _, a, b), a) == True{} : Bool}
      V.U.not_lt(a, b, ec)

def SE.min_le(a, b):
  %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
    {U32.is_le(_, a) == True{} : Bool}
  SE.min_le.c(a, b, U32.is_lt(a, b), {==})

law SE.nlt0:
  for +x: U32
  {U32.is_lt(x, 0) == False{} : Bool}

def SE.nlt0(x):
  %Equal.sym(Cmp, U32.cmp(x, 0), Nat.cmp(V.U.N(x), 0n), V.U.cmp_nat(x, 0)) :
    {Cmp.is_lt(_) == False{} : Bool}
  EM_.EM.nlt0(V.U.N(x))

law SE.instz.c:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for hJ: EI_.EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, len, val, run}) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(len, 0) == z : Bool}
  EI_.EI.J(EM_.EM.inst(tt, run, pos, len, val, cpl, w0, e), EI_.EI.ginst(tt, run, pos, len, val, cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def SE.instz.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, len, val, hJ, hwok, hH, hok, z, ez):
  match z:
    case True{}:
      %Equal.sym(U32, len, 0, V.U.is_eq(len, 0, ez)) : EI_.EI.J(EM_.EM.inst(tt, run, pos, _, val, cpl, w0, e), EI_.EI.ginst(tt, run, pos, _, val, cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
      %Equal.sym(Bool, U32.is_lt(EM_.EM.cut(pos, EM_.EM.uo(e)), 0), False{}, SE.nlt0(EM_.EM.cut(pos, EM_.EM.uo(e)))) : EI_.EI.J(EM_.EM.iif(_, tt, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(0, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), cpl, w0, e), EI_.EI.gif(_, tt, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(0, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
      hJ
    case False{}:
      EI_.EI.inst(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, len, val, hJ, hwok, hH,
        EM_.EM.and2(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)),
          P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))), hok),
          EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val),
            P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))), hok)),
            (%ez : {Bool.or(_, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)) == True{} : Bool}; P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))), hok))))))

# Writing a buffered match fit to write.
law SE.instz:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for hJ: EI_.EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, len, val, run}) == True{} : Bool}
  EI_.EI.J(EM_.EM.inst(tt, run, pos, len, val, cpl, w0, e), EI_.EI.ginst(tt, run, pos, len, val, cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def SE.instz(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, len, val, hJ, hwok, hH, hok):
  SE.instz.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, len, val, hJ, hwok, hH, hok, U32.is_eq(len, 0), {==})

law SE.lear:
  for +x: Nat
  for +y: Nat
  for +a: Nat
  for +h: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(x, a), Nat.add(y, a))) == True{} : Bool}

def SE.lear(x, y, a, h):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(x, a), Nat.add(y, a)), Nat.cmp(x, y), P.Nat.cmp_add_rr(x, y, a)) : {Cmp.is_le(_) == True{} : Bool}
  h

law SE.cc_pre:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +pos: U32
  for +l: U32
  for +k: U32
  for +val: U32
  for +hk: {U32.is_le(k, l) == True{} : Bool}
  for +c0: Bool
  for +e0: {U32.is_lt(val, cpl) == c0 : Bool}
  for +hcp: {Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val) == True{} : Bool}
  for +hcb: {Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es) == True{} : Bool}
  {Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, k, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, k, val, Es)) == True{} : Bool}

def SE.cc_pre(ts, tt, seg, cpl, w0, w1, Es, pos, l, k, val, hk, c0, e0, hcp, hcb):
  match c0:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(val, cpl), True{}, e0) :
        {Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(k, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(k), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(k), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos))))) == True{} : Bool}
      EM_.EM.and2(Bool.and(U32.is_le(k, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(k), ts, U32.add(seg, val)), tt, pos)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), V.U.N(U32.add(seg, val))), V.U.N(Es))),
        EM_.EM.and2(U32.is_le(k, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(k), ts, U32.add(seg, val)), tt, pos),
          V.U.N_le(k, U32.sub(cpl, val), P.Nat.le_trans(V.U.N(k), V.U.N(l), V.U.N(U32.sub(cpl, val)), V.U.le_N(k, l, hk), V.U.le_N(l, U32.sub(cpl, val), P.Bool.and_l(U32.is_le(l, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(l), ts, U32.add(seg, val)), tt, pos), (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(l, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(l), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(l), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp))))),
          EI_.EI.sl_pre(k, l, ts, U32.add(seg, val), tt, pos, hk, P.Bool.and_r(U32.is_le(l, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(l), ts, U32.add(seg, val)), tt, pos), (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(l, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(l), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(l), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp)))),
        P.Nat.le_trans(Nat.add(V.U.N(k), V.U.N(U32.add(seg, val))), Nat.add(V.U.N(l), V.U.N(U32.add(seg, val))), V.U.N(Es), SE.lear(V.U.N(k), V.U.N(l), V.U.N(U32.add(seg, val)), V.U.le_N(k, l, hk)), (%e0 : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(l), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)))) == True{} : Bool}; hcb)))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(val, cpl), False{}, e0) :
        {Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(k, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(k), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(k), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos))))) == True{} : Bool}
      EM_.EM.and2(S.S.has(S.S.sl(V.U.N(k), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos))),
        EI_.EI.sl_pre(k, l, tt, U32.add(w0, U32.sub(val, cpl)), tt, pos, hk, (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(l, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(l), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(l), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp)),
        (%e0 : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(l), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)))) == True{} : Bool}; hcb))

law SE.ek_pre:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +k: U32
  for +val: U32
  for +hk: {U32.is_le(k, l) == True{} : Bool}
  for +h: {EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val) == True{} : Bool}
  {EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val) == True{} : Bool}

def SE.ek_pre(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, k, val, hk, h):
  match run:
    case True{}:
      EI_.EI.rep_pre(k, l, val, tt, pos, hk, h)
    case False{}:
      EM_.EM.and2(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, k, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, k, val, Es)),
        P.Bool.and_l(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es)), h),
        SE.cc_pre(ts, tt, seg, cpl, w0, w1, Es, pos, l, k, val, hk, U32.is_lt(val, cpl), {==},
          P.Bool.and_l(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es), P.Bool.and_r(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es)), h)),
          P.Bool.and_r(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es), P.Bool.and_r(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, l, val, Es)), h))))

law SE.nle0:
  for +n: Nat
  for +h: {Cmp.is_le(Nat.cmp(n, 0n)) == True{} : Bool}
  {Cmp.is_eq(Nat.cmp(n, 0n)) == True{} : Bool}

def SE.nle0(n, h):
  match n:
    case 0n:
      {==}
    case 1n+p:
      P.Bool.false_true({Cmp.is_eq(Nat.cmp(1n+p, 0n)) == True{} : Bool}, h)

# Below an empty length: empty.
law SE.le_z:
  for +k: U32
  for +l: U32
  for +hk: {U32.is_le(k, l) == True{} : Bool}
  for +hl: {U32.is_eq(l, 0) == True{} : Bool}
  {U32.is_eq(k, 0) == True{} : Bool}

def SE.le_z(k, l, hk, hl):
  %Equal.sym(Cmp, U32.cmp(k, 0), Nat.cmp(V.U.N(k), 0n), V.U.cmp_nat(k, 0)) :
    {Cmp.is_eq(_) == True{} : Bool}
  SE.nle0(V.U.N(k), (%V.U.is_eq(l, 0, hl) : {Cmp.is_le(Nat.cmp(V.U.N(k), V.U.N(_))) == True{} : Bool}; V.U.le_N(k, l, hk)))

law SE.or_pre.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +k: U32
  for +val: U32
  for +hk: {U32.is_le(k, l) == True{} : Bool}
  for +h: {Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(l, 0) == z : Bool}
  {Bool.or(U32.is_eq(k, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val)) == True{} : Bool}

def SE.or_pre.c(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, k, val, hk, h, z, ez):
  match z:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 0), True{}, SE.le_z(k, l, hk, ez)) :
        {Bool.or(_, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val), True{}, SE.ek_pre(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, k, val, hk, (%ez : {Bool.or(_, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)) == True{} : Bool}; h))) :
        {Bool.or(U32.is_eq(k, 0), _) == True{} : Bool}
      P.Bool.or_true(U32.is_eq(k, 0))

# The first k bytes of a match fit to write.
law SE.pre:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +k: U32
  for +val: U32
  for +hk: {U32.is_le(k, l) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, k, val, run}) == True{} : Bool}

def SE.pre(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, k, val, hk, h):
  EM_.EM.and2(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(k)), V.U.N(w1))), Bool.or(U32.is_eq(k, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val))),
    P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h),
    EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(k)), V.U.N(w1))), Bool.or(U32.is_eq(k, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, k, val)),
      P.Nat.le_trans(Nat.add(V.U.N(pos), V.U.N(k)), Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1), EI_.EI.lea(V.U.N(pos), V.U.N(k), V.U.N(l), V.U.le_N(k, l, hk)), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h))),
      SE.or_pre.c(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, k, val, hk, P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h)), U32.is_eq(l, 0), {==})))

law SE.s.pc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(w1))) == True{} : Bool}

def SE.s.pc(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h):
  P.Nat.le_trans(Nat.add(V.U.N(pos), V.U.N(c)), Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1), EI_.EI.lea(V.U.N(pos), V.U.N(c), V.U.N(l), V.U.le_N(c, l, hc)), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h)))

law SE.s.lo:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  {U32.is_le(w0, U32.add(pos, c)) == True{} : Bool}

def SE.s.lo(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h):
  V.U.N_le(w0, U32.add(pos, c), (%Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), V.U.add_N(pos, c, w1, SE.s.pc(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h))) : {Cmp.is_le(Nat.cmp(V.U.N(w0), _)) == True{} : Bool};
    P.Nat.le_trans(V.U.N(w0), V.U.N(pos), Nat.add(V.U.N(pos), V.U.N(c)), V.U.le_N(w0, pos, P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h)), P.Nat.cmp_add_r(V.U.N(pos), V.U.N(c)))))

law SE.s.hi:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(l, c))), V.U.N(w1))) == True{} : Bool}

def SE.s.hi(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h):
  %Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), V.U.add_N(pos, c, w1, SE.s.pc(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.sub(l, c))), V.U.N(w1))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(U32.sub(l, c))), Nat.add(V.U.N(pos), Nat.add(V.U.N(c), V.U.N(U32.sub(l, c)))), P.Nat.add_assoc(V.U.N(pos), V.U.N(c), V.U.N(U32.sub(l, c)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}
  %EI_.EI.nsplit(c, l, hc) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), _), V.U.N(w1))) == True{} : Bool}
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h))

law SE.s.or.t:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  for +hlt: {U32.is_lt(c, l) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(l, 0) == z : Bool}
  {Bool.or(U32.is_eq(U32.sub(l, c), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))) == True{} : Bool}

def SE.s.or.t(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h, hlt, z, ez):
  match z:
    case True{}:
      P.Bool.false_true({Bool.or(U32.is_eq(U32.sub(l, c), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))) == True{} : Bool}, (%SE.nlt0(c) : {_ == True{} : Bool}; (%V.U.is_eq(l, 0, ez) : {U32.is_lt(c, _) == True{} : Bool}; hlt)))
    case False{}:
      %Equal.sym(Bool, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c))), True{}, EI_.EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)), EI_.EI.suf(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, val, c, hH, hlt, EM_.EM.and2(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h), EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h)), (%ez : {Bool.or(_, EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)) == True{} : Bool}; P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(l)), V.U.N(w1))), Bool.or(U32.is_eq(l, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, l, val))), h)))))))) :
        {Bool.or(U32.is_eq(U32.sub(l, c), 0), _) == True{} : Bool}
      P.Bool.or_true(U32.is_eq(U32.sub(l, c), 0))

law SE.s.or:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(c, l) == z : Bool}
  {Bool.or(U32.is_eq(U32.sub(l, c), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))) == True{} : Bool}

def SE.s.or(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h, z, ez):
  match z:
    case True{}:
      SE.s.or.t(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h, ez, U32.is_eq(l, 0), {==})
    case False{}:
      %Equal.sym(U32, c, l, EI_.EI.le_anti32(c, l, hc, V.U.not_lt(c, l, ez))) : {Bool.or(U32.is_eq(U32.sub(l, _), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))) == True{} : Bool}
      %Equal.sym(U32, U32.sub(l, l), 0, K.WD.sub_self(l)) :
        {Bool.or(U32.is_eq(_, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))) == True{} : Bool}
      {==}

# The bytes past the first c of a match fit to write.
law SE.suf:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +run: Bool
  for +pos: U32
  for +l: U32
  for +c: U32
  for +val: U32
  for +hc: {U32.is_le(c, l) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, l, val, run}) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)), run}) == True{} : Bool}

def SE.suf(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h):
  EM_.EM.and2(U32.is_le(w0, U32.add(pos, c)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(l, c))), V.U.N(w1))), Bool.or(U32.is_eq(U32.sub(l, c), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c))))), SE.s.lo(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h),
    EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(l, c))), V.U.N(w1))), Bool.or(U32.is_eq(U32.sub(l, c), 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(l, c), N.u32.pick(run, val, U32.add(val, c)))), SE.s.hi(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h), SE.s.or(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, l, c, val, hc, hH, h, U32.is_lt(c, l), {==})))

# The first of two overlapping matches, trimmed: a part of it.
law SE.trim_a:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +p1: U32
  for +l1: U32
  for +v1: U32
  for +u1: Bool
  for +p2: U32
  for +l2: U32
  for +v2: U32
  for +u2: Bool
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{p1, l1, v1, u1}) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.ee.a(N.ent.trim(N.Ent{p1, l1, v1, u1}, N.Ent{p2, l2, v2, u2}))) == True{} : Bool}

def SE.trim_a(ts, tt, seg, cpl, w0, w1, Es, p1, l1, v1, u1, p2, l2, v2, u2, h):
  SE.pre(ts, tt, seg, cpl, w0, w1, Es, u1, p1, l1, U32.min(l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), U32.sub(l1, U32.sub(U32.add(p1, l1), p2)), U32.sub(l1, N.u32.pick(U32.is_gt(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))))), U32.sub(U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))), U32.sub(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))))), v1, SE.min_le(l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), U32.sub(l1, U32.sub(U32.add(p1, l1), p2)), U32.sub(l1, N.u32.pick(U32.is_gt(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))))), U32.sub(U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))), U32.sub(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))))), h)

# The second, trimmed: its bytes past some of its first.
law SE.trim_b:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +p1: U32
  for +l1: U32
  for +v1: U32
  for +u1: Bool
  for +p2: U32
  for +l2: U32
  for +v2: U32
  for +u2: Bool
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{p2, l2, v2, u2}) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.ee.b(N.ent.trim(N.Ent{p1, l1, v1, u1}, N.Ent{p2, l2, v2, u2}))) == True{} : Bool}

def SE.trim_b(ts, tt, seg, cpl, w0, w1, Es, HB, p1, l1, v1, u1, p2, l2, v2, u2, hH, h):
  SE.suf(ts, tt, seg, cpl, w0, w1, Es, HB, u2, p2, l2, U32.min(l2, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), U32.sub(U32.add(p1, l1), p2), N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), 0, U32.sub(U32.add(p1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), U32.sub(l1, U32.sub(U32.add(p1, l1), p2)), U32.sub(l1, N.u32.pick(U32.is_gt(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))))), U32.sub(U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))), U32.sub(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))))), p2)))), v2, SE.min_le(l2, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), U32.sub(U32.add(p1, l1), p2), N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), 0, U32.sub(U32.add(p1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l1), l1, N.u32.pick(U32.is_gt(U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))), l2), U32.sub(l1, U32.sub(U32.add(p1, l1), p2)), U32.sub(l1, N.u32.pick(U32.is_gt(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))))), U32.sub(U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n)))), U32.sub(p2, U32.sub(U32.add(p1, l1), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))), U32.sub(l1, U32.min(18, U32.sub(U32.sub(U32.add(p2, l2), p1), U32.shrn(U32.sub(U32.add(p2, l2), p1), 1n))))))))), p2)))), hH, h)

# The k buffered matches from i are fit to write.
def SE.oks(+k: Nat, +ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +Es: U32, +tio: A.Tr, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, i)), SE.oks(p, ts, tt, seg, cpl, w0, w1, Es, tio, U32.add(i, 1)))

law SE.oks_at:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tio: A.Tr
  for +i: U32
  for +j: U32
  for +B: U32
  for +h1: {Cmp.is_le(Nat.cmp(V.U.N(i), V.U.N(j))) == True{} : Bool}
  for +h2: {Nat.cmp(V.U.N(j), Nat.add(V.U.N(i), k)) == LT{} : Cmp}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(B))) == True{} : Bool}
  for +h: {SE.oks(k, ts, tt, seg, cpl, w0, w1, Es, tio, i) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j)) == True{} : Bool}

law SE.oks_at.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tio: A.Tr
  for +i: U32
  for +p: Nat
  for +j: U32
  for +B: U32
  for +h: {SE.oks(1n+p, ts, tt, seg, cpl, w0, w1, Es, tio, i) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(j, i) == z : Bool}
  for ih: {U32.is_eq(j, i) == False{} : Bool} -> {SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j)) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j)) == True{} : Bool}

def SE.oks_at.c(ts, tt, seg, cpl, w0, w1, Es, tio, i, p, j, B, h, z, ez, ih):
  match z:
    case True{}:
      %Equal.sym(U32, j, i, V.U.is_eq(j, i, ez)) : {SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, _)) == True{} : Bool}
      P.Bool.and_l(SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, i)), SE.oks(p, ts, tt, seg, cpl, w0, w1, Es, tio, U32.add(i, 1)), h)
    case False{}:
      ih(ez)

law SE.n1:
  for +i: U32
  for +B: U32
  for +p: Nat
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(B))) == True{} : Bool}
  {V.U.N(U32.add(i, 1)) == 1n+V.U.N(i) : Nat}

def SE.n1(i, B, p, hb):
  V.U.succ_N(i, B, P.Nat.lt_le_trans(V.U.N(i), Nat.add(V.U.N(i), 1n+p), V.U.N(B), (%P.Nat.add_zero_r(V.U.N(i)) : {Nat.cmp(_, Nat.add(V.U.N(i), 1n+p)) == LT{} : Cmp}; (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(i), 0n), Nat.add(V.U.N(i), 1n+p)), Nat.cmp(0n, 1n+p), P.Nat.cmp_add_l(V.U.N(i), 0n, 1n+p)) : {_ == LT{} : Cmp}; {==})), hb))

law SE.next_le:
  for +i: U32
  for +j: U32
  for +B: U32
  for +p: Nat
  for +h1: {Cmp.is_le(Nat.cmp(V.U.N(i), V.U.N(j))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(B))) == True{} : Bool}
  for +ez: {U32.is_eq(j, i) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(i, 1)), V.U.N(j))) == True{} : Bool}

law SE.lt_of_ne:
  for +a: Nat
  for +b: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_eq(Nat.cmp(b, a)) == False{} : Bool}
  {Nat.cmp(a, b) == LT{} : Cmp}

def SE.lt_of_ne(a, b, h1, h2):
  match a b:
    case 0n 0n:
      P.Bool.false_true({Nat.cmp(0n, 0n) == LT{} : Cmp}, Equal.sym(Bool, True{}, False{}, h2))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      P.Bool.false_true({Nat.cmp(1n+p, 0n) == LT{} : Cmp}, h1)
    case 1n+p 1n+q:
      SE.lt_of_ne(p, q, h1, h2)

def SE.next_le(i, j, B, p, h1, hb, ez):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), SE.n1(i, B, p, hb)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(j))) == True{} : Bool}
  P.Nat.lt_le_succ(V.U.N(i), V.U.N(j), SE.lt_of_ne(V.U.N(i), V.U.N(j), h1, (%V.U.cmp_nat(j, i) : {Cmp.is_eq(_) == False{} : Bool}; ez)))

law SE.next_lt:
  for +i: U32
  for +j: U32
  for +B: U32
  for +p: Nat
  for +h2: {Nat.cmp(V.U.N(j), Nat.add(V.U.N(i), 1n+p)) == LT{} : Cmp}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(B))) == True{} : Bool}
  {Nat.cmp(V.U.N(j), Nat.add(V.U.N(U32.add(i, 1)), p)) == LT{} : Cmp}

def SE.next_lt(i, j, B, p, h2, hb):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), SE.n1(i, B, p, hb)) :
    {Nat.cmp(V.U.N(j), Nat.add(_, p)) == LT{} : Cmp}
  %P.Nat.add_succ_r(V.U.N(i), p) : {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
  h2

law SE.next_b:
  for +i: U32
  for +B: U32
  for +p: Nat
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), 1n+p), V.U.N(B))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(i, 1)), p), V.U.N(B))) == True{} : Bool}

def SE.next_b(i, B, p, hb):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), SE.n1(i, B, p, hb)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, p), V.U.N(B))) == True{} : Bool}
  %P.Nat.add_succ_r(V.U.N(i), p) : {Cmp.is_le(Nat.cmp(_, V.U.N(B))) == True{} : Bool}
  hb

def SE.oks_at(k, ts, tt, seg, cpl, w0, w1, Es, tio, i, j, B, h1, h2, hb, h):
  match k:
    case 0n:
      P.Bool.false_true({SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j)) == True{} : Bool},
        (%EI_.EI.flip_le(Nat.cmp(V.U.N(i), V.U.N(j)), h1) : {_ == True{} : Bool};
          (%P.Nat.cmp_swap(V.U.N(i), V.U.N(j)) : {Cmp.is_lt(_) == True{} : Bool};
            (%P.Nat.add_zero_r(V.U.N(i)) : {Cmp.is_lt(Nat.cmp(V.U.N(j), _)) == True{} : Bool};
              (%Equal.sym(Cmp, Nat.cmp(V.U.N(j), Nat.add(V.U.N(i), 0n)), LT{}, h2) : {Cmp.is_lt(_) == True{} : Bool}; {==})))))
    case 1n+p:
      SE.oks_at.c(ts, tt, seg, cpl, w0, w1, Es, tio, i, p, j, B, h, U32.is_eq(j, i), {==},
        ez => SE.oks_at(p, ts, tt, seg, cpl, w0, w1, Es, tio, U32.add(i, 1), j, B, SE.next_le(i, j, B, p, h1, hb, ez), SE.next_lt(i, j, B, p, h2, hb), SE.next_b(i, B, p, hb), P.Bool.and_r(SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, i)), SE.oks(p, ts, tt, seg, cpl, w0, w1, Es, tio, U32.add(i, 1)), h)))

# Every buffered match below n is fit to write.
law SE.at:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tio: A.Tr
  for +n: U32
  for +j: U32
  for +hj: {U32.is_lt(j, n) == True{} : Bool}
  for +h: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j)) == True{} : Bool}

law SE.le0:
  for +n: Nat
  {Cmp.is_le(Nat.cmp(0n, n)) == True{} : Bool}

def SE.le0(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def SE.at(ts, tt, seg, cpl, w0, w1, Es, tio, n, j, hj, h):
  SE.oks_at(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0, j, n, SE.le0(V.U.N(j)), V.U.lt_N(j, n, hj), C.CP.le_refl(V.U.N(n)), h)

# The code
# --------

law SE.cut_le.c:
  for +pos: U32
  for +u: U32
  for +w1: U32
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(pos), V.U.N(w1))) == True{} : Bool}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(u), V.U.N(w1))) == True{} : Bool}
  for +b: Bool
  for +eb: {U32.is_lt(pos, u) == b : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(pos, N.u32.pick(b, U32.sub(u, pos), 0))), V.U.N(w1))) == True{} : Bool}

def SE.cut_le.c(pos, u, w1, hp, hu, b, eb):
  match b:
    case True{}:
      %Equal.sym(U32, U32.add(pos, U32.sub(u, pos)), u, EM_.EM.addsub(pos, u)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(w1))) == True{} : Bool}
      hu
    case False{}:
      %Equal.sym(U32, U32.add(pos, 0), pos, V.U.add_zero_r(pos)) :
        {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(w1))) == True{} : Bool}
      hp

# A match cut at u still ends by w1.
law SE.cut_le:
  for +pos: U32
  for +u: U32
  for +w1: U32
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(pos), V.U.N(w1))) == True{} : Bool}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(u), V.U.N(w1))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(pos, EM_.EM.cut(pos, u))), V.U.N(w1))) == True{} : Bool}

def SE.cut_le(pos, u, w1, hp, hu):
  SE.cut_le.c(pos, u, w1, hp, hu, U32.is_lt(pos, u), {==})

law SE.inst_code.k:
  for +td: A.Tr
  for +ti: A.Tr
  for +ta: A.Tr
  for +tc: A.Tr
  for +dl: U32
  for +il: U32
  for +al: U32
  for +slot: U32
  for +uoff: U32
  for +pt: U32
  for +ps: U32
  for +pm: U32
  for +pc: U32
  for +ops: List<&2, Q.OP>
  for +ph: Q.HF
  for +dd: Nat
  for +di: Nat
  for +da: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +run: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, len, val, run}) == True{} : Bool}
  {N.em.inst(A.A.from(tt), run, pos, len, val, cpl, w0, EM_.EM.em(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc})) == (A.A.from(tt), EM_.EM.em(EM_.EM.inst(tt, run, pos, len, val, cpl, w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}))) : Array<U32> & N.Em}

law SE.ic.hs:
  for +pos: U32
  for +uoff: U32
  for +w1: U32
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(pos), V.U.N(w1))) == True{} : Bool}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(uoff), V.U.N(w1))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff)), V.U.N(uoff)), V.U.N(w1))) == True{} : Bool}

def SE.ic.hs(pos, uoff, w1, hp, hu):
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff)), V.U.N(uoff)), V.U.N(U32.add(pos, EM_.EM.cut(pos, uoff))), V.U.sub_nat(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff, EI_.EI.cut_ge(pos, uoff))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}
  SE.cut_le(pos, uoff, w1, hp, hu)

def SE.inst_code.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, pos, len, val, hinv, hok):
  EM_.EM.inst_code(tt, run, pos, len, val, cpl, w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, w1,
    P.Nat.le_trans(Nat.add(V.U.N(U32.sub(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff)), V.U.N(dl)), Nat.add(V.U.N(U32.sub(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff)), V.U.N(uoff)), V.U.N(w1),
      EI_.EI.lea(V.U.N(U32.sub(U32.add(pos, EM_.EM.cut(pos, uoff)), uoff)), V.U.N(dl), V.U.N(uoff), P.Nat.le_trans(V.U.N(dl), V.U.N(U32.sub(uoff, w0)), V.U.N(uoff), EM_.EM.R.dl(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.sub_le(uoff, w0, EM_.EM.R.lo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))),
      SE.ic.hs(pos, uoff, w1, P.Nat.le_trans(V.U.N(pos), Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(pos), V.U.N(len)), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))), hok))), V.U.le_N(uoff, w1, EM_.EM.R.hi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))),
    SE.ic.hs(pos, uoff, w1, P.Nat.le_trans(V.U.N(pos), Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(pos), V.U.N(len)), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val)), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), EI_.EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, len, val))), hok))), V.U.le_N(uoff, w1, EM_.EM.R.hi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))))

# em.inst on a match fit to write is its mirror.
law SE.inst_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +run: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.Ent{pos, len, val, run}) == True{} : Bool}
  {N.em.inst(A.A.from(tt), run, pos, len, val, cpl, w0, EM_.EM.em(e)) == (A.A.from(tt), EM_.EM.em(EM_.EM.inst(tt, run, pos, len, val, cpl, w0, e))) : Array<U32> & N.Em}

def SE.inst_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, pos, len, val, hinv, hok):
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      SE.inst_code.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, pos, len, val, hinv, hok)

# The mirror
# ----------

# io.flush's state, with the emitter's ghost.
type FT is Data:
  FT{e: EM_.ET, g: EM_.EG, r1: N.Ent, i: U32, has: Bool}

def SE.fs(+tio: A.Tr, +tt: A.Tr, +st: FT) -> N.FS:
  match st:
    case FT{e, g, r1, i, has}:
      N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(e), r1, i, has}

def SE.emit(+tt: A.Tr, +en: N.Ent, +cpl: U32, +w0: U32, +e: EM_.ET) -> EM_.ET:
  match en:
    case N.Ent{pos, len, val, run}:
      EM_.EM.inst(tt, run, pos, len, val, cpl, w0, e)

def SE.gemit(+tt: A.Tr, +en: N.Ent, +cpl: U32, +w0: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match en:
    case N.Ent{pos, len, val, run}:
      EI_.EI.ginst(tt, run, pos, len, val, cpl, w0, e, g)

def SE.emif(+z: Bool, +tt: A.Tr, +en: N.Ent, +cpl: U32, +w0: U32, +e: EM_.ET) -> EM_.ET:
  match z:
    case False{}:
      e
    case True{}:
      SE.emit(tt, en, cpl, w0, e)

def SE.gemif(+z: Bool, +tt: A.Tr, +en: N.Ent, +cpl: U32, +w0: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match z:
    case False{}:
      g
    case True{}:
      SE.gemit(tt, en, cpl, w0, e, g)

# fs.decide.
def SE.dec(+n: U32, +cpl: U32, +w0: U32, +tio: A.Tr, +tt: A.Tr, +e: EM_.ET, +g: EM_.EG, +r1: N.Ent, +i: U32, +r2: N.Ent, +r3: N.Ent) -> Bool & FT:
  +e1 = N.ent.end(r1)
  +p2 = N.ent.pos(r2)
  +e2 = N.ent.end(r2)
  +p1 = N.ent.pos(r1)
  +apart = (e1 <= p2 : U32)
  +has3 = ((i + 1 : U32) < n : U32)
  +drop2 = Bool.not(apart) && has3 && (N.ent.pos(r3) <= (e1 + 1 : U32) : U32)
  +near = (((e2 - p1 : U32) < 8 : U32) || ((e2 - e1 : U32) <= 2 : U32)
    || ((p2 - p1 : U32) <= 2 : U32))
  +one = Bool.not(apart) && Bool.not(drop2) && near
  +take2 = one && (N.ent.len(r1) < N.ent.len(r2) : U32)
  +keep1 = one && Bool.not(take2)
  +trim = Bool.not(apart) && Bool.not(drop2) && Bool.not(near)
  +tt2 = N.ent.trim(r1, r2)
  +out = Bool.pick(N.Ent, trim, N.ee.a(tt2), r1)
  +emit = apart || keep1 || trim
  +nr1 = Bool.pick(N.Ent, apart || take2, r2,
    Bool.pick(N.Ent, keep1, r3, Bool.pick(N.Ent, trim, N.ee.b(tt2), r1)))
  +ni = (i + N.u32.pick(keep1, 2, 1) : U32)
  +nhas = Bool.not(keep1) || has3
  (nhas, FT{SE.emif(emit, tt, out, cpl, w0, e), SE.gemif(emit, tt, out, cpl, w0, e, g), nr1, ni, nhas})

def SE.sgo(+z: Bool, +n: U32, +cpl: U32, +w0: U32, +tio: A.Tr, +tt: A.Tr, +e: EM_.ET, +g: EM_.EG, +r1: N.Ent, +i: U32) -> Bool & FT:
  match z:
    case True{}:
      SE.dec(n, cpl, w0, tio, tt, e, g, r1, i, SE.ent(tio, i), SE.ent(tio, U32.add(i, 1)))
    case False{}:
      (False{}, FT{SE.emit(tt, r1, cpl, w0, e), SE.gemit(tt, r1, cpl, w0, e, g), r1, i, False{}})

def SE.step(+n: U32, +cpl: U32, +w0: U32, +tio: A.Tr, +tt: A.Tr, +st: FT) -> Bool & FT:
  match st:
    case FT{e, g, r1, i, has}:
      SE.sgo(U32.is_lt(i, n), n, cpl, w0, tio, tt, e, g, r1, i)

def SE.loop(k: Nat, +n: U32, +cpl: U32, +w0: U32, +tio: A.Tr, +tt: A.Tr, s: Bool & FT) -> FT:
  match k s:
    case 0n Tuple{h, st}:
      st
    case 1n+p Tuple{False{}, st}:
      st
    case 1n+p Tuple{True{}, st}:
      SE.loop(p, n, cpl, w0, tio, tt, SE.step(n, cpl, w0, tio, tt, st))

law SE.emit_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +en: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, en) == True{} : Bool}
  {N.fs.emit(A.A.from(tt), en, cpl, w0, EM_.EM.em(e)) == (A.A.from(tt), EM_.EM.em(SE.emit(tt, en, cpl, w0, e))) : Array<U32> & N.Em}

def SE.emit_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, en, hinv, hok):
  match en:
    case N.Ent{pos, len, val, run}:
      SE.inst_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, pos, len, val, hinv, hok)

law SE.emif_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +z: Bool
  for +en: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, en) == True{} : Bool}
  {N.fs.emit.if(z, A.A.from(tt), en, cpl, w0, EM_.EM.em(e)) == (A.A.from(tt), EM_.EM.em(SE.emif(z, tt, en, cpl, w0, e))) : Array<U32> & N.Em}

def SE.emif_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, z, en, hinv, hok):
  match z:
    case False{}:
      {==}
    case True{}:
      SE.emit_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, en, hinv, hok)

law SE.next_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +tio: A.Tr
  for +nr1: N.Ent
  for +ni: U32
  for +nhas: Bool
  for +emit: Bool
  for +en: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, en) == True{} : Bool}
  {N.fs.next(A.A.from(tio), nr1, ni, nhas, N.fs.emit.if(emit, A.A.from(tt), en, cpl, w0, EM_.EM.em(e))) == (nhas, N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(SE.emif(emit, tt, en, cpl, w0, e)), nr1, ni, nhas}) : Bool & N.FS}

def SE.next_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, tio, nr1, ni, nhas, emit, en, hinv, hok):
  %Equal.sym(Array<U32> & N.Em, N.fs.emit.if(emit, A.A.from(tt), en, cpl, w0, EM_.EM.em(e)), (A.A.from(tt), EM_.EM.em(SE.emif(emit, tt, en, cpl, w0, e))), SE.emif_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, emit, en, hinv, hok)) :
    {N.fs.next(A.A.from(tio), nr1, ni, nhas, _) == (nhas, N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(SE.emif(emit, tt, en, cpl, w0, e)), nr1, ni, nhas}) : Bool & N.FS}
  {==}

law SE.out_ok:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tr: Bool
  for +r1: N.Ent
  for +r2: N.Ent
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, Bool.pick(N.Ent, tr, N.ee.a(N.ent.trim(r1, r2)), r1)) == True{} : Bool}

def SE.out_ok(ts, tt, seg, cpl, w0, w1, Es, tr, r1, r2, h):
  match tr r1 r2:
    case True{} N.Ent{p1, l1, v1, u1} N.Ent{p2, l2, v2, u2}:
      SE.trim_a(ts, tt, seg, cpl, w0, w1, Es, p1, l1, v1, u1, p2, l2, v2, u2, h)
    case False{} r1 r2:
      h

def SE.dfs(+tio: A.Tr, +tt: A.Tr, p: Bool & FT) -> Bool & N.FS:
  match p:
    case Tuple{h, st}:
      (h, SE.fs(tio, tt, st))

# fs.decide is its mirror.
law SE.dec_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +n: U32
  for +tio: A.Tr
  for +r1: N.Ent
  for +i: U32
  for +r2: N.Ent
  for +r3: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  {N.fs.decide(n, cpl, w0, A.A.from(tt), EM_.EM.em(e), r1, i, r2, (A.A.from(tio), r3)) == SE.dfs(tio, tt, SE.dec(n, cpl, w0, tio, tt, e, g, r1, i, r2, r3)) : Bool & N.FS}

def SE.dec_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, n, tio, r1, i, r2, r3, hinv, hok):
  SE.next_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, tio, Bool.pick(N.Ent, Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))), r2, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2))))), r3, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.b(N.ent.trim(r1, r2)), r1))), U32.add(i, N.u32.pick(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2))))), 2, 1)), Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), U32.is_lt(U32.add(i, 1), n)), Bool.or(Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))))), Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.a(N.ent.trim(r1, r2)), r1), hinv, SE.out_ok(ts, tt, seg, cpl, w0, w1, Es, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), r1, r2, hok))

# The invariant
# -------------

def SE.has(+st: FT) -> Bool:
  match st:
    case FT{e, g, r1, i, has}:
      has

# Trees, compared.
def SE.teq(+a: A.Tr, +b: A.Tr) -> Bool:
  match a b:
    case A.TL{x} A.TL{y}:
      U32.is_eq(x, y)
    case A.TN{a1, a2} A.TN{b1, b2}:
      Bool.and(SE.teq(a1, b1), SE.teq(a2, b2))
    case A.TL{x} A.TN{b1, b2}:
      False{}
    case A.TN{a1, a2} A.TL{y}:
      False{}

law SE.teq_refl:
  for +a: A.Tr
  {SE.teq(a, a) == True{} : Bool}

def SE.teq_refl(a):
  match a:
    case A.TL{x}:
      V.U.is_eq_refl(x)
    case A.TN{a1, a2}:
      %Equal.sym(Bool, SE.teq(a1, a1), True{}, SE.teq_refl(a1)) :
        {Bool.and(_, SE.teq(a2, a2)) == True{} : Bool}
      %Equal.sym(Bool, SE.teq(a2, a2), True{}, SE.teq_refl(a2)) :
        {Bool.and(True{}, _) == True{} : Bool}
      {==}

law SE.teq_eq:
  for +a: A.Tr
  for +b: A.Tr
  for +h: {SE.teq(a, b) == True{} : Bool}
  {a == b : A.Tr}

def SE.teq_eq(a, b, h):
  match a b:
    case A.TL{x} A.TL{y}:
      %V.U.is_eq(x, y, h) : {A.TL{x} == A.TL{_} : A.Tr}
      {==}
    case A.TN{a1, a2} A.TN{b1, b2}:
      %SE.teq_eq(a1, b1, P.Bool.and_l(SE.teq(a1, b1), SE.teq(a2, b2), h)) : {A.TN{a1, a2} == A.TN{_, b2} : A.Tr}
      %SE.teq_eq(a2, b2, P.Bool.and_r(SE.teq(a1, b1), SE.teq(a2, b2), h)) : {A.TN{a1, a2} == A.TN{a1, _} : A.Tr}
      {==}
    case A.TL{x} A.TN{b1, b2}:
      P.Bool.false_true({A.TL{x} == A.TN{b1, b2} : A.Tr}, h)
    case A.TN{a1, a2} A.TL{y}:
      P.Bool.false_true({A.TN{a1, a2} == A.TL{y} : A.Tr}, h)

# The emitter keeps its invariant, its cache is the decoder's, and the
# match in hand is fit to write.
def SE.Ib(+ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +E: U32, +Es: U32, +BIG: U32, +st: FT) -> Bool:
  match st:
    case FT{e, g, r1, i, has}:
      Bool.and(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1))))

def SE.Ip(+ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +E: U32, +Es: U32, +BIG: U32, s: Bool & FT) -> Type:
  match s:
    case Tuple{h, st}:
      {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, st) == True{} : Bool} & {h == SE.has(st) : Bool}

law SE.mkI:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +r1: N.Ent
  for +i: U32
  for +has: Bool
  for hJ: EI_.EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hok: {Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)) == True{} : Bool}
  {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, FT{e, g, r1, i, has}) == True{} : Bool}

def SE.mkI(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hJ, hok):
  match hJ:
    case Tuple{+hinv, +hc}:
      %Equal.sym(A.Tr, EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))), hc) :
        {Bool.and(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(SE.teq(_, Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)))) == True{} : Bool}
      %Equal.sym(Bool, SE.teq(Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), True{}, SE.teq_refl(Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))) :
        {Bool.and(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(_, Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)))) == True{} : Bool}
      %Equal.sym(Bool, EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), True{}, hinv) :
        {Bool.and(_, Bool.and(True{}, Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)))) == True{} : Bool}
      hok

law SE.emif_J:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +z: Bool
  for +en: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hok: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, en) == True{} : Bool}
  EI_.EI.J(SE.emif(z, tt, en, cpl, w0, e), SE.gemif(z, tt, en, cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def SE.emif_J(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, z, en, hinv, hc, hwok, hH, hok):
  match z en:
    case False{} en:
      (hinv, hc)
    case True{} N.Ent{pos, len, val, run}:
      SE.instz(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, len, val, (hinv, hc), hwok, hH, hok)

law SE.eeb_ok:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +r1: N.Ent
  for +r2: N.Ent
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +h: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r2) == True{} : Bool}
  {SE.ok(ts, tt, seg, cpl, w0, w1, Es, N.ee.b(N.ent.trim(r1, r2))) == True{} : Bool}

def SE.eeb_ok(ts, tt, seg, cpl, w0, w1, Es, HB, r1, r2, hH, h):
  match r1 r2:
    case N.Ent{p1, l1, v1, u1} N.Ent{p2, l2, v2, u2}:
      SE.trim_b(ts, tt, seg, cpl, w0, w1, Es, HB, p1, l1, v1, u1, p2, l2, v2, u2, hH, h)

law SE.nr1_ok:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +ap: Bool
  for +k1: Bool
  for +tr: Bool
  for +h3: Bool
  for +r1: N.Ent
  for +r2: N.Ent
  for +r3: N.Ent
  for +eb: N.Ent
  for +hok1: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  for +hok2: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r2) == True{} : Bool}
  for +hok3: {Bool.or(Bool.not(h3), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r3)) == True{} : Bool}
  for +hokb: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, eb) == True{} : Bool}
  {Bool.or(Bool.not(Bool.or(Bool.not(k1), h3)), SE.ok(ts, tt, seg, cpl, w0, w1, Es, Bool.pick(N.Ent, ap, r2, Bool.pick(N.Ent, k1, r3, Bool.pick(N.Ent, tr, eb, r1))))) == True{} : Bool}

def SE.nr1_ok(ts, tt, seg, cpl, w0, w1, Es, ap, k1, tr, h3, r1, r2, r3, eb, hok1, hok2, hok3, hokb):
  match ap k1 tr h3:
    case True{} k1 tr h3:
      %Equal.sym(Bool, SE.ok(ts, tt, seg, cpl, w0, w1, Es, r2), True{}, hok2) :
        {Bool.or(Bool.not(Bool.or(Bool.not(k1), h3)), _) == True{} : Bool}
      P.Bool.or_true(Bool.not(Bool.or(Bool.not(k1), h3)))
    case False{} True{} tr True{}:
      hok3
    case False{} True{} tr False{}:
      {==}
    case False{} False{} True{} h3:
      %Equal.sym(Bool, SE.ok(ts, tt, seg, cpl, w0, w1, Es, eb), True{}, hokb) :
        {_ == True{} : Bool}
      {==}
    case False{} False{} False{} h3:
      %Equal.sym(Bool, SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1), True{}, hok1) :
        {_ == True{} : Bool}
      {==}

law SE.imp_at.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tio: A.Tr
  for +n: U32
  for +j: U32
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(j, n) == z : Bool}
  {Bool.or(Bool.not(z), SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j))) == True{} : Bool}

def SE.imp_at.c(ts, tt, seg, cpl, w0, w1, Es, tio, n, j, hall, z, ez):
  match z:
    case True{}:
      SE.at(ts, tt, seg, cpl, w0, w1, Es, tio, n, j, ez, hall)
    case False{}:
      {==}

law SE.imp_at:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +tio: A.Tr
  for +n: U32
  for +j: U32
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  {Bool.or(Bool.not(U32.is_lt(j, n)), SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, j))) == True{} : Bool}

def SE.imp_at(ts, tt, seg, cpl, w0, w1, Es, tio, n, j, hall):
  SE.imp_at.c(ts, tt, seg, cpl, w0, w1, Es, tio, n, j, hall, U32.is_lt(j, n), {==})

law SE.dec_inv:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for +r1: N.Ent
  for +i: U32
  for +r2: N.Ent
  for +r3: N.Ent
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  for +hok1: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  for +hok2: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r2) == True{} : Bool}
  for +hok3: {Bool.or(Bool.not(U32.is_lt(U32.add(i, 1), n)), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r3)) == True{} : Bool}
  SE.Ip(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.dec(n, cpl, w0, tio, tt, e, g, r1, i, r2, r3))

def SE.dec_inv(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, r1, i, r2, r3, hinv, hc, hwok, hH, hall, hok1, hok2, hok3):
  (SE.mkI(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.emif(Bool.or(Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))))), tt, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.a(N.ent.trim(r1, r2)), r1), cpl, w0, e), SE.gemif(Bool.or(Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))))), tt, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.a(N.ent.trim(r1, r2)), r1), cpl, w0, e, g), Bool.pick(N.Ent, Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))), r2, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2))))), r3, Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.b(N.ent.trim(r1, r2)), r1))), U32.add(i, N.u32.pick(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2))))), 2, 1)), Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), U32.is_lt(U32.add(i, 1), n)),
    SE.emif_J(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, Bool.or(Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))))), Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))))), Bool.pick(N.Ent, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), N.ee.a(N.ent.trim(r1, r2)), r1), hinv, hc, hwok, hH, SE.out_ok(ts, tt, seg, cpl, w0, w1, Es, Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), r1, r2, hok1)),
    SE.nr1_ok(ts, tt, seg, cpl, w0, w1, Es, Bool.or(U32.is_le(N.ent.end(r1), N.ent.pos(r2)), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2)))), Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), Bool.not(Bool.and(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2))), U32.is_lt(N.ent.len(r1), N.ent.len(r2))))), Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), Bool.not(Bool.and(Bool.and(Bool.not(U32.is_le(N.ent.end(r1), N.ent.pos(r2))), U32.is_lt(U32.add(i, 1), n)), U32.is_le(N.ent.pos(r3), U32.add(N.ent.end(r1), 1))))), Bool.not(Bool.or(Bool.or(U32.is_lt(U32.sub(N.ent.end(r2), N.ent.pos(r1)), 8), U32.is_le(U32.sub(N.ent.end(r2), N.ent.end(r1)), 2)), U32.is_le(U32.sub(N.ent.pos(r2), N.ent.pos(r1)), 2)))), U32.is_lt(U32.add(i, 1), n), r1, r2, r3, N.ee.b(N.ent.trim(r1, r2)), hok1, hok2, hok3, SE.eeb_ok(ts, tt, seg, cpl, w0, w1, Es, HB, r1, r2, hH, hok2))), {==})

law SE.sgo_inv:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for +r1: N.Ent
  for +i: U32
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  for +hok1: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(i, n) == z : Bool}
  SE.Ip(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.sgo(z, n, cpl, w0, tio, tt, e, g, r1, i))

def SE.sgo_inv(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, r1, i, hinv, hc, hwok, hH, hall, hok1, z, ez):
  match z:
    case True{}:
      SE.dec_inv(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, r1, i, SE.ent(tio, i), SE.ent(tio, U32.add(i, 1)), hinv, hc, hwok, hH, hall, hok1, SE.at(ts, tt, seg, cpl, w0, w1, Es, tio, n, i, ez, hall), SE.imp_at(ts, tt, seg, cpl, w0, w1, Es, tio, n, U32.add(i, 1), hall))
    case False{}:
      (SE.mkI(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.emit(tt, r1, cpl, w0, e), SE.gemit(tt, r1, cpl, w0, e, g), r1, i, False{}, SE.emif_J(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, True{}, r1, hinv, hc, hwok, hH, hok1), {==}), {==})

law SE.sgo_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +n: U32
  for +tio: A.Tr
  for +r1: N.Ent
  for +i: U32
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok1: {SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1) == True{} : Bool}
  for +z: Bool
  {N.fs.step.go(z, n, cpl, w0, A.A.from(tio), A.A.from(tt), EM_.EM.em(e), r1, i) == SE.dfs(tio, tt, SE.sgo(z, n, cpl, w0, tio, tt, e, g, r1, i)) : Bool & N.FS}

def SE.sgo_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, n, tio, r1, i, hinv, hok1, z):
  match z:
    case True{}:
      %Equal.sym(Array<U32> & N.Ent, N.io.get(A.A.from(tio), i), (A.A.from(tio), SE.ent(tio, i)), SE.get(tio, i)) :
        {N.fs.r2(n, cpl, w0, A.A.from(tt), EM_.EM.em(e), r1, i, _) == SE.dfs(tio, tt, SE.dec(n, cpl, w0, tio, tt, e, g, r1, i, SE.ent(tio, i), SE.ent(tio, U32.add(i, 1)))) : Bool & N.FS}
      %Equal.sym(Array<U32> & N.Ent, N.io.get(A.A.from(tio), U32.add(i, 1)), (A.A.from(tio), SE.ent(tio, U32.add(i, 1))), SE.get(tio, U32.add(i, 1))) :
        {N.fs.decide(n, cpl, w0, A.A.from(tt), EM_.EM.em(e), r1, i, SE.ent(tio, i), _) == SE.dfs(tio, tt, SE.dec(n, cpl, w0, tio, tt, e, g, r1, i, SE.ent(tio, i), SE.ent(tio, U32.add(i, 1)))) : Bool & N.FS}
      SE.dec_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, n, tio, r1, i, SE.ent(tio, i), SE.ent(tio, U32.add(i, 1)), hinv, hok1)
    case False{}:
      %Equal.sym(Array<U32> & N.Em, N.fs.emit(A.A.from(tt), r1, cpl, w0, EM_.EM.em(e)), (A.A.from(tt), EM_.EM.em(SE.emit(tt, r1, cpl, w0, e))), SE.emit_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, r1, hinv, hok1)) :
        {N.fs.last(A.A.from(tio), r1, i, cpl, w0, _) == (False{}, N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(SE.emit(tt, r1, cpl, w0, e)), r1, i, False{}}) : Bool & N.FS}
      {==}

law SE.fs_ft:
  for +tio: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +g: EM_.EG
  for +r1: N.Ent
  for +i: U32
  for +has: Bool
  {SE.fs(tio, tt, FT{e, g, r1, i, has}) == N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(e), r1, i, has} : N.FS}

def SE.fs_ft(tio, tt, e, g, r1, i, has):
  {==}

law SE.Ii:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +r1: N.Ent
  for +i: U32
  for +has: Bool
  for +h: {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, FT{e, g, r1, i, has}) == True{} : Bool}
  {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def SE.Ii(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, h):
  P.Bool.and_l(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1))), h)

law SE.Ic:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +r1: N.Ent
  for +i: U32
  for +has: Bool
  for +h: {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, FT{e, g, r1, i, has}) == True{} : Bool}
  {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}

def SE.Ic(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, h):
  SE.teq_eq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))), P.Bool.and_l(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)), P.Bool.and_r(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1))), h)))

law SE.Io:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +r1: N.Ent
  for +i: U32
  for +has: Bool
  for +h: {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, FT{e, g, r1, i, has}) == True{} : Bool}
  {Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)) == True{} : Bool}

def SE.Io(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, h):
  P.Bool.and_r(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)), P.Bool.and_r(EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(SE.teq(EM_.EM.tc(e), Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.or(Bool.not(has), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1))), h))

# fs.loop is its mirror...
law SE.loop_code:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for s: Bool & FT
  for hip: SE.Ip(ts, tt, seg, cpl, w0, w1, E, Es, BIG, s)
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  {N.fs.loop(k, n, cpl, w0, SE.dfs(tio, tt, s)) == SE.fs(tio, tt, SE.loop(k, n, cpl, w0, tio, tt, s)) : N.FS}

def SE.loop_code(k, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, s, hip, hwok, hH, hall):
  match k s:
    case 0n Tuple{h, st}:
      {==}
    case 1n+p Tuple{False{}, st}:
      {==}
    case 1n+p Tuple{True{}, FT{+e, +g, +r1, +i, +has}}:
      match hip:
        case Tuple{+hib, +heq}:
          %Equal.sym(N.FS, SE.fs(tio, tt, FT{e, g, r1, i, has}), N.FS{A.A.from(tio), A.A.from(tt), EM_.EM.em(e), r1, i, has}, SE.fs_ft(tio, tt, e, g, r1, i, has)) :
            {N.fs.loop(p, n, cpl, w0, N.fs.step(n, cpl, w0, _)) == SE.fs(tio, tt, SE.loop(p, n, cpl, w0, tio, tt, SE.step(n, cpl, w0, tio, tt, FT{e, g, r1, i, has}))) : N.FS}
          %Equal.sym(Bool & N.FS, N.fs.step.go(U32.is_lt(i, n), n, cpl, w0, A.A.from(tio), A.A.from(tt), EM_.EM.em(e), r1, i), SE.dfs(tio, tt, SE.sgo(U32.is_lt(i, n), n, cpl, w0, tio, tt, e, g, r1, i)), SE.sgo_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, n, tio, r1, i, SE.Ii(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib), (%Equal.sym(Bool, True{}, has, heq) : {Bool.or(Bool.not(_), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)) == True{} : Bool}; SE.Io(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib)), U32.is_lt(i, n))) :
            {N.fs.loop(p, n, cpl, w0, _) == SE.fs(tio, tt, SE.loop(p, n, cpl, w0, tio, tt, SE.sgo(U32.is_lt(i, n), n, cpl, w0, tio, tt, e, g, r1, i))) : N.FS}
          SE.loop_code(p, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, SE.sgo(U32.is_lt(i, n), n, cpl, w0, tio, tt, e, g, r1, i), SE.sgo_inv(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, r1, i, SE.Ii(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib), SE.Ic(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib), hwok, hH, hall, (%Equal.sym(Bool, True{}, has, heq) : {Bool.or(Bool.not(_), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)) == True{} : Bool}; SE.Io(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib)), U32.is_lt(i, n), {==}), hwok, hH, hall)

# ... and keeps the invariant.
law SE.loop_inv:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for s: Bool & FT
  for hip: SE.Ip(ts, tt, seg, cpl, w0, w1, E, Es, BIG, s)
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.loop(k, n, cpl, w0, tio, tt, s)) == True{} : Bool}

def SE.loop_inv(k, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, s, hip, hwok, hH, hall):
  match k s:
    case 0n Tuple{h, st}:
      match hip:
        case Tuple{+hi, +heq}:
          hi
    case 1n+p Tuple{False{}, st}:
      match hip:
        case Tuple{+hi, +heq}:
          hi
    case 1n+p Tuple{True{}, FT{+e, +g, +r1, +i, +has}}:
      match hip:
        case Tuple{+hib, +heq}:
          SE.loop_inv(p, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, SE.sgo(U32.is_lt(i, n), n, cpl, w0, tio, tt, e, g, r1, i), SE.sgo_inv(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, r1, i, SE.Ii(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib), SE.Ic(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib), hwok, hH, hall, (%Equal.sym(Bool, True{}, has, heq) : {Bool.or(Bool.not(_), SE.ok(ts, tt, seg, cpl, w0, w1, Es, r1)) == True{} : Bool}; SE.Io(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, hib)), U32.is_lt(i, n), {==}), hwok, hH, hall)

# io.flush
# --------

def SE.fe(+st: FT) -> EM_.ET:
  match st:
    case FT{e, g, r1, i, has}:
      e

def SE.fg(+st: FT) -> EM_.EG:
  match st:
    case FT{e, g, r1, i, has}:
      g

law SE.ok0.c:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +n: U32
  for +tio: A.Tr
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(n, 0) == z : Bool}
  {Bool.or(Bool.not(Bool.not(z)), SE.ok(ts, tt, seg, cpl, w0, w1, Es, SE.ent(tio, 0))) == True{} : Bool}

law SE.pos_ne:
  for +n: U32
  for +h: {U32.is_eq(n, 0) == False{} : Bool}
  {U32.is_lt(0, n) == True{} : Bool}

law SE.pos_ne.n:
  for +m: Nat
  for +h: {Cmp.is_eq(Nat.cmp(m, 0n)) == False{} : Bool}
  {Cmp.is_lt(Nat.cmp(0n, m)) == True{} : Bool}

def SE.pos_ne.n(m, h):
  match m:
    case 0n:
      P.Bool.false_true({Cmp.is_lt(Nat.cmp(0n, 0n)) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case 1n+p:
      {==}

def SE.pos_ne(n, h):
  %Equal.sym(Cmp, U32.cmp(0, n), Nat.cmp(0n, V.U.N(n)), V.U.cmp_nat(0, n)) :
    {Cmp.is_lt(_) == True{} : Bool}
  SE.pos_ne.n(V.U.N(n), (%V.U.cmp_nat(n, 0) : {Cmp.is_eq(_) == False{} : Bool}; h))

def SE.ok0.c(ts, tt, seg, cpl, w0, w1, Es, n, tio, hall, z, ez):
  match z:
    case True{}:
      {==}
    case False{}:
      SE.at(ts, tt, seg, cpl, w0, w1, Es, tio, n, 0, SE.pos_ne(n, ez), hall)

law SE.Ip0:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  SE.Ip(ts, tt, seg, cpl, w0, w1, E, Es, BIG, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}))

def SE.Ip0(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, hinv, hc, hwok, hH, hall):
  (SE.mkI(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0), (hinv, hc), SE.ok0.c(ts, tt, seg, cpl, w0, w1, Es, n, tio, hall, U32.is_eq(n, 0), {==})), {==})

# io.flush settles and writes the n buffered matches: it is its mirror...
law SE.flush_code:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  {N.io.flush(A.A.from(tio), n, cpl, w0, A.A.from(tt), EM_.EM.em(e)) == (A.A.from(tio), (A.A.from(tt), EM_.EM.em(SE.fe(SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)})))))) : Array<U32> & (Array<U32> & N.Em)}

law SE.done_fs:
  for +tio: A.Tr
  for +tt: A.Tr
  for +st: FT
  {N.fs.done(SE.fs(tio, tt, st)) == (A.A.from(tio), (A.A.from(tt), EM_.EM.em(SE.fe(st)))) : Array<U32> & (Array<U32> & N.Em)}

def SE.done_fs(tio, tt, st):
  match st:
    case FT{e, g, r1, i, has}:
      {==}

def SE.flush_code(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, hinv, hc, hwok, hH, hall):
  %Equal.sym(Array<U32> & N.Ent, N.io.get(A.A.from(tio), 0), (A.A.from(tio), SE.ent(tio, 0)), SE.get(tio, 0)) :
    {N.fs.start(n, cpl, w0, A.A.from(tt), EM_.EM.em(e), _) == (A.A.from(tio), (A.A.from(tt), EM_.EM.em(SE.fe(SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)})))))) : Array<U32> & Array<U32> & N.Em}
  %Equal.sym(N.FS, N.fs.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, SE.dfs(tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}))), SE.fs(tio, tt, SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}))), SE.loop_code(V.U.N(U32.add(n, 1)), ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}), SE.Ip0(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, hinv, hc, hwok, hH, hall), hwok, hH, hall)) :
    {N.fs.done(_) == (A.A.from(tio), (A.A.from(tt), EM_.EM.em(SE.fe(SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)})))))) : Array<U32> & Array<U32> & N.Em}
  SE.done_fs(tio, tt, SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)})))

law SE.Ib_J:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +st: FT
  for +h: {SE.Ib(ts, tt, seg, cpl, w0, w1, E, Es, BIG, st) == True{} : Bool}
  EI_.EI.J(SE.fe(st), SE.fg(st), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def SE.Ib_J(ts, tt, seg, cpl, w0, w1, E, Es, BIG, st, h):
  match st:
    case FT{e, g, r1, i, has}:
      (SE.Ii(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, h), SE.Ic(ts, tt, seg, cpl, w0, w1, E, Es, BIG, e, g, r1, i, has, h))

# ... and keeps the emitter's invariant.
law SE.flush_J:
  for +e: EM_.ET
  for +g: EM_.EG
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +HB: U32
  for +n: U32
  for +tio: A.Tr
  for +hinv: {EM_.EM.inv(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) : A.Tr}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hall: {SE.oks(V.U.N(n), ts, tt, seg, cpl, w0, w1, Es, tio, 0) == True{} : Bool}
  EI_.EI.J(SE.fe(SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}))), SE.fg(SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}))), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def SE.flush_J(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, hinv, hc, hwok, hH, hall):
  SE.Ib_J(ts, tt, seg, cpl, w0, w1, E, Es, BIG, SE.loop(V.U.N(U32.add(n, 1)), n, cpl, w0, tio, tt, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)})), SE.loop_inv(V.U.N(U32.add(n, 1)), ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, (U32.is_ne(n, 0), FT{e, g, SE.ent(tio, 0), 1, U32.is_ne(n, 0)}), SE.Ip0(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, n, tio, hinv, hc, hwok, hH, hall), hwok, hH, hall))
