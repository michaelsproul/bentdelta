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
import ./ctab.bend as T
import ./emit.bend as EM_

# Emitting instructions
# =====================
#
# What the emitter's steps (em.gap, em.inst, em.flush) keep, for the
# instructions the window's settled matches give.

# The emitter's invariant, with its cache the decoder's after the halves.
def EI.J(+e: EM_.ET, +g: EM_.EG, +w: EM_.EW) -> Type:
  {EM_.EM.inv(e, g, w) == True{} : Bool} & {EM_.EM.tc(e) == Q.SP.sc(Q.SP.run(EM_.EM.ghs(g), EM_.EM.x(w), EM_.EM.s0(w))) : A.Tr}

def EI.gadd(+tt: A.Tr, +size: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  EM_.EM.gq(EM_.EM.add.e1(tt, EM_.EM.uo(e), size, e), EM_.EM.add.g(e, g, size), Q.HA{size, S.S.sl(V.U.N(size), tt, EM_.EM.uo(e))})

# An ADD of the next size bytes.
law EI.add:
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
  for +size: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hsz: {Cmp.is_le(Nat.cmp(1n, V.U.N(size))) == True{} : Bool}
  for +hend: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(EM_.EM.uo(e)), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  EI.J(EM_.EM.add(tt, EM_.EM.uo(e), size, e), EI.gadd(tt, size, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.add(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, hJ, hwok, hsz, hend):
  match e g hJ:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da} Tuple{+hinv, +hc}:
      (EM_.EM.add_ok(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, hinv, hwok, hsz, hend),
       EM_.EM.add_tc(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, hinv, hc))

# What a buffered match must be to be written: inside the window, and a
# RUN of its byte, or a COPY from an earlier window address.
def EI.ek(+ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +Es: U32, +run: Bool, +pos: U32, +size: U32, +val: U32) -> Bool:
  match run:
    case True{}:
      S.S.has(C.CP.rep(V.U.N(size), val), tt, pos)
    case False{}:
      Bool.and(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es)))

def EI.eok(+ts: A.Tr, +tt: A.Tr, +seg: U32, +cpl: U32, +w0: U32, +w1: U32, +Es: U32, +run: Bool, +pos: U32, +size: U32, +val: U32) -> Bool:
  Bool.and(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val)))

law EI.eok.hi:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +size: U32
  for +val: U32
  for +h: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}

def EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val)), h))

law EI.eok.lo:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +size: U32
  for +val: U32
  for +h: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  {U32.is_le(w0, pos) == True{} : Bool}

def EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val, h):
  P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val)), h)

law EI.eok.k:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +run: Bool
  for +pos: U32
  for +size: U32
  for +val: U32
  for +h: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  {EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}

def EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val, h):
  P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val), P.Bool.and_r(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))), EI.ek(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val)), h))

def EI.grun(+size: U32, +b: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  EM_.EM.gq(EM_.EM.run.e1(EM_.EM.uo(e), size, b, e), EM_.EM.run.g(e, g), Q.HR{size, b})

def EI.gcopy(+size: U32, +addr: U32, +here: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  EM_.EM.gq(EM_.EM.copy.e1(EM_.EM.uo(e), size, addr, here, e), EM_.EM.copy.g(e, g), EM_.EM.copy.h(size, addr, here, e))

# A RUN of the next size bytes.
law EI.run:
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
  for +size: U32
  for +b: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, True{}, EM_.EM.uo(e), size, b) == True{} : Bool}
  for +hsz: {Cmp.is_le(Nat.cmp(1n, V.U.N(size))) == True{} : Bool}
  EI.J(EM_.EM.run(EM_.EM.uo(e), size, b, e), EI.grun(size, b, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.run(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, b, hJ, hwok, hok, hsz):
  match e g hJ:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da} Tuple{+hinv, +hc}:
      (EM_.EM.run_ok(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, b, hinv, hwok, EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, True{}, uoff, size, b, hok), hsz, EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, True{}, uoff, size, b, hok)),
       EM_.EM.run_tc(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, b, hinv, hc))

# A COPY of the next size bytes from window address addr.
law EI.copy:
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
  for +size: U32
  for +addr: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, False{}, EM_.EM.uo(e), size, addr) == True{} : Bool}
  for +hsz: {Cmp.is_le(Nat.cmp(1n, V.U.N(size))) == True{} : Bool}
  EI.J(EM_.EM.copy(EM_.EM.uo(e), size, addr, U32.add(cpl, U32.sub(EM_.EM.uo(e), w0)), e), EI.gcopy(size, addr, U32.add(cpl, U32.sub(EM_.EM.uo(e), w0)), e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

law EI.copy.k:
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
  for +size: U32
  for +addr: U32
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hc: {tc == Q.SP.sc(Q.SP.run(EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, Q.SP.s0(w0))) : A.Tr}
  for +hk: {Bool.and(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es))) == True{} : Bool}
  for +hsz: {Cmp.is_le(Nat.cmp(1n, V.U.N(size))) == True{} : Bool}
  for +hend: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(uoff), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  EI.J(EM_.EM.copy(uoff, size, addr, U32.add(cpl, U32.sub(uoff, w0)), EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gcopy(size, addr, U32.add(cpl, U32.sub(uoff, w0)), EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.copy.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, addr, hinv, hwok, hc, hk, hsz, hend):
  (EM_.EM.copy_ok(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, addr, hinv, hwok, hc, P.Bool.and_l(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk), P.Bool.and_l(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es), P.Bool.and_r(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk)), P.Bool.and_r(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es), P.Bool.and_r(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk)), hsz, hend),
   EM_.EM.copy_tc(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, addr, hinv, hwok, hc, P.Bool.and_l(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk), P.Bool.and_l(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es), P.Bool.and_r(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk)), P.Bool.and_r(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es), P.Bool.and_r(U32.is_lt(addr, U32.add(cpl, U32.sub(uoff, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, uoff, size, addr, Es)), hk)), hsz, hend))

def EI.copy(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, addr, hJ, hwok, hok, hsz):
  match e g hJ:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da} Tuple{+hinv, +hc}:
      EI.copy.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, addr, hinv, hwok, hc, EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, False{}, uoff, size, addr, hok), hsz, EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, False{}, uoff, size, addr, hok))

# Where the emitter is
# ====================

law EI.uo_qk:
  for +td: A.Tr
  for +ta: A.Tr
  for +tc: A.Tr
  for +dl: U32
  for +al: U32
  for +slot: U32
  for +uoff: U32
  for +t: U32
  for +size: U32
  for +mode: U32
  for +r: EM_.TI
  {EM_.EM.uo(EM_.EM.qk(td, ta, tc, dl, al, slot, uoff, t, size, mode, r)) == uoff : U32}

def EI.uo_qk(td, ta, tc, dl, al, slot, uoff, t, size, mode, r):
  match r:
    case EM_.TI{ti, il}:
      {==}

law EI.uo_qg:
  for +dbl: Bool
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
  for +pc: U32
  for +code: U32
  for +t: U32
  for +size: U32
  for +mode: U32
  {EM_.EM.uo(EM_.EM.qg(dbl, td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pc, code, t, size, mode)) == uoff : U32}

def EI.uo_qg(dbl, td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pc, code, t, size, mode):
  match dbl:
    case True{}:
      {==}
    case False{}:
      EI.uo_qk(td, ta, tc, dl, al, slot, uoff, t, size, mode, EM_.EM.sg(pt, ps, pc, ti, il))

# Queueing leaves the position.
law EI.uo_q:
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
  for +t: U32
  for +size: U32
  for +mode: U32
  {EM_.EM.uo(EM_.EM.q(t, size, mode, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc})) == uoff : U32}

def EI.uo_q(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, t, size, mode):
  EI.uo_qg(U32.is_ne(N.op.double(pt, ps, pm, t, size, mode), 0), td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pc, N.op.double(pt, ps, pm, t, size, mode), t, size, mode)

# An ADD at pos moves the emitter to its end.
law EI.uo_add:
  for +tt: A.Tr
  for +pos: U32
  for +size: U32
  for +e: EM_.ET
  {EM_.EM.uo(EM_.EM.add(tt, pos, size, e)) == U32.add(pos, size) : U32}

def EI.uo_add(tt, pos, size, e):
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      EI.uo_q(S.S.puts(S.S.sl(V.U.N(size), tt, pos), EM_.GR.t(td, dl, U32.add(dl, size)), dl), EM_.GR.t(ti, il, U32.add(il, 12)), EM_.GR.t(ta, al, U32.add(al, 6)), tc, U32.add(dl, size), il, al, slot, U32.add(pos, size), pt, ps, pm, pc, 1, size, 0)

law EI.le_anti:
  for +a: Nat
  for +b: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(b, a)) == True{} : Bool}
  {a == b : Nat}

def EI.le_anti(a, b, h1, h2):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      P.Bool.false_true({0n == 1n+q : Nat}, h2)
    case 1n+p 0n:
      P.Bool.false_true({1n+p == 0n : Nat}, h1)
    case 1n+p 1n+q:
      %EI.le_anti(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

law EI.le_anti32:
  for +a: U32
  for +b: U32
  for +h1: {U32.is_le(a, b) == True{} : Bool}
  for +h2: {U32.is_le(b, a) == True{} : Bool}
  {a == b : U32}

def EI.le_anti32(a, b, h1, h2):
  V.U.eq_N(a, b, EI.le_anti(V.U.N(a), V.U.N(b), V.U.le_N(a, b, h1), V.U.le_N(b, a, h2)))

law EI.sub_pos:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(1n, V.U.N(U32.sub(b, a)))) == True{} : Bool}

def EI.sub_pos(a, b, h):
  P.Nat.lt_le_succ(0n, V.U.N(U32.sub(b, a)), P.Nat.lt_of_sum(0n, V.U.N(b), V.U.N(U32.sub(b, a)), V.U.N(a), Equal.sym(Nat, Nat.add(V.U.N(U32.sub(b, a)), V.U.N(a)), V.U.N(b), V.U.sub_nat(b, a, V.U.lt_to_le(a, b, h))), V.U.lt_N(a, b, h)))

# The gap
# =======

def EI.ggi(+z: Bool, +tt: A.Tr, +pos: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match z:
    case True{}:
      EI.gadd(tt, U32.sub(pos, EM_.EM.uo(e)), e, g)
    case False{}:
      g

def EI.ggap(+tt: A.Tr, +pos: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  EI.ggi(U32.is_lt(EM_.EM.uo(e), pos), tt, pos, e, g)

law EI.gap.c:
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
  for +pos: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(pos), V.U.N(w1))) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(EM_.EM.uo(e), pos) == z : Bool}
  EI.J(EM_.EM.gapi(z, tt, EM_.EM.uo(e), pos, e), EI.ggi(z, tt, pos, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.gap.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, pos, hJ, hwok, hp, z, ez):
  match z:
    case True{}:
      EI.add(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, U32.sub(pos, EM_.EM.uo(e)), hJ, hwok, EI.sub_pos(EM_.EM.uo(e), pos, ez),
        (%P.Nat.add_comm(V.U.N(U32.sub(pos, EM_.EM.uo(e))), V.U.N(EM_.EM.uo(e))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool};
          (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(pos, EM_.EM.uo(e))), V.U.N(EM_.EM.uo(e))), V.U.N(pos), V.U.sub_nat(pos, EM_.EM.uo(e), V.U.lt_to_le(EM_.EM.uo(e), pos, ez))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool};
            hp)))
    case False{}:
      hJ

# The ADD of the bytes before pos not yet written.
law EI.gap:
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
  for +pos: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hp: {Cmp.is_le(Nat.cmp(V.U.N(pos), V.U.N(w1))) == True{} : Bool}
  EI.J(EM_.EM.gap(tt, pos, e), EI.ggap(tt, pos, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.gap(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, pos, hJ, hwok, hp):
  EI.gap.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, pos, hJ, hwok, hp, U32.is_lt(EM_.EM.uo(e), pos), {==})

law EI.uo_gap.c:
  for +tt: A.Tr
  for +pos: U32
  for +e: EM_.ET
  for +hle: {U32.is_le(EM_.EM.uo(e), pos) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(EM_.EM.uo(e), pos) == z : Bool}
  {EM_.EM.uo(EM_.EM.gapi(z, tt, EM_.EM.uo(e), pos, e)) == pos : U32}

def EI.uo_gap.c(tt, pos, e, hle, z, ez):
  match z:
    case True{}:
      %Equal.sym(U32, EM_.EM.uo(EM_.EM.add(tt, EM_.EM.uo(e), U32.sub(pos, EM_.EM.uo(e)), e)), U32.add(EM_.EM.uo(e), U32.sub(pos, EM_.EM.uo(e))), EI.uo_add(tt, EM_.EM.uo(e), U32.sub(pos, EM_.EM.uo(e)), e)) :
        {_ == pos : U32}
      EM_.EM.addsub(EM_.EM.uo(e), pos)
    case False{}:
      EI.le_anti32(EM_.EM.uo(e), pos, hle, V.U.not_lt(EM_.EM.uo(e), pos, ez))

# After the gap to pos, the emitter is at pos.
law EI.uo_gap:
  for +tt: A.Tr
  for +pos: U32
  for +e: EM_.ET
  for +hle: {U32.is_le(EM_.EM.uo(e), pos) == True{} : Bool}
  {EM_.EM.uo(EM_.EM.gap(tt, pos, e)) == pos : U32}

def EI.uo_gap(tt, pos, e, hle):
  EI.uo_gap.c(tt, pos, e, hle, U32.is_lt(EM_.EM.uo(e), pos), {==})

# Cutting the front off a match
# =============================

law EI.nsplit:
  for +c: U32
  for +size: U32
  for +h: {U32.is_le(c, size) == True{} : Bool}
  {V.U.N(size) == Nat.add(V.U.N(c), V.U.N(U32.sub(size, c))) : Nat}

def EI.nsplit(c, size, h):
  %P.Nat.add_comm(V.U.N(U32.sub(size, c)), V.U.N(c)) : {V.U.N(size) == _ : Nat}
  Equal.sym(Nat, Nat.add(V.U.N(U32.sub(size, c)), V.U.N(c)), V.U.N(size), V.U.sub_nat(size, c, h))

# The bytes past the first c of a slice held at p.
law EI.sl_suf:
  for +c: U32
  for +size: U32
  for +u: A.Tr
  for +s: U32
  for +t: A.Tr
  for +p: U32
  for +hc: {U32.is_le(c, size) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(size), u, s), t, p) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), u, U32.add(s, c)), t, U32.add(p, c)) == True{} : Bool}

def EI.sl_suf(c, size, u, s, t, p, hc, h):
  P.Bool.and_r(S.S.has(S.S.sl(V.U.N(c), u, s), t, p), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), u, U32.add(s, c)), t, U32.add(p, c)),
    (%K.WD.has_app(S.S.sl(V.U.N(c), u, s), S.S.sl(V.U.N(U32.sub(size, c)), u, U32.add(s, c)), t, p, c, Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(c), u, s)), V.U.N(c), S.S.len_sl(V.U.N(c), u, s))) : {_ == True{} : Bool};
      (%K.WD.sl_app(V.U.N(c), V.U.N(U32.sub(size, c)), u, s, c, {==}) : {S.S.has(_, t, p) == True{} : Bool};
        (%EI.nsplit(c, size, hc) : {S.S.has(S.S.sl(_, u, s), t, p) == True{} : Bool};
          h))))

# The bytes past the first c of a run held at p.
law EI.rep_suf:
  for +c: U32
  for +size: U32
  for +b: U32
  for +t: A.Tr
  for +p: U32
  for +hc: {U32.is_le(c, size) == True{} : Bool}
  for +h: {S.S.has(C.CP.rep(V.U.N(size), b), t, p) == True{} : Bool}
  {S.S.has(C.CP.rep(V.U.N(U32.sub(size, c)), b), t, U32.add(p, c)) == True{} : Bool}

def EI.rep_suf(c, size, b, t, p, hc, h):
  P.Bool.and_r(S.S.has(C.CP.rep(V.U.N(c), b), t, p), S.S.has(C.CP.rep(V.U.N(U32.sub(size, c)), b), t, U32.add(p, c)),
    (%K.WD.has_app(C.CP.rep(V.U.N(c), b), C.CP.rep(V.U.N(U32.sub(size, c)), b), t, p, c, Equal.sym(Nat, S.S.len(C.CP.rep(V.U.N(c), b)), V.U.N(c), C.CP.len_rep(V.U.N(c), b))) : {_ == True{} : Bool};
      (%C.CP.rep_app(V.U.N(c), V.U.N(U32.sub(size, c)), b) : {S.S.has(_, t, p) == True{} : Bool};
        (%EI.nsplit(c, size, hc) : {S.S.has(C.CP.rep(_, b), t, p) == True{} : Bool};
          h))))

# The first k bytes of a slice held at p.
law EI.sl_pre:
  for +k: U32
  for +size: U32
  for +u: A.Tr
  for +s: U32
  for +t: A.Tr
  for +p: U32
  for +hk: {U32.is_le(k, size) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(size), u, s), t, p) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(k), u, s), t, p) == True{} : Bool}

def EI.sl_pre(k, size, u, s, t, p, hk, h):
  P.Bool.and_l(S.S.has(S.S.sl(V.U.N(k), u, s), t, p), S.S.has(S.S.sl(V.U.N(U32.sub(size, k)), u, U32.add(s, k)), t, U32.add(p, k)),
    (%K.WD.has_app(S.S.sl(V.U.N(k), u, s), S.S.sl(V.U.N(U32.sub(size, k)), u, U32.add(s, k)), t, p, k, Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(k), u, s)), V.U.N(k), S.S.len_sl(V.U.N(k), u, s))) : {_ == True{} : Bool};
      (%K.WD.sl_app(V.U.N(k), V.U.N(U32.sub(size, k)), u, s, k, {==}) : {S.S.has(_, t, p) == True{} : Bool};
        (%EI.nsplit(k, size, hk) : {S.S.has(S.S.sl(_, u, s), t, p) == True{} : Bool};
          h))))

# The first k bytes of a run held at p.
law EI.rep_pre:
  for +k: U32
  for +size: U32
  for +b: U32
  for +t: A.Tr
  for +p: U32
  for +hk: {U32.is_le(k, size) == True{} : Bool}
  for +h: {S.S.has(C.CP.rep(V.U.N(size), b), t, p) == True{} : Bool}
  {S.S.has(C.CP.rep(V.U.N(k), b), t, p) == True{} : Bool}

def EI.rep_pre(k, size, b, t, p, hk, h):
  P.Bool.and_l(S.S.has(C.CP.rep(V.U.N(k), b), t, p), S.S.has(C.CP.rep(V.U.N(U32.sub(size, k)), b), t, U32.add(p, k)),
    (%K.WD.has_app(C.CP.rep(V.U.N(k), b), C.CP.rep(V.U.N(U32.sub(size, k)), b), t, p, k, Equal.sym(Nat, S.S.len(C.CP.rep(V.U.N(k), b)), V.U.N(k), C.CP.len_rep(V.U.N(k), b))) : {_ == True{} : Bool};
      (%C.CP.rep_app(V.U.N(k), V.U.N(U32.sub(size, k)), b) : {S.S.has(_, t, p) == True{} : Bool};
        (%EI.nsplit(k, size, hk) : {S.S.has(C.CP.rep(_, b), t, p) == True{} : Bool};
          h))))

law EI.flip_le:
  for +c: Cmp
  for +h: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_lt(P.Cmp.flip(c)) == False{} : Bool}

def EI.flip_le(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.false_true({Cmp.is_lt(P.Cmp.flip(GT{})) == False{} : Bool}, h)

# a <= b: b is not below a.
law EI.le_nlt:
  for +a: U32
  for +b: U32
  for +h: {Cmp.is_le(Nat.cmp(V.U.N(a), V.U.N(b))) == True{} : Bool}
  {U32.is_lt(b, a) == False{} : Bool}

def EI.le_nlt(a, b, h):
  %Equal.sym(Cmp, U32.cmp(b, a), Nat.cmp(V.U.N(b), V.U.N(a)), V.U.cmp_nat(b, a)) :
    {Cmp.is_lt(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(b), V.U.N(a)), P.Cmp.flip(Nat.cmp(V.U.N(a), V.U.N(b))), P.Nat.cmp_swap(V.U.N(a), V.U.N(b))) :
    {Cmp.is_lt(_) == False{} : Bool}
  EI.flip_le(Nat.cmp(V.U.N(a), V.U.N(b)), h)

law EI.lea:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(a, x), Nat.add(a, y))) == True{} : Bool}

def EI.lea(a, x, y, h):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(a, x), Nat.add(a, y)), Nat.cmp(x, y), P.Nat.cmp_add_l(a, x, y)) : {Cmp.is_le(_) == True{} : Bool}
  h

law EI.s.hpc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(w1))) == True{} : Bool}

def EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  P.Nat.le_trans(Nat.add(V.U.N(pos), V.U.N(c)), Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1), EI.lea(V.U.N(pos), V.U.N(c), V.U.N(size), V.U.le_N(c, size, V.U.lt_to_le(c, size, hc))), hpos)

law EI.s.Npc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {V.U.N(U32.add(pos, c)) == Nat.add(V.U.N(pos), V.U.N(c)) : Nat}

def EI.s.Npc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  V.U.add_N(pos, c, w1, EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))

law EI.s.lo1:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {U32.is_le(w0, U32.add(pos, c)) == True{} : Bool}

def EI.s.lo1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  V.U.N_le(w0, U32.add(pos, c), P.Nat.le_trans(V.U.N(w0), V.U.N(pos), V.U.N(U32.add(pos, c)), V.U.le_N(w0, pos, hlo), (%Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), EI.s.Npc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) : {Cmp.is_le(Nat.cmp(V.U.N(pos), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(pos), V.U.N(c)))))

law EI.s.hi1:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {U32.is_le(U32.add(pos, c), w1) == True{} : Bool}

def EI.s.hi1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  V.U.N_le(U32.add(pos, c), w1, (%Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), EI.s.Npc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)))

law EI.s.hi0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {U32.is_le(pos, w1) == True{} : Bool}

def EI.s.hi0(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  V.U.N_le(pos, w1, P.Nat.le_trans(V.U.N(pos), Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(pos), V.U.N(c)), EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)))

law EI.s.hiN:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(size, c))), V.U.N(w1))) == True{} : Bool}

def EI.s.hiN(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  %Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), EI.s.Npc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.sub(size, c))), V.U.N(w1))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(U32.sub(size, c))), Nat.add(V.U.N(pos), Nat.add(V.U.N(c), V.U.N(U32.sub(size, c)))), P.Nat.add_assoc(V.U.N(pos), V.U.N(c), V.U.N(U32.sub(size, c)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}
  %EI.nsplit(c, size, V.U.lt_to_le(c, size, hc)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), _), V.U.N(w1))) == True{} : Bool}
  hpos

law EI.s.b0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), V.U.N(HB))) == True{} : Bool}

def EI.s.b0(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  P.Nat.le_trans(Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB), EI.lea(V.U.N(cpl), V.U.N(U32.sub(pos, w0)), V.U.N(U32.sub(w1, w0)), EM_.EM.k_le(pos, w1, w0, hlo, EI.s.hi0(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))), hH)

law EI.s.b1:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0))), V.U.N(HB))) == True{} : Bool}

def EI.s.b1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  P.Nat.le_trans(Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB), EI.lea(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0)), V.U.N(U32.sub(w1, w0)), EM_.EM.k_le(U32.add(pos, c), w1, w0, EI.s.lo1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc), EI.s.hi1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))), hH)

law EI.s.kc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  {V.U.N(U32.sub(U32.add(pos, c), w0)) == Nat.add(V.U.N(U32.sub(pos, w0)), V.U.N(c)) : Nat}

def EI.s.kc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc):
  EM_.EM.kadd(pos, c, w0, w1, hlo, EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))

law EI.s.vlt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  {Nat.cmp(V.U.N(val), Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0)))) == LT{} : Cmp}

def EI.s.vlt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt):
  %V.U.add_N(cpl, U32.sub(pos, w0), HB, EI.s.b0(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) : {Nat.cmp(V.U.N(val), _) == LT{} : Cmp}
  V.U.lt_N(val, U32.add(cpl, U32.sub(pos, w0)), hlt)

law EI.s.vclt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  {Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0)))) == LT{} : Cmp}

def EI.s.vclt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt):
  %Equal.sym(Nat, V.U.N(U32.sub(U32.add(pos, c), w0)), Nat.add(V.U.N(U32.sub(pos, w0)), V.U.N(c)), EI.s.kc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) :
    {Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(cpl), _)) == LT{} : Cmp}
  %P.Nat.add_assoc(V.U.N(cpl), V.U.N(U32.sub(pos, w0)), V.U.N(c)) :
    {Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), _) == LT{} : Cmp}
  P.Nat.add_lt_r(V.U.N(val), Nat.add(V.U.N(cpl), V.U.N(U32.sub(pos, w0))), V.U.N(c), EI.s.vlt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt))

law EI.s.vcb:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), V.U.N(HB))) == True{} : Bool}

def EI.s.vcb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt):
  P.Nat.le_trans(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0))), V.U.N(HB), P.Nat.lt_to_le(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0))), EI.s.vclt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt)), EI.s.b1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))

law EI.s.Nvc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  {V.U.N(U32.add(val, c)) == Nat.add(V.U.N(val), V.U.N(c)) : Nat}

def EI.s.Nvc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt):
  V.U.add_N(val, c, HB, EI.s.vcb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt))

law EI.s.lt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  {U32.is_lt(U32.add(val, c), U32.add(cpl, U32.sub(U32.add(pos, c), w0))) == True{} : Bool}

def EI.s.lt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt):
  V.U.N_lt(U32.add(val, c), U32.add(cpl, U32.sub(U32.add(pos, c), w0)), (%Equal.sym(Nat, V.U.N(U32.add(val, c)), Nat.add(V.U.N(val), V.U.N(c)), EI.s.Nvc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt)) : {Nat.cmp(_, V.U.N(U32.add(cpl, U32.sub(U32.add(pos, c), w0)))) == LT{} : Cmp};
    (%Equal.sym(Nat, V.U.N(U32.add(cpl, U32.sub(U32.add(pos, c), w0))), Nat.add(V.U.N(cpl), V.U.N(U32.sub(U32.add(pos, c), w0))), V.U.add_N(cpl, U32.sub(U32.add(pos, c), w0), HB, EI.s.b1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc))) : {Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), _) == LT{} : Cmp};
      EI.s.vclt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt))))

law EI.s.vs:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +e0: {U32.is_lt(val, cpl) == True{} : Bool}
  for +hsz: {U32.is_le(size, U32.sub(cpl, val)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), V.U.N(size)), V.U.N(cpl))) == True{} : Bool}

def EI.s.vs(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz):
  P.Nat.le_trans(Nat.add(V.U.N(val), V.U.N(size)), Nat.add(V.U.N(val), V.U.N(U32.sub(cpl, val))), V.U.N(cpl), EI.lea(V.U.N(val), V.U.N(size), V.U.N(U32.sub(cpl, val)), V.U.le_N(size, U32.sub(cpl, val), hsz)),
    (%P.Nat.add_comm(V.U.N(U32.sub(cpl, val)), V.U.N(val)) : {Cmp.is_le(Nat.cmp(_, V.U.N(cpl))) == True{} : Bool};
      (%V.U.sub_nat(cpl, val, V.U.lt_to_le(val, cpl, e0)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(cpl, val)), V.U.N(val)), _)) == True{} : Bool};
        C.CP.le_refl(Nat.add(V.U.N(U32.sub(cpl, val)), V.U.N(val))))))

law EI.s.slt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +e0: {U32.is_lt(val, cpl) == True{} : Bool}
  for +hsz: {U32.is_le(size, U32.sub(cpl, val)) == True{} : Bool}
  {U32.is_lt(U32.add(val, c), cpl) == True{} : Bool}

def EI.s.slt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz):
  V.U.N_lt(U32.add(val, c), cpl, (%Equal.sym(Nat, V.U.N(U32.add(val, c)), Nat.add(V.U.N(val), V.U.N(c)), EI.s.Nvc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt)) : {Nat.cmp(_, V.U.N(cpl)) == LT{} : Cmp};
    P.Nat.lt_le_trans(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(val), V.U.N(size)), V.U.N(cpl), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(val), V.U.N(c)), Nat.add(V.U.N(val), V.U.N(size))), Nat.cmp(V.U.N(c), V.U.N(size)), P.Nat.cmp_add_l(V.U.N(val), V.U.N(c), V.U.N(size))) : {_ == LT{} : Cmp}; V.U.lt_N(c, size, hc)), EI.s.vs(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz))))

law EI.s.sle2:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +e0: {U32.is_lt(val, cpl) == True{} : Bool}
  for +hsz: {U32.is_le(size, U32.sub(cpl, val)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(val, c))), Nat.add(V.U.N(U32.sub(cpl, U32.add(val, c))), V.U.N(U32.add(val, c))))) == True{} : Bool}

def EI.s.sle2(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz):
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(cpl, U32.add(val, c))), V.U.N(U32.add(val, c))), V.U.N(cpl), V.U.sub_nat(cpl, U32.add(val, c), V.U.lt_to_le(U32.add(val, c), cpl, EI.s.slt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(val, c))), _)) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(val, c)), Nat.add(V.U.N(val), V.U.N(c)), EI.s.Nvc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), _), V.U.N(cpl))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(size, c)), Nat.add(V.U.N(val), V.U.N(c))), Nat.add(Nat.add(V.U.N(val), V.U.N(c)), V.U.N(U32.sub(size, c))), P.Nat.add_comm(V.U.N(U32.sub(size, c)), Nat.add(V.U.N(val), V.U.N(c)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(cpl))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V.U.N(val), V.U.N(c)), V.U.N(U32.sub(size, c))), Nat.add(V.U.N(val), Nat.add(V.U.N(c), V.U.N(U32.sub(size, c)))), P.Nat.add_assoc(V.U.N(val), V.U.N(c), V.U.N(U32.sub(size, c)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(cpl))) == True{} : Bool}
  %EI.nsplit(c, size, V.U.lt_to_le(c, size, hc)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(val), _), V.U.N(cpl))) == True{} : Bool}
  EI.s.vs(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz)

law EI.s.sle:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +e0: {U32.is_lt(val, cpl) == True{} : Bool}
  for +hsz: {U32.is_le(size, U32.sub(cpl, val)) == True{} : Bool}
  {U32.is_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c))) == True{} : Bool}

def EI.s.sle(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz):
  V.U.N_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c)), (%P.Nat.cmp_add_rr(V.U.N(U32.sub(size, c)), V.U.N(U32.sub(cpl, U32.add(val, c))), V.U.N(U32.add(val, c))) : {Cmp.is_le(_) == True{} : Bool}; EI.s.sle2(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, hsz)))

law EI.s.shas:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hh: {S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, U32.add(seg, U32.add(val, c))), tt, U32.add(pos, c)) == True{} : Bool}

def EI.s.shas(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hh):
  %V.U.add_assoc(seg, val, c) :
    {S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, _), tt, U32.add(pos, c)) == True{} : Bool}
  EI.sl_suf(c, size, ts, U32.add(seg, val), tt, pos, V.U.lt_to_le(c, size, hc), hh)

law EI.s.scb:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(size), V.U.N(U32.add(seg, val))), V.U.N(Es))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(seg, U32.add(val, c)))), V.U.N(Es))) == True{} : Bool}

def EI.s.scb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hb):
  %V.U.add_assoc(seg, val, c) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(_)), V.U.N(Es))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(seg, val), c)), Nat.add(V.U.N(U32.add(seg, val)), V.U.N(c)), V.U.add_N(U32.add(seg, val), c, Es, P.Nat.le_trans(Nat.add(V.U.N(U32.add(seg, val)), V.U.N(c)), Nat.add(V.U.N(size), V.U.N(U32.add(seg, val))), V.U.N(Es), (%P.Nat.add_comm(V.U.N(U32.add(seg, val)), V.U.N(size)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(seg, val)), V.U.N(c)), _)) == True{} : Bool}; EI.lea(V.U.N(U32.add(seg, val)), V.U.N(c), V.U.N(size), V.U.le_N(c, size, V.U.lt_to_le(c, size, hc)))), hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), _), V.U.N(Es))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.add(seg, val)), V.U.N(c)), Nat.add(V.U.N(c), V.U.N(U32.add(seg, val))), P.Nat.add_comm(V.U.N(U32.add(seg, val)), V.U.N(c))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), _), V.U.N(Es))) == True{} : Bool}
  %P.Nat.add_assoc(V.U.N(U32.sub(size, c)), V.U.N(c), V.U.N(U32.add(seg, val))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(Es))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(size, c)), V.U.N(c)), V.U.N(size), V.U.sub_nat(size, c, V.U.lt_to_le(c, size, hc))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(U32.add(seg, val))), V.U.N(Es))) == True{} : Bool}
  hb

law EI.s.tnlt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +e0: {U32.is_lt(val, cpl) == False{} : Bool}
  {U32.is_lt(U32.add(val, c), cpl) == False{} : Bool}

def EI.s.tnlt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0):
  EI.le_nlt(cpl, U32.add(val, c), (%Equal.sym(Nat, V.U.N(U32.add(val, c)), Nat.add(V.U.N(val), V.U.N(c)), EI.s.Nvc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt)) : {Cmp.is_le(Nat.cmp(V.U.N(cpl), _)) == True{} : Bool};
    P.Nat.le_trans(V.U.N(cpl), V.U.N(val), Nat.add(V.U.N(val), V.U.N(c)), V.U.le_N(cpl, val, V.U.not_lt(val, cpl, e0)), P.Nat.cmp_add_r(V.U.N(val), V.U.N(c)))))

law EI.s.tidx:
  for +w0: U32
  for +val: U32
  for +c: U32
  for +cpl: U32
  {U32.add(w0, U32.sub(U32.add(val, c), cpl)) == U32.add(U32.add(w0, U32.sub(val, cpl)), c) : U32}

def EI.s.tidx(w0, val, c, cpl):
  %Equal.sym(U32, U32.sub(U32.add(val, c), cpl), U32.add(U32.sub(val, cpl), c), EM_.EM.subadd(val, c, cpl)) :
    {U32.add(w0, _) == U32.add(U32.add(w0, U32.sub(val, cpl)), c) : U32}
  %V.U.add_assoc(w0, U32.sub(val, cpl), c) :
    {_ == U32.add(U32.add(w0, U32.sub(val, cpl)), c) : U32}
  {==}

law EI.s.thas:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hh: {S.S.has(S.S.sl(V.U.N(size), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), tt, U32.add(w0, U32.sub(U32.add(val, c), cpl))), tt, U32.add(pos, c)) == True{} : Bool}

def EI.s.thas(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hh):
  %Equal.sym(U32, U32.add(w0, U32.sub(U32.add(val, c), cpl)), U32.add(U32.add(w0, U32.sub(val, cpl)), c), EI.s.tidx(w0, val, c, cpl)) :
    {S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), tt, _), tt, U32.add(pos, c)) == True{} : Bool}
  EI.sl_suf(c, size, tt, U32.add(w0, U32.sub(val, cpl)), tt, pos, V.U.lt_to_le(c, size, hc), hh)

law EI.s.tcb:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hb: {Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos))) == True{} : Bool}
  {Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.add(val, c), cpl))), V.U.N(U32.add(pos, c)))) == True{} : Bool}

def EI.s.tcb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hb):
  %Equal.sym(U32, U32.add(w0, U32.sub(U32.add(val, c), cpl)), U32.add(U32.add(w0, U32.sub(val, cpl)), c), EI.s.tidx(w0, val, c, cpl)) :
    {Cmp.is_lt(Nat.cmp(V.U.N(_), V.U.N(U32.add(pos, c)))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(pos, c)), Nat.add(V.U.N(pos), V.U.N(c)), EI.s.Npc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)) :
    {Cmp.is_lt(Nat.cmp(V.U.N(U32.add(U32.add(w0, U32.sub(val, cpl)), c)), _)) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(U32.add(U32.add(w0, U32.sub(val, cpl)), c)), Nat.add(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(c)), V.U.add_N(U32.add(w0, U32.sub(val, cpl)), c, w1, P.Nat.le_trans(Nat.add(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(c)), Nat.add(V.U.N(pos), V.U.N(c)), V.U.N(w1), P.Nat.lt_to_le(Nat.add(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(c)), Nat.add(V.U.N(pos), V.U.N(c)), P.Nat.add_lt_r(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos), V.U.N(c), P.Cmp.is_lt_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)), hb))), EI.s.hpc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc)))) :
    {Cmp.is_lt(Nat.cmp(_, Nat.add(V.U.N(pos), V.U.N(c)))) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(c)), Nat.add(V.U.N(pos), V.U.N(c))), LT{}, P.Nat.add_lt_r(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos), V.U.N(c), P.Cmp.is_lt_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)), hb))) :
    {Cmp.is_lt(_) == True{} : Bool}
  {==}

law EI.suf.cc:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +Es: U32
  for +HB: U32
  for +pos: U32
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hlo: {U32.is_le(w0, pos) == True{} : Bool}
  for +hpos: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(size)), V.U.N(w1))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hlt: {U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))) == True{} : Bool}
  for +c0: Bool
  for +e0: {U32.is_lt(val, cpl) == c0 : Bool}
  for +hcp: {Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val) == True{} : Bool}
  for +hcb: {Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es) == True{} : Bool}
  {Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c)), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c), Es)) == True{} : Bool}

def EI.suf.cc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, c0, e0, hcp, hcb):
  match c0:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(U32.add(val, c), cpl), True{}, EI.s.slt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, P.Bool.and_l(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos), (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(size), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp)))) :
        {Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, U32.add(seg, U32.add(val, c))), tt, U32.add(pos, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), tt, U32.add(w0, U32.sub(U32.add(val, c), cpl))), tt, U32.add(pos, c))), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(seg, U32.add(val, c)))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.add(val, c), cpl))), V.U.N(U32.add(pos, c)))))) == True{} : Bool}
      EM_.EM.and2(Bool.and(U32.is_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, U32.add(seg, U32.add(val, c))), tt, U32.add(pos, c))), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(seg, U32.add(val, c)))), V.U.N(Es))),
        EM_.EM.and2(U32.is_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, U32.add(seg, U32.add(val, c))), tt, U32.add(pos, c)),
          EI.s.sle(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0, P.Bool.and_l(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos), (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(size), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp))),
          EI.s.shas(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, P.Bool.and_r(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos), (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(size), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp)))),
        EI.s.scb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, (%e0 : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(size), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)))) == True{} : Bool}; hcb)))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(U32.add(val, c), cpl), False{}, EI.s.tnlt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, hlt, e0)) :
        {Bool.and(Bool.pick(Bool, _, Bool.and(U32.is_le(U32.sub(size, c), U32.sub(cpl, U32.add(val, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), ts, U32.add(seg, U32.add(val, c))), tt, U32.add(pos, c))), S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), tt, U32.add(w0, U32.sub(U32.add(val, c), cpl))), tt, U32.add(pos, c))), Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(size, c)), V.U.N(U32.add(seg, U32.add(val, c)))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.add(val, c), cpl))), V.U.N(U32.add(pos, c)))))) == True{} : Bool}
      EM_.EM.and2(S.S.has(S.S.sl(V.U.N(U32.sub(size, c)), tt, U32.add(w0, U32.sub(U32.add(val, c), cpl))), tt, U32.add(pos, c)), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(U32.add(val, c), cpl))), V.U.N(U32.add(pos, c)))),
        EI.s.thas(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, (%e0 : {Bool.pick(Bool, _, Bool.and(U32.is_le(size, U32.sub(cpl, val)), S.S.has(S.S.sl(V.U.N(size), ts, U32.add(seg, val)), tt, pos)), S.S.has(S.S.sl(V.U.N(size), tt, U32.add(w0, U32.sub(val, cpl))), tt, pos)) == True{} : Bool}; hcp)),
        EI.s.tcb(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, hlo, hpos, hc, (%e0 : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(size), V.U.N(U32.add(seg, val))), V.U.N(Es))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(w0, U32.sub(val, cpl))), V.U.N(pos)))) == True{} : Bool}; hcb)))

# Cutting the first c bytes off a match leaves a match.
law EI.suf:
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
  for +size: U32
  for +val: U32
  for +c: U32
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hc: {U32.is_lt(c, size) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, c), U32.sub(size, c), N.u32.pick(run, val, U32.add(val, c))) == True{} : Bool}

def EI.suf(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, size, val, c, hH, hc, hok):
  match run:
    case True{}:
      EM_.EM.and2(U32.is_le(w0, U32.add(pos, c)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(size, c))), V.U.N(w1))), S.S.has(C.CP.rep(V.U.N(U32.sub(size, c)), val), tt, U32.add(pos, c))),
        EI.s.lo1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, True{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, True{}, pos, size, val, hok), hc),
        EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(size, c))), V.U.N(w1))), S.S.has(C.CP.rep(V.U.N(U32.sub(size, c)), val), tt, U32.add(pos, c)),
          EI.s.hiN(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, True{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, True{}, pos, size, val, hok), hc),
          EI.rep_suf(c, size, val, tt, pos, V.U.lt_to_le(c, size, hc), EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, True{}, pos, size, val, hok))))
    case False{}:
      EM_.EM.and2(U32.is_le(w0, U32.add(pos, c)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(size, c))), V.U.N(w1))), Bool.and(U32.is_lt(U32.add(val, c), U32.add(cpl, U32.sub(U32.add(pos, c), w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c)), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c), Es)))),
        EI.s.lo1(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), hc),
        EM_.EM.and2(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(pos, c)), V.U.N(U32.sub(size, c))), V.U.N(w1))), Bool.and(U32.is_lt(U32.add(val, c), U32.add(cpl, U32.sub(U32.add(pos, c), w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c)), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c), Es))),
          EI.s.hiN(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), hc),
          EM_.EM.and2(U32.is_lt(U32.add(val, c), U32.add(cpl, U32.sub(U32.add(pos, c), w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c)), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, U32.add(pos, c), U32.sub(size, c), U32.add(val, c), Es)),
            EI.s.lt(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), hc, P.Bool.and_l(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es)), EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok))),
            EI.suf.cc(ts, tt, seg, cpl, w0, w1, Es, HB, pos, size, val, c, hH, EI.eok.lo(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok), hc, P.Bool.and_l(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es)), EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok)), U32.is_lt(val, cpl), {==}, P.Bool.and_l(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es), P.Bool.and_r(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es)), EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok))), P.Bool.and_r(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es), P.Bool.and_r(U32.is_lt(val, U32.add(cpl, U32.sub(pos, w0))), Bool.and(Q.SP.cpok(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val), Q.SP.cbnd(Q.XC{ts, tt, seg, cpl, w0, w1}, pos, size, val, Es)), EI.eok.k(ts, tt, seg, cpl, w0, w1, Es, False{}, pos, size, val, hok)))))))

# Writing a match
# ===============

law EI.cut_ge.c:
  for +pos: U32
  for +u: U32
  for +b: Bool
  for +eb: {U32.is_lt(pos, u) == b : Bool}
  {U32.is_le(u, U32.add(pos, N.u32.pick(b, U32.sub(u, pos), 0))) == True{} : Bool}

def EI.cut_ge.c(pos, u, b, eb):
  match b:
    case True{}:
      %Equal.sym(U32, U32.add(pos, U32.sub(u, pos)), u, EM_.EM.addsub(pos, u)) :
        {U32.is_le(u, _) == True{} : Bool}
      V.U.N_le(u, u, C.CP.le_refl(V.U.N(u)))
    case False{}:
      %Equal.sym(U32, U32.add(pos, 0), pos, V.U.add_zero_r(pos)) :
        {U32.is_le(u, _) == True{} : Bool}
      V.U.not_lt(pos, u, eb)

# A match cut to start at u starts at or after u.
law EI.cut_ge:
  for +pos: U32
  for +u: U32
  {U32.is_le(u, U32.add(pos, EM_.EM.cut(pos, u))) == True{} : Bool}

def EI.cut_ge(pos, u):
  EI.cut_ge.c(pos, u, U32.is_lt(pos, u), {==})

def EI.ggo(+run: Bool, +pos: U32, +size: U32, +val: U32, +here: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match run:
    case True{}:
      EI.grun(size, val, e, g)
    case False{}:
      EI.gcopy(size, val, here, e, g)

def EI.gif(+z: Bool, +tt: A.Tr, +run: Bool, +pos: U32, +size: U32, +val: U32, +cpl: U32, +w0: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match z:
    case True{}:
      EI.ggo(run, pos, size, val, U32.add(cpl, U32.sub(pos, w0)), EM_.EM.gap(tt, pos, e), EI.ggap(tt, pos, e, g))
    case False{}:
      g

def EI.ginst(+tt: A.Tr, +run: Bool, +pos: U32, +size: U32, +val: U32, +cpl: U32, +w0: U32, +e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  EI.gif(U32.is_lt(EM_.EM.cut(pos, EM_.EM.uo(e)), size), tt, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), cpl, w0, e, g)

law EI.igo:
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
  for +size: U32
  for +val: U32
  for +hu: {EM_.EM.uo(e) == pos : U32}
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  for +hsz: {Cmp.is_le(Nat.cmp(1n, V.U.N(size))) == True{} : Bool}
  EI.J(EM_.EM.igo(run, pos, size, val, U32.add(cpl, U32.sub(pos, w0)), e), EI.ggo(run, pos, size, val, U32.add(cpl, U32.sub(pos, w0)), e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.igo(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, pos, size, val, hu, hJ, hwok, hok, hsz):
  match run:
    case True{}:
      %hu : EI.J(EM_.EM.run(_, size, val, e), EI.grun(size, val, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
      EI.run(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, val, hJ, hwok, (%Equal.sym(U32, EM_.EM.uo(e), pos, hu) : {EI.eok(ts, tt, seg, cpl, w0, w1, Es, True{}, _, size, val) == True{} : Bool}; hok), hsz)
    case False{}:
      %hu : EI.J(EM_.EM.copy(_, size, val, U32.add(cpl, U32.sub(_, w0)), e), EI.gcopy(size, val, U32.add(cpl, U32.sub(_, w0)), e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
      EI.copy(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, size, val, hJ, hwok, (%Equal.sym(U32, EM_.EM.uo(e), pos, hu) : {EI.eok(ts, tt, seg, cpl, w0, w1, Es, False{}, _, size, val) == True{} : Bool}; hok), hsz)

law EI.inst.c:
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
  for +size: U32
  for +val: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(EM_.EM.cut(pos, EM_.EM.uo(e)), size) == z : Bool}
  EI.J(EM_.EM.iif(z, tt, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), cpl, w0, e), EI.gif(z, tt, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.inst.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, size, val, hJ, hwok, hH, hok, z, ez):
  match z:
    case True{}:
      EI.igo(EM_.EM.gap(tt, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), e), EI.ggap(tt, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), e, g), ts, tt, seg, cpl, w0, w1, E, Es, BIG, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))),
        EI.uo_gap(tt, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), e, EI.cut_ge(pos, EM_.EM.uo(e))),
        EI.gap(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), hJ, hwok, P.Nat.le_trans(V.U.N(U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e)))), Nat.add(V.U.N(U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e)))), V.U.N(U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))))), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e)))), V.U.N(U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))))), EI.eok.hi(ts, tt, seg, cpl, w0, w1, Es, run, U32.add(pos, EM_.EM.cut(pos, EM_.EM.uo(e))), U32.sub(size, EM_.EM.cut(pos, EM_.EM.uo(e))), N.u32.pick(run, val, U32.add(val, EM_.EM.cut(pos, EM_.EM.uo(e)))), EI.suf(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, size, val, EM_.EM.cut(pos, EM_.EM.uo(e)), hH, ez, hok)))),
        hwok,
        EI.suf(ts, tt, seg, cpl, w0, w1, Es, HB, run, pos, size, val, EM_.EM.cut(pos, EM_.EM.uo(e)), hH, ez, hok),
        EI.sub_pos(EM_.EM.cut(pos, EM_.EM.uo(e)), size, ez))
    case False{}:
      hJ

# em.inst writes a match, cut to start at the bytes not yet written.
law EI.inst:
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
  for +size: U32
  for +val: U32
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(cpl), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hok: {EI.eok(ts, tt, seg, cpl, w0, w1, Es, run, pos, size, val) == True{} : Bool}
  EI.J(EM_.EM.inst(tt, run, pos, size, val, cpl, w0, e), EI.ginst(tt, run, pos, size, val, cpl, w0, e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})

def EI.inst(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, size, val, hJ, hwok, hH, hok):
  EI.inst.c(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, HB, run, pos, size, val, hJ, hwok, hH, hok, U32.is_lt(EM_.EM.cut(pos, EM_.EM.uo(e)), size), {==})

# A window's end
# ==============

# What the window's sections and halves are once nothing is pending: the
# sections hold the instructions ops, which rebuild the target up to
# uoff, and the sections' sizes are bounded.
def EI.F(+e: EM_.ET, +g: EM_.EG, +w: EM_.EW) -> Bool:
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      Bool.and(EM_.EM.S1(e, Q.SP.halves(ops)), Bool.and(EM_.EM.S2(e, ops), Bool.and(EM_.EM.S3(e, Q.SP.halves(ops)), Bool.and(EM_.EM.V(Q.SP.halves(ops), ops, w),
      Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)),
      Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(w), EM_.EM.s0(w)))),
      Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(w))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(w)))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(w)))))))))))))))))))

def EI.gfl(+e: EM_.ET, +g: EM_.EG) -> EM_.EG:
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      EM_.EM.gqs(U32.is_ne(pt, 0), ops, ph, Q.HN{}, pc, dd, di, da)

law EI.hv_fl:
  for +ops: List<&2, Q.OP>
  for +ph: Q.HF
  for +pc: U32
  for +hp: {EM_.EM.pend(ph) == ph <> [] : List<&2, Q.HF>}
  {Q.SP.halves(EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])) == EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []) : List<&2, Q.HF>}

def EI.hv_fl(ops, ph, pc, hp):
  %Equal.sym(List<&2, Q.HF>, Q.SP.halves(EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])), EM_.EM.happ(Q.SP.halves(ops), Q.SP.halves(Q.OP{pc, ph, Q.HN{}} <> [])), EM_.EM.halves_app(ops, Q.OP{pc, ph, Q.HN{}} <> [])) :
    {_ == EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []) : List<&2, Q.HF>}
  %Equal.sym(List<&2, Q.HF>, EM_.EM.pend(ph), ph <> [], hp) :
    {EM_.EM.happ(Q.SP.halves(ops), Q.SP.halves(Q.OP{pc, ph, Q.HN{}} <> [])) == EM_.EM.happ(EM_.EM.happ(Q.SP.halves(ops), _), Q.HN{} <> []) : List<&2, Q.HF>}
  %Equal.sym(List<&2, Q.HF>, EM_.EM.happ(EM_.EM.happ(Q.SP.halves(ops), ph <> []), Q.HN{} <> []), EM_.EM.happ(Q.SP.halves(ops), EM_.EM.happ(ph <> [], Q.HN{} <> [])), EM_.EM.happ_assoc(Q.SP.halves(ops), ph <> [], Q.HN{} <> [])) :
    {EM_.EM.happ(Q.SP.halves(ops), Q.SP.halves(Q.OP{pc, ph, Q.HN{}} <> [])) == _ : List<&2, Q.HF>}
  {==}

law EI.fl.k:
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
  for +r: EM_.TI
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hp: {EM_.EM.pend(ph) == ph <> [] : List<&2, Q.HF>}
  for +hcok: {Q.SP.cok(A.A.to(D.ct.table()), Q.OP{pc, ph, Q.HN{}}) == True{} : Bool}
  for +hrsec: {Bool.and(S.S.has(K.WD.app(Q.SP.insl(ops), Q.SP.ins(Q.OP{pc, ph, Q.HN{}})), EM_.EM.tit(r), 0), Q.SP.lenis(K.WD.app(Q.SP.insl(ops), Q.SP.ins(Q.OP{pc, ph, Q.HN{}})), EM_.EM.tin(r))) == True{} : Bool}
  for +hrpf: {A.T.pf(di, EM_.EM.tit(r)) == True{} : Bool}
  for +hrle: {Cmp.is_le(Nat.cmp(V.U.N(EM_.EM.tin(r)), Nat.add(V.U.N(il), 6n))) == True{} : Bool}
  {EI.F(EM_.EM.flk(td, ta, tc, dl, al, slot, uoff, r), EM_.EG{EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), Q.HN{}, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

law EI.fl.s1:
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
  for +ti2: A.Tr
  for +il2: U32
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  {EM_.EM.S1(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])) == True{} : Bool}

def EI.fl.s1(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, ti2, il2, hinv):
  %Equal.sym(List<&2, U32>, Q.SP.datl(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), K.WD.app(Q.SP.datl(EM_.EM.hs(ops, ph)), Q.SP.dat(Q.HN{})), EM_.EM.datl1(EM_.EM.hs(ops, ph), Q.HN{})) :
    {Bool.and(S.S.has(_, td, 0), Q.SP.lenis(_, dl)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, K.WD.app(Q.SP.datl(EM_.EM.hs(ops, ph)), []), Q.SP.datl(EM_.EM.hs(ops, ph)), K.WD.app_nil(Q.SP.datl(EM_.EM.hs(ops, ph)))) :
    {Bool.and(S.S.has(_, td, 0), Q.SP.lenis(_, dl)) == True{} : Bool}
  EM_.EM.inv.s1(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)

law EI.fl.s3:
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
  for +ti2: A.Tr
  for +il2: U32
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  {EM_.EM.S3(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])) == True{} : Bool}

def EI.fl.s3(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, ti2, il2, hinv):
  %Equal.sym(List<&2, U32>, Q.SP.adrl(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), K.WD.app(Q.SP.adrl(EM_.EM.hs(ops, ph)), Q.SP.adr(Q.HN{})), EM_.EM.adrl1(EM_.EM.hs(ops, ph), Q.HN{})) :
    {Bool.and(S.S.has(_, ta, 0), Q.SP.lenis(_, al)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, K.WD.app(Q.SP.adrl(EM_.EM.hs(ops, ph)), []), Q.SP.adrl(EM_.EM.hs(ops, ph)), K.WD.app_nil(Q.SP.adrl(EM_.EM.hs(ops, ph)))) :
    {Bool.and(S.S.has(_, ta, 0), Q.SP.lenis(_, al)) == True{} : Bool}
  EM_.EM.inv.s3(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)

law EI.fl.s2:
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
  for +pc2: U32
  for +ph: Q.HF
  for +ti2: A.Tr
  for +il2: U32
  for +hsec: {Bool.and(S.S.has(K.WD.app(Q.SP.insl(ops), Q.SP.ins(Q.OP{pc2, ph, Q.HN{}})), ti2, 0), Q.SP.lenis(K.WD.app(Q.SP.insl(ops), Q.SP.ins(Q.OP{pc2, ph, Q.HN{}})), il2)) == True{} : Bool}
  {EM_.EM.S2(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.oapp(ops, Q.OP{pc2, ph, Q.HN{}} <> [])) == True{} : Bool}

def EI.fl.s2(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, pc2, ph, ti2, il2, hsec):
  %Equal.sym(List<&2, U32>, Q.SP.insl(EM_.EM.oapp(ops, Q.OP{pc2, ph, Q.HN{}} <> [])), K.WD.app(Q.SP.insl(ops), Q.SP.insl(Q.OP{pc2, ph, Q.HN{}} <> [])), EM_.EM.insl_app(ops, Q.OP{pc2, ph, Q.HN{}} <> [])) :
    {Bool.and(S.S.has(_, ti2, 0), Q.SP.lenis(_, il2)) == True{} : Bool}
  %Equal.sym(List<&2, U32>, K.WD.app(Q.SP.ins(Q.OP{pc2, ph, Q.HN{}}), []), Q.SP.ins(Q.OP{pc2, ph, Q.HN{}}), K.WD.app_nil(Q.SP.ins(Q.OP{pc2, ph, Q.HN{}}))) :
    {Bool.and(S.S.has(K.WD.app(Q.SP.insl(ops), _), ti2, 0), Q.SP.lenis(K.WD.app(Q.SP.insl(ops), _), il2)) == True{} : Bool}
  hsec

law EI.fl.uo:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  {U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))) == True{} : Bool}

def EI.fl.uo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv):
  %Equal.sym(Q.ST, Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Q.SP.next(EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Q.HN{}), EM_.EM.run1(EM_.EM.hs(ops, ph), Q.HN{}, EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))) :
    {U32.is_eq(uoff, Q.SP.so(_)) == True{} : Bool}
  %Equal.sym(Q.ST, Q.SP.next(EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Q.HN{}), Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), EM_.EM.next_hn(EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))) :
    {U32.is_eq(uoff, Q.SP.so(_)) == True{} : Bool}
  EM_.EM.R.uo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))

law EI.fl.v:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hcok: {Q.SP.cok(A.A.to(D.ct.table()), Q.OP{pc, ph, Q.HN{}}) == True{} : Bool}
  {EM_.EM.V(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, hcok):
  %Equal.sym(Bool, Q.SP.coks(EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), A.A.to(D.ct.table())), Bool.and(Q.SP.coks(ops, A.A.to(D.ct.table())), Q.SP.coks(Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table()))), EM_.EM.coks_app(ops, Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table()))) :
    {Bool.and(Q.SP.vhs(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), _))) == True{} : Bool}
  EM_.EM.and2(Q.SP.vhs(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(Q.SP.coks(ops, A.A.to(D.ct.table())), Q.SP.coks(Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table()))))), EM_.EM.vhs1(EM_.EM.hs(ops, ph), Q.HN{}, Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.V.v(EM_.EM.hs(ops, ph), ops, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.vst_hn(Q.XC{ts, tt, seg, cpl, w0, w1}, Q.SP.run(EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), EM_.EM.and2(Q.SP.bnds(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(Q.SP.coks(ops, A.A.to(D.ct.table())), Q.SP.coks(Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table())))), EM_.EM.bnds1(EM_.EM.hs(ops, ph), Q.HN{}, Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es, EM_.EM.V.b(EM_.EM.hs(ops, ph), ops, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), (%Equal.sym(Bool, Q.SP.bnd(Q.XC{ts, tt, seg, cpl, w0, w1}, Q.SP.run(EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Q.HN{}, E, Es), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(Q.SP.so(Q.SP.run(EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), V.U.N(E))), True{}), EM_.EM.bnd_hn(Q.XC{ts, tt, seg, cpl, w0, w1}, Q.SP.run(EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), E, Es)) : {_ == True{} : Bool}; EM_.EM.and2(Cmp.is_le(Nat.cmp(V.U.N(Q.SP.so(Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), V.U.N(E))), True{}, P.Nat.le_trans(V.U.N(Q.SP.so(Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), V.U.N(w1), V.U.N(E), (%V.U.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.hs(ops, ph), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))), EM_.EM.R.uo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))) : {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(w1))) == True{} : Bool}; V.U.le_N(uoff, w1, EM_.EM.R.hi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))), EM_.EM.wok.e(Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hwok)), {==}))), EM_.EM.and2(Q.SP.doks(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(Q.SP.coks(ops, A.A.to(D.ct.table())), Q.SP.coks(Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table()))), EM_.EM.doks1(EM_.EM.hs(ops, ph), Q.HN{}, EM_.EM.V.d(EM_.EM.hs(ops, ph), ops, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), {==}), EM_.EM.and2(Q.SP.coks(ops, A.A.to(D.ct.table())), Q.SP.coks(Q.OP{pc, ph, Q.HN{}} <> [], A.A.to(D.ct.table())), EM_.EM.V.c(EM_.EM.hs(ops, ph), ops, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Q.SP.cok(A.A.to(D.ct.table()), Q.OP{pc, ph, Q.HN{}}), True{}, hcok, {==})))))

def EI.fl.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, r, hinv, hwok, hp, hcok, hrsec, hrpf, hrle):
  match r:
    case EM_.TI{ti2, il2}:
      %Equal.sym(List<&2, Q.HF>, Q.SP.halves(EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])), EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EI.hv_fl(ops, ph, pc, hp)) :
        {Bool.and(EM_.EM.S1(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, _), Bool.and(EM_.EM.S2(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])), Bool.and(EM_.EM.S3(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, _), Bool.and(EM_.EM.V(_, EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(_, EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))))))))) == True{} : Bool}
      EM_.EM.and2(EM_.EM.S1(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(EM_.EM.S2(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])), Bool.and(EM_.EM.S3(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(EM_.EM.V(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))))))), EI.fl.s1(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, ti2, il2, hinv), EM_.EM.and2(EM_.EM.S2(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> [])), Bool.and(EM_.EM.S3(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(EM_.EM.V(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))))))), EI.fl.s2(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, pc, ph, ti2, il2, hrsec), EM_.EM.and2(EM_.EM.S3(EM_.ET{td, ti2, ta, tc, dl, il2, al, slot, uoff, 0, 0, 0, 0}, EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> [])), Bool.and(EM_.EM.V(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))))), EI.fl.s3(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, ti2, il2, hinv), EM_.EM.and2(EM_.EM.V(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.oapp(ops, Q.OP{pc, ph, Q.HN{}} <> []), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))))), EI.fl.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, hcok), EM_.EM.and2(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))), EM_.EM.P.pd(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))), EM_.EM.P.dd(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(A.T.pf(di, ti2), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))), hrpf, EM_.EM.and2(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))), EM_.EM.P.di(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))), EM_.EM.P.pa(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))), EM_.EM.P.da(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(U32.is_eq(uoff, Q.SP.so(Q.SP.run(EM_.EM.happ(EM_.EM.hs(ops, ph), Q.HN{} <> []), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))), EI.fl.uo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv), EM_.EM.and2(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))), EM_.EM.R.dl(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_le(Nat.cmp(V.U.N(il2), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), P.Nat.le_trans(V.U.N(il2), Nat.add(V.U.N(il), 6n), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n), hrle, C.CP.le_add_r(V.U.N(il), Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n, EM_.EM.R.il(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))), EM_.EM.R.al(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, ph), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))))))))))))))

law EI.le6:
  for +il: U32
  for +vl: U32
  for +q: Nat
  for +BIG: U32
  for +hvl: {Cmp.is_le(Nat.cmp(V.U.N(vl), 5n)) == True{} : Bool}
  for +hq: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(il), 6n), q)) == True{} : Bool}
  for +hB: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(il), 12n), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(il, 1)), V.U.N(vl)), q)) == True{} : Bool}

def EI.le6(il, vl, q, BIG, hvl, hq, hB):
  %Equal.sym(Nat, V.U.N(U32.add(il, 1)), Nat.add(V.U.N(il), 1n), V.U.add_N(il, 1, BIG, EM_.EM.le_k(V.U.N(il), 1n, 12n, V.U.N(BIG), {==}, hB))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(vl)), q)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(V.U.N(il), 1n), V.U.N(vl)), Nat.add(V.U.N(il), Nat.add(1n, V.U.N(vl))), P.Nat.add_assoc(V.U.N(il), 1n, V.U.N(vl))) :
    {Cmp.is_le(Nat.cmp(_, q)) == True{} : Bool}
  EM_.EM.le_k(V.U.N(il), Nat.add(1n, V.U.N(vl)), 6n, q, hvl, hq)

# The pending half written alone, with room for 6 bytes.
law EI.sgi.sec6:
  for +z: Bool
  for +ps: U32
  for +pc: U32
  for +ti: A.Tr
  for +il: U32
  for +di: Nat
  for +BIG: U32
  for +L: List<&2, U32>
  for +ph: Q.HF
  for +ez: {N.op.sized(pc) == z : Bool}
  for +hzs: {Bool.or(Bool.and(Q.SP.z(Q.SP.e1(pc)), N.op.sized(pc)), Bool.and(Bool.not(Q.SP.z(Q.SP.e1(pc))), Bool.not(N.op.sized(pc)))) == True{} : Bool}
  for +hz2: {Bool.not(Q.SP.z(Q.SP.e2(pc))) == True{} : Bool}
  for +hps: {ps == Q.SP.size(ph) : U32}
  for +hpf: {A.T.pf(di, ti) == True{} : Bool}
  for +hdi: {Nat.cmp(di, 32n) == LT{} : Cmp}
  for +hh: {S.S.has(L, ti, 0) == True{} : Bool}
  for +hl: {Q.SP.lenis(L, il) == True{} : Bool}
  for +hP6: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(il), 6n), EM_.EM.cap(di))) == True{} : Bool}
  for +hB: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(il), 12n), V.U.N(BIG))) == True{} : Bool}
  {Bool.and(S.S.has(K.WD.app(L, Q.SP.ins(Q.OP{pc, ph, Q.HN{}})), EM_.EM.tit(EM_.EM.sgi(z, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))), 0), Q.SP.lenis(K.WD.app(L, Q.SP.ins(Q.OP{pc, ph, Q.HN{}})), EM_.EM.tin(EM_.EM.sgi(z, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))))) == True{} : Bool}

def EI.sgi.sec6(z, ps, pc, ti, il, di, BIG, L, ph, ez, hzs, hz2, hps, hpf, hdi, hh, hl, hP6, hB):
  match z:
    case True{}:
      %Equal.sym(List<&2, U32>, Q.SP.ins(Q.OP{pc, ph, Q.HN{}}), K.WD.app(pc <> [], R.VI.var(ps)), EM_.EM.ins_sg.t(pc, ph, ps, EM_.EM.zs_t(Q.SP.z(Q.SP.e1(pc)), N.op.sized(pc), hzs, ez), hz2, hps)) :
        {Bool.and(S.S.has(K.WD.app(L, _), EM_.EM.tit(EM_.EM.sgi(True{}, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))), 0), Q.SP.lenis(K.WD.app(L, _), EM_.EM.tin(EM_.EM.sgi(True{}, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))))) == True{} : Bool}
      %K.WD.app_assoc(L, pc <> [], R.VI.var(ps)) :
        {Bool.and(S.S.has(_, S.S.puts(R.VI.var(ps), Y.BP.put(ti, il, pc), U32.add(il, 1)), 0), Q.SP.lenis(_, U32.add(U32.add(il, 1), B.B.var.len(ps)))) == True{} : Bool}
      EM_.EM.secw(di, K.WD.app(L, pc <> []), R.VI.var(ps), Y.BP.put(ti, il, pc), U32.add(il, 1), B.B.var.len(ps), BIG,
        A.T.pf_set(di, ti, U32.shrn(il, 2n), Y.BP.ins(A.T.word(ti, U32.shrn(il, 2n)), B.B.sh(il), pc), hpf), hdi,
        P.Bool.and_l(S.S.has(K.WD.app(L, pc <> []), S.S.puts(pc <> [], ti, il), 0), Q.SP.lenis(K.WD.app(L, pc <> []), U32.add(il, 1)), EM_.EM.secw(di, L, pc <> [], ti, il, 1, BIG, hpf, hdi, hh, hl, {==}, EM_.EM.le_k(V.U.N(il), 1n, 6n, EM_.EM.cap(di), {==}, hP6), EM_.EM.le_k(V.U.N(il), 1n, 12n, V.U.N(BIG), {==}, hB))), P.Bool.and_r(S.S.has(K.WD.app(L, pc <> []), S.S.puts(pc <> [], ti, il), 0), Q.SP.lenis(K.WD.app(L, pc <> []), U32.add(il, 1)), EM_.EM.secw(di, L, pc <> [], ti, il, 1, BIG, hpf, hdi, hh, hl, {==}, EM_.EM.le_k(V.U.N(il), 1n, 6n, EM_.EM.cap(di), {==}, hP6), EM_.EM.le_k(V.U.N(il), 1n, 12n, V.U.N(BIG), {==}, hB))), R.VI.len_var(ps),
        EI.le6(il, B.B.var.len(ps), EM_.EM.cap(di), BIG, EM_.EM.vl5(ps), hP6, hB), EM_.EM.le12(il, B.B.var.len(ps), V.U.N(BIG), BIG, EM_.EM.vl5(ps), hB, hB))
    case False{}:
      %Equal.sym(List<&2, U32>, Q.SP.ins(Q.OP{pc, ph, Q.HN{}}), pc <> [], EM_.EM.ins_sg.f(pc, ph, EM_.EM.zs_f(Q.SP.z(Q.SP.e1(pc)), N.op.sized(pc), hzs, ez), hz2)) :
        {Bool.and(S.S.has(K.WD.app(L, _), EM_.EM.tit(EM_.EM.sgi(False{}, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))), 0), Q.SP.lenis(K.WD.app(L, _), EM_.EM.tin(EM_.EM.sgi(False{}, ps, Y.BP.put(ti, il, pc), U32.add(il, 1))))) == True{} : Bool}
      EM_.EM.secw(di, L, pc <> [], ti, il, 1, BIG, hpf, hdi, hh, hl, {==}, EM_.EM.le_k(V.U.N(il), 1n, 6n, EM_.EM.cap(di), {==}, hP6), EM_.EM.le_k(V.U.N(il), 1n, 12n, V.U.N(BIG), {==}, hB))

law EI.fl.t:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hne: {U32.is_ne(pt, 0) == True{} : Bool}
  {EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, hne):
  %Equal.sym(Bool, U32.is_ne(pt, 0), True{}, hne) :
    {EI.F(EM_.EM.flk(td, ta, tc, dl, al, slot, uoff, EM_.EM.sgo(_, ps, pc, ti, il)), EM_.EM.gqs(_, ops, ph, Q.HN{}, pc, dd, di, da), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  EI.fl.k(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, EM_.EM.sgi(N.op.sized(pc), ps, Y.BP.put(ti, il, pc), U32.add(il, 1)), hinv, hwok,
    EM_.EM.pend_ne(ph, pt, V.U.is_eq(pt, Q.SP.kind(ph), EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), hne),
    EM_.EM.cok_sg(pc, ph, pt, ps, pm, V.U.is_eq(pt, Q.SP.kind(ph), EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(ps, Q.SP.size(ph), EM_.EM.D.s(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(pm, Q.SP.mode(ph), EM_.EM.D.m(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(pc, N.op.single(pt, ps, pm), (%EM_.EM.notT(U32.is_eq(pt, 0), hne) : {Bool.or(_, U32.is_eq(pc, N.op.single(pt, ps, pm))) == True{} : Bool}; EM_.EM.D.c(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))), EM_.EM.cs_ph(ph, pt, ps, pm, V.U.is_eq(pt, Q.SP.kind(ph), EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(ps, Q.SP.size(ph), EM_.EM.D.s(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(pm, Q.SP.mode(ph), EM_.EM.D.m(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.D.m8(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), hne)),
    EI.sgi.sec6(N.op.sized(pc), ps, pc, ti, il, di, BIG, Q.SP.insl(ops), ph, {==}, EM_.EM.CS.z1(pc, pt, ps, pm, (%Equal.sym(U32, pc, N.op.single(pt, ps, pm), V.U.is_eq(pc, N.op.single(pt, ps, pm), (%EM_.EM.notT(U32.is_eq(pt, 0), hne) : {Bool.or(_, U32.is_eq(pc, N.op.single(pt, ps, pm))) == True{} : Bool}; EM_.EM.D.c(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))) : {T.CT.S(_, pt, ps, pm) == True{} : Bool}; EM_.EM.cs_ph(ph, pt, ps, pm, V.U.is_eq(pt, Q.SP.kind(ph), EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(ps, Q.SP.size(ph), EM_.EM.D.s(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(pm, Q.SP.mode(ph), EM_.EM.D.m(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.D.m8(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), hne))), EM_.EM.CS.z2(pc, pt, ps, pm, (%Equal.sym(U32, pc, N.op.single(pt, ps, pm), V.U.is_eq(pc, N.op.single(pt, ps, pm), (%EM_.EM.notT(U32.is_eq(pt, 0), hne) : {Bool.or(_, U32.is_eq(pc, N.op.single(pt, ps, pm))) == True{} : Bool}; EM_.EM.D.c(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))) : {T.CT.S(_, pt, ps, pm) == True{} : Bool}; EM_.EM.cs_ph(ph, pt, ps, pm, V.U.is_eq(pt, Q.SP.kind(ph), EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(ps, Q.SP.size(ph), EM_.EM.D.s(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), V.U.is_eq(pm, Q.SP.mode(ph), EM_.EM.D.m(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.D.m8(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), hne))), V.U.is_eq(ps, Q.SP.size(ph), EM_.EM.D.s(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ph, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.P.pi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.lt32(di, EM_.EM.P.di(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.S2.h(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, EM_.EM.inv.s2(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.S2.l(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, EM_.EM.inv.s2(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.P.room(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.bil(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok)),
    EM_.EM.sgi.pf(N.op.sized(pc), ps, pc, ti, il, di, EM_.EM.P.pi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))),
    EM_.EM.sgi.le(N.op.sized(pc), ps, pc, ti, il, BIG, EM_.EM.bil(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok)))

law EI.notF:
  for +b: Bool
  for +h: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}

def EI.notF(b, h):
  match b:
    case True{}:
      {==}
    case False{}:
      P.Bool.false_true({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

# Nothing pending: the sections already hold the instructions.
law EI.fl.n:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, Q.HN{}, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  {EI.F(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, EM_.EG{ops, Q.HN{}, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl.n(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv):
  EM_.EM.and2(EM_.EM.S1(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, Q.SP.halves(ops)), Bool.and(EM_.EM.S2(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, ops), Bool.and(EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, Q.SP.halves(ops)), Bool.and(EM_.EM.V(Q.SP.halves(ops), ops, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))))))), (%EM_.EM.happ_nil(Q.SP.halves(ops)) : {EM_.EM.S1(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, _) == True{} : Bool}; EM_.EM.inv.s1(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(EM_.EM.S2(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, ops), Bool.and(EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, Q.SP.halves(ops)), Bool.and(EM_.EM.V(Q.SP.halves(ops), ops, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))))))), EM_.EM.inv.s2(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv), EM_.EM.and2(EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, Q.SP.halves(ops)), Bool.and(EM_.EM.V(Q.SP.halves(ops), ops, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))))), (%EM_.EM.happ_nil(Q.SP.halves(ops)) : {EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, 0, 0, 0, 0}, _) == True{} : Bool}; EM_.EM.inv.s3(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(EM_.EM.V(Q.SP.halves(ops), ops, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), Bool.and(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))))), (%EM_.EM.happ_nil(Q.SP.halves(ops)) : {EM_.EM.V(_, ops, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}; EM_.EM.inv.v(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(A.T.pf(dd, td), Bool.and(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))))), EM_.EM.P.pd(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_lt(Nat.cmp(dd, 32n)), Bool.and(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))))), EM_.EM.P.dd(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(A.T.pf(di, ti), Bool.and(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))))), EM_.EM.P.pi(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_lt(Nat.cmp(di, 32n)), Bool.and(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))))), EM_.EM.P.di(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(A.T.pf(da, ta), Bool.and(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))))), EM_.EM.P.pa(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_lt(Nat.cmp(da, 32n)), Bool.and(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))))), EM_.EM.P.da(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, EM_.EM.inv.p(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(U32.is_eq(uoff, Q.SP.so(Q.SP.run(Q.SP.halves(ops), EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))))), (%EM_.EM.happ_nil(Q.SP.halves(ops)) : {U32.is_eq(uoff, Q.SP.so(Q.SP.run(_, EM_.EM.x(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))) == True{} : Bool}; EM_.EM.R.uo(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))), EM_.EM.and2(Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}))))))), EM_.EM.R.dl(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), EM_.EM.and2(Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n))), Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), P.Nat.le_trans(V.U.N(il), Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n), EM_.EM.R.il(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)), P.Nat.cmp_add_r(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(uoff, EM_.EM.w0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))))), 6n)), EM_.EM.R.al(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, EM_.EM.hs(ops, Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, EM_.EM.inv.r(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HN{}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv)))))))))))))))

law EI.fl.f:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hz: {U32.is_ne(pt, 0) == False{} : Bool}
  {EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl.f(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hz):
  match ph:
    case Q.HN{}:
      %Equal.sym(Bool, U32.is_ne(pt, 0), False{}, hz) :
        {EI.F(EM_.EM.flk(td, ta, tc, dl, al, slot, uoff, EM_.EM.sgo(_, ps, pc, ti, il)), EM_.EM.gqs(_, ops, Q.HN{}, Q.HN{}, pc, dd, di, da), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
      EI.fl.n(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv)
    case Q.HA{n, xs}:
      P.Bool.false_true({EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, Q.HA{n, xs}, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}, (%V.U.is_eq(pt, 0, EI.notF(U32.is_eq(pt, 0), hz)) : {U32.is_eq(_, Q.SP.kind(Q.HA{n, xs})) == True{} : Bool}; EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, Q.HA{n, xs}, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HA{n, xs}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))
    case Q.HR{n, b}:
      P.Bool.false_true({EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, Q.HR{n, b}, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}, (%V.U.is_eq(pt, 0, EI.notF(U32.is_eq(pt, 0), hz)) : {U32.is_eq(_, Q.SP.kind(Q.HR{n, b})) == True{} : Bool}; EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, Q.HR{n, b}, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HR{n, b}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))
    case Q.HC{n, m, v}:
      P.Bool.false_true({EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, Q.HC{n, m, v}, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}, (%V.U.is_eq(pt, 0, EI.notF(U32.is_eq(pt, 0), hz)) : {U32.is_eq(_, Q.SP.kind(Q.HC{n, m, v})) == True{} : Bool}; EM_.EM.D.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, Q.HC{n, m, v}, EM_.EM.inv.d(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, Q.HC{n, m, v}, dd, di, da, Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG, hinv))))

law EI.fl.c:
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
  for +hinv: {EM_.EM.inv(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_ne(pt, 0) == z : Bool}
  {EI.F(EM_.EM.fl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), EI.gfl(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl.c(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, z, ez):
  match z:
    case True{}:
      EI.fl.t(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, ez)
    case False{}:
      EI.fl.f(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, ez)

# em.flush writes the pending instruction: the window's sections are then
# whole.
law EI.fl:
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
  for hJ: EI.J(e, g, EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})
  for +hwok: {EM_.EM.wok(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}
  {EI.F(EM_.EM.fl(e), EI.gfl(e, g), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def EI.fl(e, g, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hJ, hwok):
  match e g hJ:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da} Tuple{+hinv, +hc}:
      EI.fl.c(td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, ops, ph, dd, di, da, ts, tt, seg, cpl, w0, w1, E, Es, BIG, hinv, hwok, U32.is_ne(pt, 0), {==})
