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

# The decoder (vcdiff.bend) on a window whose sections hold instructions
# as proofs/spec.bend writes them: each half of an opcode, then each
# opcode, then the instruction loop.
#
# Source: proofs/dec.bp (tools/bpp.py writes proofs/dec.bend from it).

# The decoder's state with its arrays as trees, and no error.
def DX.st(+ts: A.Tr, +td: A.Tr, +to: A.Tr, +tb: A.Tr, +ca: A.Tr, +opos: U32,
  +dpos: U32, +ipos: U32, +apos: U32, +slot: U32) -> D.Dec:
  D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0}

# Data
# ====

# Writing the bytes a tree holds is writing the list it holds.
law DX.puts_held:
  for +xs: List<&2, U32>
  for +rest: List<&2, U32>
  for +td: A.Tr
  for +q: U32
  for +to: A.Tr
  for +p: U32
  for +h: {S.S.has(K.WD.app(xs, rest), td, q) == True{} : Bool}
  {S.S.puts(S.S.sl(S.S.len(xs), td, q), to, p) == S.S.puts(xs, to, p) : A.Tr}

def DX.puts_held(xs, rest, td, q, to, p, h):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(U32, Y.BP.byt(td, q), U32.and(x, 255), V.U.is_eq(Y.BP.byt(td, q), U32.and(x, 255), P.Bool.and_l(U32.is_eq(Y.BP.byt(td, q), U32.and(x, 255)), S.S.has(K.WD.app(r, rest), td, U32.add(q, 1)), h))) :
        {S.S.puts(S.S.sl(S.S.len(r), td, U32.add(q, 1)), Y.BP.put(to, p, _), U32.add(p, 1)) == S.S.puts(r, Y.BP.put(to, p, x), U32.add(p, 1)) : A.Tr}
      %Equal.sym(A.Tr, Y.BP.put(to, p, U32.and(x, 255)), Y.BP.put(to, p, x), C.CP.put_mask(to, p, x)) :
        {S.S.puts(S.S.sl(S.S.len(r), td, U32.add(q, 1)), _, U32.add(p, 1)) == S.S.puts(r, Y.BP.put(to, p, x), U32.add(p, 1)) : A.Tr}
      %Equal.sym(A.Tr, S.S.puts(S.S.sl(S.S.len(r), td, U32.add(q, 1)), Y.BP.put(to, p, x), U32.add(p, 1)), S.S.puts(r, Y.BP.put(to, p, x), U32.add(p, 1)), DX.puts_held(r, rest, td, U32.add(q, 1), Y.BP.put(to, p, x), U32.add(p, 1), R.VI.tl(td, q, x, K.WD.app(r, rest), h))) :
        {_ == S.S.puts(r, Y.BP.put(to, p, x), U32.add(p, 1)) : A.Tr}
      {==}

law DX.cmp_eq_true:
  for +c: Cmp
  for +h: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def DX.cmp_eq_true(c, h):
  match c:
    case LT{}:
      P.Bool.false_true({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.false_true({GT{} == EQ{} : Cmp}, h)

# n = len(xs) when SP.lenis says so.
law DX.lenis:
  for +xs: List<&2, U32>
  for +n: U32
  for +h: {Q.SP.lenis(xs, n) == True{} : Bool}
  {U32.to_nat(n) == S.S.len(xs) : Nat}

def DX.lenis(xs, n, h):
  Equal.sym(Nat, S.S.len(xs), U32.to_nat(n), P.Nat.cmp_eq(S.S.len(xs), U32.to_nat(n), DX.cmp_eq_true(Nat.cmp(S.S.len(xs), U32.to_nat(n)), h)))

# Halves
# ======

# ADD: the data section's next bytes, to the target.
law DX.add:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +xs: List<&2, U32>
  for +rest: List<&2, U32>
  for +hd: {S.S.has(K.WD.app(xs, rest), td, dpos) == True{} : Bool}
  for +hl: {Q.SP.lenis(xs, n) == True{} : Bool}
  for +hdb: {U32.is_le(n, U32.sub(dend, dpos)) == True{} : Bool}
  for +hob: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  {D.dec.add(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, (n, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot) : D.Dec}

def DX.add(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, xs, rest, hd, hl, hdb, hob):
  %Equal.sym(Bool, U32.is_le(n, U32.sub(dend, dpos)), True{}, hdb) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, D.u32.pick(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), n, 0), Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), B.B.copy.bytes(U32.to_nat(D.u32.pick(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), n, 0)), A.A.from(to), opos, dpos, B.B.get(A.A.from(td), dpos))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Bool, U32.is_le(n, U32.sub(oend, opos)), True{}, hob) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, D.u32.pick(Bool.and(True{}, _), n, 0), Bool.and(True{}, _), B.B.copy.bytes(U32.to_nat(D.u32.pick(Bool.and(True{}, _), n, 0)), A.A.from(to), opos, dpos, B.B.get(A.A.from(td), dpos))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), dpos), (A.A.from(td), Y.BP.byt(td, dpos)), Y.BP.get_from(td, dpos)) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, n, True{}, B.B.copy.bytes(U32.to_nat(n), A.A.from(to), opos, dpos, _)) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Array<U32> & Array<U32>, B.B.copy.bytes(U32.to_nat(n), A.A.from(to), opos, dpos, (A.A.from(td), Y.BP.byt(td, dpos))), (A.A.from(td), A.A.from(S.S.puts(S.S.sl(U32.to_nat(n), td, dpos), to, opos))), C.CP.bytes(U32.to_nat(n), to, opos, td, dpos)) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, n, True{}, _) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Nat, U32.to_nat(n), S.S.len(xs), DX.lenis(xs, n, hl)) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, n, True{}, (A.A.from(td), A.A.from(S.S.puts(S.S.sl(_, td, dpos), to, opos)))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(A.Tr, S.S.puts(S.S.sl(S.S.len(xs), td, dpos), to, opos), S.S.puts(xs, to, opos), DX.puts_held(xs, rest, td, dpos, to, opos, hd)) :
    {D.dec.add.k(A.A.from(ts), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, n, True{}, (A.A.from(td), A.A.from(_))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(xs, to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, n), ipos, apos, slot, 0} : D.Dec}
  {==}

law DX.rep_mask:
  for +k: Nat
  for +b: U32
  for +t: A.Tr
  for +d: U32
  {S.S.puts(C.CP.rep(k, U32.and(b, 255)), t, d) == S.S.puts(C.CP.rep(k, b), t, d) : A.Tr}

def DX.rep_mask(k, b, t, d):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(A.Tr, Y.BP.put(t, d, U32.and(b, 255)), Y.BP.put(t, d, b), C.CP.put_mask(t, d, b)) :
        {S.S.puts(C.CP.rep(p, U32.and(b, 255)), _, U32.add(d, 1)) == S.S.puts(C.CP.rep(p, b), Y.BP.put(t, d, b), U32.add(d, 1)) : A.Tr}
      %Equal.sym(A.Tr, S.S.puts(C.CP.rep(p, U32.and(b, 255)), Y.BP.put(t, d, b), U32.add(d, 1)), S.S.puts(C.CP.rep(p, b), Y.BP.put(t, d, b), U32.add(d, 1)), DX.rep_mask(p, b, Y.BP.put(t, d, b), U32.add(d, 1))) :
        {_ == S.S.puts(C.CP.rep(p, b), Y.BP.put(t, d, b), U32.add(d, 1)) : A.Tr}
      {==}

# RUN: n copies of the data section's next byte.
law DX.run:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +b: U32
  for +rest: List<&2, U32>
  for +E: U32
  for +hd: {S.S.has(b <> rest, td, dpos) == True{} : Bool}
  for +hdb: {U32.is_lt(dpos, dend) == True{} : Bool}
  for +hob: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  {D.dec.run(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, (n, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot) : D.Dec}

def DX.run(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, b, rest, E, hd, hdb, hob, hE):
  %Equal.sym(Bool, U32.is_lt(dpos, dend), True{}, hdb) :
    {D.dec.run.k(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, D.u32.pick(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), n, 0), Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), B.B.get(A.A.from(td), dpos)) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), b), to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Bool, U32.is_le(n, U32.sub(oend, opos)), True{}, hob) :
    {D.dec.run.k(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, D.u32.pick(Bool.and(True{}, _), n, 0), Bool.and(True{}, _), B.B.get(A.A.from(td), dpos)) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), b), to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), dpos), (A.A.from(td), U32.and(b, 255)), R.VI.rd(td, dpos, b, rest, hd)) :
    {D.dec.run.k(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, apos, slot, 0, n, True{}, _) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), b), to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(Array<U32>, B.B.fill(A.A.from(to), opos, U32.and(b, 255), n), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), U32.and(b, 255)), to, opos)), C.CP.fill(to, opos, U32.and(b, 255), n, E, hE)) :
    {D.Dec{A.A.from(ts), A.A.from(td), _, A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), b), to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} : D.Dec}
  %Equal.sym(A.Tr, S.S.puts(C.CP.rep(V.U.N(n), U32.and(b, 255)), to, opos), S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), DX.rep_mask(V.U.N(n), b, to, opos)) :
    {D.Dec{A.A.from(ts), A.A.from(td), A.A.from(_), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(C.CP.rep(V.U.N(n), b), to, opos)), A.A.from(tb), A.A.from(ca), U32.add(opos, n), U32.add(dpos, 1), ipos, apos, slot, 0} : D.Dec}
  {==}

law DX.is_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_lt(Nat.cmp(a, b)) == True{} : Bool}
  {Nat.cmp(a, b) == LT{} : Cmp}

law DX.is_lt.go:
  for +c: Cmp
  for +h: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}

def DX.is_lt.go(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      P.Bool.false_true({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      P.Bool.false_true({GT{} == LT{} : Cmp}, h)

def DX.is_lt(a, b, h):
  DX.is_lt.go(Nat.cmp(a, b), h)

law DX.cput:
  for +ca: A.Tr
  for +slot: U32
  for +addr: U32
  {D.cache.put(A.A.from(ca), slot, addr) == A.A.from(Q.SP.cput(ca, slot, addr)) : Array<U32>}

def DX.cput(ca, slot, addr):
  %Equal.sym(Array<U32>, Array.set(U32, A.A.from(ca), U32.add(768, slot), addr), A.A.from(A.T.set(ca, U32.add(768, slot), addr)), A.A.set_from(ca, U32.add(768, slot), addr)) :
    {Array.set(U32, _, U32.mod(addr, 768), addr) == A.A.from(A.T.set(A.T.set(ca, U32.add(768, slot), addr), U32.mod(addr, 768), addr)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, A.A.from(A.T.set(ca, U32.add(768, slot), addr)), U32.mod(addr, 768), addr), A.A.from(A.T.set(A.T.set(ca, U32.add(768, slot), addr), U32.mod(addr, 768), addr)), A.A.set_from(A.T.set(ca, U32.add(768, slot), addr), U32.mod(addr, 768), addr)) :
    {_ == A.A.from(A.T.set(A.T.set(ca, U32.add(768, slot), addr), U32.mod(addr, 768), addr)) : Array<U32>}
  {==}

# A COPY once its address is known: from the source segment, or from
# earlier in the target window (forward, so it may read its own output).
law DX.copy_at.go:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +addr: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +hlt: {U32.is_lt(addr, U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +hroom: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hseg: {Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}
  for +hB: {Bool.pick(Bool, U32.is_lt(addr, cpl), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, addr))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos)))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(addr, cpl) == c : Bool}
  {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, addr, True{}, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), tb, Q.SP.cput(ca, slot, addr), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot)) : D.Dec}

def DX.copy_at.go(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, addr, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(addr, U32.add(cpl, U32.sub(opos, wst))), True{}, hlt) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, U32.is_le(n, U32.sub(oend, opos)), True{}, hroom) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))), True{}, hseg) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(True{}, True{}), _), n, 0), Bool.and(Bool.and(True{}, True{}), _), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(True{}, True{}), _), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, U32.is_lt(addr, cpl), True{}, ec) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, D.dec.copy.go(Bool.or(Bool.not(_), False{}), n, Bool.pick(U32, _, U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, _, S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy(A.A.from(to), opos, A.A.from(ts), U32.add(seg, addr), n), (A.A.from(ts), A.A.from(S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos))), C.CP.copy(to, opos, ts, U32.add(seg, addr), n, E, hob, (%ec : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, addr))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos)))) == True{} : Bool}; hB))) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, _) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos)), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Array<U32>, D.cache.put(A.A.from(ca), slot, addr), A.A.from(Q.SP.cput(ca, slot, addr)), DX.cput(ca, slot, addr)) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), _, opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, (A.A.from(ts), A.A.from(S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos)))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos)), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_lt(addr, U32.add(cpl, U32.sub(opos, wst))), True{}, hlt) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(_, U32.is_le(n, U32.sub(oend, opos))), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, U32.is_le(n, U32.sub(oend, opos)), True{}, hroom) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(True{}, _), Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr)))), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))), True{}, hseg) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, D.u32.pick(Bool.and(Bool.and(True{}, True{}), _), n, 0), Bool.and(Bool.and(True{}, True{}), _), D.dec.copy.go(Bool.or(Bool.not(U32.is_lt(addr, cpl)), False{}), D.u32.pick(Bool.and(Bool.and(True{}, True{}), _), n, 0), D.u32.pick(U32.is_lt(addr, cpl), U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Bool, U32.is_lt(addr, cpl), False{}, ec) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, D.dec.copy.go(Bool.or(Bool.not(_), False{}), n, Bool.pick(U32, _, U32.add(seg, addr), U32.add(wst, U32.sub(addr, cpl))), opos, A.A.from(ts), A.A.from(to))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Bool.pick(A.Tr, _, S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Array<U32>, B.B.move(A.A.from(to), opos, U32.add(wst, U32.sub(addr, cpl)), n), A.A.from(C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), C.CP.move(to, opos, U32.add(wst, U32.sub(addr, cpl)), n, dp, E, hp, hdp, he, hob, DX.is_lt(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos), (%ec : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, addr))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos)))) == True{} : Bool}; hB)))) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), D.cache.put(A.A.from(ca), slot, addr), opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, (A.A.from(ts), _)) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      %Equal.sym(Array<U32>, D.cache.put(A.A.from(ca), slot, addr), A.A.from(Q.SP.cput(ca, slot, addr)), DX.cput(ca, slot, addr)) :
        {D.dec.copy.k(A.A.from(td), A.A.from(tb), _, opos, dpos, ipos, apos, D.cache.next(slot), 0, n, True{}, (A.A.from(ts), A.A.from(C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))))) == D.Dec{A.A.from(ts), A.A.from(td), A.A.from(C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), A.A.from(tb), A.A.from(Q.SP.cput(ca, slot, addr)), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot), 0} : D.Dec}
      {==}

law DX.copy_at:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +addr: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +hlt: {U32.is_lt(addr, U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +hroom: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hseg: {Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}
  for +hB: {Bool.pick(Bool, U32.is_lt(addr, cpl), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, addr))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos)))) == True{} : Bool}
  {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, addr, True{}, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), tb, Q.SP.cput(ca, slot, addr), U32.add(opos, n), dpos, ipos, apos, D.cache.next(slot)) : D.Dec}

def DX.copy_at(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, addr, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB):
  DX.copy_at.go(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, addr, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB, U32.is_lt(addr, cpl), {==})

# COPY with its address a varint (SELF, HERE, NEAR).
law DX.copy_v:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +m: U32
  for +v: U32
  for +rest: List<&2, U32>
  for +hm: {U32.is_lt(m, 6) == True{} : Bool}
  for +ha: {S.S.has(K.WD.app(R.VI.var(v), rest), td, apos) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(B.B.var.len(v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  for +hok: {Q.SP.aok(m, v, U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  {D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, m, (n, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot)) : D.Dec}

def DX.copy_v(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, rest, hm, ha, hab, hok):
  %Equal.sym(Bool, U32.is_lt(m, 6), True{}, hm) :
    {D.dec.copy.v(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, m, U32.add(cpl, U32.sub(opos, wst)), A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, slot, 0, D.dec.addr.v(_, A.A.from(td), apos, aend)) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  %Equal.sym(B.VR, B.B.var.get(A.A.from(td), apos, aend), B.VR{A.A.from(td), v, U32.add(apos, B.B.var.len(v)), True{}}, R.VI.get(td, apos, aend, v, rest, ha, hab)) :
    {D.dec.copy.v(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, m, U32.add(cpl, U32.sub(opos, wst)), A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, slot, 0, _) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(m, 6), True{}, hm) :
    {D.dec.copy.c(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0, D.dec.addr.c(m, U32.add(cpl, U32.sub(opos, wst)), v, True{}, Array.get(U32, A.A.from(ca), Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))))) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ca), U32.add(766, m)), (A.A.from(ca), A.T.word(ca, U32.add(766, m))), A.A.get_from(ca, U32.add(766, m))) :
    {D.dec.copy.c(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0, D.dec.addr.c(m, U32.add(cpl, U32.sub(opos, wst)), v, True{}, _)) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(m, 6), True{}, hm) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, _, U32.add(A.T.word(ca, U32.add(766, m)), v), A.T.word(ca, U32.add(766, m))))), Bool.and(Bool.and(True{}, U32.is_lt(m, 9)), Bool.or(U32.is_ne(m, 1), U32.is_le(v, U32.add(cpl, U32.sub(opos, wst))))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, _, U32.add(A.T.word(ca, Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), v), A.T.word(ca, Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))))))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  %Equal.sym(Bool, Bool.and(U32.is_lt(m, 9), Bool.or(U32.is_ne(m, 1), U32.is_le(v, U32.add(cpl, U32.sub(opos, wst))))), True{}, hok) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), U32.add(A.T.word(ca, U32.add(766, m)), v))), _, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), U32.add(A.T.word(ca, U32.add(766, m)), v))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, B.B.var.len(v)), slot, 0}) : D.Dec}
  {==}

# COPY with its address a byte (SAME).
law DX.copy_b:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +m: U32
  for +v: U32
  for +rest: List<&2, U32>
  for +hm: {U32.is_lt(m, 6) == False{} : Bool}
  for +hm0: {U32.is_eq(m, 0) == False{} : Bool}
  for +hm1: {U32.is_eq(m, 1) == False{} : Bool}
  for +hm9: {U32.is_lt(m, 9) == True{} : Bool}
  for +ha: {S.S.has(v <> rest, td, apos) == True{} : Bool}
  for +hab: {U32.is_lt(apos, aend) == True{} : Bool}
  {D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, m, (n, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, U32.add(apos, 1), slot)) : D.Dec}

def DX.copy_b(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, rest, hm, hm0, hm1, hm9, ha, hab):
  %Equal.sym(Bool, U32.is_lt(m, 6), False{}, hm) :
    {D.dec.copy.v(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, m, U32.add(cpl, U32.sub(opos, wst)), A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, slot, 0, D.dec.addr.v(_, A.A.from(td), apos, aend)) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), apos), (A.A.from(td), U32.and(v, 255)), R.VI.rd(td, apos, v, rest, ha)) :
    {D.dec.copy.v(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, m, U32.add(cpl, U32.sub(opos, wst)), A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, slot, 0, B.B.byte.k(apos, aend, _)) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(apos, aend), True{}, hab) :
    {D.dec.copy.v(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, m, U32.add(cpl, U32.sub(opos, wst)), A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, slot, 0, B.VR{A.A.from(td), U32.and(v, 255), U32.add(apos, 1), _}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(m, 6), False{}, hm) :
    {D.dec.copy.c(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), opos, dpos, ipos, U32.add(apos, 1), slot, 0, D.dec.addr.c(m, U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255), True{}, Array.get(U32, A.A.from(ca), Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(U32.and(v, 255), 255)))))) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(U32, U32.and(U32.and(v, 255), 255), U32.and(v, 255), Z.BB.and255(v)) :
    {D.dec.copy.c(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), opos, dpos, ipos, U32.add(apos, 1), slot, 0, D.dec.addr.c(m, U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255), True{}, Array.get(U32, A.A.from(ca), U32.add(U32.mul(U32.sub(m, 6), 256), _)))) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ca), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), (A.A.from(ca), A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), A.A.get_from(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))) :
    {D.dec.copy.c(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), opos, dpos, ipos, U32.add(apos, 1), slot, 0, D.dec.addr.c(m, U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255), True{}, _)) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(m, 6), False{}, hm) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), U32.and(v, 255), Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255)), Bool.pick(U32, _, U32.add(A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), U32.and(v, 255)), A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))))), Bool.and(Bool.and(True{}, U32.is_lt(m, 9)), Bool.or(U32.is_ne(m, 1), U32.is_le(U32.and(v, 255), U32.add(cpl, U32.sub(opos, wst))))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, U32.is_eq(m, 0), v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, _, U32.add(A.T.word(ca, Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), v), A.T.word(ca, Bool.pick(U32, _, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))))))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_eq(m, 0), False{}, hm0) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, _, U32.and(v, 255), Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255)), Bool.pick(U32, False{}, U32.add(A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), U32.and(v, 255)), A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))))), Bool.and(Bool.and(True{}, U32.is_lt(m, 9)), Bool.or(U32.is_ne(m, 1), U32.is_le(U32.and(v, 255), U32.add(cpl, U32.sub(opos, wst))))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, _, v, Bool.pick(U32, U32.is_eq(m, 1), U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, False{}, U32.add(A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), v), A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))))))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_eq(m, 1), False{}, hm1) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, False{}, U32.and(v, 255), Bool.pick(U32, _, U32.sub(U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255)), Bool.pick(U32, False{}, U32.add(A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), U32.and(v, 255)), A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))))), Bool.and(Bool.and(True{}, U32.is_lt(m, 9)), Bool.or(U32.is_ne(m, 1), U32.is_le(U32.and(v, 255), U32.add(cpl, U32.sub(opos, wst))))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, False{}, v, Bool.pick(U32, _, U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, False{}, U32.add(A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), v), A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))))))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, U32.is_lt(m, 9), True{}, hm9) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, False{}, U32.and(v, 255), Bool.pick(U32, False{}, U32.sub(U32.add(cpl, U32.sub(opos, wst)), U32.and(v, 255)), Bool.pick(U32, False{}, U32.add(A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), U32.and(v, 255)), A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))))), Bool.and(Bool.and(True{}, _), Bool.or(U32.is_ne(m, 1), U32.is_le(U32.and(v, 255), U32.add(cpl, U32.sub(opos, wst))))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Bool.pick(U32, False{}, v, Bool.pick(U32, False{}, U32.sub(U32.add(cpl, U32.sub(opos, wst)), v), Bool.pick(U32, False{}, U32.add(A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255)))), v), A.T.word(ca, Bool.pick(U32, False{}, U32.add(766, m), U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))))))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(m, 1)), False{}, hm1) :
    {D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), Bool.or(Bool.not(_), U32.is_le(U32.and(v, 255), U32.add(cpl, U32.sub(opos, wst)))), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) == D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, A.T.word(ca, U32.add(U32.mul(U32.sub(m, 6), 256), U32.and(v, 255))), True{}, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, ipos, U32.add(apos, 1), slot, 0}) : D.Dec}
  {==}

law DX.or_self:
  for +a: Bool
  for +h: {Bool.or(a, a) == True{} : Bool}
  {a == True{} : Bool}

def DX.or_self(a, h):
  match a:
    case False{}:
      P.Bool.false_true({False{} == True{} : Bool}, h)
    case True{}:
      {==}

# A half takes its size from the instruction section: its bytes, and their
# length.
law DX.sz_true:
  for +h: U32
  for +f: Q.HF
  for +ez: {Q.SP.z(h) == True{} : Bool}
  {Q.SP.sz(h, f) == R.VI.var(Q.SP.size(f)) : List<&2, U32>}

def DX.sz_true(h, f, ez):
  %Equal.sym(Bool, Q.SP.z(h), True{}, ez) :
    {Bool.pick(List<&2, U32>, _, R.VI.var(Q.SP.size(f)), []) == R.VI.var(Q.SP.size(f)) : List<&2, U32>}
  {==}

law DX.hi_v:
  for +h: U32
  for +f: Q.HF
  for +td: A.Tr
  for +ipos: U32
  for +rest: List<&2, U32>
  for +ez: {Q.SP.z(h) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, f), rest), td, ipos) == True{} : Bool}
  {S.S.has(K.WD.app(R.VI.var(Q.SP.size(f)), rest), td, ipos) == True{} : Bool}

def DX.hi_v(h, f, td, ipos, rest, ez, hi):
  %DX.sz_true(h, f, ez) :
    {S.S.has(K.WD.app(_, rest), td, ipos) == True{} : Bool}
  hi

law DX.hib_v:
  for +h: U32
  for +f: Q.HF
  for +ipos: U32
  for +iend: U32
  for +ez: {Q.SP.z(h) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, f)), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(B.B.var.len(Q.SP.size(f))), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}

def DX.hib_v(h, f, ipos, iend, ez, hib):
  %R.VI.len_var(Q.SP.size(f)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  %DX.sz_true(h, f, ez) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(_), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  hib

law DX.z_eq:
  for +h: U32
  for +hz: {U32.is_ne(Q.SP.ht(h), 0) == True{} : Bool}
  {Q.SP.z(h) == U32.is_eq(Q.SP.hs(h), 0) : Bool}

law DX.and_true:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def DX.and_true(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def DX.z_eq(h, hz):
  %Equal.sym(Bool, U32.is_ne(Q.SP.ht(h), 0), True{}, hz) :
    {Bool.and(U32.is_eq(Q.SP.hs(h), 0), _) == U32.is_eq(Q.SP.hs(h), 0) : Bool}
  DX.and_true(U32.is_eq(Q.SP.hs(h), 0))

law DX.z_true:
  for +h: U32
  for +hz: {U32.is_ne(Q.SP.ht(h), 0) == True{} : Bool}
  for +ec: {U32.is_eq(Q.SP.hs(h), 0) == True{} : Bool}
  {Q.SP.z(h) == True{} : Bool}

def DX.z_true(h, hz, ec):
  %Equal.sym(Bool, Q.SP.z(h), U32.is_eq(Q.SP.hs(h), 0), DX.z_eq(h, hz)) :
    {_ == True{} : Bool}
  ec

# The size of a half (of a type other than NOOP) from its table half: there,
# or a varint in the instruction section.
law DX.size.k:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +f: Q.HF
  for +h: U32
  for +rest: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(f))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, f), rest), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, f)), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +hz: {U32.is_ne(Q.SP.ht(h), 0) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_eq(Q.SP.hs(h), 0) == c : Bool}
  {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, f, ipos), apos, slot)) : U32 & D.Dec}

def DX.size.k(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, f, h, rest, hok, hi, hib, hz, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, Q.SP.z(h), U32.is_eq(Q.SP.hs(h), 0), DX.z_eq(h, hz)) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, f, ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(Bool, Q.SP.z(h), U32.is_eq(Q.SP.hs(h), 0), DX.z_eq(h, hz)) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_eq(Q.SP.hs(h), 0), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Bool.pick(U32, _, U32.add(ipos, B.B.var.len(Q.SP.size(f))), ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(Bool, U32.is_eq(Q.SP.hs(h), 0), True{}, ec) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Bool.pick(U32, _, U32.add(ipos, B.B.var.len(Q.SP.size(f))), ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(B.VR, B.B.var.get(A.A.from(td), ipos, iend), B.VR{A.A.from(td), Q.SP.size(f), U32.add(ipos, B.B.var.len(Q.SP.size(f))), True{}}, R.VI.get(td, ipos, iend, Q.SP.size(f), rest, DX.hi_v(h, f, td, ipos, rest, DX.z_true(h, hz, ec), hi), DX.hib_v(h, f, ipos, iend, DX.z_true(h, hz, ec), hib))) :
        {D.dec.size.k(A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, apos, slot, 0, _) == (Q.SP.size(f), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(tb), A.A.from(ca), opos, dpos, U32.add(ipos, B.B.var.len(Q.SP.size(f))), apos, slot, 0}) : U32 & D.Dec}
      {==}
    case False{}:
      %Equal.sym(Bool, Q.SP.z(h), U32.is_eq(Q.SP.hs(h), 0), DX.z_eq(h, hz)) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, f, ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(Bool, Q.SP.z(h), U32.is_eq(Q.SP.hs(h), 0), DX.z_eq(h, hz)) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_eq(Q.SP.hs(h), 0), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Bool.pick(U32, _, U32.add(ipos, B.B.var.len(Q.SP.size(f))), ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(Bool, U32.is_eq(Q.SP.hs(h), 0), False{}, ec) :
        {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Bool.pick(U32, _, U32.add(ipos, B.B.var.len(Q.SP.size(f))), ipos), apos, slot)) : U32 & D.Dec}
      %Equal.sym(U32, Q.SP.hs(h), Q.SP.size(f), V.U.is_eq(Q.SP.hs(h), Q.SP.size(f), (%ec : {Bool.or(_, U32.is_eq(Q.SP.hs(h), Q.SP.size(f))) == True{} : Bool}; hok))) :
        {(_, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) : U32 & D.Dec}
      {==}

law DX.size:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +f: Q.HF
  for +h: U32
  for +rest: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(f))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, f), rest), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, f)), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +hz: {U32.is_ne(Q.SP.ht(h), 0) == True{} : Bool}
  {D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == (Q.SP.size(f), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, f, ipos), apos, slot)) : U32 & D.Dec}

def DX.size(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, f, h, rest, hok, hi, hib, hz):
  DX.size.k(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, f, h, rest, hok, hi, hib, hz, U32.is_eq(Q.SP.hs(h), 0), {==})

# Halves of each type
# ===================

law DX.h_add:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +xs: List<&2, U32>
  for +h: U32
  for +restI: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(Q.HA{n, xs}))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, Q.HA{n, xs}), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, Q.HA{n, xs})), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +restD: List<&2, U32>
  for +ht: {Q.SP.ht(h) == 1 : U32}
  for +hd: {S.S.has(K.WD.app(xs, restD), td, dpos) == True{} : Bool}
  for +hl: {Q.SP.lenis(xs, n) == True{} : Bool}
  for +hdb: {U32.is_le(n, U32.sub(dend, dpos)) == True{} : Bool}
  for +hob: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot) : D.Dec}

def DX.h_add(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, xs, h, restI, hok, hi, hib, restD, ht, hd, hl, hdb, hob):
  %Equal.sym(U32 & D.Dec, D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), (Q.SP.size(Q.HA{n, xs}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot)), DX.size(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, Q.HA{n, xs}, h, restI, hok, hi, hib, (%Equal.sym(U32, Q.SP.ht(h), 1, ht) : {U32.is_ne(_, 0) == True{} : Bool}; {==}))) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(Q.SP.ht(h), 2), 0), U32.is_ne(U32.and(Q.SP.ht(h), 1), 0), Q.SP.hm(h), _) == DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot) : D.Dec}
  %Equal.sym(U32, Q.SP.ht(h), 1, ht) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(_, 2), 0), U32.is_ne(U32.and(_, 1), 0), Q.SP.hm(h), (Q.SP.size(Q.HA{n, xs}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot))) == DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot) : D.Dec}
  %Equal.sym(D.Dec, D.dec.add(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot))), DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot), DX.add(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, xs, restD, hd, hl, hdb, hob)) :
    {_ == DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot) : D.Dec}
  {==}

law DX.h_run:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +b: U32
  for +h: U32
  for +restI: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(Q.HR{n, b}))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, Q.HR{n, b}), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, Q.HR{n, b})), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +restD: List<&2, U32>
  for +E: U32
  for +ht: {Q.SP.ht(h) == 2 : U32}
  for +hd: {S.S.has(b <> restD, td, dpos) == True{} : Bool}
  for +hdb: {U32.is_lt(dpos, dend) == True{} : Bool}
  for +hob: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot) : D.Dec}

def DX.h_run(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, b, h, restI, hok, hi, hib, restD, E, ht, hd, hdb, hob, hE):
  %Equal.sym(U32 & D.Dec, D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), (Q.SP.size(Q.HR{n, b}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot)), DX.size(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, Q.HR{n, b}, h, restI, hok, hi, hib, (%Equal.sym(U32, Q.SP.ht(h), 2, ht) : {U32.is_ne(_, 0) == True{} : Bool}; {==}))) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(Q.SP.ht(h), 2), 0), U32.is_ne(U32.and(Q.SP.ht(h), 1), 0), Q.SP.hm(h), _) == DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot) : D.Dec}
  %Equal.sym(U32, Q.SP.ht(h), 2, ht) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(_, 2), 0), U32.is_ne(U32.and(_, 1), 0), Q.SP.hm(h), (Q.SP.size(Q.HR{n, b}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot))) == DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot) : D.Dec}
  %Equal.sym(D.Dec, D.dec.run(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot))), DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot), DX.run(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, b, restD, E, hd, hdb, hob, hE)) :
    {_ == DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot) : D.Dec}
  {==}

law DX.h_noop:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +h: U32
  for +ht: {Q.SP.ht(h) == 0 : U32}
  for +hs0: {U32.is_eq(Q.SP.hs(h), 0) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot) : D.Dec}

def DX.h_noop(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, h, ht, hs0):
  %Equal.sym(U32, Q.SP.ht(h), 0, ht) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(_, 2), 0), U32.is_ne(U32.and(_, 1), 0), Q.SP.hm(h), D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Bool.and(U32.is_eq(Q.SP.hs(h), 0), U32.is_ne(_, 0)), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot) : D.Dec}
  %Equal.sym(Bool, U32.is_eq(Q.SP.hs(h), 0), True{}, hs0) :
    {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(0, 2), 0), U32.is_ne(U32.and(0, 1), 0), Q.SP.hm(h), D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Bool.and(_, U32.is_ne(0, 0)), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot))) == DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot) : D.Dec}
  {==}

law DX.ne_lt6:
  for +m: U32
  for +k: U32
  for +hm: {U32.is_lt(m, 6) == False{} : Bool}
  for +hk: {U32.is_lt(k, 6) == True{} : Bool}
  {U32.is_eq(m, k) == False{} : Bool}

law DX.ne_lt6.go:
  for +m: U32
  for +k: U32
  for +hm: {U32.is_lt(m, 6) == False{} : Bool}
  for +hk: {U32.is_lt(k, 6) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_eq(m, k) == c : Bool}
  {c == False{} : Bool}

law DX.lt6_m:
  for +m: U32
  for +k: U32
  for +ec: {U32.is_eq(m, k) == True{} : Bool}
  for +hk: {U32.is_lt(k, 6) == True{} : Bool}
  {U32.is_lt(m, 6) == True{} : Bool}

def DX.lt6_m(m, k, ec, hk):
  %Equal.sym(U32, m, k, V.U.is_eq(m, k, ec)) :
    {U32.is_lt(_, 6) == True{} : Bool}
  hk

def DX.ne_lt6.go(m, k, hm, hk, c, ec):
  match c:
    case False{}:
      {==}
    case True{}:
      P.Bool.false_true({True{} == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(m, 6), True{}, Equal.sym(Bool, U32.is_lt(m, 6), False{}, hm), DX.lt6_m(m, k, ec, hk)))

def DX.ne_lt6(m, k, hm, hk):
  DX.ne_lt6.go(m, k, hm, hk, U32.is_eq(m, k), {==})

law DX.ha_v:
  for +m: U32
  for +v: U32
  for +td: A.Tr
  for +apos: U32
  for +restA: List<&2, U32>
  for +ec: {U32.is_lt(m, 6) == True{} : Bool}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr.m(U32.is_lt(m, 6), v), restA), td, apos) == True{} : Bool}
  {S.S.has(K.WD.app(R.VI.var(v), restA), td, apos) == True{} : Bool}

def DX.ha_v(m, v, td, apos, restA, ec, ha):
  (%ec : {S.S.has(K.WD.app(Q.SP.adr.m(_, v), restA), td, apos) == True{} : Bool}; ha)

law DX.hab_v:
  for +m: U32
  for +v: U32
  for +apos: U32
  for +aend: U32
  for +ec: {U32.is_lt(m, 6) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(U32.is_lt(m, 6), v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(B.B.var.len(v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}

def DX.hab_v(m, v, apos, aend, ec, hab):
  %R.VI.len_var(v) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  (%ec : {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(_, v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}; hab)

law DX.ha_b:
  for +m: U32
  for +v: U32
  for +td: A.Tr
  for +apos: U32
  for +restA: List<&2, U32>
  for +ec: {U32.is_lt(m, 6) == False{} : Bool}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr.m(U32.is_lt(m, 6), v), restA), td, apos) == True{} : Bool}
  {S.S.has(v <> restA, td, apos) == True{} : Bool}

def DX.ha_b(m, v, td, apos, restA, ec, ha):
  (%ec : {S.S.has(K.WD.app(Q.SP.adr.m(_, v), restA), td, apos) == True{} : Bool}; ha)

law DX.hab_b:
  for +m: U32
  for +v: U32
  for +apos: U32
  for +aend: U32
  for +ec: {U32.is_lt(m, 6) == False{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(U32.is_lt(m, 6), v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  {U32.is_lt(apos, aend) == True{} : Bool}

def DX.hab_b(m, v, apos, aend, ec, hab):
  V.U.N_lt(apos, aend, K.WD.lt_of_succ_le(V.U.N(apos), V.U.N(aend), (%ec : {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(_, v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}; hab)))

law DX.aok9:
  for +m: U32
  for +v: U32
  for +here: U32
  for +h: {Q.SP.aok(m, v, here) == True{} : Bool}
  {U32.is_lt(m, 9) == True{} : Bool}

def DX.aok9(m, v, here, h):
  P.Bool.and_l(U32.is_lt(m, 9), Bool.or(U32.is_ne(m, 1), U32.is_le(v, here)), h)

law DX.h_copy.go:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +m: U32
  for +v: U32
  for +h: U32
  for +restI: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(Q.HC{n, m, v}))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, Q.HC{n, m, v}), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, Q.HC{n, m, v})), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +restA: List<&2, U32>
  for +ht: {Q.SP.ht(h) == 3 : U32}
  for +hm: {Q.SP.hm(h) == m : U32}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr.m(U32.is_lt(m, 6), v), restA), td, apos) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(U32.is_lt(m, 6), v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  for +haok: {Q.SP.aok(m, v, U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +hlt: {U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +hroom: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hseg: {Bool.or(Bool.not(U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)), U32.is_le(n, U32.sub(cpl, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)))) == True{} : Bool}
  for +hB: {Bool.pick(Bool, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl))), V.U.N(opos)))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(m, 6) == c : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}

def DX.h_copy.go(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, h, restI, hok, hi, hib, restA, ht, hm, ha, hab, haok, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32 & D.Dec, D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), (Q.SP.size(Q.HC{n, m, v}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot)), DX.size(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, Q.HC{n, m, v}, h, restI, hok, hi, hib, (%Equal.sym(U32, Q.SP.ht(h), 3, ht) : {U32.is_ne(_, 0) == True{} : Bool}; {==}))) :
        {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(Q.SP.ht(h), 2), 0), U32.is_ne(U32.and(Q.SP.ht(h), 1), 0), Q.SP.hm(h), _) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}
      %Equal.sym(U32, Q.SP.ht(h), 3, ht) :
        {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(_, 2), 0), U32.is_ne(U32.and(_, 1), 0), Q.SP.hm(h), (Q.SP.size(Q.HC{n, m, v}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}
      %Equal.sym(U32, Q.SP.hm(h), m, hm) :
        {D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(D.Dec, D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, m, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))), D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, B.B.var.len(v)), slot)), DX.copy_v(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, restA, ec, DX.ha_v(m, v, td, apos, restA, ec, ha), DX.hab_v(m, v, apos, aend, ec, hab), haok)) :
        {_ == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(D.Dec, D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, B.B.var.len(v)), slot)), DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, B.B.var.len(v)), D.cache.next(slot)), DX.copy_at(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, B.B.var.len(v)), slot, seg, cpl, wst, oend, dend, iend, aend, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB)) :
        {_ == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(Bool, U32.is_lt(m, 6), True{}, ec) :
        {DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, B.B.var.len(v)), D.cache.next(slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, _, U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      {==}
    case False{}:
      %Equal.sym(U32 & D.Dec, D.dec.size(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.z(h), Q.SP.hs(h), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), (Q.SP.size(Q.HC{n, m, v}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot)), DX.size(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, Q.HC{n, m, v}, h, restI, hok, hi, hib, (%Equal.sym(U32, Q.SP.ht(h), 3, ht) : {U32.is_ne(_, 0) == True{} : Bool}; {==}))) :
        {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(Q.SP.ht(h), 2), 0), U32.is_ne(U32.and(Q.SP.ht(h), 1), 0), Q.SP.hm(h), _) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}
      %Equal.sym(U32, Q.SP.ht(h), 3, ht) :
        {D.dec.half.go(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, U32.is_ne(U32.and(_, 2), 0), U32.is_ne(U32.and(_, 1), 0), Q.SP.hm(h), (Q.SP.size(Q.HC{n, m, v}), DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}
      %Equal.sym(U32, Q.SP.hm(h), m, hm) :
        {D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(D.Dec, D.dec.copy(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, m, (n, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot))), D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, 1), slot)), DX.copy_b(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, restA, ec, DX.ne_lt6(m, 0, ec, {==}), DX.ne_lt6(m, 1, ec, {==}), DX.aok9(m, v, U32.add(cpl, U32.sub(opos, wst)), haok), DX.ha_b(m, v, td, apos, restA, ec, ha), DX.hab_b(m, v, apos, aend, ec, hab))) :
        {_ == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(D.Dec, D.dec.copy.at(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), True{}, DX.st(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, 1), slot)), DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, 1), D.cache.next(slot)), DX.copy_at(ts, td, to, tb, ca, opos, dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, 1), slot, seg, cpl, wst, oend, dend, iend, aend, n, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB)) :
        {_ == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, U32.is_lt(m, 6), U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      %Equal.sym(Bool, U32.is_lt(m, 6), False{}, ec) :
        {DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), U32.add(apos, 1), D.cache.next(slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Bool.pick(U32, _, U32.add(apos, B.B.var.len(v)), U32.add(apos, 1)), D.cache.next(slot)) : D.Dec}
      {==}

law DX.h_copy:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +n: U32
  for +m: U32
  for +v: U32
  for +h: U32
  for +restI: List<&2, U32>
  for +hok: {Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), Q.SP.size(Q.HC{n, m, v}))) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, Q.HC{n, m, v}), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, Q.HC{n, m, v})), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +restA: List<&2, U32>
  for +ht: {Q.SP.ht(h) == 3 : U32}
  for +hm: {Q.SP.hm(h) == m : U32}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr.m(U32.is_lt(m, 6), v), restA), td, apos) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr.m(U32.is_lt(m, 6), v)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  for +haok: {Q.SP.aok(m, v, U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +hlt: {U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), U32.add(cpl, U32.sub(opos, wst))) == True{} : Bool}
  for +hroom: {U32.is_le(n, U32.sub(oend, opos)) == True{} : Bool}
  for +hseg: {Bool.or(Bool.not(U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)), U32.is_le(n, U32.sub(cpl, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)))) == True{} : Bool}
  for +hB: {Bool.pick(Bool, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)))), V.U.N(E))), Cmp.is_lt(Nat.cmp(V.U.N(U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl))), V.U.N(opos)))) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)) : D.Dec}

def DX.h_copy(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, h, restI, hok, hi, hib, restA, ht, hm, ha, hab, haok, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB):
  DX.h_copy.go(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, h, restI, hok, hi, hib, restA, ht, hm, ha, hab, haok, dp, E, hp, hdp, he, hob, hlt, hroom, hseg, hB, U32.is_lt(m, 6), {==})

# n <= e - d (as words) when n + d <= e (as values).
law DX.le_sub:
  for +n: U32
  for +d: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(e))) == True{} : Bool}
  {U32.is_le(n, U32.sub(e, d)) == True{} : Bool}

law DX.le_sub.go:
  for +n: U32
  for +d: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(U32.sub(e, d)))) == True{} : Bool}

def DX.le_sub.go(n, d, e, h):
  %P.Nat.cmp_add_l(V.U.N(d), V.U.N(n), V.U.N(U32.sub(e, d))) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(d), V.U.N(U32.sub(e, d))), Nat.add(V.U.N(U32.sub(e, d)), V.U.N(d)), P.Nat.add_comm(V.U.N(d), V.U.N(U32.sub(e, d)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(d), V.U.N(n)), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(e, d)), V.U.N(d)), V.U.N(e), V.U.sub_nat(e, d, V.U.N_le(d, e, P.Nat.le_trans(V.U.N(d), Nat.add(V.U.N(n), V.U.N(d)), V.U.N(e), P.Nat.le_add_l(V.U.N(n), V.U.N(d)), h)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(d), V.U.N(n)), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(d), V.U.N(n)), Nat.add(V.U.N(n), V.U.N(d)), P.Nat.add_comm(V.U.N(d), V.U.N(n))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  h

def DX.le_sub(n, d, e, h):
  V.U.N_le(n, U32.sub(e, d), DX.le_sub.go(n, d, e, h))

law DX.hdb_a:
  for +xs: List<&2, U32>
  for +n: U32
  for +d: U32
  for +e: U32
  for +hl: {Q.SP.lenis(xs, n) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(d)), V.U.N(e))) == True{} : Bool}
  {U32.is_le(n, U32.sub(e, d)) == True{} : Bool}

law DX.hdb_a.go:
  for +xs: List<&2, U32>
  for +n: U32
  for +d: U32
  for +e: U32
  for +hl: {Q.SP.lenis(xs, n) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(d)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(e))) == True{} : Bool}

def DX.hdb_a.go(xs, n, d, e, hl, h):
  %Equal.sym(Nat, U32.to_nat(n), S.S.len(xs), DX.lenis(xs, n, hl)) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, U32.to_nat(d)), U32.to_nat(e))) == True{} : Bool}
  h

def DX.hdb_a(xs, n, d, e, hl, h):
  DX.le_sub(n, d, e, DX.hdb_a.go(xs, n, d, e, hl, h))

law DX.hseg.go:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +h: {Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, addr) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(addr, cpl) == c : Bool}
  {Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}

law DX.hseg.t:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +h: {Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, addr) == True{} : Bool}
  for +ec: {U32.is_lt(addr, cpl) == True{} : Bool}
  {U32.is_le(n, U32.sub(cpl, addr)) == True{} : Bool}

def DX.hseg.t(ts, tt, seg, cpl, wst, oend, opos, n, addr, h, ec):
  P.Bool.and_l(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos),
    (%ec : {Bool.pick(Bool, _, Bool.and(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos)), S.S.has(S.S.sl(U32.to_nat(n), tt, U32.add(wst, U32.sub(addr, cpl))), tt, opos)) == True{} : Bool}; h))

def DX.hseg.go(ts, tt, seg, cpl, wst, oend, opos, n, addr, h, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(addr, cpl), True{}, ec) :
        {Bool.or(Bool.not(_), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}
      DX.hseg.t(ts, tt, seg, cpl, wst, oend, opos, n, addr, h, ec)
    case False{}:
      %Equal.sym(Bool, U32.is_lt(addr, cpl), False{}, ec) :
        {Bool.or(Bool.not(_), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}
      {==}

law DX.hseg:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +h: {Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, addr) == True{} : Bool}
  {Bool.or(Bool.not(U32.is_lt(addr, cpl)), U32.is_le(n, U32.sub(cpl, addr))) == True{} : Bool}

def DX.hseg(ts, tt, seg, cpl, wst, oend, opos, n, addr, h):
  DX.hseg.go(ts, tt, seg, cpl, wst, oend, opos, n, addr, h, U32.is_lt(addr, cpl), {==})

# A half
# ======

# The decoder on a half of an opcode, its table half h fitting it: the data,
# instruction and address sections move past what it takes, and the target,
# cache and slot change as proofs/spec says.
law DX.half:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +ca: A.Tr
  for +opos: U32
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +slot: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +tt: A.Tr
  for +h: U32
  for +f: Q.HF
  for +restI: List<&2, U32>
  for +restD: List<&2, U32>
  for +restA: List<&2, U32>
  for +hok: {Q.SP.hok(h, f) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, f), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, f)), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +hd: {S.S.has(K.WD.app(Q.SP.dat(f), restD), td, dpos) == True{} : Bool}
  for +hdb: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.dat(f)), V.U.N(dpos)), V.U.N(dend))) == True{} : Bool}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr(f), restA), td, apos) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr(f)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  for +hv: {Q.SP.vh(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, ca, f) == True{} : Bool}
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(Q.SP.size(f)), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +hB: {Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, f, E) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)) == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, f), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, f)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, f)), Q.SP.dnext(f, dpos), Q.SP.ipos(h, f, ipos), Q.SP.anext(f, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, f))) : D.Dec}

def DX.half(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, tt, h, f, restI, restD, restA, hok, hi, hib, hd, hdb, ha, hab, hv, dp, E, hp, hdp, he, hob, hB):
  match f:
    case Q.HN{}:
      %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot), DX.h_noop(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, h, V.U.is_eq(Q.SP.ht(h), 0, P.Bool.and_l(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0))), Bool.or(U32.is_ne(0, 3), U32.is_eq(Q.SP.hm(h), 0)), hok))), DX.or_self(U32.is_eq(Q.SP.hs(h), 0), P.Bool.and_r(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0))), Bool.or(U32.is_ne(0, 3), U32.is_eq(Q.SP.hm(h), 0)), hok))))) :
        {_ == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HN{}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.dnext(Q.HN{}, dpos), Q.SP.ipos(h, Q.HN{}, ipos), Q.SP.anext(Q.HN{}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{}))) : D.Dec}
      %Equal.sym(U32, Q.SP.ht(h), 0, V.U.is_eq(Q.SP.ht(h), 0, P.Bool.and_l(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0))), Bool.or(U32.is_ne(0, 3), U32.is_eq(Q.SP.hm(h), 0)), hok)))) :
        {DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot) == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HN{}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.dnext(Q.HN{}, dpos), Bool.pick(U32, Bool.and(U32.is_eq(Q.SP.hs(h), 0), U32.is_ne(_, 0)), U32.add(ipos, B.B.var.len(Q.SP.size(Q.HN{}))), ipos), Q.SP.anext(Q.HN{}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{}))) : D.Dec}
      %Equal.sym(Bool, U32.is_eq(Q.SP.hs(h), 0), True{}, DX.or_self(U32.is_eq(Q.SP.hs(h), 0), P.Bool.and_r(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 0), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), 0))), Bool.or(U32.is_ne(0, 3), U32.is_eq(Q.SP.hm(h), 0)), hok)))) :
        {DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot) == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HN{}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{})), Q.SP.dnext(Q.HN{}, dpos), Bool.pick(U32, Bool.and(_, U32.is_ne(0, 0)), U32.add(ipos, B.B.var.len(Q.SP.size(Q.HN{}))), ipos), Q.SP.anext(Q.HN{}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HN{}))) : D.Dec}
      {==}
    case Q.HA{n, xs}:
      %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), DX.st(ts, td, S.S.puts(xs, to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, n), Q.SP.ipos(h, Q.HA{n, xs}, ipos), apos, slot), DX.h_add(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, xs, h, restI, P.Bool.and_r(U32.is_eq(Q.SP.ht(h), 1), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 1), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(1, 3), U32.is_eq(Q.SP.hm(h), 0)), hok)), hi, hib, restD, V.U.is_eq(Q.SP.ht(h), 1, P.Bool.and_l(U32.is_eq(Q.SP.ht(h), 1), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 1), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(1, 3), U32.is_eq(Q.SP.hm(h), 0)), hok))), hd, P.Bool.and_l(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), S.S.has(xs, Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv)), DX.hdb_a(xs, n, dpos, dend, P.Bool.and_l(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), S.S.has(xs, Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv)), hdb), P.Bool.and_r(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), S.S.has(xs, Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv)))) :
        {_ == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HA{n, xs}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HA{n, xs})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HA{n, xs})), Q.SP.dnext(Q.HA{n, xs}, dpos), Q.SP.ipos(h, Q.HA{n, xs}, ipos), Q.SP.anext(Q.HA{n, xs}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HA{n, xs}))) : D.Dec}
      {==}
    case Q.HR{n, b}:
      %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), DX.st(ts, td, S.S.puts(C.CP.rep(V.U.N(n), b), to, opos), tb, ca, U32.add(opos, n), U32.add(dpos, 1), Q.SP.ipos(h, Q.HR{n, b}, ipos), apos, slot), DX.h_run(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, b, h, restI, P.Bool.and_r(U32.is_eq(Q.SP.ht(h), 2), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 2), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(2, 3), U32.is_eq(Q.SP.hm(h), 0)), hok)), hi, hib, restD, E, V.U.is_eq(Q.SP.ht(h), 2, P.Bool.and_l(U32.is_eq(Q.SP.ht(h), 2), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 2), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(2, 3), U32.is_eq(Q.SP.hm(h), 0)), hok))), hd, V.U.N_lt(dpos, dend, K.WD.lt_of_succ_le(V.U.N(dpos), V.U.N(dend), hdb)), P.Bool.and_l(Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), S.S.has(C.CP.rep(U32.to_nat(n), b), Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv), hob)) :
        {_ == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HR{n, b}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HR{n, b})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HR{n, b})), Q.SP.dnext(Q.HR{n, b}, dpos), Q.SP.ipos(h, Q.HR{n, b}, ipos), Q.SP.anext(Q.HR{n, b}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HR{n, b}))) : D.Dec}
      {==}
    case Q.HC{n, m, v}:
      %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot)), DX.st(ts, td, Bool.pick(A.Tr, U32.is_lt(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl), S.S.puts(S.S.sl(V.U.N(n), ts, U32.add(seg, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca))), to, opos), C.CP.mv(V.U.N(n), to, opos, U32.add(wst, U32.sub(Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca), cpl)))), tb, Q.SP.cput(ca, slot, Q.SP.daddr(m, v, U32.add(cpl, U32.sub(opos, wst)), ca)), U32.add(opos, n), dpos, Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), D.cache.next(slot)), DX.h_copy(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, n, m, v, h, restI, P.Bool.and_r(U32.is_eq(Q.SP.ht(h), 3), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 3), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(3, 3), U32.is_eq(Q.SP.hm(h), m)), hok)), hi, hib, restA, V.U.is_eq(Q.SP.ht(h), 3, P.Bool.and_l(U32.is_eq(Q.SP.ht(h), 3), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n)), P.Bool.and_l(Bool.and(U32.is_eq(Q.SP.ht(h), 3), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(3, 3), U32.is_eq(Q.SP.hm(h), m)), hok))), V.U.is_eq(Q.SP.hm(h), m, P.Bool.and_r(Bool.and(U32.is_eq(Q.SP.ht(h), 3), Bool.or(U32.is_eq(Q.SP.hs(h), 0), U32.is_eq(Q.SP.hs(h), n))), Bool.or(U32.is_ne(3, 3), U32.is_eq(Q.SP.hm(h), m)), hok)), ha, hab, P.Bool.and_l(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), P.Bool.and_l(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca)), hv))), dp, E, hp, hdp, he, hob, P.Bool.and_r(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), P.Bool.and_l(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca)), hv))), P.Bool.and_r(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca)), hv)), DX.hseg(ts, tt, seg, cpl, wst, oend, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), P.Bool.and_r(Bool.and(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), ca)), hv)), hB)) :
        {_ == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, Q.ST{opos, ca, slot}, Q.HC{n, m, v}), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HC{n, m, v})), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HC{n, m, v})), Q.SP.dnext(Q.HC{n, m, v}, dpos), Q.SP.ipos(h, Q.HC{n, m, v}, ipos), Q.SP.anext(Q.HC{n, m, v}, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, ca, slot}, Q.HC{n, m, v}))) : D.Dec}
      {==}

# Sections
# ========

# b + (c + a) = (a + b) + c.
law DX.nat3:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(b, Nat.add(c, a)) == Nat.add(Nat.add(a, b), c) : Nat}

def DX.nat3(a, b, c):
  %Equal.sym(Nat, Nat.add(c, a), Nat.add(a, c), P.Nat.add_comm(c, a)) :
    {Nat.add(b, _) == Nat.add(Nat.add(a, b), c) : Nat}
  %P.Nat.add_assoc(b, a, c) :
    {_ == Nat.add(Nat.add(a, b), c) : Nat}
  %Equal.sym(Nat, Nat.add(b, a), Nat.add(a, b), P.Nat.add_comm(b, a)) :
    {Nat.add(_, c) == Nat.add(Nat.add(a, b), c) : Nat}
  {==}

law DX.at_has:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +h: {Q.SP.at(xs, t, q, e) == True{} : Bool}
  {S.S.has(xs, t, q) == True{} : Bool}

def DX.at_has(xs, t, q, e, h):
  P.Bool.and_l(S.S.has(xs, t, q), Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), U32.to_nat(q)), U32.to_nat(e))), h)

law DX.at_le:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +h: {Q.SP.at(xs, t, q, e) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), V.U.N(e))) == True{} : Bool}

def DX.at_le(xs, t, q, e, h):
  P.Bool.and_r(S.S.has(xs, t, q), Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), U32.to_nat(q)), U32.to_nat(e))), h)

law DX.at_mk:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +h1: {S.S.has(xs, t, q) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Q.SP.at(xs, t, q, e) == True{} : Bool}

def DX.at_mk(xs, t, q, e, h1, h2):
  %Equal.sym(Bool, S.S.has(xs, t, q), True{}, h1) :
    {Bool.and(_, Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), V.U.N(e)))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), V.U.N(e))), True{}, h2) :
    {Bool.and(True{}, _) == True{} : Bool}
  {==}

# The bound past a held prefix.
law DX.at_next.le:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(ys), V.U.N(U32.add(q, x))), V.U.N(e))) == True{} : Bool}

law DX.at_next.qx:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(q), V.U.N(x)), V.U.N(e))) == True{} : Bool}

def DX.at_next.qx(xs, ys, q, e, x, ex, h):
  %Equal.sym(Nat, V.U.N(x), S.S.len(xs), ex) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(q), _), V.U.N(e))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(q), S.S.len(xs)), Nat.add(S.S.len(xs), V.U.N(q)), P.Nat.add_comm(V.U.N(q), S.S.len(xs))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  P.Nat.le_trans(Nat.add(S.S.len(xs), V.U.N(q)), Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(q)), V.U.N(e),
    C.CP.le_add_r(S.S.len(xs), S.S.len(K.WD.app(xs, ys)), V.U.N(q),
      (%Equal.sym(Nat, S.S.len(K.WD.app(xs, ys)), Nat.add(S.S.len(xs), S.S.len(ys)), K.WD.len_app(xs, ys)) :
          {Cmp.is_le(Nat.cmp(S.S.len(xs), _)) == True{} : Bool};
        P.Nat.cmp_add_r(S.S.len(xs), S.S.len(ys)))),
    h)

def DX.at_next.le(xs, ys, q, e, x, ex, h):
  %Equal.sym(Nat, V.U.N(U32.add(q, x)), Nat.add(V.U.N(q), V.U.N(x)), V.U.add_N(q, x, e, DX.at_next.qx(xs, ys, q, e, x, ex, h))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(ys), _), V.U.N(e))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(x), S.S.len(xs), ex) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(ys), Nat.add(V.U.N(q), _)), V.U.N(e))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(S.S.len(ys), Nat.add(V.U.N(q), S.S.len(xs))), Nat.add(Nat.add(S.S.len(xs), S.S.len(ys)), V.U.N(q)), DX.nat3(S.S.len(xs), S.S.len(ys), V.U.N(q))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  %K.WD.len_app(xs, ys) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  h

law DX.has_tail:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {S.S.has(K.WD.app(xs, ys), t, q) == True{} : Bool}
  {S.S.has(ys, t, U32.add(q, x)) == True{} : Bool}

def DX.has_tail(xs, ys, t, q, x, ex, h):
  P.Bool.and_r(S.S.has(xs, t, q), S.S.has(ys, t, U32.add(q, x)), (%K.WD.has_app(xs, ys, t, q, x, ex) : {_ == True{} : Bool}; h))

law DX.has_head:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {S.S.has(K.WD.app(xs, ys), t, q) == True{} : Bool}
  {S.S.has(xs, t, q) == True{} : Bool}

def DX.has_head(xs, ys, t, q, x, ex, h):
  P.Bool.and_l(S.S.has(xs, t, q), S.S.has(ys, t, U32.add(q, x)), (%K.WD.has_app(xs, ys, t, q, x, ex) : {_ == True{} : Bool}; h))

# Past a held prefix, the rest is held.
law DX.at_next:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +x: U32
  for +ex: {V.U.N(x) == S.S.len(xs) : Nat}
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {Q.SP.at(ys, t, U32.add(q, x), e) == True{} : Bool}

def DX.at_next(xs, ys, t, q, e, x, ex, h):
  DX.at_mk(ys, t, U32.add(q, x), e,
    DX.has_tail(xs, ys, t, q, x, ex, DX.at_has(K.WD.app(xs, ys), t, q, e, h)),
    DX.at_next.le(xs, ys, q, e, x, ex, DX.at_le(K.WD.app(xs, ys), t, q, e, h)))

law DX.sz_next.go:
  for +h: U32
  for +f: Q.HF
  for +rest: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +hat: {Q.SP.at(K.WD.app(Q.SP.sz(h, f), rest), t, q, e) == True{} : Bool}
  for +c: Bool
  for +ec: {Q.SP.z(h) == c : Bool}
  {Q.SP.at(rest, t, Q.SP.ipos(h, f, q), e) == True{} : Bool}

law DX.sz_false:
  for +h: U32
  for +f: Q.HF
  for +ez: {Q.SP.z(h) == False{} : Bool}
  {Q.SP.sz(h, f) == [] : List<&2, U32>}

def DX.sz_false(h, f, ez):
  %Equal.sym(Bool, Q.SP.z(h), False{}, ez) :
    {Bool.pick(List<&2, U32>, _, R.VI.var(Q.SP.size(f)), []) == [] : List<&2, U32>}
  {==}

def DX.sz_next.go(h, f, rest, t, q, e, hat, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, Q.SP.z(h), True{}, ec) :
        {Q.SP.at(rest, t, Bool.pick(U32, _, U32.add(q, B.B.var.len(Q.SP.size(f))), q), e) == True{} : Bool}
      DX.at_next(R.VI.var(Q.SP.size(f)), rest, t, q, e, B.B.var.len(Q.SP.size(f)), Equal.sym(Nat, S.S.len(R.VI.var(Q.SP.size(f))), V.U.N(B.B.var.len(Q.SP.size(f))), R.VI.len_var(Q.SP.size(f))), (%DX.sz_true(h, f, ec) : {Q.SP.at(K.WD.app(_, rest), t, q, e) == True{} : Bool}; hat))
    case False{}:
      %Equal.sym(Bool, Q.SP.z(h), False{}, ec) :
        {Q.SP.at(rest, t, Bool.pick(U32, _, U32.add(q, B.B.var.len(Q.SP.size(f))), q), e) == True{} : Bool}
      (%DX.sz_false(h, f, ec) : {Q.SP.at(K.WD.app(_, rest), t, q, e) == True{} : Bool}; hat)

law DX.sz_next:
  for +h: U32
  for +f: Q.HF
  for +rest: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +hat: {Q.SP.at(K.WD.app(Q.SP.sz(h, f), rest), t, q, e) == True{} : Bool}
  {Q.SP.at(rest, t, Q.SP.ipos(h, f, q), e) == True{} : Bool}

def DX.sz_next(h, f, rest, t, q, e, hat):
  DX.sz_next.go(h, f, rest, t, q, e, hat, Q.SP.z(h), {==})

law DX.dat_next:
  for +f: Q.HF
  for +rest: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +hdok: {Q.SP.dok(f) == True{} : Bool}
  for +hat: {Q.SP.at(K.WD.app(Q.SP.dat(f), rest), t, q, e) == True{} : Bool}
  {Q.SP.at(rest, t, Q.SP.dnext(f, q), e) == True{} : Bool}

def DX.dat_next(f, rest, t, q, e, hdok, hat):
  match f:
    case Q.HN{}:
      hat
    case Q.HA{n, xs}:
      DX.at_next(xs, rest, t, q, e, n, DX.lenis(xs, n, hdok), hat)
    case Q.HR{n, b}:
      DX.at_next(b <> [], rest, t, q, e, 1, {==}, hat)
    case Q.HC{n, m, v}:
      hat

law DX.adr_next.go:
  for +m: U32
  for +v: U32
  for +rest: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +hat: {Q.SP.at(K.WD.app(Q.SP.adr.m(U32.is_lt(m, 6), v), rest), t, q, e) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(m, 6) == c : Bool}
  {Q.SP.at(rest, t, Bool.pick(U32, U32.is_lt(m, 6), U32.add(q, B.B.var.len(v)), U32.add(q, 1)), e) == True{} : Bool}

def DX.adr_next.go(m, v, rest, t, q, e, hat, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(m, 6), True{}, ec) :
        {Q.SP.at(rest, t, Bool.pick(U32, _, U32.add(q, B.B.var.len(v)), U32.add(q, 1)), e) == True{} : Bool}
      DX.at_next(R.VI.var(v), rest, t, q, e, B.B.var.len(v), Equal.sym(Nat, S.S.len(R.VI.var(v)), V.U.N(B.B.var.len(v)), R.VI.len_var(v)), (%ec : {Q.SP.at(K.WD.app(Q.SP.adr.m(_, v), rest), t, q, e) == True{} : Bool}; hat))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(m, 6), False{}, ec) :
        {Q.SP.at(rest, t, Bool.pick(U32, _, U32.add(q, B.B.var.len(v)), U32.add(q, 1)), e) == True{} : Bool}
      DX.at_next(v <> [], rest, t, q, e, 1, {==}, (%ec : {Q.SP.at(K.WD.app(Q.SP.adr.m(_, v), rest), t, q, e) == True{} : Bool}; hat))

law DX.adr_next:
  for +f: Q.HF
  for +rest: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +hat: {Q.SP.at(K.WD.app(Q.SP.adr(f), rest), t, q, e) == True{} : Bool}
  {Q.SP.at(rest, t, Q.SP.anext(f, q), e) == True{} : Bool}

def DX.adr_next(f, rest, t, q, e, hat):
  match f:
    case Q.HN{}:
      hat
    case Q.HA{n, xs}:
      hat
    case Q.HR{n, b}:
      hat
    case Q.HC{n, m, v}:
      DX.adr_next.go(m, v, rest, t, q, e, hat, U32.is_lt(m, 6), {==})

# A half from any state.
law DX.half_s:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +s: Q.ST
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +tt: A.Tr
  for +h: U32
  for +f: Q.HF
  for +restI: List<&2, U32>
  for +restD: List<&2, U32>
  for +restA: List<&2, U32>
  for +hok: {Q.SP.hok(h, f) == True{} : Bool}
  for +hi: {S.S.has(K.WD.app(Q.SP.sz(h, f), restI), td, ipos) == True{} : Bool}
  for +hib: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.sz(h, f)), V.U.N(ipos)), V.U.N(iend))) == True{} : Bool}
  for +hd: {S.S.has(K.WD.app(Q.SP.dat(f), restD), td, dpos) == True{} : Bool}
  for +hdb: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.dat(f)), V.U.N(dpos)), V.U.N(dend))) == True{} : Bool}
  for +ha: {S.S.has(K.WD.app(Q.SP.adr(f), restA), td, apos) == True{} : Bool}
  for +hab: {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.adr(f)), V.U.N(apos)), V.U.N(aend))) == True{} : Bool}
  for +hv: {Q.SP.vst(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f) == True{} : Bool}
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(Q.SP.size(f)), V.U.N(Q.SP.so(s))), V.U.N(E))) == True{} : Bool}
  for +hB: {Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f, E) == True{} : Bool}
  {D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, h, DX.st(ts, td, to, tb, Q.SP.sc(s), Q.SP.so(s), dpos, ipos, apos, Q.SP.ss(s))) == DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f)), Q.SP.dnext(f, dpos), Q.SP.ipos(h, f, ipos), Q.SP.anext(f, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f))) : D.Dec}

def DX.half_s(ts, td, to, tb, s, dpos, ipos, apos, seg, cpl, wst, oend, dend, iend, aend, tt, h, f, restI, restD, restA, hok, hi, hib, hd, hdb, ha, hab, hv, dp, E, hp, hdp, he, hob, hB):
  match s:
    case Q.ST{opos, ca, slot}:
      DX.half(ts, td, to, tb, ca, opos, dpos, ipos, apos, slot, seg, cpl, wst, oend, dend, iend, aend, tt, h, f, restI, restD, restA, hok, hi, hib, hd, hdb, ha, hab, hv, dp, E, hp, hdp, he, hob, hB)

# A half keeps the target tree perfect.
law DX.pf_out:
  for +x: Q.XC
  for +to: A.Tr
  for +s: Q.ST
  for +f: Q.HF
  for +dp: Nat
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  {A.T.pf(dp, Q.SP.out(x, to, s, f)) == True{} : Bool}

law DX.pf_cout:
  for +x: Q.XC
  for +to: A.Tr
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +dp: Nat
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  {A.T.pf(dp, Q.SP.cout(x, to, opos, n, addr)) == True{} : Bool}

law DX.pf_cout.go:
  for +ts: A.Tr
  for +to: A.Tr
  for +opos: U32
  for +n: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +addr: U32
  for +dp: Nat
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +c: Bool
  {A.T.pf(dp, Bool.pick(A.Tr, c, S.S.puts(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl))))) == True{} : Bool}

def DX.pf_cout.go(ts, to, opos, n, seg, cpl, wst, addr, dp, hp, c):
  match c:
    case True{}:
      S.S.pf_puts(dp, S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos, hp)
    case False{}:
      C.CP.pf_mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl)), dp, hp)

def DX.pf_cout(x, to, opos, n, addr, dp, hp):
  match x:
    case Q.XC{ts, tt, seg, cpl, wst, oend}:
      DX.pf_cout.go(ts, to, opos, n, seg, cpl, wst, addr, dp, hp, U32.is_lt(addr, cpl))

def DX.pf_out(x, to, s, f, dp, hp):
  match s f:
    case Q.ST{opos, c, slot} Q.HN{}:
      hp
    case Q.ST{opos, c, slot} Q.HA{n, xs}:
      S.S.pf_puts(dp, xs, to, opos, hp)
    case Q.ST{opos, c, slot} Q.HR{n, b}:
      S.S.pf_puts(dp, C.CP.rep(U32.to_nat(n), b), to, opos, hp)
    case Q.ST{opos, c, slot} Q.HC{n, m, v}:
      DX.pf_cout(x, to, opos, n, Q.SP.daddr(m, v, Q.SP.here(x, opos), c), dp, hp)

# The bound of a held list bounds its prefix.
law DX.at_pre:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +q: U32
  for +e: U32
  for +h: {Q.SP.at(K.WD.app(xs, ys), t, q, e) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), V.U.N(q)), V.U.N(e))) == True{} : Bool}

def DX.at_pre(xs, ys, t, q, e, h):
  P.Nat.le_trans(Nat.add(S.S.len(xs), V.U.N(q)), Nat.add(S.S.len(K.WD.app(xs, ys)), V.U.N(q)), V.U.N(e),
    C.CP.le_add_r(S.S.len(xs), S.S.len(K.WD.app(xs, ys)), V.U.N(q),
      (%Equal.sym(Nat, S.S.len(K.WD.app(xs, ys)), Nat.add(S.S.len(xs), S.S.len(ys)), K.WD.len_app(xs, ys)) :
          {Cmp.is_le(Nat.cmp(S.S.len(xs), _)) == True{} : Bool};
        P.Nat.cmp_add_r(S.S.len(xs), S.S.len(ys)))),
    DX.at_le(K.WD.app(xs, ys), t, q, e, h))

# An opcode
# =========

# The decoder on an opcode: its byte, its table entry, its two halves, then
# whether to go on.
law DX.op:
  for +ts: A.Tr
  for +td: A.Tr
  for +to: A.Tr
  for +tb: A.Tr
  for +s: Q.ST
  for +dpos: U32
  for +ipos: U32
  for +apos: U32
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +oend: U32
  for +dend: U32
  for +iend: U32
  for +aend: U32
  for +tt: A.Tr
  for +c: U32
  for +f1: Q.HF
  for +f2: Q.HF
  for +restI: List<&2, U32>
  for +restD: List<&2, U32>
  for +restA: List<&2, U32>
  for +hc: {Q.SP.cok(tb, Q.OP{c, f1, f2}) == True{} : Bool}
  for +hi: {Q.SP.at(K.WD.app(Q.SP.ins(Q.OP{c, f1, f2}), restI), td, ipos, iend) == True{} : Bool}
  for +hd: {Q.SP.at(K.WD.app(Q.SP.dat(f1), K.WD.app(Q.SP.dat(f2), restD)), td, dpos, dend) == True{} : Bool}
  for +ha: {Q.SP.at(K.WD.app(Q.SP.adr(f1), K.WD.app(Q.SP.adr(f2), restA)), td, apos, aend) == True{} : Bool}
  for +hv1: {Q.SP.vst(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1) == True{} : Bool}
  for +hv2: {Q.SP.vst(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2) == True{} : Bool}
  for +hdok1: {Q.SP.dok(f1) == True{} : Bool}
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hdp: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hob1: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(Q.SP.size(f1)), V.U.N(Q.SP.so(s))), V.U.N(E))) == True{} : Bool}
  for +hob2: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(Q.SP.size(f2)), V.U.N(Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)))), V.U.N(E))) == True{} : Bool}
  for +hB1: {Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1, E) == True{} : Bool}
  for +hB2: {Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2, E) == True{} : Bool}
  {D.dec.step(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, DX.st(ts, td, to, tb, Q.SP.sc(s), Q.SP.so(s), dpos, ipos, apos, Q.SP.ss(s))) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)))) : Bool & D.Dec}

def DX.op(ts, td, to, tb, s, dpos, ipos, apos, seg, cpl, wst, oend, dend, iend, aend, tt, c, f1, f2, restI, restD, restA, hc, hi, hd, ha, hv1, hv2, hdok1, dp, E, hp, hdp, he, hob1, hob2, hB1, hB2):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(td), ipos), (A.A.from(td), U32.and(c, 255)), R.VI.rd(td, ipos, c, K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), DX.at_has(c <> K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), td, ipos, iend, hi))) :
    {D.dec.opcode(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(Q.SP.sc(s)), Q.SP.so(s), dpos, ipos, apos, Q.SP.ss(s), 0, _) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) : Bool & D.Dec}
  %Equal.sym(U32, U32.and(c, 255), c, V.U.mask_id(c, 8n, {==}, P.Bool.and_l(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c)), P.Bool.and_l(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1), P.Bool.and_l(Bool.and(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1)), Q.SP.hok(Q.SP.e2(c), f2), hc))))) :
    {D.dec.opcode(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, A.A.from(ts), A.A.from(to), A.A.from(tb), A.A.from(Q.SP.sc(s)), Q.SP.so(s), dpos, ipos, apos, Q.SP.ss(s), 0, (A.A.from(td), _)) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) : Bool & D.Dec}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), c), (A.A.from(tb), A.T.word(tb, c)), A.A.get_from(tb, c)) :
    {D.dec.op(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(Q.SP.sc(s)), Q.SP.so(s), dpos, U32.add(ipos, 1), apos, Q.SP.ss(s), 0, _) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) : Bool & D.Dec}
  %Equal.sym(U32, A.T.word(tb, c), D.ct.entry(c), V.U.is_eq(A.T.word(tb, c), D.ct.entry(c), P.Bool.and_r(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c)), P.Bool.and_l(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1), P.Bool.and_l(Bool.and(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1)), Q.SP.hok(Q.SP.e2(c), f2), hc))))) :
    {D.dec.op(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, A.A.from(ts), A.A.from(td), A.A.from(to), A.A.from(Q.SP.sc(s)), Q.SP.so(s), dpos, U32.add(ipos, 1), apos, Q.SP.ss(s), 0, (A.A.from(tb), _)) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) : Bool & D.Dec}
  %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.e1(c), DX.st(ts, td, to, tb, Q.SP.sc(s), Q.SP.so(s), dpos, U32.add(ipos, 1), apos, Q.SP.ss(s))), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)), Q.SP.dnext(f1, dpos), Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1)), Q.SP.anext(f1, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1))), DX.half_s(ts, td, to, tb, s, dpos, U32.add(ipos, 1), apos, seg, cpl, wst, oend, dend, iend, aend, tt, Q.SP.e1(c), f1, K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI), K.WD.app(Q.SP.dat(f2), restD), K.WD.app(Q.SP.adr(f2), restA), P.Bool.and_r(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1), P.Bool.and_l(Bool.and(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1)), Q.SP.hok(Q.SP.e2(c), f2), hc)), DX.at_has(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI)), td, U32.add(ipos, 1), iend, (%K.WD.app_assoc(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2), restI) : {Q.SP.at(_, td, U32.add(ipos, 1), iend) == True{} : Bool}; DX.at_next(c <> [], K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), td, ipos, iend, 1, {==}, hi))), DX.at_pre(Q.SP.sz(Q.SP.e1(c), f1), K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI), td, U32.add(ipos, 1), iend, (%K.WD.app_assoc(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2), restI) : {Q.SP.at(_, td, U32.add(ipos, 1), iend) == True{} : Bool}; DX.at_next(c <> [], K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), td, ipos, iend, 1, {==}, hi))), DX.at_has(K.WD.app(Q.SP.dat(f1), K.WD.app(Q.SP.dat(f2), restD)), td, dpos, dend, hd), DX.at_pre(Q.SP.dat(f1), K.WD.app(Q.SP.dat(f2), restD), td, dpos, dend, hd), DX.at_has(K.WD.app(Q.SP.adr(f1), K.WD.app(Q.SP.adr(f2), restA)), td, apos, aend, ha), DX.at_pre(Q.SP.adr(f1), K.WD.app(Q.SP.adr(f2), restA), td, apos, aend, ha), hv1, dp, E, hp, hdp, he, hob1, hB1)) :
    {D.dec.more(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.e2(c), _)) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)))) : Bool & D.Dec}
  %Equal.sym(D.Dec, D.dec.half(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, Q.SP.e2(c), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)), Q.SP.dnext(f1, dpos), Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1)), Q.SP.anext(f1, apos), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1)))), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), DX.half_s(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), tb, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), Q.SP.dnext(f1, dpos), Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1)), Q.SP.anext(f1, apos), seg, cpl, wst, oend, dend, iend, aend, tt, Q.SP.e2(c), f2, restI, restD, restA, P.Bool.and_r(Bool.and(Bool.and(U32.is_lt(c, 256), U32.is_eq(A.T.word(tb, c), D.ct.entry(c))), Q.SP.hok(Q.SP.e1(c), f1)), Q.SP.hok(Q.SP.e2(c), f2), hc), DX.at_has(K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI), td, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1)), iend, DX.sz_next(Q.SP.e1(c), f1, K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI), td, U32.add(ipos, 1), iend, (%K.WD.app_assoc(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2), restI) : {Q.SP.at(_, td, U32.add(ipos, 1), iend) == True{} : Bool}; DX.at_next(c <> [], K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), td, ipos, iend, 1, {==}, hi)))), DX.at_pre(Q.SP.sz(Q.SP.e2(c), f2), restI, td, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1)), iend, DX.sz_next(Q.SP.e1(c), f1, K.WD.app(Q.SP.sz(Q.SP.e2(c), f2), restI), td, U32.add(ipos, 1), iend, (%K.WD.app_assoc(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2), restI) : {Q.SP.at(_, td, U32.add(ipos, 1), iend) == True{} : Bool}; DX.at_next(c <> [], K.WD.app(K.WD.app(Q.SP.sz(Q.SP.e1(c), f1), Q.SP.sz(Q.SP.e2(c), f2)), restI), td, ipos, iend, 1, {==}, hi)))), DX.at_has(K.WD.app(Q.SP.dat(f2), restD), td, Q.SP.dnext(f1, dpos), dend, DX.dat_next(f1, K.WD.app(Q.SP.dat(f2), restD), td, dpos, dend, hdok1, hd)), DX.at_pre(Q.SP.dat(f2), restD, td, Q.SP.dnext(f1, dpos), dend, DX.dat_next(f1, K.WD.app(Q.SP.dat(f2), restD), td, dpos, dend, hdok1, hd)), DX.at_has(K.WD.app(Q.SP.adr(f2), restA), td, Q.SP.anext(f1, apos), aend, DX.adr_next(f1, K.WD.app(Q.SP.adr(f2), restA), td, apos, aend, ha)), DX.at_pre(Q.SP.adr(f2), restA, td, Q.SP.anext(f1, apos), aend, DX.adr_next(f1, K.WD.app(Q.SP.adr(f2), restA), td, apos, aend, ha)), hv2, dp, E, DX.pf_out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1, dp, hp), hdp, he, hob2, hB2)) :
    {D.dec.more(D.WinC{seg, cpl, False{}, wst, oend, dend, iend, aend}, _) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), DX.st(ts, td, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2), tb, Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)))) : Bool & D.Dec}
  %Equal.sym(Bool, Bool.and(U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), True{}), U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), DX.and_true(U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend))) :
    {(_, D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) == (U32.is_lt(Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), iend), D.Dec{A.A.from(ts), A.A.from(td), A.A.from(Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.out(Q.XC{ts, tt, seg, cpl, wst, oend}, to, s, f1), Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), A.A.from(tb), A.A.from(Q.SP.sc(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2))), Q.SP.so(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), Q.SP.dnext(f2, Q.SP.dnext(f1, dpos)), Q.SP.ipos(Q.SP.e2(c), f2, Q.SP.ipos(Q.SP.e1(c), f1, U32.add(ipos, 1))), Q.SP.anext(f2, Q.SP.anext(f1, apos)), Q.SP.ss(Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.SP.next(Q.XC{ts, tt, seg, cpl, wst, oend}, s, f1), f2)), 0}) : Bool & D.Dec}
  {==}
