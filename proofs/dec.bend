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
