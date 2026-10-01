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
import ./spec.bend as Q

# What the decoder writes: when a tree holds a target's first bytes,
# writing bytes the target has next, or copying forward from earlier in
# it, makes it hold more of the target.
#
# Source: proofs/sem.bp (tools/bpp.py writes proofs/sem.bend from it).

# Order
# =====

law SM.absurd:
  for -A: Type
  for +x: Nat
  for +y: Nat
  for +hle: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}
  for +hlt: {Nat.cmp(y, x) == LT{} : Cmp}
  A

def SM.absurd(A, x, y, hle, hlt):
  P.Cmp.eq_lt(A, Equal.trans(Cmp, EQ{}, Nat.cmp(y, y), LT{}, Equal.sym(Cmp, Nat.cmp(y, y), EQ{}, P.Nat.cmp_refl(y)), P.Nat.lt_le_trans(y, x, y, hlt, hle)))

# x <= y and x != y: x < y.
law SM.lt_of_le_ne.go:
  for +x: U32
  for +y: U32
  for +hle: {Cmp.is_le(Nat.cmp(V.U.N(x), V.U.N(y))) == True{} : Bool}
  for +hne: {U32.is_eq(x, y) == False{} : Bool}
  for +c: Cmp
  for +ec: {Nat.cmp(V.U.N(x), V.U.N(y)) == c : Cmp}
  {Nat.cmp(V.U.N(x), V.U.N(y)) == LT{} : Cmp}

def SM.lt_of_le_ne.go(x, y, hle, hne, c, ec):
  match c:
    case LT{}:
      ec
    case EQ{}:
      P.Bool.false_true({Nat.cmp(V.U.N(x), V.U.N(y)) == LT{} : Cmp},
        Equal.trans(Bool, False{}, U32.is_eq(x, y), True{}, Equal.sym(Bool, U32.is_eq(x, y), False{}, hne),
          (%V.U.eq_N(x, y, P.Nat.cmp_eq(V.U.N(x), V.U.N(y), ec)) : {U32.is_eq(x, _) == True{} : Bool}; V.U.is_eq_refl(x))))
    case GT{}:
      P.Bool.false_true({Nat.cmp(V.U.N(x), V.U.N(y)) == LT{} : Cmp}, (%ec : {Cmp.is_le(_) == True{} : Bool}; hle))

law SM.lt_of_le_ne:
  for +x: U32
  for +y: U32
  for +hle: {Cmp.is_le(Nat.cmp(V.U.N(x), V.U.N(y))) == True{} : Bool}
  for +hne: {U32.is_eq(x, y) == False{} : Bool}
  {Nat.cmp(V.U.N(x), V.U.N(y)) == LT{} : Cmp}

def SM.lt_of_le_ne(x, y, hle, hne):
  SM.lt_of_le_ne.go(x, y, hle, hne, Nat.cmp(V.U.N(x), V.U.N(y)), {==})

# A held byte
# ===========

law SM.byt_head:
  for +tt: A.Tr
  for +t: A.Tr
  for +q: U32
  for +r: Nat
  for +h: {S.S.has(S.S.sl(1n+r, tt, q), t, q) == True{} : Bool}
  {Y.BP.byt(t, q) == Y.BP.byt(tt, q) : U32}

def SM.byt_head(tt, t, q, r, h):
  %Equal.sym(U32, Y.BP.byt(t, q), U32.and(Y.BP.byt(tt, q), 255), V.U.is_eq(Y.BP.byt(t, q), U32.and(Y.BP.byt(tt, q), 255), P.Bool.and_l(U32.is_eq(Y.BP.byt(t, q), U32.and(Y.BP.byt(tt, q), 255)), S.S.has(S.S.sl(r, tt, U32.add(q, 1)), t, U32.add(q, 1)), h))) :
    {_ == Y.BP.byt(tt, q) : U32}
  Y.BP.byt_255(tt, q)

# The value of q + 1, below a bound past q.
law SM.succ_N:
  for +r: Nat
  for +q: U32
  for +e: U32
  for +he: {Cmp.is_le(Nat.cmp(Nat.add(1n+r, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {V.U.N(U32.add(q, 1)) == 1n+V.U.N(q) : Nat}

def SM.succ_N(r, q, e, he):
  V.U.succ_N(q, e, K.WD.lt_of_succ_le(V.U.N(q), V.U.N(e), P.Nat.le_trans(1n+V.U.N(q), 1n+Nat.add(r, V.U.N(q)), V.U.N(e), P.Nat.le_add_l(r, V.U.N(q)), he)))

law SM.next_le:
  for +r: Nat
  for +q: U32
  for +e: U32
  for +he: {Cmp.is_le(Nat.cmp(Nat.add(1n+r, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(r, V.U.N(U32.add(q, 1))), V.U.N(e))) == True{} : Bool}

def SM.next_le(r, q, e, he):
  %Equal.sym(Nat, V.U.N(U32.add(q, 1)), 1n+V.U.N(q), SM.succ_N(r, q, e, he)) :
    {Cmp.is_le(Nat.cmp(Nat.add(r, _), V.U.N(e))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(r, 1n+V.U.N(q)), 1n+Nat.add(r, V.U.N(q)), P.Nat.add_succ_r(r, V.U.N(q))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  he

law SM.next_lt:
  for +r: Nat
  for +q: U32
  for +j: U32
  for +e: U32
  for +hj: {Nat.cmp(V.U.N(j), Nat.add(1n+r, V.U.N(q))) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(Nat.add(1n+r, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Nat.cmp(V.U.N(j), Nat.add(r, V.U.N(U32.add(q, 1)))) == LT{} : Cmp}

def SM.next_lt(r, q, j, e, hj, he):
  %Equal.sym(Nat, V.U.N(U32.add(q, 1)), 1n+V.U.N(q), SM.succ_N(r, q, e, he)) :
    {Nat.cmp(V.U.N(j), Nat.add(r, _)) == LT{} : Cmp}
  %Equal.sym(Nat, Nat.add(r, 1n+V.U.N(q)), 1n+Nat.add(r, V.U.N(q)), P.Nat.add_succ_r(r, V.U.N(q))) :
    {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
  hj

law SM.succ_le:
  for +r: Nat
  for +q: U32
  for +j: U32
  for +e: U32
  for +ec: {U32.is_eq(q, j) == False{} : Bool}
  for +hq: {Cmp.is_le(Nat.cmp(V.U.N(q), V.U.N(j))) == True{} : Bool}
  for +he: {Cmp.is_le(Nat.cmp(Nat.add(1n+r, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(q, 1)), V.U.N(j))) == True{} : Bool}

def SM.succ_le(r, q, j, e, ec, hq, he):
  %Equal.sym(Nat, V.U.N(U32.add(q, 1)), 1n+V.U.N(q), SM.succ_N(r, q, e, he)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(j))) == True{} : Bool}
  P.Nat.lt_le_succ(V.U.N(q), V.U.N(j), SM.lt_of_le_ne(q, j, hq, ec))

# A tree holding tt's bytes [q, q + a) has tt's byte at j in that range.
law SM.byt_held.go:
  for +a: Nat
  for +tt: A.Tr
  for +t: A.Tr
  for +q: U32
  for +j: U32
  for +e: U32
  for +h: {S.S.has(S.S.sl(a, tt, q), t, q) == True{} : Bool}
  for +hq: {Cmp.is_le(Nat.cmp(V.U.N(q), V.U.N(j))) == True{} : Bool}
  for +hj: {Nat.cmp(V.U.N(j), Nat.add(a, V.U.N(q))) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(Nat.add(a, V.U.N(q)), V.U.N(e))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_eq(q, j) == c : Bool}
  {Y.BP.byt(t, j) == Y.BP.byt(tt, j) : U32}

def SM.byt_held.go(a, tt, t, q, j, e, h, hq, hj, he, c, ec):
  match a c:
    case 0n _:
      SM.absurd({Y.BP.byt(t, j) == Y.BP.byt(tt, j) : U32}, V.U.N(q), V.U.N(j), hq, hj)
    case 1n+r True{}:
      %V.U.is_eq(q, j, ec) :
        {Y.BP.byt(t, _) == Y.BP.byt(tt, _) : U32}
      SM.byt_head(tt, t, q, r, h)
    case 1n+r False{}:
      SM.byt_held.go(r, tt, t, U32.add(q, 1), j, e, P.Bool.and_r(U32.is_eq(Y.BP.byt(t, q), U32.and(Y.BP.byt(tt, q), 255)), S.S.has(S.S.sl(r, tt, U32.add(q, 1)), t, U32.add(q, 1)), h), SM.succ_le(r, q, j, e, ec, hq, he), SM.next_lt(r, q, j, e, hj, he), SM.next_le(r, q, e, he), U32.is_eq(U32.add(q, 1), j), {==})

law SM.byt_held:
  for +a: Nat
  for +tt: A.Tr
  for +t: A.Tr
  for +j: U32
  for +e: U32
  for +h: {S.S.has(S.S.sl(a, tt, 0), t, 0) == True{} : Bool}
  for +hj: {Nat.cmp(V.U.N(j), a) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(a, V.U.N(e))) == True{} : Bool}
  {Y.BP.byt(t, j) == Y.BP.byt(tt, j) : U32}

def SM.byt_held(a, tt, t, j, e, h, hj, he):
  SM.byt_held.go(a, tt, t, 0, j, e, h, P.Nat.le_zero(V.U.N(j)), (%Equal.sym(Nat, Nat.add(a, 0n), a, P.Nat.add_zero_r(a)) : {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}; hj), (%Equal.sym(Nat, Nat.add(a, 0n), a, P.Nat.add_zero_r(a)) : {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}; he), U32.is_eq(0, j), {==})

# Extending a held prefix
# =======================

# Two trees holding ys at p hold each other's bytes there.
law SM.has_sl:
  for +ys: List<&2, U32>
  for +tt: A.Tr
  for +t: A.Tr
  for +p: U32
  for +h1: {S.S.has(ys, tt, p) == True{} : Bool}
  for +h2: {S.S.has(ys, t, p) == True{} : Bool}
  {S.S.has(S.S.sl(S.S.len(ys), tt, p), t, p) == True{} : Bool}

def SM.has_sl(ys, tt, t, p, h1, h2):
  match ys:
    case []:
      {==}
    case y <> r:
      %Equal.sym(U32, Y.BP.byt(tt, p), U32.and(y, 255), V.U.is_eq(Y.BP.byt(tt, p), U32.and(y, 255), P.Bool.and_l(U32.is_eq(Y.BP.byt(tt, p), U32.and(y, 255)), S.S.has(r, tt, U32.add(p, 1)), h1))) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, p), U32.and(_, 255)), S.S.has(S.S.sl(S.S.len(r), tt, U32.add(p, 1)), t, U32.add(p, 1))) == True{} : Bool}
      %Equal.sym(U32, U32.and(U32.and(y, 255), 255), U32.and(y, 255), Z.BB.and255(y)) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, p), _), S.S.has(S.S.sl(S.S.len(r), tt, U32.add(p, 1)), t, U32.add(p, 1))) == True{} : Bool}
      %Equal.sym(U32, Y.BP.byt(t, p), U32.and(y, 255), V.U.is_eq(Y.BP.byt(t, p), U32.and(y, 255), P.Bool.and_l(U32.is_eq(Y.BP.byt(t, p), U32.and(y, 255)), S.S.has(r, t, U32.add(p, 1)), h2))) :
        {Bool.and(U32.is_eq(_, U32.and(y, 255)), S.S.has(S.S.sl(S.S.len(r), tt, U32.add(p, 1)), t, U32.add(p, 1))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(U32.and(y, 255), U32.and(y, 255)), True{}, V.U.is_eq_refl(U32.and(y, 255))) :
        {Bool.and(_, S.S.has(S.S.sl(S.S.len(r), tt, U32.add(p, 1)), t, U32.add(p, 1))) == True{} : Bool}
      SM.has_sl(r, tt, t, U32.add(p, 1), P.Bool.and_r(U32.is_eq(Y.BP.byt(tt, p), U32.and(y, 255)), S.S.has(r, tt, U32.add(p, 1)), h1), P.Bool.and_r(U32.is_eq(Y.BP.byt(t, p), U32.and(y, 255)), S.S.has(r, t, U32.add(p, 1)), h2))

law SM.zero_add:
  for +p: U32
  {U32.add(0, p) == p : U32}

def SM.zero_add(p):
  %Equal.sym(U32, U32.add(0, p), U32.add(p, 0), U32.add_comm(0, p)) :
    {_ == p : U32}
  V.U.add_zero_r(p)

# A tree holding tt's first p bytes, written at p with bytes tt has there,
# holds tt's first p + len(ys) bytes.
law SM.ext:
  for +dp: Nat
  for +tt: A.Tr
  for +t: A.Tr
  for +p: U32
  for +ys: List<&2, U32>
  for +e: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), S.S.len(ys)), V.U.N(e))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(p), tt, 0), t, 0) == True{} : Bool}
  for +hy: {S.S.has(ys, tt, p) == True{} : Bool}
  {S.S.has(S.S.sl(Nat.add(V.U.N(p), S.S.len(ys)), tt, 0), S.S.puts(ys, t, p), 0) == True{} : Bool}

def SM.ext(dp, tt, t, p, ys, e, hp, hd, he, hb, h, hy):
  %Equal.sym(List<&2, U32>, S.S.sl(Nat.add(V.U.N(p), S.S.len(ys)), tt, 0), K.WD.app(S.S.sl(V.U.N(p), tt, 0), S.S.sl(S.S.len(ys), tt, U32.add(0, p))), K.WD.sl_app(V.U.N(p), S.S.len(ys), tt, 0, p, {==})) :
    {S.S.has(_, S.S.puts(ys, t, p), 0) == True{} : Bool}
  %Equal.sym(U32, U32.add(0, p), p, SM.zero_add(p)) :
    {S.S.has(K.WD.app(S.S.sl(V.U.N(p), tt, 0), S.S.sl(S.S.len(ys), tt, _)), S.S.puts(ys, t, p), 0) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(K.WD.app(S.S.sl(V.U.N(p), tt, 0), S.S.sl(S.S.len(ys), tt, p)), S.S.puts(ys, t, p), 0), Bool.and(S.S.has(S.S.sl(V.U.N(p), tt, 0), S.S.puts(ys, t, p), 0), S.S.has(S.S.sl(S.S.len(ys), tt, p), S.S.puts(ys, t, p), U32.add(0, p))), K.WD.has_app(S.S.sl(V.U.N(p), tt, 0), S.S.sl(S.S.len(ys), tt, p), S.S.puts(ys, t, p), 0, p, Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(p), tt, 0)), V.U.N(p), S.S.len_sl(V.U.N(p), tt, 0)))) :
    {_ == True{} : Bool}
  %Equal.sym(U32, U32.add(0, p), p, SM.zero_add(p)) :
    {Bool.and(S.S.has(S.S.sl(V.U.N(p), tt, 0), S.S.puts(ys, t, p), 0), S.S.has(S.S.sl(S.S.len(ys), tt, p), S.S.puts(ys, t, p), _)) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(p), tt, 0), S.S.puts(ys, t, p), 0), S.S.has(S.S.sl(V.U.N(p), tt, 0), t, 0), S.S.has_puts_lt(dp, S.S.sl(V.U.N(p), tt, 0), t, p, ys, 0, e, hp, hd, he, hb, (%Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(p), tt, 0)), V.U.N(p), S.S.len_sl(V.U.N(p), tt, 0)) : {Cmp.is_le(Nat.cmp(Nat.add(0n, _), V.U.N(p))) == True{} : Bool}; C.CP.le_refl(V.U.N(p))))) :
    {Bool.and(_, S.S.has(S.S.sl(S.S.len(ys), tt, p), S.S.puts(ys, t, p), p)) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(p), tt, 0), t, 0), True{}, h) :
    {Bool.and(_, S.S.has(S.S.sl(S.S.len(ys), tt, p), S.S.puts(ys, t, p), p)) == True{} : Bool}
  SM.has_sl(ys, tt, S.S.puts(ys, t, p), p, hy, S.S.has_puts(dp, ys, t, p, e, hp, hd, he, hb))

# x + 1 as a value, below e.
law SM.succ_N2:
  for +x: U32
  for +e: U32
  for +h: {Nat.cmp(V.U.N(x), V.U.N(e)) == LT{} : Cmp}
  {Nat.add(V.U.N(x), 1n) == V.U.N(U32.add(x, 1)) : Nat}

def SM.succ_N2(x, e, h):
  %Equal.sym(Nat, V.U.N(U32.add(x, 1)), 1n+V.U.N(x), V.U.succ_N(x, e, h)) :
    {Nat.add(V.U.N(x), 1n) == _ : Nat}
  P.Nat.add_one(V.U.N(x))

law SM.lt_e:
  for +opos: U32
  for +m: Nat
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n+m), V.U.N(e))) == True{} : Bool}
  {Nat.cmp(V.U.N(opos), V.U.N(e)) == LT{} : Cmp}

law SM.le_succ_add:
  for +a: Nat
  for +m: Nat
  {Cmp.is_le(Nat.cmp(1n+a, Nat.add(a, 1n+m))) == True{} : Bool}

def SM.le_succ_add(a, m):
  %Equal.sym(Nat, Nat.add(a, 1n+m), 1n+Nat.add(a, m), P.Nat.add_succ_r(a, m)) :
    {Cmp.is_le(Nat.cmp(1n+a, _)) == True{} : Bool}
  P.Nat.cmp_add_r(a, m)

def SM.lt_e(opos, m, e, hb):
  K.WD.lt_of_succ_le(V.U.N(opos), V.U.N(e), P.Nat.le_trans(1n+V.U.N(opos), Nat.add(V.U.N(opos), 1n+m), V.U.N(e), SM.le_succ_add(V.U.N(opos), m), hb))

law SM.hy1:
  for +tt: A.Tr
  for +opos: U32
  for +from: U32
  for +m: Nat
  for +hc: {S.S.has(S.S.sl(1n+m, tt, from), tt, opos) == True{} : Bool}
  {S.S.has(Y.BP.byt(tt, from) <> [], tt, opos) == True{} : Bool}

def SM.hy1(tt, opos, from, m, hc):
  %Equal.sym(U32, Y.BP.byt(tt, opos), U32.and(Y.BP.byt(tt, from), 255), V.U.is_eq(Y.BP.byt(tt, opos), U32.and(Y.BP.byt(tt, from), 255), P.Bool.and_l(U32.is_eq(Y.BP.byt(tt, opos), U32.and(Y.BP.byt(tt, from), 255)), S.S.has(S.S.sl(m, tt, U32.add(from, 1)), tt, U32.add(opos, 1)), hc))) :
    {Bool.and(U32.is_eq(_, U32.and(Y.BP.byt(tt, from), 255)), True{}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(U32.and(Y.BP.byt(tt, from), 255), U32.and(Y.BP.byt(tt, from), 255)), True{}, V.U.is_eq_refl(U32.and(Y.BP.byt(tt, from), 255))) :
    {Bool.and(_, True{}) == True{} : Bool}
  {==}

# A forward copy from earlier in tt, of bytes tt repeats there, extends the
# held prefix (a copy may read bytes it wrote).
law SM.mv:
  for +k: Nat
  for +dp: Nat
  for +tt: A.Tr
  for +t: A.Tr
  for +opos: U32
  for +from: U32
  for +e: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), k), V.U.N(e))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(opos), tt, 0), t, 0) == True{} : Bool}
  for +hc: {S.S.has(S.S.sl(k, tt, from), tt, opos) == True{} : Bool}
  for +hf: {Nat.cmp(V.U.N(from), V.U.N(opos)) == LT{} : Cmp}
  {S.S.has(S.S.sl(Nat.add(V.U.N(opos), k), tt, 0), C.CP.mv(k, t, opos, from), 0) == True{} : Bool}

law SM.mv.hb:
  for +opos: U32
  for +m: Nat
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n+m), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(opos, 1)), m), V.U.N(e))) == True{} : Bool}

def SM.mv.hb(opos, m, e, hb):
  %Equal.sym(Nat, V.U.N(U32.add(opos, 1)), 1n+V.U.N(opos), V.U.succ_N(opos, e, SM.lt_e(opos, m, e, hb))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, m), V.U.N(e))) == True{} : Bool}
  %P.Nat.add_succ_r(V.U.N(opos), m) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  hb

law SM.mv.hb1:
  for +opos: U32
  for +m: Nat
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n+m), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n), V.U.N(e))) == True{} : Bool}

def SM.mv.hb1(opos, m, e, hb):
  %Equal.sym(Nat, Nat.add(V.U.N(opos), 1n), 1n+V.U.N(opos), P.Nat.add_one(V.U.N(opos))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  P.Nat.lt_le_succ(V.U.N(opos), V.U.N(e), SM.lt_e(opos, m, e, hb))

law SM.mv.hf:
  for +opos: U32
  for +from: U32
  for +m: Nat
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), 1n+m), V.U.N(e))) == True{} : Bool}
  for +hf: {Nat.cmp(V.U.N(from), V.U.N(opos)) == LT{} : Cmp}
  {Nat.cmp(V.U.N(U32.add(from, 1)), V.U.N(U32.add(opos, 1))) == LT{} : Cmp}

def SM.mv.hf(opos, from, m, e, hb, hf):
  %Equal.sym(Nat, V.U.N(U32.add(opos, 1)), 1n+V.U.N(opos), V.U.succ_N(opos, e, SM.lt_e(opos, m, e, hb))) :
    {Nat.cmp(V.U.N(U32.add(from, 1)), _) == LT{} : Cmp}
  %Equal.sym(Nat, V.U.N(U32.add(from, 1)), 1n+V.U.N(from), V.U.succ_N(from, e, P.Nat.lt_trans(V.U.N(from), V.U.N(opos), V.U.N(e), hf, SM.lt_e(opos, m, e, hb)))) :
    {Nat.cmp(_, 1n+V.U.N(opos)) == LT{} : Cmp}
  hf

def SM.mv(k, dp, tt, t, opos, from, e, hp, hd, he, hb, h, hc, hf):
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(V.U.N(opos), 0n), V.U.N(opos), P.Nat.add_zero_r(V.U.N(opos))) :
        {S.S.has(S.S.sl(_, tt, 0), C.CP.mv(0n, t, opos, from), 0) == True{} : Bool}
      h
    case 1n+m:
      %Equal.sym(U32, Y.BP.byt(t, from), Y.BP.byt(tt, from), SM.byt_held(V.U.N(opos), tt, t, from, e, h, hf, P.Nat.lt_to_le(V.U.N(opos), V.U.N(e), SM.lt_e(opos, m, e, hb)))) :
        {S.S.has(S.S.sl(Nat.add(V.U.N(opos), 1n+m), tt, 0), C.CP.mv(m, Y.BP.put(t, opos, _), U32.add(opos, 1), U32.add(from, 1)), 0) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(V.U.N(opos), 1n+m), 1n+Nat.add(V.U.N(opos), m), P.Nat.add_succ_r(V.U.N(opos), m)) :
        {S.S.has(S.S.sl(_, tt, 0), C.CP.mv(m, Y.BP.put(t, opos, Y.BP.byt(tt, from)), U32.add(opos, 1), U32.add(from, 1)), 0) == True{} : Bool}
      (%V.U.succ_N(opos, e, SM.lt_e(opos, m, e, hb)) : {S.S.has(S.S.sl(Nat.add(_, m), tt, 0), C.CP.mv(m, Y.BP.put(t, opos, Y.BP.byt(tt, from)), U32.add(opos, 1), U32.add(from, 1)), 0) == True{} : Bool};
        SM.mv(m, dp, tt, Y.BP.put(t, opos, Y.BP.byt(tt, from)), U32.add(opos, 1), U32.add(from, 1), e,
          Y.BP.pf_put(dp, t, opos, Y.BP.byt(tt, from), hp), hd, he,
          SM.mv.hb(opos, m, e, hb),
          (%SM.succ_N2(opos, e, SM.lt_e(opos, m, e, hb)) : {S.S.has(S.S.sl(_, tt, 0), Y.BP.put(t, opos, Y.BP.byt(tt, from)), 0) == True{} : Bool};
            SM.ext(dp, tt, t, opos, Y.BP.byt(tt, from) <> [], e, hp, hd, he, SM.mv.hb1(opos, m, e, hb), h, SM.hy1(tt, opos, from, m, hc))),
          P.Bool.and_r(U32.is_eq(Y.BP.byt(tt, opos), U32.and(Y.BP.byt(tt, from), 255)), S.S.has(S.S.sl(m, tt, U32.add(from, 1)), tt, U32.add(opos, 1)), hc),
          SM.mv.hf(opos, from, m, e, hb, hf)))

# A half keeps the target tree perfect.
law SM.pf_out:
  for +x: Q.XC
  for +to: A.Tr
  for +s: Q.ST
  for +f: Q.HF
  for +dp: Nat
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  {A.T.pf(dp, Q.SP.out(x, to, s, f)) == True{} : Bool}

law SM.pf_cout:
  for +x: Q.XC
  for +to: A.Tr
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +dp: Nat
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  {A.T.pf(dp, Q.SP.cout(x, to, opos, n, addr)) == True{} : Bool}

law SM.pf_cout.go:
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

def SM.pf_cout.go(ts, to, opos, n, seg, cpl, wst, addr, dp, hp, c):
  match c:
    case True{}:
      S.S.pf_puts(dp, S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos, hp)
    case False{}:
      C.CP.pf_mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl)), dp, hp)

def SM.pf_cout(x, to, opos, n, addr, dp, hp):
  match x:
    case Q.XC{ts, tt, seg, cpl, wst, oend}:
      SM.pf_cout.go(ts, to, opos, n, seg, cpl, wst, addr, dp, hp, U32.is_lt(addr, cpl))

def SM.pf_out(x, to, s, f, dp, hp):
  match s f:
    case Q.ST{opos, c, slot} Q.HN{}:
      hp
    case Q.ST{opos, c, slot} Q.HA{n, xs}:
      S.S.pf_puts(dp, xs, to, opos, hp)
    case Q.ST{opos, c, slot} Q.HR{n, b}:
      S.S.pf_puts(dp, C.CP.rep(U32.to_nat(n), b), to, opos, hp)
    case Q.ST{opos, c, slot} Q.HC{n, m, v}:
      SM.pf_cout(x, to, opos, n, Q.SP.daddr(m, v, Q.SP.here(x, opos), c), dp, hp)

# Halves
# ======

# Writing n bytes tt has at opos (n their length, opos + n below E).
law SM.put_n:
  for +tt: A.Tr
  for +to: A.Tr
  for +opos: U32
  for +n: U32
  for +ys: List<&2, U32>
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hl: {S.S.len(ys) == V.U.N(n) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(opos)), V.U.N(E))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(opos), tt, 0), to, 0) == True{} : Bool}
  for +hy: {S.S.has(ys, tt, opos) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(U32.add(opos, n)), tt, 0), S.S.puts(ys, to, opos), 0) == True{} : Bool}

def SM.put_n(tt, to, opos, n, ys, dp, E, hp, hd, he, hl, hb, h, hy):
  %Equal.sym(Nat, V.U.N(U32.add(opos, n)), Nat.add(V.U.N(opos), V.U.N(n)), V.U.add_N(opos, n, E, (%P.Nat.add_comm(V.U.N(n), V.U.N(opos)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb))) :
    {S.S.has(S.S.sl(_, tt, 0), S.S.puts(ys, to, opos), 0) == True{} : Bool}
  %hl :
    {S.S.has(S.S.sl(Nat.add(V.U.N(opos), _), tt, 0), S.S.puts(ys, to, opos), 0) == True{} : Bool}
  SM.ext(dp, tt, to, opos, ys, E, hp, hd, he, (%Equal.sym(Nat, S.S.len(ys), V.U.N(n), hl) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(opos), _), V.U.N(E))) == True{} : Bool}; (%P.Nat.add_comm(V.U.N(n), V.U.N(opos)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb)), h, hy)

law SM.lenis:
  for +xs: List<&2, U32>
  for +n: U32
  for +h: {Q.SP.lenis(xs, n) == True{} : Bool}
  {S.S.len(xs) == V.U.N(n) : Nat}

law SM.cmp_eq_t:
  for +c: Cmp
  for +h: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def SM.cmp_eq_t(c, h):
  match c:
    case LT{}:
      P.Bool.false_true({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.false_true({GT{} == EQ{} : Cmp}, h)

def SM.lenis(xs, n, h):
  P.Nat.cmp_eq(S.S.len(xs), V.U.N(n), SM.cmp_eq_t(Nat.cmp(S.S.len(xs), V.U.N(n)), h))

law SM.cmp_lt_t:
  for +c: Cmp
  for +h: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}

def SM.cmp_lt_t(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      P.Bool.false_true({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      P.Bool.false_true({GT{} == LT{} : Cmp}, h)

# A COPY's bytes extend the held prefix, for either kind of address.
law SM.copy.go:
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +wst: U32
  for +to: A.Tr
  for +opos: U32
  for +n: U32
  for +addr: U32
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(opos)), U32.to_nat(E))) == True{} : Bool}
  for +hcp: {Bool.pick(Bool, U32.is_lt(addr, cpl), Bool.and(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos)), S.S.has(S.S.sl(U32.to_nat(n), tt, U32.add(wst, U32.sub(addr, cpl))), tt, opos)) == True{} : Bool}
  for +hcb: {Bool.pick(Bool, U32.is_lt(addr, cpl), Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(U32.add(seg, addr))), U32.to_nat(Es))), Cmp.is_lt(Nat.cmp(U32.to_nat(U32.add(wst, U32.sub(addr, cpl))), U32.to_nat(opos)))) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(opos), tt, 0), to, 0) == True{} : Bool}
  for +k: Bool
  for +ek: {U32.is_lt(addr, cpl) == k : Bool}
  {S.S.has(S.S.sl(V.U.N(U32.add(opos, n)), tt, 0), Bool.pick(A.Tr, U32.is_lt(addr, cpl), S.S.puts(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), 0) == True{} : Bool}

def SM.copy.go(ts, tt, seg, cpl, wst, to, opos, n, addr, dp, E, Es, hp, hd, he, hb, hcp, hcb, h, k, ek):
  match k:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(addr, cpl), True{}, ek) :
        {S.S.has(S.S.sl(V.U.N(U32.add(opos, n)), tt, 0), Bool.pick(A.Tr, _, S.S.puts(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), 0) == True{} : Bool}
      SM.put_n(tt, to, opos, n, S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), dp, E, hp, hd, he, S.S.len_sl(U32.to_nat(n), ts, U32.add(seg, addr)), hb, h, P.Bool.and_r(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos), (%ek : {Bool.pick(Bool, _, Bool.and(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos)), S.S.has(S.S.sl(U32.to_nat(n), tt, U32.add(wst, U32.sub(addr, cpl))), tt, opos)) == True{} : Bool}; hcp)))
    case False{}:
      %Equal.sym(Bool, U32.is_lt(addr, cpl), False{}, ek) :
        {S.S.has(S.S.sl(V.U.N(U32.add(opos, n)), tt, 0), Bool.pick(A.Tr, _, S.S.puts(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), to, opos), C.CP.mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl)))), 0) == True{} : Bool}
      %Equal.sym(Nat, V.U.N(U32.add(opos, n)), Nat.add(V.U.N(opos), V.U.N(n)), V.U.add_N(opos, n, E, (%P.Nat.add_comm(V.U.N(n), V.U.N(opos)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb))) :
        {S.S.has(S.S.sl(_, tt, 0), C.CP.mv(U32.to_nat(n), to, opos, U32.add(wst, U32.sub(addr, cpl))), 0) == True{} : Bool}
      SM.mv(U32.to_nat(n), dp, tt, to, opos, U32.add(wst, U32.sub(addr, cpl)), E, hp, hd, he, (%P.Nat.add_comm(V.U.N(n), V.U.N(opos)) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb), h, (%ek : {Bool.pick(Bool, _, Bool.and(U32.is_le(n, U32.sub(cpl, addr)), S.S.has(S.S.sl(U32.to_nat(n), ts, U32.add(seg, addr)), tt, opos)), S.S.has(S.S.sl(U32.to_nat(n), tt, U32.add(wst, U32.sub(addr, cpl))), tt, opos)) == True{} : Bool}; hcp), SM.cmp_lt_t(Nat.cmp(V.U.N(U32.add(wst, U32.sub(addr, cpl))), V.U.N(opos)), (%ek : {Bool.pick(Bool, _, Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(U32.add(seg, addr))), U32.to_nat(Es))), Cmp.is_lt(Nat.cmp(U32.to_nat(U32.add(wst, U32.sub(addr, cpl))), U32.to_nat(opos)))) == True{} : Bool}; hcb)))

# A half extends the held prefix of the target as far as it writes.
law SM.out:
  for +x: Q.XC
  for +to: A.Tr
  for +s: Q.ST
  for +f: Q.HF
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hv: {Q.SP.vst(x, s, f) == True{} : Bool}
  for +hb: {Q.SP.bnd(x, s, f, E, Es) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(Q.SP.so(s)), Q.SP.tt(x), 0), to, 0) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(Q.SP.so(Q.SP.next(x, s, f))), Q.SP.tt(x), 0), Q.SP.out(x, to, s, f), 0) == True{} : Bool}

def SM.out(x, to, s, f, dp, E, Es, hp, hd, he, hv, hb, h):
  match x s f:
    case Q.XC{ts, tt, seg, cpl, wst, oend} Q.ST{opos, c, slot} Q.HN{}:
      h
    case Q.XC{ts, tt, seg, cpl, wst, oend} Q.ST{opos, c, slot} Q.HA{n, xs}:
      SM.put_n(tt, to, opos, n, xs, dp, E, hp, hd, he, SM.lenis(xs, n, P.Bool.and_l(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), P.Bool.and_l(Bool.and(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), S.S.has(xs, Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv))), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(opos)), U32.to_nat(E))), Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, c, slot}, Q.HA{n, xs}, Es), hb), h, P.Bool.and_r(Bool.and(Q.SP.lenis(xs, n), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), S.S.has(xs, Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv))
    case Q.XC{ts, tt, seg, cpl, wst, oend} Q.ST{opos, c, slot} Q.HR{n, b}:
      SM.put_n(tt, to, opos, n, C.CP.rep(U32.to_nat(n), b), dp, E, hp, hd, he, C.CP.len_rep(U32.to_nat(n), b), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(opos)), U32.to_nat(E))), Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, c, slot}, Q.HR{n, b}, Es), hb), h, P.Bool.and_r(Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n), S.S.has(C.CP.rep(U32.to_nat(n), b), Q.SP.tt(Q.XC{ts, tt, seg, cpl, wst, oend}), opos), hv))
    case Q.XC{ts, tt, seg, cpl, wst, oend} Q.ST{opos, c, slot} Q.HC{n, m, v}:
      SM.copy.go(ts, tt, seg, cpl, wst, to, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), c), dp, E, Es, hp, hd, he, P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(opos)), U32.to_nat(E))), Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, c, slot}, Q.HC{n, m, v}, Es), hb), P.Bool.and_r(Bool.and(Bool.and(Q.SP.aok(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos)), U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), c), Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos))), Q.SP.room(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n)), Q.SP.cpok(Q.XC{ts, tt, seg, cpl, wst, oend}, opos, n, Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), c)), hv), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat(opos)), U32.to_nat(E))), Q.SP.hbnd(Q.XC{ts, tt, seg, cpl, wst, oend}, Q.ST{opos, c, slot}, Q.HC{n, m, v}, Es), hb), h, U32.is_lt(Q.SP.daddr(m, v, Q.SP.here(Q.XC{ts, tt, seg, cpl, wst, oend}, opos), c), cpl), {==})

# All the halves of a window, in turn.
law SM.outs:
  for +hs: List<&2, Q.HF>
  for +x: Q.XC
  for +to: A.Tr
  for +s: Q.ST
  for +dp: Nat
  for +E: U32
  for +Es: U32
  for +hp: {A.T.pf(dp, to) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hv: {Q.SP.vhs(hs, x, s) == True{} : Bool}
  for +hb: {Q.SP.bnds(hs, x, s, E, Es) == True{} : Bool}
  for +h: {S.S.has(S.S.sl(V.U.N(Q.SP.so(s)), Q.SP.tt(x), 0), to, 0) == True{} : Bool}
  {S.S.has(S.S.sl(V.U.N(Q.SP.so(Q.SP.run(hs, x, s))), Q.SP.tt(x), 0), Q.SP.outs(hs, x, to, s), 0) == True{} : Bool}

def SM.outs(hs, x, to, s, dp, E, Es, hp, hd, he, hv, hb, h):
  match hs:
    case []:
      h
    case f <> r:
      SM.outs(r, x, Q.SP.out(x, to, s, f), Q.SP.next(x, s, f), dp, E, Es, SM.pf_out(x, to, s, f, dp, hp), hd, he,
        P.Bool.and_r(Q.SP.vst(x, s, f), Q.SP.vhs(r, x, Q.SP.next(x, s, f)), hv),
        P.Bool.and_r(Q.SP.bnd(x, s, f, E, Es), Q.SP.bnds(r, x, Q.SP.next(x, s, f), E, Es), hb),
        SM.out(x, to, s, f, dp, E, Es, hp, hd, he, P.Bool.and_l(Q.SP.vst(x, s, f), Q.SP.vhs(r, x, Q.SP.next(x, s, f)), hv), P.Bool.and_l(Q.SP.bnd(x, s, f, E, Es), Q.SP.bnds(r, x, Q.SP.next(x, s, f), E, Es), hb), h))
