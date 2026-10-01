import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S

# B.eq is sound: when it says two byte strings agree, their bytes do.

# The comparison loop, on trees.
def E.w(n: Nat, +i: U32, +ta: A.Tr, +tb: A.Tr, s: Bool) -> Bool:
  match n s:
    case 0n b:
      b
    case 1n+p False{}:
      False{}
    case 1n+p True{}:
      E.w(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i)))

law E.loop:
  for +n: Nat
  for +i: U32
  for +ta: A.Tr
  for +tb: A.Tr
  for +s: Bool
  {B.B.eq.words(n, i, (s, (A.A.from(ta), A.A.from(tb))))
    == ((A.A.from(ta), A.A.from(tb)), E.w(n, i, ta, tb, s)) : (Array<U32> & Array<U32>) & Bool}

def E.loop(n, i, ta, tb, s):
  match n s:
    case 0n b:
      {==}
    case 1n+p False{}:
      {==}
    case 1n+p True{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(ta), i), (A.A.from(ta), A.T.word(ta, i)), A.A.get_from(ta, i)) :
        {B.B.eq.words(p, (i + 1 : U32), B.B.eq.k(_, Array.get(U32, A.A.from(tb), i)))
          == ((A.A.from(ta), A.A.from(tb)), E.w(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i))))
          : (Array<U32> & Array<U32>) & Bool}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), i), (A.A.from(tb), A.T.word(tb, i)), A.A.get_from(tb, i)) :
        {B.B.eq.words(p, (i + 1 : U32), B.B.eq.k((A.A.from(ta), A.T.word(ta, i)), _))
          == ((A.A.from(ta), A.A.from(tb)), E.w(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i))))
          : (Array<U32> & Array<U32>) & Bool}
      E.loop(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i)))

# A pass needs the flag it started with.
law E.s:
  for +n: Nat
  for +i: U32
  for +ta: A.Tr
  for +tb: A.Tr
  for +s: Bool
  for +h: {E.w(n, i, ta, tb, s) == True{} : Bool}
  {s == True{} : Bool}

def E.s(n, i, ta, tb, s, h):
  match n s:
    case 0n b:
      h
    case 1n+p False{}:
      P.Bool.false_true({False{} == True{} : Bool}, h)
    case 1n+p True{}:
      {==}

# A pass gives the words agree at every index it compared.
law E.at:
  for +n: Nat
  for +i: U32
  for +ta: A.Tr
  for +tb: A.Tr
  for +j: U32
  for +c: Cmp
  for +ec: {Nat.cmp(V.U.N(i), V.U.N(j)) == c : Cmp}
  for +h: {E.w(n, i, ta, tb, True{}) == True{} : Bool}
  for +lo: {Cmp.is_le(c) == True{} : Bool}
  for +hi: {Nat.cmp(V.U.N(j), Nat.add(V.U.N(i), n)) == LT{} : Cmp}
  for +e: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), n), V.U.N(e))) == True{} : Bool}
  {A.T.word(ta, j) == A.T.word(tb, j) : U32}

def E.at(n, i, ta, tb, j, c, ec, h, lo, hi, e, hb):
  match n c:
    case 0n _:
      P.Cmp.eq_lt({A.T.word(ta, j) == A.T.word(tb, j) : U32},
        (%P.Nat.cmp_refl(V.U.N(i)) : {_ == LT{} : Cmp}
          P.Nat.le_lt_trans(V.U.N(i), V.U.N(j), V.U.N(i),
            (%Equal.sym(Cmp, Nat.cmp(V.U.N(i), V.U.N(j)), c, ec) : {Cmp.is_le(_) == True{} : Bool}
              lo),
            (%P.Nat.add_zero_r(V.U.N(i)) : {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
              hi))))
    case 1n+p EQ{}:
      %V.U.eq_N(i, j, P.Nat.cmp_eq(V.U.N(i), V.U.N(j), ec)) : {A.T.word(ta, _) == A.T.word(tb, _) : U32}
      V.U.is_eq(A.T.word(ta, i), A.T.word(tb, i),
        E.s(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i)), h))
    case 1n+p LT{}:
      E.at(p, (i + 1 : U32), ta, tb, j, Nat.cmp(V.U.N((i + 1 : U32)), V.U.N(j)), {==},
        (%E.s(p, (i + 1 : U32), ta, tb, U32.is_eq(A.T.word(ta, i), A.T.word(tb, i)), h) :
            {E.w(p, (i + 1 : U32), ta, tb, _) == True{} : Bool}
          h),
        (%Equal.sym(Nat, V.U.N((i + 1 : U32)), 1n+V.U.N(i), V.U.succ_N(i, e, S.S.lt_of_bound(i, p, e, hb))) :
            {Cmp.is_le(Nat.cmp(_, V.U.N(j))) == True{} : Bool}
          P.Nat.lt_le_succ(V.U.N(i), V.U.N(j), ec)),
        (%Equal.sym(Nat, V.U.N((i + 1 : U32)), 1n+V.U.N(i), V.U.succ_N(i, e, S.S.lt_of_bound(i, p, e, hb))) :
            {Nat.cmp(V.U.N(j), Nat.add(_, p)) == LT{} : Cmp}
          (%P.Nat.add_succ_r(V.U.N(i), p) : {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
            hi)),
        e, S.S.bound_succ(i, p, e, hb))
    case 1n+p GT{}:
      P.Bool.false_true({A.T.word(ta, j) == A.T.word(tb, j) : U32}, lo)

# The words of la bytes, as a value.
law E.Nw:
  for +la: U32
  for +hla: {U32.is_lt(la, 134217728) == True{} : Bool}
  {V.U.N(B.B.words(la)) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(la), 3n))) : Nat}

def E.Nw(la, hla):
  %Equal.sym(Nat, V.U.N(U32.shr(U32.shr((la + 3 : U32)))), P.Nat.half(V.U.N(U32.shr((la + 3 : U32)))),
    V.U.N_shr(U32.shr((la + 3 : U32)))) :
    {_ == P.Nat.half(P.Nat.half(Nat.add(V.U.N(la), 3n))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shr((la + 3 : U32))), P.Nat.half(V.U.N((la + 3 : U32))), V.U.N_shr((la + 3 : U32))) :
    {P.Nat.half(_) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(la), 3n))) : Nat}
  %Equal.sym(Nat, V.U.N((la + 3 : U32)), Nat.add(V.U.N(la), V.U.N(3)),
    V.U.add_top(la, 3, V.U.bit_lt_pow(la, 27n, 31n, hla, {==}, {==}), {==})) :
    {P.Nat.half(P.Nat.half(_)) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(la), 3n))) : Nat}
  {==}

law E.refl:
  for +x: Nat
  {Cmp.is_le(Nat.cmp(x, x)) == True{} : Bool}

def E.refl(x):
  (%Equal.sym(Cmp, Nat.cmp(x, x), EQ{}, P.Nat.cmp_refl(x)) : {Cmp.is_le(_) == True{} : Bool}
    {==})

# Bytes below la, whose words agree, agree.
law E.sl:
  for +n: Nat
  for +ta: A.Tr
  for +tb: A.Tr
  for +p: U32
  for +la: U32
  for +hla: {U32.is_lt(la, 134217728) == True{} : Bool}
  for +hw: {E.w(V.U.N(B.B.words(la)), 0, ta, tb, True{}) == True{} : Bool}
  for +hp: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), n), V.U.N(la))) == True{} : Bool}
  {S.S.sl(n, ta, p) == S.S.sl(n, tb, p) : List<&2, U32>}

def E.sl(n, ta, tb, p, la, hla, hw, hp):
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(U32, A.T.word(ta, U32.shrn(p, 2n)), A.T.word(tb, U32.shrn(p, 2n)),
        E.at(V.U.N(B.B.words(la)), 0, ta, tb, U32.shrn(p, 2n), Nat.cmp(V.U.N(0), V.U.N(U32.shrn(p, 2n))), {==}, hw,
          P.Nat.le_zero(V.U.N(U32.shrn(p, 2n))),
          (%Equal.sym(Nat, V.U.N(U32.shr(U32.shr(p))), P.Nat.half(V.U.N(U32.shr(p))), V.U.N_shr(U32.shr(p))) :
              {Nat.cmp(_, V.U.N(B.B.words(la))) == LT{} : Cmp}
            (%Equal.sym(Nat, V.U.N(U32.shr(p)), P.Nat.half(V.U.N(p)), V.U.N_shr(p)) :
                {Nat.cmp(P.Nat.half(_), V.U.N(B.B.words(la))) == LT{} : Cmp}
              (%Equal.sym(Nat, V.U.N(B.B.words(la)), P.Nat.half(P.Nat.half(Nat.add(V.U.N(la), 3n))), E.Nw(la, hla)) :
                  {Nat.cmp(P.Nat.half(P.Nat.half(V.U.N(p))), _) == LT{} : Cmp}
                (%P.Nat.add_comm(3n, V.U.N(la)) :
                    {Nat.cmp(P.Nat.half(P.Nat.half(V.U.N(p))), P.Nat.half(P.Nat.half(_))) == LT{} : Cmp}
                  P.Nat.hh_lt(V.U.N(p), V.U.N(la), S.S.lt_of_bound(p, m, la, hp)))))),
          B.B.words(la), E.refl(V.U.N(B.B.words(la))))) :
        {Y.BP.ext(_, B.B.sh(p)) <> S.S.sl(m, ta, (p + 1 : U32)) == Y.BP.byt(tb, p) <> S.S.sl(m, tb, (p + 1 : U32))
          : List<&2, U32>}
      %Equal.sym(List<&2, U32>, S.S.sl(m, ta, (p + 1 : U32)), S.S.sl(m, tb, (p + 1 : U32)),
        E.sl(m, ta, tb, (p + 1 : U32), la, hla, hw, S.S.bound_succ(p, m, la, hp))) :
        {Y.BP.byt(tb, p) <> _ == Y.BP.byt(tb, p) <> S.S.sl(m, tb, (p + 1 : U32)) : List<&2, U32>}
      {==}

# What B.eq's passing pass means: the same bytes.
law E.sound:
  for +la: U32
  for +ta: A.Tr
  for +lb: U32
  for +tb: A.Tr
  for +hlb: {U32.is_lt(lb, 134217728) == True{} : Bool}
  for +h: {E.w(V.U.N(B.B.words(la)), 0, ta, tb, U32.is_eq(la, lb)) == True{} : Bool}
  {B.B.list(B.Bytes{la, A.A.from(ta)}) == B.B.list(B.Bytes{lb, A.A.from(tb)}) : List<&2, U32>}

def E.sound(la, ta, lb, tb, hlb, h):
  %Equal.sym(List<&2, U32>, B.B.list(B.Bytes{la, A.A.from(ta)}), S.S.sl(U32.to_nat(la), ta, 0), S.S.list(la, ta)) :
    {_ == B.B.list(B.Bytes{lb, A.A.from(tb)}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.B.list(B.Bytes{lb, A.A.from(tb)}), S.S.sl(U32.to_nat(lb), tb, 0), S.S.list(lb, tb)) :
    {S.S.sl(U32.to_nat(la), ta, 0) == _ : List<&2, U32>}
  %V.U.is_eq(la, lb, E.s(V.U.N(B.B.words(la)), 0, ta, tb, U32.is_eq(la, lb), h)) :
    {S.S.sl(U32.to_nat(la), ta, 0) == S.S.sl(U32.to_nat(_), tb, 0) : List<&2, U32>}
  E.sl(U32.to_nat(la), ta, tb, 0, la,
    (%Equal.sym(U32, la, lb, V.U.is_eq(la, lb, E.s(V.U.N(B.B.words(la)), 0, ta, tb, U32.is_eq(la, lb), h))) :
        {U32.is_lt(_, 134217728) == True{} : Bool}
      hlb),
    (%E.s(V.U.N(B.B.words(la)), 0, ta, tb, U32.is_eq(la, lb), h) :
        {E.w(V.U.N(B.B.words(la)), 0, ta, tb, _) == True{} : Bool}
      h),
    E.refl(V.U.N(la)))
