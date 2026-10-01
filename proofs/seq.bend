import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y

# Byte strings as lists: the bytes of a tree from a position, writing a list
# of bytes, and whether a tree holds a list. Writes in a perfect tree, inside
# its range, leave the bytes below them alone, so a list written stays.

# Lists
# =====

def S.len(+xs: List<&2, U32>) -> Nat:
  match xs:
    case []:
      0n
    case x <> r:
      1n+S.len(r)

# The n bytes of t from i.
def S.sl(+n: Nat, +t: A.Tr, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+k:
      Y.BP.byt(t, i) <> S.sl(k, t, (i + 1 : U32))

# t after writing the bytes xs from i.
def S.puts(+xs: List<&2, U32>, +t: A.Tr, +i: U32) -> A.Tr:
  match xs:
    case []:
      t
    case x <> r:
      S.puts(r, Y.BP.put(t, i, x), (i + 1 : U32))

# Whether t holds the bytes xs (mod 256) from i.
def S.has(+xs: List<&2, U32>, +t: A.Tr, +i: U32) -> Bool:
  match xs:
    case []:
      True{}
    case x <> r:
      Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(x, 255)), S.has(r, t, (i + 1 : U32)))

# The position after xs from i.
def S.adv(+xs: List<&2, U32>, +i: U32) -> U32:
  match xs:
    case []:
      i
    case x <> r:
      S.adv(r, (i + 1 : U32))

# Positions
# =========

# k + 1 + n <= e gives k < e.
law S.lt_of_bound:
  for +k: U32
  for +n: Nat
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), 1n+n), V.U.N(e))) == True{} : Bool}
  {Nat.cmp(V.U.N(k), V.U.N(e)) == LT{} : Cmp}

def S.lt_of_bound(k, n, e, h):
  P.Nat.lt_of_add_succ(V.U.N(k), n, V.U.N(e), h)

# k + 1 + n <= e gives (k + 1) + n <= e.
law S.bound_succ:
  for +k: U32
  for +n: Nat
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), 1n+n), V.U.N(e))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N((k + 1 : U32)), n), V.U.N(e))) == True{} : Bool}

def S.bound_succ(k, n, e, h):
  %Equal.sym(Nat, V.U.N((k + 1 : U32)), 1n+V.U.N(k), V.U.succ_N(k, e, S.lt_of_bound(k, n, e, h))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, n), V.U.N(e))) == True{} : Bool}
  %P.Nat.add_succ_r(V.U.N(k), n) : {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}
  h

# The position after xs.
law S.adv_N:
  for +xs: List<&2, U32>
  for +i: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), S.len(xs)), V.U.N(e))) == True{} : Bool}
  {V.U.N(S.adv(xs, i)) == Nat.add(V.U.N(i), S.len(xs)) : Nat}

def S.adv_N(xs, i, e, h):
  match xs:
    case []:
      %Equal.sym(Nat, Nat.add(V.U.N(i), 0n), V.U.N(i), P.Nat.add_zero_r(V.U.N(i))) : {V.U.N(i) == _ : Nat}
      {==}
    case x <> r:
      %Equal.sym(Nat, Nat.add(V.U.N(i), 1n+S.len(r)), 1n+Nat.add(V.U.N(i), S.len(r)), P.Nat.add_succ_r(V.U.N(i), S.len(r))) :
        {V.U.N(S.adv(r, (i + 1 : U32))) == _ : Nat}
      %V.U.succ_N(i, e, S.lt_of_bound(i, S.len(r), e, h)) :
        {V.U.N(S.adv(r, (i + 1 : U32))) == Nat.add(_, S.len(r)) : Nat}
      S.adv_N(r, (i + 1 : U32), e, S.bound_succ(i, S.len(r), e, h))

# Writing
# =======

law S.pf_puts:
  for +d: Nat
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +k: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {A.T.pf(d, S.puts(ys, t, k)) == True{} : Bool}

def S.pf_puts(d, ys, t, k, hp):
  match ys:
    case []:
      hp
    case y <> r:
      S.pf_puts(d, r, Y.BP.put(t, k, y), (k + 1 : U32), Y.BP.pf_put(d, t, k, y, hp))

# Writes from k leave the bytes below k.
law S.byt_puts_lt:
  for +d: Nat
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +k: U32
  for +j: U32
  for +e: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), S.len(ys)), V.U.N(e))) == True{} : Bool}
  for +hj: {Nat.cmp(V.U.N(j), V.U.N(k)) == LT{} : Cmp}
  {Y.BP.byt(S.puts(ys, t, k), j) == Y.BP.byt(t, j) : U32}

def S.byt_puts_lt(d, ys, t, k, j, e, hp, hd, he, hb, hj):
  match ys:
    case []:
      {==}
    case y <> r:
      %Equal.sym(U32, Y.BP.byt(S.puts(r, Y.BP.put(t, k, y), (k + 1 : U32)), j), Y.BP.byt(Y.BP.put(t, k, y), j),
        S.byt_puts_lt(d, r, Y.BP.put(t, k, y), (k + 1 : U32), j, e, Y.BP.pf_put(d, t, k, y, hp), hd, he, S.bound_succ(k, S.len(r), e, hb), (%Equal.sym(Nat, V.U.N((k + 1 : U32)), 1n+V.U.N(k), V.U.succ_N(k, e, S.lt_of_bound(k, S.len(r), e, hb))) :
              {Nat.cmp(V.U.N(j), _) == LT{} : Cmp}
            P.Nat.le_lt_succ(V.U.N(j), V.U.N(k), P.Nat.lt_to_le(V.U.N(j), V.U.N(k), hj))))) :
        {_ == Y.BP.byt(t, j) : U32}
      Y.BP.byt_put_lt(d, t, k, j, y, hp, hd, Y.BP.in_range(d, k, e, hd, he, S.lt_of_bound(k, S.len(r), e, hb)),
        V.U.N_lt(j, k, hj))

# Writes from k leave a list held below k.
law S.has_puts_lt:
  for +d: Nat
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +k: U32
  for +ys: List<&2, U32>
  for +q: U32
  for +e: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(k), S.len(ys)), V.U.N(e))) == True{} : Bool}
  for +hq: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(q), S.len(xs)), V.U.N(k))) == True{} : Bool}
  {S.has(xs, S.puts(ys, t, k), q) == S.has(xs, t, q) : Bool}

def S.has_puts_lt(d, xs, t, k, ys, q, e, hp, hd, he, hb, hq):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(U32, Y.BP.byt(S.puts(ys, t, k), q), Y.BP.byt(t, q),
        S.byt_puts_lt(d, ys, t, k, q, e, hp, hd, he, hb, S.lt_of_bound(q, S.len(r), k, hq))) :
        {Bool.and(U32.is_eq(_, U32.and(x, 255)), S.has(r, S.puts(ys, t, k), (q + 1 : U32)))
          == Bool.and(U32.is_eq(Y.BP.byt(t, q), U32.and(x, 255)), S.has(r, t, (q + 1 : U32))) : Bool}
      %Equal.sym(Bool, S.has(r, S.puts(ys, t, k), (q + 1 : U32)), S.has(r, t, (q + 1 : U32)),
        S.has_puts_lt(d, r, t, k, ys, (q + 1 : U32), e, hp, hd, he, hb, S.bound_succ(q, S.len(r), k, hq))) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, q), U32.and(x, 255)), _)
          == Bool.and(U32.is_eq(Y.BP.byt(t, q), U32.and(x, 255)), S.has(r, t, (q + 1 : U32))) : Bool}
      {==}

# A list written is held.
law S.has_puts:
  for +d: Nat
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +i: U32
  for +e: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), S.len(xs)), V.U.N(e))) == True{} : Bool}
  {S.has(xs, S.puts(xs, t, i), i) == True{} : Bool}

def S.has_puts(d, xs, t, i, e, hp, hd, he, hb):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(U32, Y.BP.byt(S.puts(r, Y.BP.put(t, i, x), (i + 1 : U32)), i), Y.BP.byt(Y.BP.put(t, i, x), i),
        S.byt_puts_lt(d, r, Y.BP.put(t, i, x), (i + 1 : U32), i, e, Y.BP.pf_put(d, t, i, x, hp), hd, he, S.bound_succ(i, S.len(r), e, hb), (%Equal.sym(Nat, V.U.N((i + 1 : U32)), 1n+V.U.N(i), V.U.succ_N(i, e, S.lt_of_bound(i, S.len(r), e, hb))) :
              {Nat.cmp(V.U.N(i), _) == LT{} : Cmp}
            P.Nat.cmp_succ(V.U.N(i))))) :
        {Bool.and(U32.is_eq(_, U32.and(x, 255)), S.has(r, S.puts(r, Y.BP.put(t, i, x), (i + 1 : U32)), (i + 1 : U32)))
          == True{} : Bool}
      %Equal.sym(U32, Y.BP.byt(Y.BP.put(t, i, x), i), U32.and(x, 255), Y.BP.byt_put(t, i, x)) :
        {Bool.and(U32.is_eq(_, U32.and(x, 255)), S.has(r, S.puts(r, Y.BP.put(t, i, x), (i + 1 : U32)), (i + 1 : U32)))
          == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(U32.and(x, 255), U32.and(x, 255)), True{}, V.U.is_eq_refl(U32.and(x, 255))) :
        {Bool.and(_, S.has(r, S.puts(r, Y.BP.put(t, i, x), (i + 1 : U32)), (i + 1 : U32))) == True{} : Bool}
      S.has_puts(d, r, Y.BP.put(t, i, x), (i + 1 : U32), e, Y.BP.pf_put(d, t, i, x, hp), hd, he, S.bound_succ(i, S.len(r), e, hb))

# Reading
# =======

# A tree that holds the bytes of another has them.
law S.sl_has:
  for +n: Nat
  for +t: A.Tr
  for +p: U32
  for +u: A.Tr
  for +q: U32
  for +h: {S.has(S.sl(n, u, q), t, p) == True{} : Bool}
  {S.sl(n, t, p) == S.sl(n, u, q) : List<&2, U32>}

def S.sl_has(n, t, p, u, q, h):
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(U32, Y.BP.byt(t, p), U32.and(Y.BP.byt(u, q), 255),
        V.U.is_eq(Y.BP.byt(t, p), U32.and(Y.BP.byt(u, q), 255),
          P.Bool.and_l(U32.is_eq(Y.BP.byt(t, p), U32.and(Y.BP.byt(u, q), 255)),
            S.has(S.sl(m, u, (q + 1 : U32)), t, (p + 1 : U32)), h))) :
        {_ <> S.sl(m, t, (p + 1 : U32)) == Y.BP.byt(u, q) <> S.sl(m, u, (q + 1 : U32)) : List<&2, U32>}
      %Equal.sym(U32, U32.and(Y.BP.byt(u, q), 255), Y.BP.byt(u, q), Y.BP.byt_255(u, q)) :
        {_ <> S.sl(m, t, (p + 1 : U32)) == Y.BP.byt(u, q) <> S.sl(m, u, (q + 1 : U32)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, S.sl(m, t, (p + 1 : U32)), S.sl(m, u, (q + 1 : U32)),
        S.sl_has(m, t, (p + 1 : U32), u, (q + 1 : U32), P.Bool.and_r(U32.is_eq(Y.BP.byt(t, p), U32.and(Y.BP.byt(u, q), 255)),
            S.has(S.sl(m, u, (q + 1 : U32)), t, (p + 1 : U32)), h))) :
        {Y.BP.byt(u, q) <> _ == Y.BP.byt(u, q) <> S.sl(m, u, (q + 1 : U32)) : List<&2, U32>}
      {==}

law S.list_go:
  for +k: Nat
  for +t: A.Tr
  for +i: U32
  {B.B.list.go(k, i, (A.A.from(t), Y.BP.byt(t, i))) == S.sl(k, t, i) : List<&2, U32>}

def S.list_go(k, t, i):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), (i + 1 : U32)), (A.A.from(t), Y.BP.byt(t, (i + 1 : U32))),
        Y.BP.get_from(t, (i + 1 : U32))) :
        {Y.BP.byt(t, i) <> B.B.list.go(p, (i + 1 : U32), _) == Y.BP.byt(t, i) <> S.sl(p, t, (i + 1 : U32))
          : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.B.list.go(p, (i + 1 : U32), (A.A.from(t), Y.BP.byt(t, (i + 1 : U32)))),
        S.sl(p, t, (i + 1 : U32)), S.list_go(p, t, (i + 1 : U32))) :
        {Y.BP.byt(t, i) <> _ == Y.BP.byt(t, i) <> S.sl(p, t, (i + 1 : U32)) : List<&2, U32>}
      {==}

# The bytes of a byte string, as a list.
law S.list:
  for +n: U32
  for +t: A.Tr
  {B.B.list(B.Bytes{n, A.A.from(t)}) == S.sl(U32.to_nat(n), t, 0) : List<&2, U32>}

def S.list(n, t):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), 0), (A.A.from(t), Y.BP.byt(t, 0)), Y.BP.get_from(t, 0)) :
    {B.B.list.go(U32.to_nat(n), 0, _) == S.sl(U32.to_nat(n), t, 0) : List<&2, U32>}
  S.list_go(U32.to_nat(n), t, 0)

law S.len_sl:
  for +n: Nat
  for +t: A.Tr
  for +i: U32
  {S.len(S.sl(n, t, i)) == n : Nat}

def S.len_sl(n, t, i):
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Nat, S.len(S.sl(m, t, (i + 1 : U32))), m, S.len_sl(m, t, (i + 1 : U32))) : {1n+_ == 1n+m : Nat}
      {==}
