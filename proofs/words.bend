import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./bits.bend as Z

# Words and their bytes: where a byte position's word and lane are, the four
# bytes of a word read at any position, and a word written as its four bytes.
#
# Source: proofs/words.bp (tools/bpp.py writes proofs/words.bend from it).

# Lists
# =====

def WD.app(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case []:
      ys
    case x <> r:
      x <> WD.app(r, ys)

# The four bytes of a word, low first.
def WD.w4(+w: U32) -> List<&2, U32>:
  Y.BP.ext(w, 0n) <> Y.BP.ext(w, 8n) <> Y.BP.ext(w, 16n) <> Y.BP.ext(w, 24n) <> []

law WD.len_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {S.S.len(WD.app(xs, ys)) == Nat.add(S.S.len(xs), S.S.len(ys)) : Nat}

def WD.len_app(xs, ys):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(Nat, S.S.len(WD.app(r, ys)), Nat.add(S.S.len(r), S.S.len(ys)), WD.len_app(r, ys)) :
        {1n+_ == 1n+Nat.add(S.S.len(r), S.S.len(ys)) : Nat}
      {==}

law WD.app_assoc:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {WD.app(WD.app(xs, ys), zs) == WD.app(xs, WD.app(ys, zs)) : List<&2, U32>}

def WD.app_assoc(xs, ys, zs):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(List<&2, U32>, WD.app(WD.app(r, ys), zs), WD.app(r, WD.app(ys, zs)), WD.app_assoc(r, ys, zs)) :
        {x <> _ == x <> WD.app(r, WD.app(ys, zs)) : List<&2, U32>}
      {==}

law WD.app_nil:
  for +xs: List<&2, U32>
  {WD.app(xs, []) == xs : List<&2, U32>}

def WD.app_nil(xs):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(List<&2, U32>, WD.app(r, []), r, WD.app_nil(r)) :
        {x <> _ == x <> r : List<&2, U32>}
      {==}

# Positions
# =========

# Shifting down by two halves the value twice.
law WD.half2:
  for +x: U32
  {V.U.N(U32.shrn(x, 2n)) == P.Nat.half(P.Nat.half(V.U.N(x))) : Nat}

def WD.half2(x):
  %Equal.sym(Nat, V.U.N(U32.shr(U32.shr(x))), P.Nat.half(V.U.N(U32.shr(x))), V.U.N_shr(U32.shr(x))) :
    {_ == P.Nat.half(P.Nat.half(V.U.N(x))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shr(x)), P.Nat.half(V.U.N(x)), V.U.N_shr(x)) :
    {P.Nat.half(_) == P.Nat.half(P.Nat.half(V.U.N(x))) : Nat}
  {==}

# A value m + 4k with m < 4 has k as its quarter.
law WD.quarter:
  for +m: Nat
  for +k: Nat
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  {P.Nat.half(P.Nat.half(Nat.add(m, Nat.double(Nat.double(k))))) == k : Nat}

def WD.quarter(m, k, hm):
  match m:
    case 0n:
      %Equal.sym(Nat, P.Nat.half(Nat.add(0n, Nat.double(Nat.double(k)))), Nat.add(P.Nat.half(0n), Nat.double(k)), P.Nat.half_add_double(0n, Nat.double(k))) :
        {P.Nat.half(_) == k : Nat}
      P.Nat.half_double(k)
    case 1n:
      %Equal.sym(Nat, P.Nat.half(Nat.add(1n, Nat.double(Nat.double(k)))), Nat.add(P.Nat.half(1n), Nat.double(k)), P.Nat.half_add_double(1n, Nat.double(k))) :
        {P.Nat.half(_) == k : Nat}
      P.Nat.half_double(k)
    case 2n:
      %Equal.sym(Nat, P.Nat.half(Nat.add(2n, Nat.double(Nat.double(k)))), Nat.add(P.Nat.half(2n), Nat.double(k)), P.Nat.half_add_double(2n, Nat.double(k))) :
        {P.Nat.half(_) == k : Nat}
      P.Nat.half_double1(k)
    case 3n:
      %Equal.sym(Nat, P.Nat.half(Nat.add(3n, Nat.double(Nat.double(k)))), Nat.add(P.Nat.half(3n), Nat.double(k)), P.Nat.half_add_double(3n, Nat.double(k))) :
        {P.Nat.half(_) == k : Nat}
      P.Nat.half_double1(k)
    case 4n+p:
      P.Nat.lt_zero({P.Nat.half(P.Nat.half(Nat.add(4n+p, Nat.double(Nat.double(k))))) == k : Nat}, p, hm)

# The word of a position m + 4k (m < 4) is k.
law WD.at:
  for +x: U32
  for +k: U32
  for +m: Nat
  for +e: {V.U.N(x) == Nat.add(m, Nat.double(Nat.double(V.U.N(k)))) : Nat}
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  {U32.shrn(x, 2n) == k : U32}

def WD.at(x, k, m, e, hm):
  V.U.eq_N(U32.shrn(x, 2n), k,
    (%Equal.sym(Nat, V.U.N(U32.shrn(x, 2n)), P.Nat.half(P.Nat.half(V.U.N(x))), WD.half2(x)) :
        {_ == V.U.N(k) : Nat}
      (%Equal.sym(Nat, V.U.N(x), Nat.add(m, Nat.double(Nat.double(V.U.N(k)))), e) :
          {P.Nat.half(P.Nat.half(_)) == V.U.N(k) : Nat}
        WD.quarter(m, V.U.N(k), hm))))

# The lane of a position from its value: its low two bits.
law WD.sh_bits.go:
  for +b0: Bool
  for +b1: Bool
  for +r: Nat
  {Y.BP.shv(b0, b1) == Y.BP.shv(P.Nat.odd(P.Nat.bit(b0)),
    P.Nat.odd(Nat.add(P.Nat.half(P.Nat.bit(b0)), Nat.add(P.Nat.bit(b1), Nat.double(r))))) : Nat}

def WD.sh_bits.go(b0, b1, r):
  match b0 b1:
    case False{} False{}:
      %Equal.sym(Bool, P.Nat.odd(Nat.double(r)), False{}, P.Nat.odd_double(r)) :
        {0n == Y.BP.shv(False{}, _) : Nat}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, P.Nat.odd(Nat.double(r)), False{}, P.Nat.odd_double(r)) :
        {16n == Y.BP.shv(False{}, Bool.not(_)) : Nat}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, P.Nat.odd(Nat.double(r)), False{}, P.Nat.odd_double(r)) :
        {8n == Y.BP.shv(True{}, _) : Nat}
      {==}
    case True{} True{}:
      %Equal.sym(Bool, P.Nat.odd(Nat.double(r)), False{}, P.Nat.odd_double(r)) :
        {24n == Y.BP.shv(True{}, Bool.not(_)) : Nat}
      {==}

law WD.sh_N:
  for +x: U32
  {B.B.sh(x) == Y.BP.shv(P.Nat.odd(V.U.N(x)), P.Nat.odd(P.Nat.half(V.U.N(x)))) : Nat}

def WD.sh_N(x):
  match x:
    case U32{WCon{b0, WCon{b1, r}}}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{b0, WCon{b1, r}}}), Y.BP.shv(b0, b1), Y.BP.sh_val(b0, b1, r)) :
        {_ == Y.BP.shv(P.Nat.odd(V.U.N(U32{WCon{b0, WCon{b1, r}}})), P.Nat.odd(P.Nat.half(V.U.N(U32{WCon{b0, WCon{b1, r}}})))) : Nat}
      %Equal.sym(Nat, Word.to_nat(32n, WCon{b0, WCon{b1, r}}), Nat.add(P.Nat.bit(b0), Nat.double(Word.to_nat(31n, WCon{b1, r}))), W.W.N_cons(31n, b0, WCon{b1, r})) :
        {Y.BP.shv(b0, b1) == Y.BP.shv(P.Nat.odd(_), P.Nat.odd(P.Nat.half(_))) : Nat}
      %Equal.sym(Nat, Word.to_nat(31n, WCon{b1, r}), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))), W.W.N_cons(30n, b1, r)) :
        {Y.BP.shv(b0, b1) == Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(b0), Nat.double(_))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(_))))) : Nat}
      %Equal.sym(Bool, P.Nat.odd(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))), P.Nat.odd(P.Nat.bit(b0)), P.Nat.odd_add_double(P.Nat.bit(b0), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))))) :
        {Y.BP.shv(b0, b1) == Y.BP.shv(_, P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))))) : Nat}
      %Equal.sym(Nat, P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))), Nat.add(P.Nat.half(P.Nat.bit(b0)), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))), P.Nat.half_add_double(P.Nat.bit(b0), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))))) :
        {Y.BP.shv(b0, b1) == Y.BP.shv(P.Nat.odd(P.Nat.bit(b0)), P.Nat.odd(_)) : Nat}
      WD.sh_bits.go(b0, b1, Word.to_nat(30n, r))

# The lane of a position m + 4k (m < 4) is 8m.
law WD.lane:
  for +x: U32
  for +k: U32
  for +m: Nat
  for +e: {V.U.N(x) == Nat.add(m, Nat.double(Nat.double(V.U.N(k)))) : Nat}
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  {B.B.sh(x) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}

def WD.lane(x, k, m, e, hm):
  %Equal.sym(Nat, B.B.sh(x), Y.BP.shv(P.Nat.odd(V.U.N(x)), P.Nat.odd(P.Nat.half(V.U.N(x)))), WD.sh_N(x)) :
    {_ == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  %Equal.sym(Nat, V.U.N(x), Nat.add(m, Nat.double(Nat.double(V.U.N(k)))), e) :
    {Y.BP.shv(P.Nat.odd(_), P.Nat.odd(P.Nat.half(_))) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(Nat.add(m, Nat.double(Nat.double(V.U.N(k))))), P.Nat.odd(m), P.Nat.odd_add_double(m, Nat.double(V.U.N(k)))) :
    {Y.BP.shv(_, P.Nat.odd(P.Nat.half(Nat.add(m, Nat.double(Nat.double(V.U.N(k))))))) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  %Equal.sym(Nat, P.Nat.half(Nat.add(m, Nat.double(Nat.double(V.U.N(k))))), Nat.add(P.Nat.half(m), Nat.double(V.U.N(k))), P.Nat.half_add_double(m, Nat.double(V.U.N(k)))) :
    {Y.BP.shv(P.Nat.odd(m), P.Nat.odd(_)) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(Nat.add(P.Nat.half(m), Nat.double(V.U.N(k)))), P.Nat.odd(P.Nat.half(m)), P.Nat.odd_add_double(P.Nat.half(m), V.U.N(k))) :
    {Y.BP.shv(P.Nat.odd(m), _) == Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))) : Nat}
  {==}

# Order
# =====

# 1 + a <= c gives a < c.
law WD.lt_of_succ_le:
  for +a: Nat
  for +c: Nat
  for +h: {Cmp.is_le(Nat.cmp(1n+a, c)) == True{} : Bool}
  {Nat.cmp(a, c) == LT{} : Cmp}

def WD.lt_of_succ_le(a, c, h):
  match c:
    case 0n:
      P.Bool.false_true({Nat.cmp(a, 0n) == LT{} : Cmp}, h)
    case 1n+q:
      P.Nat.le_lt_succ(a, q, h)

# The value of x + 1 when x is below some value.
law WD.succ_at:
  for +x: U32
  for +E: U32
  for +m: Nat
  for +K: Nat
  for +e: {V.U.N(x) == Nat.add(m, K) : Nat}
  for +h: {Nat.cmp(V.U.N(x), V.U.N(E)) == LT{} : Cmp}
  {V.U.N(U32.add(x, 1)) == Nat.add(1n+m, K) : Nat}

def WD.succ_at(x, E, m, K, e, h):
  %Equal.sym(Nat, V.U.N(U32.add(x, 1)), 1n+V.U.N(x), V.U.succ_N(x, E, h)) :
    {_ == Nat.add(1n+m, K) : Nat}
  %Equal.sym(Nat, V.U.N(x), Nat.add(m, K), e) :
    {1n+_ == Nat.add(1n+m, K) : Nat}
  {==}

# Trees
# =====

law WD.swap_swap:
  for +t: A.Tr
  for +n: U32
  for +i: U32
  for +a: U32
  for +b: U32
  for +z: Bool
  {A.T.swap.go(A.T.swap.go(t, n, i, a, z), n, i, b, z) == A.T.swap.go(t, n, i, b, z) : A.Tr}

def WD.swap_swap(t, n, i, a, b, z):
  match t z:
    case A.TL{w} _:
      {==}
    case A.TN{l, r} True{}:
      %Equal.sym(A.Tr, A.T.swap.go(A.T.swap.go(l, U32.shr(n), i, a, U32.is_lt(i, U32.shr(U32.shr(n)))), U32.shr(n), i, b, U32.is_lt(i, U32.shr(U32.shr(n)))), A.T.swap.go(l, U32.shr(n), i, b, U32.is_lt(i, U32.shr(U32.shr(n)))), WD.swap_swap(l, U32.shr(n), i, a, b, U32.is_lt(i, U32.shr(U32.shr(n))))) :
        {A.TN{_, r} == A.TN{A.T.swap.go(l, U32.shr(n), i, b, U32.is_lt(i, U32.shr(U32.shr(n)))), r} : A.Tr}
      {==}
    case A.TN{l, r} False{}:
      %Equal.sym(A.Tr, A.T.swap.go(A.T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), a, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), U32.shr(n), U32.sub(i, U32.shr(n)), b, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), A.T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), b, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), WD.swap_swap(r, U32.shr(n), U32.sub(i, U32.shr(n)), a, b, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) :
        {A.TN{l, _} == A.TN{l, A.T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), b, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))} : A.Tr}
      {==}

# A second write to a slot undoes the first.
law WD.set_set:
  for +t: A.Tr
  for +k: U32
  for +a: U32
  for +b: U32
  {A.T.set(A.T.set(t, k, a), k, b) == A.T.set(t, k, b) : A.Tr}

def WD.set_set(t, k, a, b):
  %Equal.sym(U32, A.T.size(A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), a, A.T.half(A.T.size(t), k))), A.T.size(t), A.T.size_swap(t, A.T.size(t), A.T.mask(A.T.size(t), k), a, A.T.half(A.T.size(t), k))) :
    {A.T.swap.go(A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), a, A.T.half(A.T.size(t), k)), _, A.T.mask(_, k), b, A.T.half(_, k)) == A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), b, A.T.half(A.T.size(t), k)) : A.Tr}
  %Equal.sym(A.Tr, A.T.swap.go(A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), a, A.T.half(A.T.size(t), k)), A.T.size(t), A.T.mask(A.T.size(t), k), b, A.T.half(A.T.size(t), k)), A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), b, A.T.half(A.T.size(t), k)), WD.swap_swap(t, A.T.size(t), A.T.mask(A.T.size(t), k), a, b, A.T.half(A.T.size(t), k))) :
    {_ == A.T.swap.go(t, A.T.size(t), A.T.mask(A.T.size(t), k), b, A.T.half(A.T.size(t), k)) : A.Tr}
  {==}

# A bound four bytes past a position bounds each of its four bytes.
law WD.lt4:
  for +K: Nat
  for +c: Nat
  for +j: Nat
  for +hj: {Cmp.is_le(Nat.cmp(j, 3n)) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(4n, K), c)) == True{} : Bool}
  {Nat.cmp(Nat.add(j, K), c) == LT{} : Cmp}

def WD.lt4(K, c, j, hj, h):
  match j:
    case 0n:
      WD.lt_of_succ_le(K, c, P.Nat.le_succ_l(1n+K, c, P.Nat.le_succ_l(2n+K, c, P.Nat.le_succ_l(3n+K, c, h))))
    case 1n:
      WD.lt_of_succ_le(1n+K, c, P.Nat.le_succ_l(2n+K, c, P.Nat.le_succ_l(3n+K, c, h)))
    case 2n:
      WD.lt_of_succ_le(2n+K, c, P.Nat.le_succ_l(3n+K, c, h))
    case 3n:
      WD.lt_of_succ_le(3n+K, c, h)
    case 4n+q:
      P.Bool.false_true({Nat.cmp(Nat.add(4n+q, K), c) == LT{} : Cmp}, hj)

# i advanced by j single steps.
def WD.step(+j: Nat, +i: U32) -> U32:
  match j:
    case 0n:
      i
    case 1n+q:
      U32.add(WD.step(q, i), 1)

# The values of the positions of the four bytes of an aligned word.
law WD.pos4:
  for +i: U32
  for +k: U32
  for +E: U32
  for +j: Nat
  for +hj: {Cmp.is_le(Nat.cmp(j, 3n)) == True{} : Bool}
  for +e: {V.U.N(i) == Nat.double(Nat.double(V.U.N(k))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {V.U.N(WD.step(j, i)) == Nat.add(j, Nat.double(Nat.double(V.U.N(k)))) : Nat}

def WD.pos4(i, k, E, j, hj, e, hb):
  match j:
    case 0n:
      e
    case 1n+q:
      WD.succ_at(WD.step(q, i), E, q, Nat.double(Nat.double(V.U.N(k))),
        WD.pos4(i, k, E, q, P.Nat.le_succ_l(q, 3n, hj), e, hb),
        (%Equal.sym(Nat, V.U.N(WD.step(q, i)), Nat.add(q, Nat.double(Nat.double(V.U.N(k)))),
            WD.pos4(i, k, E, q, P.Nat.le_succ_l(q, 3n, hj), e, hb)) :
            {Nat.cmp(_, V.U.N(E)) == LT{} : Cmp}
          WD.lt4(Nat.double(Nat.double(V.U.N(k))), V.U.N(E), q, P.Nat.le_succ_l(q, 3n, hj),
            (%e : {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(E))) == True{} : Bool} hb))))

# A word written at an aligned position is its four bytes written there.
law WD.put4:
  for +t: A.Tr
  for +i: U32
  for +k: U32
  for +E: U32
  for +w: U32
  for +e: {V.U.N(i) == Nat.double(Nat.double(V.U.N(k))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(i)), V.U.N(E))) == True{} : Bool}
  {S.S.puts(WD.w4(w), t, i) == A.T.set(t, k, w) : A.Tr}

def WD.put4(t, i, k, E, w, e, hb):
  %Equal.sym(U32, U32.shrn(i, 2n), k, WD.at(i, k, 0n, WD.pos4(i, k, E, 0n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, _, Y.BP.ins(A.T.word(t, _), B.B.sh(i), Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(Nat, B.B.sh(i), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), WD.lane(i, k, 0n, WD.pos4(i, k, E, 0n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n), Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), _, Y.BP.ext(w, 0n))), U32.shrn(U32.add(i, 1), 2n)), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, U32.shrn(U32.add(i, 1), 2n), k, WD.at(U32.add(i, 1), k, 1n, WD.pos4(i, k, E, 1n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), _), B.B.sh(U32.add(i, 1)), Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(Nat, B.B.sh(U32.add(i, 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), WD.lane(U32.add(i, 1), k, 1n, WD.pos4(i, k, E, 1n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), _, Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), _, Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), _, Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), _, Y.BP.ext(w, 8n))), U32.shrn(U32.add(U32.add(i, 1), 1), 2n)), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, U32.shrn(U32.add(U32.add(i, 1), 1), 2n), k, WD.at(U32.add(U32.add(i, 1), 1), k, 2n, WD.pos4(i, k, E, 2n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), _, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), _), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), _, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), _), B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(Nat, B.B.sh(U32.add(U32.add(i, 1), 1)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), WD.lane(U32.add(U32.add(i, 1), 1), k, 2n, WD.pos4(i, k, E, 2n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), _, Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), _, Y.BP.ext(w, 16n))), U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, U32.shrn(U32.add(U32.add(U32.add(i, 1), 1), 1), 2n), k, WD.at(U32.add(U32.add(U32.add(i, 1), 1), 1), k, 3n, WD.pos4(i, k, E, 3n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), Y.BP.ext(w, 16n))), _, Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), Y.BP.ext(w, 16n))), _), B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(Nat, B.B.sh(U32.add(U32.add(U32.add(i, 1), 1), 1)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n))), WD.lane(U32.add(U32.add(U32.add(i, 1), 1), 1), k, 3n, WD.pos4(i, k, E, 3n, {==}, e, hb), {==})) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), Y.BP.ext(w, 16n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k, Y.BP.ins(A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), Y.BP.ext(w, 0n))), k), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), Y.BP.ext(w, 8n))), k), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), Y.BP.ext(w, 16n))), k), _, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, A.T.word(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k), Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), A.T.word_set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)))) :
    {A.T.set(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k, Y.BP.ins(_, 8n, Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k, Y.BP.ins(_, 8n, Y.BP.ext(w, 8n))), k), 16n, Y.BP.ext(w, 16n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k, Y.BP.ins(_, 8n, Y.BP.ext(w, 8n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k, Y.BP.ins(_, 8n, Y.BP.ext(w, 8n))), k), 16n, Y.BP.ext(w, 16n))), k), 24n, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(A.Tr, A.T.set(A.T.set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n))), k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), A.T.set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), WD.set_set(t, k, Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)))) :
    {A.T.set(A.T.set(_, k, Y.BP.ins(A.T.word(_, k), 16n, Y.BP.ext(w, 16n))), k, Y.BP.ins(A.T.word(A.T.set(_, k, Y.BP.ins(A.T.word(_, k), 16n, Y.BP.ext(w, 16n))), k), 24n, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, A.T.word(A.T.set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), k), Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), A.T.word_set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)))) :
    {A.T.set(A.T.set(A.T.set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), k, Y.BP.ins(_, 16n, Y.BP.ext(w, 16n))), k, Y.BP.ins(A.T.word(A.T.set(A.T.set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), k, Y.BP.ins(_, 16n, Y.BP.ext(w, 16n))), k), 24n, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(A.Tr, A.T.set(A.T.set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n))), k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n))), A.T.set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n))), WD.set_set(t, k, Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)))) :
    {A.T.set(_, k, Y.BP.ins(A.T.word(_, k), 24n, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, A.T.word(A.T.set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n))), k), Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), A.T.word_set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)))) :
    {A.T.set(A.T.set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n))), k, Y.BP.ins(_, 24n, Y.BP.ext(w, 24n))) == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(A.Tr, A.T.set(A.T.set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n))), k, Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), 24n, Y.BP.ext(w, 24n))), A.T.set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), 24n, Y.BP.ext(w, 24n))), WD.set_set(t, k, Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), 24n, Y.BP.ext(w, 24n)))) :
    {_ == A.T.set(t, k, w) : A.Tr}
  %Equal.sym(U32, Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(A.T.word(t, k), 0n, Y.BP.ext(w, 0n)), 8n, Y.BP.ext(w, 8n)), 16n, Y.BP.ext(w, 16n)), 24n, Y.BP.ext(w, 24n)), w, Z.BB.ins4(A.T.word(t, k), w)) :
    {A.T.set(t, k, _) == A.T.set(t, k, w) : A.Tr}
  {==}

# A value split into its low two bits and its quarter.
law WD.split4:
  for +s: U32
  {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}

def WD.split4(s):
  %Equal.sym(Nat, V.U.N(U32.shrn(s, 2n)), P.Nat.half(P.Nat.half(V.U.N(s))), WD.half2(s)) :
    {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))), Nat.double(_)))) : Nat}
  %P.Nat.split(P.Nat.half(V.U.N(s))) :
    {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(_)) : Nat}
  %P.Nat.split(V.U.N(s)) :
    {V.U.N(s) == _ : Nat}
  {==}

# K <= m + 4K.
law WD.le_quad:
  for +m: Nat
  for +K: Nat
  {Cmp.is_le(Nat.cmp(K, Nat.add(m, Nat.double(Nat.double(K))))) == True{} : Bool}

def WD.le_quad(m, K):
  P.Nat.le_trans(K, Nat.double(Nat.double(K)), Nat.add(m, Nat.double(Nat.double(K))),
    P.Nat.le_trans(K, Nat.double(K), Nat.double(Nat.double(K)),
      (%Equal.sym(Nat, Nat.double(K), Nat.add(K, K), P.Nat.double_add(K)) : {Cmp.is_le(Nat.cmp(K, _)) == True{} : Bool} P.Nat.le_add_l(K, K)),
      (%Equal.sym(Nat, Nat.double(Nat.double(K)), Nat.add(Nat.double(K), Nat.double(K)), P.Nat.double_add(Nat.double(K))) : {Cmp.is_le(Nat.cmp(Nat.double(K), _)) == True{} : Bool}
        P.Nat.le_add_l(Nat.double(K), Nat.double(K)))),
    P.Nat.le_add_l(m, Nat.double(Nat.double(K))))

# The values of the positions after s, for N(s) = m + K.
law WD.posg:
  for +s: U32
  for +E: U32
  for +m: Nat
  for +K: Nat
  for +j: Nat
  for +hj: {Cmp.is_le(Nat.cmp(j, 3n)) == True{} : Bool}
  for +e: {V.U.N(s) == Nat.add(m, K) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {V.U.N(WD.step(j, s)) == Nat.add(j, Nat.add(m, K)) : Nat}

def WD.posg(s, E, m, K, j, hj, e, hb):
  match j:
    case 0n:
      e
    case 1n+q:
      WD.succ_at(WD.step(q, s), E, q, Nat.add(m, K),
        WD.posg(s, E, m, K, q, P.Nat.le_succ_l(q, 3n, hj), e, hb),
        (%Equal.sym(Nat, V.U.N(WD.step(q, s)), Nat.add(q, Nat.add(m, K)),
            WD.posg(s, E, m, K, q, P.Nat.le_succ_l(q, 3n, hj), e, hb)) :
            {Nat.cmp(_, V.U.N(E)) == LT{} : Cmp}
          WD.lt4(Nat.add(m, K), V.U.N(E), q, P.Nat.le_succ_l(q, 3n, hj),
            (%e : {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(E))) == True{} : Bool} hb))))

# A position's word is below a bound four bytes past the position.
law WD.word_lt:
  for +s: U32
  for +E: U32
  for +m: Nat
  for +e: {V.U.N(s) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n))))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {Nat.cmp(V.U.N(U32.shrn(s, 2n)), V.U.N(E)) == LT{} : Cmp}

def WD.word_lt(s, E, m, e, hb):
  P.Nat.le_lt_trans(V.U.N(U32.shrn(s, 2n)), V.U.N(s), V.U.N(E),
    (%Equal.sym(Nat, V.U.N(s), Nat.add(m, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n))))), e) :
        {Cmp.is_le(Nat.cmp(V.U.N(U32.shrn(s, 2n)), _)) == True{} : Bool}
      WD.le_quad(m, V.U.N(U32.shrn(s, 2n)))),
    WD.lt4(V.U.N(s), V.U.N(E), 0n, {==}, hb))

# The four bytes of the word read at s, for each lane of s.
law WD.join.go:
  for +u: A.Tr
  for +s: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(E))) == True{} : Bool}
  for +o0: Bool
  for +o1: Bool
  for +eo0: {P.Nat.odd(V.U.N(s)) == o0 : Bool}
  for +eo1: {P.Nat.odd(P.Nat.half(V.U.N(s))) == o1 : Bool}
  {WD.w4(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))) == S.S.sl(4n, u, s) : List<&2, U32>}

def WD.join.go(u, s, E, hb, o0, o1, eo0, eo1):
  match o0 o1:
    case False{} False{}:
      %Equal.sym(Nat, B.B.sh(s), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), WD.lane(s, U32.shrn(s, 2n), 0n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), {==})) :
        {Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 0n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 0n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n), Z.BB.join00(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {_ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 8n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n), Z.BB.join01(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 16n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n), Z.BB.join02(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), 24n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n), Z.BB.join03(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> _ <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(s, 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(s, 1), U32.shrn(s, 2n), 1n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(s, 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), WD.lane(U32.add(s, 1), U32.shrn(s, 2n), 1n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(s, 1), 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(U32.add(s, 1), 1), U32.shrn(s, 2n), 2n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(s, 1), 1)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), WD.lane(U32.add(U32.add(s, 1), 1), U32.shrn(s, 2n), 2n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n))), WD.lane(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 0n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 0n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> [] : List<&2, U32>}
      {==}
    case True{} False{}:
      %Equal.sym(Nat, B.B.sh(s), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), WD.lane(s, U32.shrn(s, 2n), 1n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), {==})) :
        {Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 0n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 0n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n), Z.BB.join10(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {_ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 8n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n), Z.BB.join11(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 16n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n), Z.BB.join12(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), 24n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), Z.BB.join13(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> _ <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(s, 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(s, 1), U32.shrn(s, 2n), 2n, WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(s, 1)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), WD.lane(U32.add(s, 1), U32.shrn(s, 2n), 2n, WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(s, 1), 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(U32.add(s, 1), 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(s, 1), 1)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n))), WD.lane(U32.add(U32.add(s, 1), 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 1n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), WD.lane(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 1n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 1n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(False{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 8n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n)))) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> [] : List<&2, U32>}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, B.B.sh(s), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), WD.lane(s, U32.shrn(s, 2n), 2n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), {==})) :
        {Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 0n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 0n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n), Z.BB.join20(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {_ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 8n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n), Z.BB.join21(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 16n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), Z.BB.join22(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), 24n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), Z.BB.join23(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> _ <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(s, 1), 2n), U32.shrn(s, 2n), WD.at(U32.add(s, 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(s, 1)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n))), WD.lane(U32.add(s, 1), U32.shrn(s, 2n), 3n, WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(s, 1), 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(U32.add(s, 1), 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 2n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(s, 1), 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(s, 1), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), WD.lane(U32.add(U32.add(s, 1), 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 2n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(s, 1), 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 1n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 2n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(1n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), WD.lane(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 1n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 2n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(1n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 2n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 16n) <> Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> [] : List<&2, U32>}
      {==}
    case True{} True{}:
      %Equal.sym(Nat, B.B.sh(s), Y.BP.shv(P.Nat.odd(3n), P.Nat.odd(P.Nat.half(3n))), WD.lane(s, U32.shrn(s, 2n), 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), {==})) :
        {Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 0n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 0n), Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n), Z.BB.join30(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {_ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 8n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 8n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n), Z.BB.join31(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 16n) <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 16n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n), Z.BB.join32(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> _ <> Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 24n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, Y.BP.ext(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 24n), 24n), Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n), Z.BB.join33(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)))) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> _ <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(s, 1), 2n)), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(s, 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(s, 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(s, 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(s, 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(s, 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n))), WD.lane(U32.add(s, 1), U32.add(U32.shrn(s, 2n), 1), 0n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(s, 1)) == Nat.add(0n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 1n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(s, 1), 1), 2n)), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(s, 1), 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(U32.add(s, 1), 1), U32.add(U32.shrn(s, 2n), 1), 1n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(s, 1), 1)) == Nat.add(1n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(s, 1), 1))) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(s, 1), 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n))), WD.lane(U32.add(U32.add(s, 1), 1), U32.add(U32.shrn(s, 2n), 1), 1n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(s, 1), 1)) == Nat.add(1n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 2n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> Y.BP.ext(A.T.word(u, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n)), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(U32, U32.shrn(U32.add(U32.add(U32.add(s, 1), 1), 1), 2n), U32.add(U32.shrn(s, 2n), 1), WD.at(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 2n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(2n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, _), B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1))) <> [] : List<&2, U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(U32.add(U32.add(s, 1), 1), 1)), Y.BP.shv(P.Nat.odd(2n), P.Nat.odd(P.Nat.half(2n))), WD.lane(U32.add(U32.add(U32.add(s, 1), 1), 1), U32.add(U32.shrn(s, 2n), 1), 2n, (%Equal.sym(Nat, V.U.N(U32.add(U32.shrn(s, 2n), 1)), 1n+V.U.N(U32.shrn(s, 2n)), V.U.succ_N(U32.shrn(s, 2n), E, WD.word_lt(s, E, 3n, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb))) : {V.U.N(U32.add(U32.add(U32.add(s, 1), 1), 1)) == Nat.add(2n, Nat.double(Nat.double(_))) : Nat}; WD.posg(s, E, 3n, Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))), 3n, {==}, (%eo0 : {V.U.N(s) == Nat.add(P.Nat.bit(_), Nat.double(Nat.add(P.Nat.bit(True{}), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; (%eo1 : {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(Nat.add(P.Nat.bit(_), Nat.double(V.U.N(U32.shrn(s, 2n)))))) : Nat}; WD.split4(s))), hb)), {==})) :
        {Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 0n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 8n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), 16n) <> [] == Y.BP.ext(A.T.word(u, U32.shrn(s, 2n)), 24n) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(0n), P.Nat.odd(P.Nat.half(0n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), Y.BP.shv(P.Nat.odd(1n), P.Nat.odd(P.Nat.half(1n)))) <> Y.BP.ext(A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), _) <> [] : List<&2, U32>}
      {==}

# The four bytes of the word read at s are the bytes at s.
law WD.join:
  for +u: A.Tr
  for +s: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {WD.w4(B.B.join(A.T.word(u, U32.shrn(s, 2n)), A.T.word(u, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))) == S.S.sl(4n, u, s) : List<&2, U32>}

def WD.join(u, s, E, hb):
  WD.join.go(u, s, E, hb, P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s))), {==}, {==})

# a + (4 + b) = 4 + (a + b).
law WD.add4r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 4n+b) == 4n+Nat.add(a, b) : Nat}

def WD.add4r(a, b):
  %Equal.sym(Nat, Nat.add(a, 4n+b), 1n+Nat.add(a, 3n+b), P.Nat.add_succ_r(a, 3n+b)) :
    {_ == 4n+Nat.add(a, b) : Nat}
  %Equal.sym(Nat, Nat.add(a, 3n+b), 1n+Nat.add(a, 2n+b), P.Nat.add_succ_r(a, 2n+b)) :
    {1n+_ == 4n+Nat.add(a, b) : Nat}
  %Equal.sym(Nat, Nat.add(a, 2n+b), 1n+Nat.add(a, 1n+b), P.Nat.add_succ_r(a, 1n+b)) :
    {1n+1n+_ == 4n+Nat.add(a, b) : Nat}
  %Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), P.Nat.add_succ_r(a, b)) :
    {1n+1n+1n+_ == 4n+Nat.add(a, b) : Nat}
  {==}

# The lanes: below 4.
law WD.lane_lt:
  for +o0: Bool
  for +o1: Bool
  {Nat.cmp(Nat.add(P.Nat.bit(o0), Nat.double(P.Nat.bit(o1))), 4n) == LT{} : Cmp}

def WD.lane_lt(o0, o1):
  match o0 o1:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Four steps from x add 4.
law WD.pos_4:
  for +x: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(x)), V.U.N(E))) == True{} : Bool}
  {V.U.N(WD.step(4n, x)) == 4n+V.U.N(x) : Nat}

def WD.pos_4(x, E, hb):
  WD.succ_at(WD.step(3n, x), E, 3n, V.U.N(x),
    WD.posg(x, E, 0n, V.U.N(x), 3n, {==}, {==}, hb),
    (%Equal.sym(Nat, V.U.N(WD.step(3n, x)), Nat.add(3n, V.U.N(x)), WD.posg(x, E, 0n, V.U.N(x), 3n, {==}, {==}, hb)) :
        {Nat.cmp(_, V.U.N(E)) == LT{} : Cmp};
      WD.lt4(V.U.N(x), V.U.N(E), 3n, {==}, hb)))

# The value split into lane and word, as an equation.
law WD.split_lane:
  for +s: U32
  {V.U.N(s) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))))), Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n))))) : Nat}

def WD.split_lane(s):
  %Equal.sym(Nat, Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))))), Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n))))), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.add(Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))), Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))))), P.Nat.add_assoc(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))), Nat.double(Nat.double(V.U.N(U32.shrn(s, 2n)))))) :
    {V.U.N(s) == _ : Nat}
  %P.Nat.double_distr(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))), Nat.double(V.U.N(U32.shrn(s, 2n)))) :
    {V.U.N(s) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), _) : Nat}
  WD.split4(s)

# Bits and values
# ===============

law WD.and_zero_r.go:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +ih: {Word.and(p, t, Word.zero(p)) == Word.zero(p) : Word(p)}
  {WCon{Bool.and(b, False{}), Word.and(p, t, Word.zero(p))} == WCon{False{}, Word.zero(p)} : Word(1n+p)}

def WD.and_zero_r.go(p, b, t, ih):
  match b:
    case False{}:
      %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), ih) :
        {WCon{Bool.and(False{}, False{}), _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
      {==}
    case True{}:
      %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), ih) :
        {WCon{Bool.and(True{}, False{}), _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
      {==}

law WD.and_zero_r:
  for +n: Nat
  for +r: Word(n)
  {Word.and(n, r, Word.zero(n)) == Word.zero(n) : Word(n)}

def WD.and_zero_r(n, r):
  match n:
    case 0n:
      match r:
        case WNil{}:
          {==}
    case 1n+p:
      match r:
        case WCon{b, t}:
          WD.and_zero_r.go(p, b, t, WD.and_zero_r(p, t))

law WD.odd_bit:
  for +b: Bool
  {P.Nat.odd(P.Nat.bit(b)) == b : Bool}

def WD.odd_bit(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law WD.half_bit:
  for +b: Bool
  {P.Nat.half(P.Nat.bit(b)) == 0n : Nat}

def WD.half_bit(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# The lane of s, as its shift: from the lane's value.
law WD.sh_lane:
  for +s: U32
  {B.B.sh(s) == Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))))) : Nat}

def WD.sh_lane(s):
  %Equal.sym(Nat, B.B.sh(s), Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))), WD.sh_N(s)) :
    {_ == Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))), P.Nat.odd(P.Nat.bit(P.Nat.odd(V.U.N(s)))), P.Nat.odd_add_double(P.Nat.bit(P.Nat.odd(V.U.N(s))), P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))))) :
    {Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))) == Y.BP.shv(_, P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))))) : Nat}
  %Equal.sym(Nat, P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(s))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))), Nat.add(P.Nat.half(P.Nat.bit(P.Nat.odd(V.U.N(s)))), P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))), P.Nat.half_add_double(P.Nat.bit(P.Nat.odd(V.U.N(s))), P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))))) :
    {Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))) == Y.BP.shv(P.Nat.odd(P.Nat.bit(P.Nat.odd(V.U.N(s)))), P.Nat.odd(_)) : Nat}
  %Equal.sym(Nat, P.Nat.half(P.Nat.bit(P.Nat.odd(V.U.N(s)))), 0n, WD.half_bit(P.Nat.odd(V.U.N(s)))) :
    {Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))) == Y.BP.shv(P.Nat.odd(P.Nat.bit(P.Nat.odd(V.U.N(s)))), P.Nat.odd(Nat.add(_, P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(P.Nat.bit(P.Nat.odd(V.U.N(s)))), P.Nat.odd(V.U.N(s)), WD.odd_bit(P.Nat.odd(V.U.N(s)))) :
    {Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))) == Y.BP.shv(_, P.Nat.odd(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s)))))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(s))))), P.Nat.odd(P.Nat.half(V.U.N(s))), WD.odd_bit(P.Nat.odd(P.Nat.half(V.U.N(s))))) :
    {Y.BP.shv(P.Nat.odd(V.U.N(s)), P.Nat.odd(P.Nat.half(V.U.N(s)))) == Y.BP.shv(P.Nat.odd(V.U.N(s)), _) : Nat}
  {==}

law WD.min:
  for +a: U32
  for +b: U32
  {U32.min(a, b) == Bool.pick(U32, U32.is_lt(a, b), a, b) : U32}

def WD.min(a, b):
  match a b:
    case U32{x} U32{y}:
      {==}

law WD.sub_self:
  for +n: U32
  {U32.sub(n, n) == 0 : U32}

def WD.sub_self(n):
  (%V.U.add_zero_r(n) : {U32.sub(_, n) == 0 : U32}; V.U.sub_add_l(n, 0))

# Lists at U32 offsets
# ====================

# A value of 0 is the word 0.
law WD.zero_of:
  for +x: U32
  for +e: {V.U.N(x) == 0n : Nat}
  {x == 0 : U32}

def WD.zero_of(x, e):
  V.U.eq_N(x, 0, e)

# x - 1, for x of value 1 + p, has value p.
law WD.pred_N:
  for +x: U32
  for +p: Nat
  for +e: {V.U.N(x) == 1n+p : Nat}
  {V.U.N(U32.sub(x, 1)) == p : Nat}

def WD.pred_N(x, p, e):
  P.Nat.succ_inj(V.U.N(U32.sub(x, 1)), p,
    (%P.Nat.add_one(V.U.N(U32.sub(x, 1))) : {_ == 1n+p : Nat};
      (%e : {Nat.add(V.U.N(U32.sub(x, 1)), 1n) == _ : Nat};
        V.U.sub_nat(x, 1, V.U.N_le(1, x,
          (%Equal.sym(Nat, V.U.N(x), 1n+p, e) : {Cmp.is_le(Nat.cmp(1n, _)) == True{} : Bool};
            P.Nat.le_zero(p)))))))

# (s + 1) + (x - 1) = s + x.
law WD.add_shift:
  for +s: U32
  for +x: U32
  {U32.add(U32.add(s, 1), U32.sub(x, 1)) == U32.add(s, x) : U32}

def WD.add_shift(s, x):
  %Equal.sym(U32, U32.add(U32.add(s, 1), U32.sub(x, 1)), U32.add(s, U32.add(1, U32.sub(x, 1))), V.U.add_assoc(s, 1, U32.sub(x, 1))) :
    {_ == U32.add(s, x) : U32}
  %Equal.sym(U32, U32.add(1, U32.sub(x, 1)), U32.add(U32.sub(x, 1), 1), U32.add_comm(1, U32.sub(x, 1))) :
    {U32.add(s, _) == U32.add(s, x) : U32}
  %Equal.sym(U32, U32.add(U32.sub(x, 1), 1), x, V.U.add_sub(x, 1)) :
    {U32.add(s, _) == U32.add(s, x) : U32}
  {==}

# The bytes of k + m from s: those of k, then those of m from s + x, where x
# has value k.
law WD.sl_app:
  for +k: Nat
  for +m: Nat
  for +u: A.Tr
  for +s: U32
  for +x: U32
  for +e: {V.U.N(x) == k : Nat}
  {S.S.sl(Nat.add(k, m), u, s) == WD.app(S.S.sl(k, u, s), S.S.sl(m, u, U32.add(s, x))) : List<&2, U32>}

def WD.sl_app(k, m, u, s, x, e):
  match k:
    case 0n:
      %Equal.sym(U32, x, 0, WD.zero_of(x, e)) :
        {S.S.sl(m, u, s) == S.S.sl(m, u, U32.add(s, _)) : List<&2, U32>}
      %Equal.sym(U32, U32.add(s, 0), s, V.U.add_zero_r(s)) :
        {S.S.sl(m, u, s) == S.S.sl(m, u, _) : List<&2, U32>}
      {==}
    case 1n+p:
      %Equal.sym(List<&2, U32>, S.S.sl(Nat.add(p, m), u, U32.add(s, 1)), WD.app(S.S.sl(p, u, U32.add(s, 1)), S.S.sl(m, u, U32.add(U32.add(s, 1), U32.sub(x, 1)))), WD.sl_app(p, m, u, U32.add(s, 1), U32.sub(x, 1), WD.pred_N(x, p, e))) :
        {Y.BP.byt(u, s) <> _ == Y.BP.byt(u, s) <> WD.app(S.S.sl(p, u, U32.add(s, 1)), S.S.sl(m, u, U32.add(s, x))) : List<&2, U32>}
      %Equal.sym(U32, U32.add(U32.add(s, 1), U32.sub(x, 1)), U32.add(s, x), WD.add_shift(s, x)) :
        {Y.BP.byt(u, s) <> WD.app(S.S.sl(p, u, U32.add(s, 1)), S.S.sl(m, u, _)) == Y.BP.byt(u, s) <> WD.app(S.S.sl(p, u, U32.add(s, 1)), S.S.sl(m, u, U32.add(s, x))) : List<&2, U32>}
      {==}

# Writing xs then ys: ys goes at i + x, where x has the length of xs.
law WD.puts_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +i: U32
  for +x: U32
  for +e: {V.U.N(x) == S.S.len(xs) : Nat}
  {S.S.puts(WD.app(xs, ys), t, i) == S.S.puts(ys, S.S.puts(xs, t, i), U32.add(i, x)) : A.Tr}

def WD.puts_app(xs, ys, t, i, x, e):
  match xs:
    case []:
      %Equal.sym(U32, x, 0, WD.zero_of(x, e)) :
        {S.S.puts(ys, t, i) == S.S.puts(ys, t, U32.add(i, _)) : A.Tr}
      %Equal.sym(U32, U32.add(i, 0), i, V.U.add_zero_r(i)) :
        {S.S.puts(ys, t, i) == S.S.puts(ys, t, _) : A.Tr}
      {==}
    case y <> r:
      %Equal.sym(A.Tr, S.S.puts(WD.app(r, ys), Y.BP.put(t, i, y), U32.add(i, 1)), S.S.puts(ys, S.S.puts(r, Y.BP.put(t, i, y), U32.add(i, 1)), U32.add(U32.add(i, 1), U32.sub(x, 1))), WD.puts_app(r, ys, Y.BP.put(t, i, y), U32.add(i, 1), U32.sub(x, 1), WD.pred_N(x, S.S.len(r), e))) :
        {_ == S.S.puts(ys, S.S.puts(r, Y.BP.put(t, i, y), U32.add(i, 1)), U32.add(i, x)) : A.Tr}
      %Equal.sym(U32, U32.add(U32.add(i, 1), U32.sub(x, 1)), U32.add(i, x), WD.add_shift(i, x)) :
        {S.S.puts(ys, S.S.puts(r, Y.BP.put(t, i, y), U32.add(i, 1)), _) == S.S.puts(ys, S.S.puts(r, Y.BP.put(t, i, y), U32.add(i, 1)), U32.add(i, x)) : A.Tr}
      {==}

# Lanes and alignment
# ===================

law WD.and3:
  for +b0: Bool
  for +b1: Bool
  for +r: Word(30n)
  {U32.and(U32{WCon{b0, WCon{b1, r}}}, 3) == U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), Word.zero(30n)}}} : U32}

def WD.and3(b0, b1, r):
  %Equal.sym(Word(30n), Word.and(30n, r, Word.zero(30n)), Word.zero(30n), WD.and_zero_r(30n, r)) :
    {U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), _}}} == U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), Word.zero(30n)}}} : U32}
  {==}

law WD.lane_N.go:
  for +b0: Bool
  for +b1: Bool
  {V.U.N(U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), Word.zero(30n)}}}) == Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) : Nat}

def WD.lane_N.go(b0, b1):
  match b0 b1:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# The low two bits of x, as a value: its lane.
law WD.lane_N:
  for +x: U32
  {V.U.N(U32.and(x, 3)) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(x))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(x)))))) : Nat}

def WD.lane_N(x):
  match x:
    case U32{WCon{b0, WCon{b1, r}}}:
      %Equal.sym(U32, U32.and(U32{WCon{b0, WCon{b1, r}}}, 3), U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), Word.zero(30n)}}}, WD.and3(b0, b1, r)) :
        {V.U.N(_) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32{WCon{b0, WCon{b1, r}}}))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32{WCon{b0, WCon{b1, r}}})))))) : Nat}
      %Equal.sym(Nat, V.U.N(U32{WCon{Bool.and(b0, True{}), WCon{Bool.and(b1, True{}), Word.zero(30n)}}}), Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))), WD.lane_N.go(b0, b1)) :
        {_ == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32{WCon{b0, WCon{b1, r}}}))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32{WCon{b0, WCon{b1, r}}})))))) : Nat}
      %Equal.sym(Nat, Word.to_nat(32n, WCon{b0, WCon{b1, r}}), Nat.add(P.Nat.bit(b0), Nat.double(Word.to_nat(31n, WCon{b1, r}))), W.W.N_cons(31n, b0, WCon{b1, r})) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(P.Nat.odd(_)), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(_))))) : Nat}
      %Equal.sym(Nat, Word.to_nat(31n, WCon{b1, r}), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))), W.W.N_cons(30n, b1, r)) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(P.Nat.odd(Nat.add(P.Nat.bit(b0), Nat.double(_)))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(_))))))) : Nat}
      %Equal.sym(Bool, P.Nat.odd(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))), P.Nat.odd(P.Nat.bit(b0)), P.Nat.odd_add_double(P.Nat.bit(b0), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))))) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))))))) : Nat}
      %Equal.sym(Nat, P.Nat.half(Nat.add(P.Nat.bit(b0), Nat.double(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))), Nat.add(P.Nat.half(P.Nat.bit(b0)), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))), P.Nat.half_add_double(P.Nat.bit(b0), Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r))))) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(P.Nat.odd(P.Nat.bit(b0))), Nat.double(P.Nat.bit(P.Nat.odd(_)))) : Nat}
      %Equal.sym(Nat, P.Nat.half(P.Nat.bit(b0)), 0n, WD.half_bit(b0)) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(P.Nat.odd(P.Nat.bit(b0))), Nat.double(P.Nat.bit(P.Nat.odd(Nat.add(_, Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))))))) : Nat}
      %Equal.sym(Bool, P.Nat.odd(Nat.add(P.Nat.bit(b1), Nat.double(Word.to_nat(30n, r)))), P.Nat.odd(P.Nat.bit(b1)), P.Nat.odd_add_double(P.Nat.bit(b1), Word.to_nat(30n, r))) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(P.Nat.odd(P.Nat.bit(b0))), Nat.double(P.Nat.bit(_))) : Nat}
      %Equal.sym(Bool, P.Nat.odd(P.Nat.bit(b0)), b0, WD.odd_bit(b0)) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.bit(b1))))) : Nat}
      %Equal.sym(Bool, P.Nat.odd(P.Nat.bit(b1)), b1, WD.odd_bit(b1)) :
        {Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(b1))) == Nat.add(P.Nat.bit(b0), Nat.double(P.Nat.bit(_))) : Nat}
      {==}

# x = (x & 3) + 4 (x >> 2).
law WD.mod4:
  for +x: U32
  {V.U.N(x) == Nat.add(V.U.N(U32.and(x, 3)), Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n))))) : Nat}

def WD.mod4(x):
  %Equal.sym(Nat, V.U.N(U32.and(x, 3)), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(x))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(x)))))), WD.lane_N(x)) :
    {V.U.N(x) == Nat.add(_, Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n))))) : Nat}
  WD.split_lane(x)

# A value 4K is its word's value times 4.
law WD.aligned:
  for +y: U32
  for +K: Nat
  for +e: {V.U.N(y) == Nat.double(Nat.double(K)) : Nat}
  {V.U.N(y) == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}

def WD.aligned(y, K, e):
  %Equal.sym(Nat, V.U.N(y), Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(y))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(y)))))), Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n))))), WD.split_lane(y)) :
    {_ == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}
  %Equal.sym(Nat, V.U.N(y), Nat.double(Nat.double(K)), e) :
    {Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(_)), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(_))))), Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n))))) == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(Nat.double(Nat.double(K))), False{}, P.Nat.odd_double(Nat.double(K))) :
    {Nat.add(Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(Nat.double(Nat.double(K))))))), Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n))))) == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}
  %Equal.sym(Nat, P.Nat.half(Nat.double(Nat.double(K))), Nat.double(K), P.Nat.half_double(Nat.double(K))) :
    {Nat.add(Nat.add(P.Nat.bit(False{}), Nat.double(P.Nat.bit(P.Nat.odd(_)))), Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n))))) == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}
  %Equal.sym(Bool, P.Nat.odd(Nat.double(K)), False{}, P.Nat.odd_double(K)) :
    {Nat.add(Nat.add(P.Nat.bit(False{}), Nat.double(P.Nat.bit(_))), Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n))))) == Nat.double(Nat.double(V.U.N(U32.shrn(y, 2n)))) : Nat}
  {==}

# A value shifted down two bits and back up: four times the word.
law WD.shl2:
  for +x: U32
  {V.U.N(U32.shln(U32.shrn(x, 2n), 2n)) == Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))) : Nat}

def WD.shl2(x):
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shl(U32.shrn(x, 2n)))), Nat.double(V.U.N(U32.shl(U32.shrn(x, 2n)))), V.U.N_shl(U32.shl(U32.shrn(x, 2n)), (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shrn(x, 2n)), 31n), V.U.bit(U32.shrn(x, 2n), 30n), V.U.bit_shl(U32.shrn(x, 2n), 30n, {==})) : {_ == False{} : Bool}; (%Equal.sym(Bool, V.U.bit(U32.shrn(x, 2n), 30n), V.U.bit(x, 32n), V.U.bit_shrn(x, 2n, 30n)) : {_ == False{} : Bool}; V.U.bit_beyond(x, 32n, {==}))))) :
    {_ == Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shrn(x, 2n))), Nat.double(V.U.N(U32.shrn(x, 2n))), V.U.N_shl(U32.shrn(x, 2n), (%Equal.sym(Bool, V.U.bit(U32.shrn(x, 2n), 31n), V.U.bit(x, 33n), V.U.bit_shrn(x, 2n, 31n)) : {_ == False{} : Bool}; V.U.bit_beyond(x, 33n, {==})))) :
    {Nat.double(_) == Nat.double(Nat.double(V.U.N(U32.shrn(x, 2n)))) : Nat}
  {==}

# Four single steps are a step of four.
law WD.step4:
  for +x: U32
  {WD.step(4n, x) == U32.add(x, 4) : U32}

def WD.step4(x):
  %Equal.sym(U32, U32.add(U32.add(x, 1), 1), U32.add(x, 2), V.U.add_assoc(x, 1, 1)) :
    {U32.add(U32.add(_, 1), 1) == U32.add(x, 4) : U32}
  %Equal.sym(U32, U32.add(U32.add(x, 2), 1), U32.add(x, 3), V.U.add_assoc(x, 2, 1)) :
    {U32.add(_, 1) == U32.add(x, 4) : U32}
  %Equal.sym(U32, U32.add(U32.add(x, 3), 1), U32.add(x, 4), V.U.add_assoc(x, 3, 1)) :
    {_ == U32.add(x, 4) : U32}
  {==}

law WD.and_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}

def WD.and_assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Holding xs then ys: xs at i and ys at i + x, where x has the length of xs.
law WD.has_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +i: U32
  for +x: U32
  for +e: {V.U.N(x) == S.S.len(xs) : Nat}
  {S.S.has(WD.app(xs, ys), t, i) == Bool.and(S.S.has(xs, t, i), S.S.has(ys, t, U32.add(i, x))) : Bool}

def WD.has_app(xs, ys, t, i, x, e):
  match xs:
    case []:
      %Equal.sym(U32, x, 0, WD.zero_of(x, e)) :
        {S.S.has(ys, t, i) == S.S.has(ys, t, U32.add(i, _)) : Bool}
      %Equal.sym(U32, U32.add(i, 0), i, V.U.add_zero_r(i)) :
        {S.S.has(ys, t, i) == S.S.has(ys, t, _) : Bool}
      {==}
    case y <> r:
      %Equal.sym(Bool, S.S.has(WD.app(r, ys), t, U32.add(i, 1)), Bool.and(S.S.has(r, t, U32.add(i, 1)), S.S.has(ys, t, U32.add(U32.add(i, 1), U32.sub(x, 1)))), WD.has_app(r, ys, t, U32.add(i, 1), U32.sub(x, 1), WD.pred_N(x, S.S.len(r), e))) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(y, 255)), _) == Bool.and(Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(y, 255)), S.S.has(r, t, U32.add(i, 1))), S.S.has(ys, t, U32.add(i, x))) : Bool}
      %Equal.sym(U32, U32.add(U32.add(i, 1), U32.sub(x, 1)), U32.add(i, x), WD.add_shift(i, x)) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(y, 255)), Bool.and(S.S.has(r, t, U32.add(i, 1)), S.S.has(ys, t, _))) == Bool.and(Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(y, 255)), S.S.has(r, t, U32.add(i, 1))), S.S.has(ys, t, U32.add(i, x))) : Bool}
      WD.and_assoc(U32.is_eq(Y.BP.byt(t, i), U32.and(y, 255)), S.S.has(r, t, U32.add(i, 1)), S.S.has(ys, t, U32.add(i, x)))

