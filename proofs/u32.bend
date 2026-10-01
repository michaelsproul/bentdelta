import Base
import ./nat.bend as P
import ./word.bend as W

# Lemmas about U32: its arithmetic, order and bits, from those of Word(32n).

# Bits
# ====

def U.bit(x: U32, +i: Nat) -> Bool:
  match x:
    case U32{w}:
      W.W.bit(32n, w, i)

law U.bit_and:
  for +x: U32
  for +y: U32
  for +i: Nat
  {U.bit(U32.and(x, y), i) == Bool.and(U.bit(x, i), U.bit(y, i)) : Bool}

def U.bit_and(x, y, i):
  match x y:
    case U32{a} U32{b}:
      W.W.bit_and(32n, a, b, i)

law U.bit_or:
  for +x: U32
  for +y: U32
  for +i: Nat
  {U.bit(U32.or(x, y), i) == Bool.or(U.bit(x, i), U.bit(y, i)) : Bool}

def U.bit_or(x, y, i):
  match x y:
    case U32{a} U32{b}:
      W.W.bit_or(32n, a, b, i)

law U.bit_xor:
  for +x: U32
  for +y: U32
  for +i: Nat
  {U.bit(U32.xor(x, y), i) == Bool.xor(U.bit(x, i), U.bit(y, i)) : Bool}

def U.bit_xor(x, y, i):
  match x y:
    case U32{a} U32{b}:
      W.W.bit_xor(32n, a, b, i)

law U.bit_not:
  for +x: U32
  for +i: Nat
  for +h: {Nat.cmp(i, 32n) == LT{} : Cmp}
  {U.bit(U32.not(x), i) == Bool.not(U.bit(x, i)) : Bool}

def U.bit_not(x, i, h):
  match x:
    case U32{a}:
      W.W.bit_not(32n, a, i, h)

law U.bit_shr:
  for +x: U32
  for +i: Nat
  {U.bit(U32.shr(x), i) == U.bit(x, 1n+i) : Bool}

def U.bit_shr(x, i):
  match x:
    case U32{a}:
      W.W.bit_shr(32n, a, i)

law U.bit_shl0:
  for +x: U32
  {U.bit(U32.shl(x), 0n) == False{} : Bool}

def U.bit_shl0(x):
  match x:
    case U32{a}:
      W.W.bit_shl0(32n, a)

law U.bit_shl:
  for +x: U32
  for +i: Nat
  for +h: {Nat.cmp(1n+i, 32n) == LT{} : Cmp}
  {U.bit(U32.shl(x), 1n+i) == U.bit(x, i) : Bool}

def U.bit_shl(x, i, h):
  match x:
    case U32{a}:
      W.W.bit_shl(32n, a, i, h)

# Shifting down by k moves bit i + k to i.
law U.bit_shrn:
  for +x: U32
  for +k: Nat
  for +i: Nat
  {U.bit(U32.shrn(x, k), i) == U.bit(x, Nat.add(i, k)) : Bool}

def U.bit_shrn(x, k, i):
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(i, 0n), i, P.Nat.add_zero_r(i)) :
        {U.bit(x, i) == U.bit(x, _) : Bool}
      {==}
    case 1n+p:
      %Equal.sym(Bool, U.bit(U32.shr(U32.shrn(x, p)), i), U.bit(U32.shrn(x, p), 1n+i),
        U.bit_shr(U32.shrn(x, p), i)) :
        {_ == U.bit(x, Nat.add(i, 1n+p)) : Bool}
      %Equal.sym(Bool, U.bit(U32.shrn(x, p), 1n+i), U.bit(x, Nat.add(1n+i, p)),
        U.bit_shrn(x, p, 1n+i)) :
        {_ == U.bit(x, Nat.add(i, 1n+p)) : Bool}
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), P.Nat.add_succ_r(i, p)) :
        {U.bit(x, 1n+Nat.add(i, p)) == U.bit(x, _) : Bool}
      {==}

# Values
# ======

def U.N(x: U32) -> Nat:
  U32.to_nat(x)

law U.cmp_nat:
  for +x: U32
  for +y: U32
  {U32.cmp(x, y) == Nat.cmp(U.N(x), U.N(y)) : Cmp}

def U.cmp_nat(x, y):
  match x y:
    case U32{a} U32{b}:
      W.W.cmp_nat(32n, a, b)

law U.cmp_refl:
  for +x: U32
  {U32.cmp(x, x) == EQ{} : Cmp}

def U.cmp_refl(x):
  match x:
    case U32{a}:
      W.W.cmp_refl(32n, a)

law U.eq_N:
  for +x: U32
  for +y: U32
  for +e: {U.N(x) == U.N(y) : Nat}
  {x == y : U32}

def U.eq_N(x, y, e):
  match x y:
    case U32{a} U32{b}:
      %W.W.eq_N(32n, a, b, e) : {U32{a} == U32{_} : U32}
      {==}

# U32.is_eq answers True only for equal words.
law U.is_eq:
  for +x: U32
  for +y: U32
  for +e: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}

law U.is_eq.go:
  for +x: U32
  for +y: U32
  for +c: Cmp
  for +q: {U32.cmp(x, y) == c : Cmp}
  for +e: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}

def U.is_eq.go(x, y, c, q, e):
  match c:
    case LT{}:
      P.Bool.false_true({x == y : U32},
        (%q : {Cmp.is_eq(_) == True{} : Bool}
          e))
    case EQ{}:
      U.eq_N(x, y, P.Nat.cmp_eq(U.N(x), U.N(y),
        (%U.cmp_nat(x, y) : {_ == EQ{} : Cmp}
          q)))
    case GT{}:
      P.Bool.false_true({x == y : U32},
        (%q : {Cmp.is_eq(_) == True{} : Bool}
          e))

def U.is_eq(x, y, e):
  U.is_eq.go(x, y, U32.cmp(x, y), {==}, e)

law U.add_nowrap:
  for +x: U32
  for +y: U32
  for +h: {U32.is_le(x, U32.add(x, y)) == True{} : Bool}
  {U.N(U32.add(x, y)) == Nat.add(U.N(x), U.N(y)) : Nat}

def U.add_nowrap(x, y, h):
  match x y:
    case U32{a} U32{b}:
      W.W.add_nowrap(32n, a, b, h)

law U.sub_nat:
  for +x: U32
  for +y: U32
  for +h: {U32.is_le(y, x) == True{} : Bool}
  {Nat.add(U.N(U32.sub(x, y)), U.N(y)) == U.N(x) : Nat}

def U.sub_nat(x, y, h):
  match x y:
    case U32{a} U32{b}:
      W.W.sub_nat(32n, a, b, h)

law U.add_sub:
  for +x: U32
  for +y: U32
  {U32.add(U32.sub(x, y), y) == x : U32}

def U.add_sub(x, y):
  match x y:
    case U32{a} U32{b}:
      %W.W.add_sub(32n, a, b) : {U32{Word.add(32n, Word.sub(32n, a, b), b)} == U32{_} : U32}
      {==}

law U.sub_add:
  for +x: U32
  for +y: U32
  {U32.sub(U32.add(x, y), y) == x : U32}

def U.sub_add(x, y):
  match x y:
    case U32{a} U32{b}:
      %W.W.sub_add(32n, a, b) : {U32{Word.sub(32n, Word.add(32n, a, b), b)} == U32{_} : U32}
      {==}

law U.add_assoc:
  for +x: U32
  for +y: U32
  for +z: U32
  {U32.add(U32.add(x, y), z) == U32.add(x, U32.add(y, z)) : U32}

def U.add_assoc(x, y, z):
  match x y z:
    case U32{a} U32{b} U32{c}:
      %W.W.add_assoc(32n, a, b, c) :
        {U32{Word.add(32n, Word.add(32n, a, b), c)} == U32{_} : U32}
      {==}

law U.N_shr:
  for +x: U32
  {U.N(U32.shr(x)) == P.Nat.half(U.N(x)) : Nat}

def U.N_shr(x):
  match x:
    case U32{a}:
      W.W.N_shr(32n, a)

law U.N_shl:
  for +x: U32
  for +h: {U.bit(x, 31n) == False{} : Bool}
  {U.N(U32.shl(x)) == Nat.double(U.N(x)) : Nat}

def U.N_shl(x, h):
  match x:
    case U32{a}:
      W.W.N_shl(31n, a, h)

law U.bit_high:
  for +x: U32
  for +p: Nat
  for +k: Nat
  for +h1: {Nat.cmp(U.N(x), P.Nat.pow2(p)) == LT{} : Cmp}
  for +h2: {Cmp.is_le(Nat.cmp(p, k)) == True{} : Bool}
  {U.bit(x, k) == False{} : Bool}

def U.bit_high(x, p, k, h1, h2):
  match x:
    case U32{a}:
      W.W.bit_high(32n, a, p, k, h1, h2)

law U.bit_beyond:
  for +x: U32
  for +k: Nat
  for +h: {Cmp.is_le(Nat.cmp(32n, k)) == True{} : Bool}
  {U.bit(x, k) == False{} : Bool}

def U.bit_beyond(x, k, h):
  match x:
    case U32{a}:
      W.W.bit_beyond(32n, a, k, h)

# Shifting up by k moves bit j to j + k.
law U.bit_shln_hi:
  for +x: U32
  for +k: Nat
  for +j: Nat
  for +h: {Nat.cmp(Nat.add(j, k), 32n) == LT{} : Cmp}
  {U.bit(U32.shln(x, k), Nat.add(j, k)) == U.bit(x, j) : Bool}

def U.bit_shln_hi(x, k, j, h):
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(j, 0n), j, P.Nat.add_zero_r(j)) :
        {U.bit(x, _) == U.bit(x, j) : Bool}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(j, 1n+p), 1n+Nat.add(j, p), P.Nat.add_succ_r(j, p)) :
        {U.bit(U32.shl(U32.shln(x, p)), _) == U.bit(x, j) : Bool}
      %Equal.sym(Bool, U.bit(U32.shl(U32.shln(x, p)), 1n+Nat.add(j, p)),
        U.bit(U32.shln(x, p), Nat.add(j, p)),
        U.bit_shl(U32.shln(x, p), Nat.add(j, p),
          (%P.Nat.add_succ_r(j, p) : {Nat.cmp(_, 32n) == LT{} : Cmp}
            h))) :
        {_ == U.bit(x, j) : Bool}
      U.bit_shln_hi(x, p, j,
        P.Nat.lt_succ_l(Nat.add(j, p), 32n,
          (%P.Nat.add_succ_r(j, p) : {Nat.cmp(_, 32n) == LT{} : Cmp}
            h)))

# Shifting up by k (at most 32) clears the bits below k.
law U.bit_shln_lo:
  for +x: U32
  for +k: Nat
  for +j: Nat
  for +h1: {Nat.cmp(j, k) == LT{} : Cmp}
  for +h2: {Cmp.is_le(Nat.cmp(k, 32n)) == True{} : Bool}
  {U.bit(U32.shln(x, k), j) == False{} : Bool}

def U.bit_shln_lo(x, k, j, h1, h2):
  match k j:
    case 0n _:
      P.Nat.lt_zero({U.bit(U32.shln(x, 0n), j) == False{} : Bool}, j, h1)
    case 1n+p 0n:
      U.bit_shl0(U32.shln(x, p))
    case 1n+p 1n+i:
      %Equal.sym(Bool, U.bit(U32.shl(U32.shln(x, p)), 1n+i), U.bit(U32.shln(x, p), i),
        U.bit_shl(U32.shln(x, p), i, P.Nat.lt_le_trans(1n+i, 1n+p, 32n, h1, h2))) :
        {_ == False{} : Bool}
      U.bit_shln_lo(x, p, i, h1, P.Nat.le_succ_l(p, 32n, h2))

law U.bit_one:
  for +k: Nat
  {U.bit(1, 1n+k) == False{} : Bool}

def U.bit_one(k):
  W.W.bit_zero(31n, k)

# 2^q (for q < 31) has its top bit clear.
law U.pow_top:
  for +q: Nat
  for +h: {Nat.cmp(1n+q, 32n) == LT{} : Cmp}
  for +e: {U.N(U32.shln(1, q)) == P.Nat.pow2(q) : Nat}
  {U.bit(U32.shln(1, q), 31n) == False{} : Bool}

def U.pow_top(q, h, e):
  U.bit_high(U32.shln(1, q), 1n+q, 31n,
    (%Equal.sym(Nat, U.N(U32.shln(1, q)), P.Nat.pow2(q), e) :
      {Nat.cmp(_, Nat.double(P.Nat.pow2(q))) == LT{} : Cmp}
      P.Nat.lt_double(P.Nat.pow2(q), P.Nat.pow2_pos(q))),
    P.Nat.lt_succ_le(1n+q, 31n, h))

# The value of 2^p as a U32.
law U.N_pow:
  for +p: Nat
  for +h: {Nat.cmp(p, 32n) == LT{} : Cmp}
  {U.N(U32.shln(1, p)) == P.Nat.pow2(p) : Nat}

law U.N_pow.go:
  for +q: Nat
  for +h: {Nat.cmp(1n+q, 32n) == LT{} : Cmp}
  for +e: {U.N(U32.shln(1, q)) == P.Nat.pow2(q) : Nat}
  {U.N(U32.shl(U32.shln(1, q))) == Nat.double(P.Nat.pow2(q)) : Nat}

def U.N_pow.go(q, h, e):
  %Equal.sym(Nat, U.N(U32.shl(U32.shln(1, q))), Nat.double(U.N(U32.shln(1, q))),
    U.N_shl(U32.shln(1, q), U.pow_top(q, h, e))) :
    {_ == Nat.double(P.Nat.pow2(q)) : Nat}
  %Equal.sym(Nat, U.N(U32.shln(1, q)), P.Nat.pow2(q), e) :
    {Nat.double(_) == Nat.double(P.Nat.pow2(q)) : Nat}
  {==}

def U.N_pow(p, h):
  match p:
    case 0n:
      {==}
    case 1n+q:
      U.N_pow.go(q, h, U.N_pow(q, P.Nat.lt_succ_l(q, 32n, h)))

# Halving 2^(1+q) gives 2^q.
law U.shr_pow:
  for +q: Nat
  for +h: {Nat.cmp(1n+q, 32n) == LT{} : Cmp}
  {U32.shr(U32.shln(1, 1n+q)) == U32.shln(1, q) : U32}

def U.shr_pow(q, h):
  U.eq_N(U32.shr(U32.shln(1, 1n+q)), U32.shln(1, q),
    (%Equal.sym(Nat, U.N(U32.shr(U32.shln(1, 1n+q))), P.Nat.half(U.N(U32.shln(1, 1n+q))),
        U.N_shr(U32.shln(1, 1n+q))) :
      {_ == U.N(U32.shln(1, q)) : Nat}
      (%Equal.sym(Nat, U.N(U32.shln(1, 1n+q)), P.Nat.pow2(1n+q), U.N_pow(1n+q, h)) :
        {P.Nat.half(_) == U.N(U32.shln(1, q)) : Nat}
        (%Equal.sym(Nat, U.N(U32.shln(1, q)), P.Nat.pow2(q), U.N_pow(q, P.Nat.lt_succ_l(q, 32n, h))) :
          {P.Nat.half(Nat.double(P.Nat.pow2(q))) == _ : Nat}
          P.Nat.half_double(P.Nat.pow2(q))))))

# Order facts
# ===========

# Not below means at or above.
law U.not_lt:
  for +x: U32
  for +y: U32
  for +h: {U32.is_lt(x, y) == False{} : Bool}
  {U32.is_le(y, x) == True{} : Bool}

law U.not_lt.go:
  for +x: U32
  for +y: U32
  for +c: Cmp
  for +e: {Nat.cmp(U.N(x), U.N(y)) == c : Cmp}
  for +h: {U32.is_lt(x, y) == False{} : Bool}
  {U32.is_le(y, x) == True{} : Bool}

def U.not_lt.go(x, y, c, e, h):
  match c:
    case LT{}:
      P.Bool.true_false({U32.is_le(y, x) == True{} : Bool},
        (%e : {Cmp.is_lt(_) == False{} : Bool}
          (%U.cmp_nat(x, y) : {Cmp.is_lt(_) == False{} : Bool}
            h)))
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(y, x), Nat.cmp(U.N(y), U.N(x)), U.cmp_nat(y, x)) :
        {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(U.N(y), U.N(x)), P.Cmp.flip(Nat.cmp(U.N(x), U.N(y))),
        P.Nat.cmp_swap(U.N(x), U.N(y))) : {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(U.N(x), U.N(y)), EQ{}, e) : {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(y, x), Nat.cmp(U.N(y), U.N(x)), U.cmp_nat(y, x)) :
        {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(U.N(y), U.N(x)), P.Cmp.flip(Nat.cmp(U.N(x), U.N(y))),
        P.Nat.cmp_swap(U.N(x), U.N(y))) : {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(U.N(x), U.N(y)), GT{}, e) : {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
      {==}

# Below 1 is 0.
law U.lt_one:
  for +j: U32
  for +h: {U32.is_lt(j, 1) == True{} : Bool}
  {j == 0 : U32}

law U.lt_one.go:
  for +m: Nat
  for +h: {Cmp.is_lt(Nat.cmp(m, 1n)) == True{} : Bool}
  {m == 0n : Nat}

def U.lt_one.go(m, h):
  match m:
    case 0n:
      {==}
    case 1n+k:
      match k:
        case 0n:
          P.Bool.false_true({1n == 0n : Nat}, h)
        case 1n+r:
          P.Bool.false_true({2n+r == 0n : Nat}, h)

def U.lt_one(j, h):
  U.eq_N(j, 0, U.lt_one.go(U.N(j),
    (%U.cmp_nat(j, 1) : {Cmp.is_lt(_) == True{} : Bool}
      h)))

def U.not_lt(x, y, h):
  U.not_lt.go(x, y, Nat.cmp(U.N(x), U.N(y)), {==}, h)

law U.lt_N:
  for +x: U32
  for +y: U32
  for +h: {U32.is_lt(x, y) == True{} : Bool}
  {Nat.cmp(U.N(x), U.N(y)) == LT{} : Cmp}

def U.lt_N(x, y, h):
  P.Cmp.is_lt_lt(Nat.cmp(U.N(x), U.N(y)),
    (%U.cmp_nat(x, y) : {Cmp.is_lt(_) == True{} : Bool}
      h))

law U.N_lt:
  for +x: U32
  for +y: U32
  for +h: {Nat.cmp(U.N(x), U.N(y)) == LT{} : Cmp}
  {U32.is_lt(x, y) == True{} : Bool}

def U.N_lt(x, y, h):
  %Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U.N(x), U.N(y)), U.cmp_nat(x, y)) :
    {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(U.N(x), U.N(y)), LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

# In the upper half of [0, 2^(1+q)), j - 2^q lies in [0, 2^q).
law U.sub_half:
  for +j: U32
  for +q: Nat
  for +hq: {Nat.cmp(1n+q, 32n) == LT{} : Cmp}
  for +hj: {U32.is_lt(j, U32.shln(1, 1n+q)) == True{} : Bool}
  for +hz: {U32.is_lt(j, U32.shln(1, q)) == False{} : Bool}
  {U32.is_lt(U32.sub(j, U32.shln(1, q)), U32.shln(1, q)) == True{} : Bool}

def U.sub_half(j, q, hq, hj, hz):
  U.N_lt(U32.sub(j, U32.shln(1, q)), U32.shln(1, q),
    (%Equal.sym(Nat, U.N(U32.shln(1, q)), P.Nat.pow2(q), U.N_pow(q, P.Nat.lt_succ_l(q, 32n, hq))) :
      {Nat.cmp(U.N(U32.sub(j, U32.shln(1, q))), _) == LT{} : Cmp}
      (%P.Nat.cmp_add_rr(U.N(U32.sub(j, U32.shln(1, q))), P.Nat.pow2(q), P.Nat.pow2(q)) :
        {_ == LT{} : Cmp}
        (%U.N_pow(q, P.Nat.lt_succ_l(q, 32n, hq)) :
          {Nat.cmp(Nat.add(U.N(U32.sub(j, U32.shln(1, q))), _), Nat.add(P.Nat.pow2(q), P.Nat.pow2(q)))
            == LT{} : Cmp}
          (%Equal.sym(Nat, Nat.add(U.N(U32.sub(j, U32.shln(1, q))), U.N(U32.shln(1, q))), U.N(j),
              U.sub_nat(j, U32.shln(1, q), U.not_lt(j, U32.shln(1, q), hz))) :
            {Nat.cmp(_, Nat.add(P.Nat.pow2(q), P.Nat.pow2(q))) == LT{} : Cmp}
            (%P.Nat.double_add(P.Nat.pow2(q)) : {Nat.cmp(U.N(j), _) == LT{} : Cmp}
              (%U.N_pow(1n+q, hq) : {Nat.cmp(U.N(j), _) == LT{} : Cmp}
                U.lt_N(j, U32.shln(1, 1n+q), hj))))))))

# Taking the same away from different words leaves different words.
law U.sub_ne:
  for +a: U32
  for +b: U32
  for +h: U32
  for +ne: {U32.is_eq(a, b) == False{} : Bool}
  {U32.is_eq(U32.sub(a, h), U32.sub(b, h)) == False{} : Bool}

law U.sub_ne.go:
  for +a: U32
  for +b: U32
  for +h: U32
  for +r: Bool
  for +e: {U32.is_eq(U32.sub(a, h), U32.sub(b, h)) == r : Bool}
  for +ne: {U32.is_eq(a, b) == False{} : Bool}
  {r == False{} : Bool}

# Equal differences from the same word come from equal words.
law U.eq_back:
  for +a: U32
  for +b: U32
  for +h: U32
  for +e: {U32.sub(a, h) == U32.sub(b, h) : U32}
  {b == a : U32}

def U.eq_back(a, b, h, e):
  %U.add_sub(a, h) : {b == _ : U32}
  %U.add_sub(b, h) : {_ == U32.add(U32.sub(a, h), h) : U32}
  %e : {U32.add(_, h) == U32.add(U32.sub(a, h), h) : U32}
  {==}

law U.is_eq_refl:
  for +x: U32
  {U32.is_eq(x, x) == True{} : Bool}

def U.is_eq_refl(x):
  %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, U.cmp_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def U.sub_ne.go(a, b, h, r, e, ne):
  match r:
    case False{}:
      {==}
    case True{}:
      P.Bool.true_false({True{} == False{} : Bool},
        (%U.is_eq_refl(b) : {_ == False{} : Bool}
          (%Equal.sym(U32, b, a, U.eq_back(a, b, h, U.is_eq(U32.sub(a, h), U32.sub(b, h), e))) :
            {U32.is_eq(_, b) == False{} : Bool}
            ne)))

def U.sub_ne(a, b, h, ne):
  U.sub_ne.go(a, b, h, U32.is_eq(U32.sub(a, h), U32.sub(b, h)), {==}, ne)

# Extensionality
# ==============

def U.allb(-x: U32, -y: U32, k: Nat) -> Data:
  match k:
    case 0n:
      Unit
    case 1n+j:
      Sigma<&2, &2, {U.bit(x, j) == U.bit(y, j) : Bool}, _ => U.allb(x, y, j)>

law U.ext:
  for +x: U32
  for +y: U32
  for +h: U.allb(x, y, 32n)
  {x == y : U32}

def U.ext(x, y, h):
  match x y:
    case U32{a} U32{b}:
      %W.W.ext(32n, a, b, h) : {U32{a} == U32{_} : U32}
      {==}

law U.bit_ones:
  for +x: U32
  for +p: Nat
  for +k: Nat
  for +e: {Nat.add(U.N(x), 1n) == P.Nat.pow2(p) : Nat}
  for +hk: {Nat.cmp(k, p) == LT{} : Cmp}
  {U.bit(x, k) == True{} : Bool}

def U.bit_ones(x, p, k, e, hk):
  match x:
    case U32{a}:
      W.W.bit_ones(32n, a, p, k, e, hk)

# The mask of p low bits.
def U.ones(+p: Nat) -> U32:
  U32.sub(U32.shln(1, p), 1)

law U.N_ones:
  for +p: Nat
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  {Nat.add(U.N(U.ones(p)), 1n) == P.Nat.pow2(p) : Nat}

def U.N_ones(p, hd):
  %U.N_pow(p, hd) : {Nat.add(U.N(U.ones(p)), 1n) == _ : Nat}
  U.sub_nat(U32.shln(1, p), 1,
    (%Equal.sym(Cmp, U32.cmp(1, U32.shln(1, p)), Nat.cmp(1n, U.N(U32.shln(1, p))),
        U.cmp_nat(1, U32.shln(1, p))) :
      {Cmp.is_le(_) == True{} : Bool}
      (%Equal.sym(Nat, U.N(U32.shln(1, p)), P.Nat.pow2(p), U.N_pow(p, hd)) :
        {Cmp.is_le(Nat.cmp(1n, _)) == True{} : Bool}
        P.Nat.one_le(P.Nat.pow2(p), P.Nat.pow2_pos(p)))))

law U.mask_bit:
  for +i: U32
  for +p: Nat
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}
  for +j: Nat
  {U.bit(U32.and(i, U.ones(p)), j) == U.bit(i, j) : Bool}

law U.mask_bit.go:
  for +i: U32
  for +p: Nat
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}
  for +j: Nat
  for +c: Cmp
  for +e: {Nat.cmp(j, p) == c : Cmp}
  {Bool.and(U.bit(i, j), U.bit(U.ones(p), j)) == U.bit(i, j) : Bool}

law U.mask_bit.hi:
  for +i: U32
  for +p: Nat
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}
  for +j: Nat
  for +h: {Cmp.is_le(P.Cmp.flip(Nat.cmp(j, p))) == True{} : Bool}
  {Bool.and(U.bit(i, j), U.bit(U.ones(p), j)) == U.bit(i, j) : Bool}

def U.mask_bit.hi(i, p, hd, hi, j, h):
  %Equal.sym(Bool, U.bit(i, j), False{},
    U.bit_high(i, p, j,
      (%U.N_pow(p, hd) : {Nat.cmp(U.N(i), _) == LT{} : Cmp}
        U.lt_N(i, U32.shln(1, p), hi)),
      (%Equal.sym(Cmp, Nat.cmp(p, j), P.Cmp.flip(Nat.cmp(j, p)), P.Nat.cmp_swap(j, p)) :
        {Cmp.is_le(_) == True{} : Bool}
        h))) :
    {Bool.and(_, U.bit(U.ones(p), j)) == _ : Bool}
  {==}

def U.mask_bit.go(i, p, hd, hi, j, c, e):
  match c:
    case LT{}:
      %Equal.sym(Bool, U.bit(U.ones(p), j), True{}, U.bit_ones(U.ones(p), p, j, U.N_ones(p, hd), e)) :
        {Bool.and(U.bit(i, j), _) == U.bit(i, j) : Bool}
      P.Bool.and_true(U.bit(i, j))
    case EQ{}:
      U.mask_bit.hi(i, p, hd, hi, j, (%Equal.sym(Cmp, Nat.cmp(j, p), EQ{}, e) :
        {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
        {==}))
    case GT{}:
      U.mask_bit.hi(i, p, hd, hi, j, (%Equal.sym(Cmp, Nat.cmp(j, p), GT{}, e) :
        {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
        {==}))

def U.mask_bit(i, p, hd, hi, j):
  %Equal.sym(Bool, U.bit(U32.and(i, U.ones(p)), j), Bool.and(U.bit(i, j), U.bit(U.ones(p), j)),
    U.bit_and(i, U.ones(p), j)) : {_ == U.bit(i, j) : Bool}
  U.mask_bit.go(i, p, hd, hi, j, Nat.cmp(j, p), {==})

def U.mask_all(+i: U32, +p: Nat, +hd: {Nat.cmp(p, 32n) == LT{} : Cmp},
  +hi: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}, +k: Nat) ->
  U.allb(U32.and(i, U.ones(p)), i, k):
  match k:
    case 0n:
      Unit{}
    case 1n+j:
      W.W.allb.con({U.bit(U32.and(i, U.ones(p)), j) == U.bit(i, j) : Bool},
        U.allb(U32.and(i, U.ones(p)), i, j),
        U.mask_bit(i, p, hd, hi, j), U.mask_all(i, p, hd, hi, j))

# Masking an index below 2^p to p bits keeps it.
law U.mask_id:
  for +i: U32
  for +p: Nat
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}
  {U32.and(i, U32.sub(U32.shln(1, p), 1)) == i : U32}

def U.mask_id(i, p, hd, hi):
  U.ext(U32.and(i, U.ones(p)), i, U.mask_all(i, p, hd, hi, 32n))

# The bits of 255: the 8 low ones.
law U.bit_255_lo:
  for +k: Nat
  for +h: {Nat.cmp(k, 8n) == LT{} : Cmp}
  {U.bit(255, k) == True{} : Bool}

def U.bit_255_lo(k, h):
  U.bit_ones(255, 8n, k, {==}, h)

law U.bit_255_hi:
  for +k: Nat
  for +h: {Cmp.is_le(Nat.cmp(8n, k)) == True{} : Bool}
  {U.bit(255, k) == False{} : Bool}

def U.bit_255_hi(k, h):
  U.bit_high(255, 8n, k, {==}, h)

# The low byte of v.
law U.bit_low:
  for +v: U32
  for +k: Nat
  for +h: {Nat.cmp(k, 8n) == LT{} : Cmp}
  {U.bit(U32.and(v, 255), k) == U.bit(v, k) : Bool}

def U.bit_low(v, k, h):
  %Equal.sym(Bool, U.bit(U32.and(v, 255), k), Bool.and(U.bit(v, k), U.bit(255, k)),
    U.bit_and(v, 255, k)) : {_ == U.bit(v, k) : Bool}
  %Equal.sym(Bool, U.bit(255, k), True{}, U.bit_255_lo(k, h)) :
    {Bool.and(U.bit(v, k), _) == U.bit(v, k) : Bool}
  P.Bool.and_true(U.bit(v, k))

law U.bit_low_hi:
  for +v: U32
  for +k: Nat
  for +h: {Cmp.is_le(Nat.cmp(8n, k)) == True{} : Bool}
  {U.bit(U32.and(v, 255), k) == False{} : Bool}

def U.bit_low_hi(v, k, h):
  %Equal.sym(Bool, U.bit(U32.and(v, 255), k), Bool.and(U.bit(v, k), U.bit(255, k)),
    U.bit_and(v, 255, k)) : {_ == False{} : Bool}
  %Equal.sym(Bool, U.bit(255, k), False{}, U.bit_255_hi(k, h)) :
    {Bool.and(U.bit(v, k), _) == False{} : Bool}
  P.Bool.and_false(U.bit(v, k))

# A sum below some U32 does not wrap.
law U.add_N:
  for +x: U32
  for +y: U32
  for +e: U32
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(U.N(x), U.N(y)), U.N(e))) == True{} : Bool}
  {U.N(U32.add(x, y)) == Nat.add(U.N(x), U.N(y)) : Nat}

def U.add_N(x, y, e, h):
  match x y e:
    case U32{a} U32{b} U32{c}:
      W.W.add_bound(32n, a, b, c, h)

# The successor of a U32 below another.
law U.succ_N:
  for +i: U32
  for +e: U32
  for +h: {Nat.cmp(U.N(i), U.N(e)) == LT{} : Cmp}
  {U.N(U32.add(i, 1)) == 1n+U.N(i) : Nat}

def U.succ_N(i, e, h):
  %P.Nat.add_one(U.N(i)) : {U.N(U32.add(i, 1)) == _ : Nat}
  U.add_N(i, 1, e,
    (%Equal.sym(Nat, Nat.add(U.N(i), 1n), 1n+U.N(i), P.Nat.add_one(U.N(i))) : {Cmp.is_le(Nat.cmp(_, U.N(e))) == True{} : Bool}
      P.Nat.lt_le_succ(U.N(i), U.N(e), h)))

law U.and_idem_r:
  for +x: U32
  for +y: U32
  {U32.and(U32.and(x, y), y) == U32.and(x, y) : U32}

def U.and_idem_r(x, y):
  match x y:
    case U32{a} U32{b}:
      %Equal.sym(Word(32n), Word.and(32n, Word.and(32n, a, b), b), Word.and(32n, a, b), W.W.and_idem_r(32n, a, b)) :
        {U32{_} == U32{Word.and(32n, a, b)} : U32}
      {==}

law U.add_comm:
  for +x: U32
  for +y: U32
  {U32.add(x, y) == U32.add(y, x) : U32}

def U.add_comm(x, y):
  match x y:
    case U32{a} U32{b}:
      %W.W.add_comm(32n, b, a) : {U32{_} == U32{Word.add(32n, b, a)} : U32}
      {==}

law U.add_zero_r:
  for +x: U32
  {U32.add(x, 0) == x : U32}

def U.add_zero_r(x):
  match x:
    case U32{a}:
      %Equal.sym(Word(32n), Word.add(32n, a, Word.zero(32n)), a, W.W.add_zero(32n, a)) : {U32{_} == U32{a} : U32}
      {==}

# (x + y) - x = y.
law U.sub_add_l:
  for +x: U32
  for +y: U32
  {U32.sub(U32.add(x, y), x) == y : U32}

def U.sub_add_l(x, y):
  %U.add_comm(y, x) : {U32.sub(_, x) == y : U32}
  U.sub_add(y, x)

law U.lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for +h1: {U32.is_lt(a, b) == True{} : Bool}
  for +h2: {U32.is_lt(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}

def U.lt_trans(a, b, c, h1, h2):
  U.N_lt(a, c, P.Nat.lt_trans(U.N(a), U.N(b), U.N(c), U.lt_N(a, b, h1), U.lt_N(b, c, h2)))

law U.gt1.m:
  for +m: Nat
  {Cmp.is_gt(Nat.cmp(0n, m)) == False{} : Bool}

def U.gt1.m(m):
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

law U.gt1.go:
  for +s: U32
  for +k: Nat
  for +e: {U.N(s) == k : Nat}
  for +ne: {U32.is_eq(s, 0) == False{} : Bool}
  {Cmp.is_gt(Nat.cmp(1n, U.N(s))) == False{} : Bool}

def U.gt1.go(s, k, e, ne):
  match k:
    case 0n:
      P.Bool.true_false({Cmp.is_gt(Nat.cmp(1n, U.N(s))) == False{} : Bool},
        (%U.eq_N(s, 0, e) : {U32.is_eq(_, 0) == False{} : Bool}
          ne))
    case 1n+m:
      %Equal.sym(Nat, U.N(s), 1n+m, e) : {Cmp.is_gt(Nat.cmp(1n, _)) == False{} : Bool}
      U.gt1.m(m)

# 1 > s only for s = 0.
law U.gt1_false:
  for +s: U32
  for +ne: {U32.is_eq(s, 0) == False{} : Bool}
  {U32.is_gt(1, s) == False{} : Bool}

def U.gt1_false(s, ne):
  %Equal.sym(Cmp, U32.cmp(1, s), Nat.cmp(U.N(1), U.N(s)), U.cmp_nat(1, s)) : {Cmp.is_gt(_) == False{} : Bool}
  U.gt1.go(s, U.N(s), {==}, ne)

law U.big.go:
  for +x: U32
  for +h: {U32.is_lt(x, 134217728) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_eq(U32.sub(2147483648, x), 0) == z : Bool}
  {U32.is_eq(U32.sub(2147483648, x), 0) == False{} : Bool}

def U.big.go(x, h, z, ez):
  match z:
    case False{}:
      ez
    case True{}:
      P.Bool.false_true({U32.is_eq(U32.sub(2147483648, x), 0) == False{} : Bool},
        (%{(%U.add_zero_r(x) : {_ == 2147483648 : U32}
              (%U.add_comm(0, x) : {_ == 2147483648 : U32}
                (%U.is_eq(U32.sub(2147483648, x), 0, ez) : {U32.add(_, x) == 2147483648 : U32}
                  U.add_sub(2147483648, x)))) : {x == 2147483648 : U32}} : {U32.is_lt(_, 134217728) == True{} : Bool}
          h))

# The decoder's limit check passes for a position below 2^27.
law U.big:
  for +x: U32
  for +h: {U32.is_lt(x, 134217728) == True{} : Bool}
  {U32.is_gt(1, U32.sub(2147483648, x)) == False{} : Bool}

def U.big(x, h):
  U.gt1_false(U32.sub(2147483648, x), U.big.go(x, h, U32.is_eq(U32.sub(2147483648, x), 0), {==}))
