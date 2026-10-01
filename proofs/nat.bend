import Base

# Lemmas about Bool, Cmp and Nat.
#
# Order facts are stated through Nat.cmp: {Nat.cmp(a, b) == LT{} : Cmp} for
# a < b, and so on. Nat values here stay symbolic: the checker writes Nat
# literals in unary, so no lemma needs a large one evaluated.

# Bool
# ====

law Bool.and_true:
  for +x: Bool
  {Bool.and(x, True{}) == x : Bool}

def Bool.and_true(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law Bool.and_false:
  for +x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def Bool.and_false(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law Bool.or_false:
  for +x: Bool
  {Bool.or(x, False{}) == x : Bool}

def Bool.or_false(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law Bool.or_true:
  for +x: Bool
  {Bool.or(x, True{}) == True{} : Bool}

def Bool.or_true(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a && b is True only if a is.
law Bool.and_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def Bool.and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law Bool.and_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

# False is not True.
def Bool.not_true(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

law Bool.false_true:
  for -A: Type
  for +e: {False{} == True{} : Bool}
  A

def Bool.false_true(A, e):
  Empty.absurd(A, (%Equal.sym(Bool, False{}, True{}, e) : Bool.not_true(_)
    Unit{}))

def Bool.and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Bool.false_true({b == True{} : Bool}, e)

# Nat: addition
# =============

law Nat.add_zero_r:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

def Nat.add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law Nat.add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def Nat.add_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law Nat.add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def Nat.add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Nat.add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), Nat.add_comm(p, b)) :
        {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Nat.add_succ_r(b, p))

law Nat.add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def Nat.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law Nat.double_add:
  for +a: Nat
  {Nat.double(a) == Nat.add(a, a) : Nat}

def Nat.double_add(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), Nat.add_succ_r(p, p)) :
        {2n+Nat.double(p) == 1n+_ : Nat}
      %Nat.double_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

# Nat: order
# ==========

law Nat.cmp_refl:
  for +a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def Nat.cmp_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_refl(p)

law Nat.cmp_succ:
  for +a: Nat
  {Nat.cmp(a, 1n+a) == LT{} : Cmp}

def Nat.cmp_succ(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_succ(p)

# a <= a + b.
law Nat.cmp_add_r:
  for +a: Nat
  for +b: Nat
  {Cmp.is_le(Nat.cmp(a, Nat.add(a, b))) == True{} : Bool}

def Nat.cmp_add_r(a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      Nat.cmp_add_r(p, b)

# Adding the same on the left keeps the order.
law Nat.cmp_add_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.add(c, a), Nat.add(c, b)) == Nat.cmp(a, b) : Cmp}

def Nat.cmp_add_l(c, a, b):
  match c:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_add_l(p, a, b)

def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

law Nat.cmp_swap:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(b, a) == Cmp.flip(Nat.cmp(a, b)) : Cmp}

def Nat.cmp_swap(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.cmp_swap(p, q)

# Nat: halves and parity
# ======================

# The bit worth 1 (True) or 0 (False).
def Nat.bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def Nat.odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      Bool.not(Nat.odd(p))

def Nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+Nat.half(q)

# 2^n.
def Nat.pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

law Nat.odd_double:
  for +m: Nat
  {Nat.odd(Nat.double(m)) == False{} : Bool}

def Nat.odd_double(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, Nat.odd(Nat.double(p)), False{}, Nat.odd_double(p)) :
        {Bool.not(Bool.not(_)) == False{} : Bool}
      {==}

law Nat.half_double:
  for +m: Nat
  {Nat.half(Nat.double(m)) == m : Nat}

def Nat.half_double(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Nat.half_double(p) : {1n+Nat.half(Nat.double(p)) == 1n+_ : Nat}
      {==}

law Nat.half_double1:
  for +m: Nat
  {Nat.half(1n+Nat.double(m)) == m : Nat}

def Nat.half_double1(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Nat.half_double1(p) : {1n+Nat.half(1n+Nat.double(p)) == 1n+_ : Nat}
      {==}

# Every n is twice its half plus its parity.
law Nat.split:
  for +n: Nat
  {n == Nat.add(Nat.bit(Nat.odd(n)), Nat.double(Nat.half(n))) : Nat}

law Nat.split.go:
  for +q: Nat
  for +o: Bool
  for +e: {Nat.odd(q) == o : Bool}
  for ih: {q == Nat.add(Nat.bit(Nat.odd(q)), Nat.double(Nat.half(q))) : Nat}
  {2n+q == Nat.add(Nat.bit(Bool.not(Bool.not(Nat.odd(q)))),
    2n+Nat.double(Nat.half(q))) : Nat}

def Nat.split.go(q, o, e, ih):
  match o:
    case False{}:
      %Equal.sym(Bool, Nat.odd(q), False{}, e) :
        {2n+q == Nat.add(Nat.bit(Bool.not(Bool.not(_))), 2n+Nat.double(Nat.half(q)))
          : Nat}
      %Equal.sym(Nat, q, Nat.add(Nat.bit(Nat.odd(q)), Nat.double(Nat.half(q))), ih) :
        {2n+_ == 2n+Nat.double(Nat.half(q)) : Nat}
      %Equal.sym(Bool, Nat.odd(q), False{}, e) :
        {2n+Nat.add(Nat.bit(_), Nat.double(Nat.half(q))) == 2n+Nat.double(Nat.half(q))
          : Nat}
      {==}
    case True{}:
      %Equal.sym(Bool, Nat.odd(q), True{}, e) :
        {2n+q == Nat.add(Nat.bit(Bool.not(Bool.not(_))), 2n+Nat.double(Nat.half(q)))
          : Nat}
      %Equal.sym(Nat, q, Nat.add(Nat.bit(Nat.odd(q)), Nat.double(Nat.half(q))), ih) :
        {2n+_ == 3n+Nat.double(Nat.half(q)) : Nat}
      %Equal.sym(Bool, Nat.odd(q), True{}, e) :
        {2n+Nat.add(Nat.bit(_), Nat.double(Nat.half(q))) == 3n+Nat.double(Nat.half(q))
          : Nat}
      {==}

def Nat.split(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Nat.split.go(q, Nat.odd(q), {==}, Nat.split(q))

# Nat: rearranging sums
# =====================

law Nat.double_distr:
  for +a: Nat
  for +b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}

def Nat.double_distr(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.double_distr(p, b) : {2n+Nat.double(Nat.add(p, b)) == 2n+_ : Nat}
      {==}

# (a + b) + (c + d) = (a + c) + (b + d).
law Nat.add_swap_mid:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def Nat.add_swap_mid(a, b, c, d):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)),
    Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add_assoc(a, b, Nat.add(c, d))) :
    {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)),
    Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add_assoc(a, c, Nat.add(b, d))) :
    {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %Nat.add_assoc(b, c, d) :
    {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  %Nat.add_assoc(c, b, d) :
    {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, _) : Nat}
  %Nat.add_comm(c, b) :
    {Nat.add(a, Nat.add(_, d)) == Nat.add(a, Nat.add(Nat.add(c, b), d)) : Nat}
  {==}

law Nat.odd_bit_double:
  for +o: Bool
  for +m: Nat
  {Nat.odd(Nat.add(Nat.bit(o), Nat.double(m))) == o : Bool}

def Nat.odd_bit_double(o, m):
  match o:
    case False{}:
      Nat.odd_double(m)
    case True{}:
      %Equal.sym(Bool, Nat.odd(Nat.double(m)), False{}, Nat.odd_double(m)) :
        {Bool.not(_) == True{} : Bool}
      {==}

law Nat.half_bit_double:
  for +o: Bool
  for +m: Nat
  {Nat.half(Nat.add(Nat.bit(o), Nat.double(m))) == m : Nat}

def Nat.half_bit_double(o, m):
  match o:
    case False{}:
      Nat.half_double(m)
    case True{}:
      Nat.half_double1(m)

# The bits of a full adder add up as its sum and carry say.
law Nat.full_add3:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.bit(c))
    == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))) : Nat}

def Nat.full_add3(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# Two split numbers and a carry add up to a split number (the arithmetic
# behind a full adder at one bit of a word).
law Nat.add_split:
  for +a: Bool
  for +x: Nat
  for +b: Bool
  for +y: Nat
  for +c: Bool
  {Nat.add(Nat.add(Nat.add(Nat.bit(a), Nat.double(x)), Nat.add(Nat.bit(b), Nat.double(y))),
    Nat.bit(c))
    == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.add(Nat.add(x, y),
        Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c)))))) : Nat}

# (a + b) + c = (a + c) + b.
law Nat.add_tail_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def Nat.add_tail_swap(a, b, c):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add_assoc(a, b, c)) :
    {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), Nat.add_assoc(a, c, b)) :
    {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %Nat.add_comm(c, b) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, b)) : Nat}
  {==}

# (a + b) + c = a + (c + b), as the right side above needs it.
law Nat.add_mid_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(c, b)) : Nat}

def Nat.add_mid_swap(a, b, c):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add_assoc(a, b, c)) :
    {_ == Nat.add(a, Nat.add(c, b)) : Nat}
  %Nat.add_comm(c, b) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, b)) : Nat}
  {==}

def Nat.add_split(a, x, b, y, c):
  # left: ((a + 2x) + (b + 2y)) + c = ((a + b) + c) + 2(x + y)
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.bit(a), Nat.double(x)), Nat.add(Nat.bit(b), Nat.double(y))),
    Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.add(Nat.double(x), Nat.double(y))),
    Nat.add_swap_mid(Nat.bit(a), Nat.double(x), Nat.bit(b), Nat.double(y))) :
    {Nat.add(_, Nat.bit(c)) == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.add(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))))
      : Nat}
  %Nat.double_distr(x, y) :
    {Nat.add(Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), _), Nat.bit(c))
      == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.add(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))))
      : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.double(Nat.add(x, y))), Nat.bit(c)),
    Nat.add(Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.bit(c)), Nat.double(Nat.add(x, y))),
    Nat.add_tail_swap(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.double(Nat.add(x, y)), Nat.bit(c))) :
    {_ == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.add(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))))
      : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.bit(a), Nat.bit(b)), Nat.bit(c)),
    Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))),
    Nat.full_add3(a, b, c)) :
    {Nat.add(_, Nat.double(Nat.add(x, y)))
      == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.add(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))))
      : Nat}
  # right: s + 2((x + y) + k) = (s + 2k) + 2(x + y)
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))),
    Nat.add(Nat.double(Nat.add(x, y)), Nat.double(Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))),
    Nat.double_distr(Nat.add(x, y), Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))) :
    {Nat.add(Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
      Nat.double(Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c))))), Nat.double(Nat.add(x, y)))
      == Nat.add(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))), _) : Nat}
  Nat.add_mid_swap(Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a, b, c))),
    Nat.double(Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a, b, c)))), Nat.double(Nat.add(x, y)))

law Pair.eta_bool:
  for p: Bool & Bool
  {p == (Pair.fst(Bool, Bool, p), Pair.snd(Bool, Bool, p)) : Bool & Bool}

def Pair.eta_bool(p):
  match p:
    case Tuple{a, b}:
      {==}

law Nat.odd_add_double:
  for +x: Nat
  for +m: Nat
  {Nat.odd(Nat.add(x, Nat.double(m))) == Nat.odd(x) : Bool}

def Nat.odd_add_double(x, m):
  match x:
    case 0n:
      Nat.odd_double(m)
    case 1n+q:
      %Equal.sym(Bool, Nat.odd(Nat.add(q, Nat.double(m))), Nat.odd(q),
        Nat.odd_add_double(q, m)) :
        {Bool.not(_) == Bool.not(Nat.odd(q)) : Bool}
      {==}

law Nat.half_add_double:
  for +x: Nat
  for +m: Nat
  {Nat.half(Nat.add(x, Nat.double(m))) == Nat.add(Nat.half(x), m) : Nat}

def Nat.half_add_double(x, m):
  match x:
    case 0n:
      Nat.half_double(m)
    case 1n+q:
      match q:
        case 0n:
          Nat.half_double1(m)
        case 1n+r:
          %Equal.sym(Nat, Nat.half(Nat.add(r, Nat.double(m))), Nat.add(Nat.half(r), m),
            Nat.half_add_double(r, m)) :
            {1n+_ == 1n+Nat.add(Nat.half(r), m) : Nat}
          {==}

# x + 1 = 1 + x.
law Nat.add_one:
  for +x: Nat
  {Nat.add(x, 1n) == 1n+x : Nat}

def Nat.add_one(x):
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), Nat.add_succ_r(x, 0n)) :
    {_ == 1n+x : Nat}
  %Equal.sym(Nat, Nat.add(x, 0n), x, Nat.add_zero_r(x)) : {1n+_ == 1n+x : Nat}
  {==}

# ((a + b) + x) + 1 = a + ((x + b) + 1).
law Nat.rearr_sub:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  {Nat.add(Nat.add(Nat.add(a, b), x), 1n) == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}

def Nat.rearr_sub(a, b, x):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), x), Nat.add(a, Nat.add(b, x)), Nat.add_assoc(a, b, x)) :
    {Nat.add(_, 1n) == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, Nat.add(b, x)), 1n), Nat.add(a, Nat.add(Nat.add(b, x), 1n)),
    Nat.add_assoc(a, Nat.add(b, x), 1n)) :
    {_ == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}
  %Nat.add_comm(x, b) :
    {Nat.add(a, Nat.add(_, 1n)) == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}
  {==}

# ((a + x) + 1) + b = a + ((x + b) + 1).
law Nat.rearr_add:
  for +a: Nat
  for +x: Nat
  for +b: Nat
  {Nat.add(Nat.add(Nat.add(a, x), 1n), b) == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}

def Nat.rearr_add(a, x, b):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(a, x), 1n), b), Nat.add(Nat.add(Nat.add(a, x), b), 1n),
    Nat.add_tail_swap(Nat.add(a, x), 1n, b)) :
    {_ == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, x), b), Nat.add(a, Nat.add(x, b)), Nat.add_assoc(a, x, b)) :
    {Nat.add(_, 1n) == Nat.add(a, Nat.add(Nat.add(x, b), 1n)) : Nat}
  Nat.add_assoc(a, Nat.add(x, b), 1n)

# Nat: comparing split numbers
# ============================

# Comparing a + 2x with b + 2y: x against y decides, then a against b.
law Nat.cmp_split:
  for +a: Bool
  for +x: Nat
  for +b: Bool
  for +y: Nat
  {Nat.cmp(Nat.add(Nat.bit(a), Nat.double(x)), Nat.add(Nat.bit(b), Nat.double(y)))
    == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}

def Nat.cmp_split(a, x, b, y):
  match a x b y:
    case False{} 0n False{} 0n:
      {==}
    case False{} 0n False{} 1n+q:
      {==}
    case False{} 1n+p False{} 0n:
      {==}
    case False{} 1n+p False{} 1n+q:
      Nat.cmp_split(False{}, p, False{}, q)
    case False{} 0n True{} 0n:
      {==}
    case False{} 0n True{} 1n+q:
      {==}
    case False{} 1n+p True{} 0n:
      {==}
    case False{} 1n+p True{} 1n+q:
      Nat.cmp_split(False{}, p, True{}, q)
    case True{} 0n False{} 0n:
      {==}
    case True{} 0n False{} 1n+q:
      {==}
    case True{} 1n+p False{} 0n:
      {==}
    case True{} 1n+p False{} 1n+q:
      Nat.cmp_split(True{}, p, False{}, q)
    case True{} 0n True{} 0n:
      {==}
    case True{} 0n True{} 1n+q:
      {==}
    case True{} 1n+p True{} 0n:
      {==}
    case True{} 1n+p True{} 1n+q:
      Nat.cmp_split(True{}, p, True{}, q)

law Nat.cmp_eq:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {a == b : Nat}

# A Cmp that is not EQ is not EQ.
def Cmp.not_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case LT{}:
      Unit
    case GT{}:
      Unit

law Cmp.lt_eq:
  for -A: Type
  for +e: {LT{} == EQ{} : Cmp}
  A

def Cmp.lt_eq(A, e):
  Empty.absurd(A, (%e : Cmp.not_eq(_)
    Unit{}))

law Cmp.gt_eq:
  for -A: Type
  for +e: {GT{} == EQ{} : Cmp}
  A

def Cmp.gt_eq(A, e):
  Empty.absurd(A, (%e : Cmp.not_eq(_)
    Unit{}))

def Nat.cmp_eq(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Cmp.lt_eq({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      Cmp.gt_eq({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %Nat.cmp_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# x + P = a + b with b < P gives x < a.
law Nat.lt_of_sum:
  for +x: Nat
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for +e: {Nat.add(x, p) == Nat.add(a, b) : Nat}
  for +h: {Nat.cmp(b, p) == LT{} : Cmp}
  {Nat.cmp(x, a) == LT{} : Cmp}

# Adding the same on the right keeps the order.
law Nat.cmp_add_rr:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.cmp(Nat.add(a, c), Nat.add(b, c)) == Nat.cmp(a, b) : Cmp}

def Nat.cmp_add_rr(a, b, c):
  %Nat.add_comm(c, a) : {Nat.cmp(_, Nat.add(b, c)) == Nat.cmp(a, b) : Cmp}
  %Nat.add_comm(c, b) : {Nat.cmp(Nat.add(c, a), _) == Nat.cmp(a, b) : Cmp}
  Nat.cmp_add_l(c, a, b)

def Nat.lt_of_sum(x, p, a, b, e, h):
  %Nat.cmp_add_rr(x, a, p) : {_ == LT{} : Cmp}
  %Equal.sym(Nat, Nat.add(x, p), Nat.add(a, b), e) : {Nat.cmp(_, Nat.add(a, p)) == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), Nat.add(a, p)), Nat.cmp(b, p),
    Nat.cmp_add_l(a, b, p)) : {_ == LT{} : Cmp}
  h

# A split number stays below 2P when its half is below P.
law Nat.split_lt:
  for +b: Bool
  for +t: Nat
  for +p: Nat
  for +h: {Nat.cmp(t, p) == LT{} : Cmp}
  {Nat.cmp(Nat.add(Nat.bit(b), Nat.double(t)), Nat.double(p)) == LT{} : Cmp}

def Nat.split_lt(b, t, p, h):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.bit(b), Nat.double(t)), Nat.add(Nat.bit(False{}), Nat.double(p))),
    Word.cmp.fin(b, False{}, Nat.cmp(t, p)), Nat.cmp_split(b, t, False{}, p)) :
    {_ == LT{} : Cmp}
  %Equal.sym(Cmp, Nat.cmp(t, p), LT{}, h) : {Word.cmp.fin(b, False{}, _) == LT{} : Cmp}
  {==}

law Cmp.eq_lt:
  for -A: Type
  for +e: {EQ{} == LT{} : Cmp}
  A

law Cmp.gt_lt:
  for -A: Type
  for +e: {GT{} == LT{} : Cmp}
  A

def Cmp.not_lt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

def Cmp.eq_lt(A, e):
  Empty.absurd(A, (%e : Cmp.not_lt(_)
    Unit{}))

def Cmp.gt_lt(A, e):
  Empty.absurd(A, (%e : Cmp.not_lt(_)
    Unit{}))

law Nat.lt_succ_l:
  for +m: Nat
  for +c: Nat
  for +h: {Nat.cmp(1n+m, c) == LT{} : Cmp}
  {Nat.cmp(m, c) == LT{} : Cmp}

def Nat.lt_succ_l(m, c, h):
  match m c:
    case 0n 0n:
      Cmp.gt_lt({Nat.cmp(0n, 0n) == LT{} : Cmp}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Cmp.gt_lt({Nat.cmp(1n+p, 0n) == LT{} : Cmp}, h)
    case 1n+p 1n+q:
      Nat.lt_succ_l(p, q, h)

# A split number below 2P has its half below P.
law Nat.split_lt_half:
  for +b: Bool
  for +t: Nat
  for +p: Nat
  for +h: {Nat.cmp(Nat.add(Nat.bit(b), Nat.double(t)), Nat.double(p)) == LT{} : Cmp}
  {Nat.cmp(t, p) == LT{} : Cmp}

law Nat.split_lt_half.go:
  for +b: Bool
  for +t: Nat
  for +p: Nat
  for +c: Cmp
  for +e: {Nat.cmp(t, p) == c : Cmp}
  for +h: {Word.cmp.fin(b, False{}, Nat.cmp(t, p)) == LT{} : Cmp}
  {Nat.cmp(t, p) == LT{} : Cmp}

def Nat.split_lt_half.go(b, t, p, c, e, h):
  match b c:
    case False{} LT{}:
      e
    case False{} EQ{}:
      Cmp.eq_lt({Nat.cmp(t, p) == LT{} : Cmp},
        (%e : {Word.cmp.fin(False{}, False{}, _) == LT{} : Cmp}
          h))
    case False{} GT{}:
      Cmp.gt_lt({Nat.cmp(t, p) == LT{} : Cmp},
        (%e : {Word.cmp.fin(False{}, False{}, _) == LT{} : Cmp}
          h))
    case True{} LT{}:
      e
    case True{} EQ{}:
      Cmp.gt_lt({Nat.cmp(t, p) == LT{} : Cmp},
        (%e : {Word.cmp.fin(True{}, False{}, _) == LT{} : Cmp}
          h))
    case True{} GT{}:
      Cmp.gt_lt({Nat.cmp(t, p) == LT{} : Cmp},
        (%e : {Word.cmp.fin(True{}, False{}, _) == LT{} : Cmp}
          h))

# A split number below 1 is 0 with a clear low bit.
law Nat.split_lt_one:
  for +b: Bool
  for +t: Nat
  for +h: {Nat.cmp(Nat.add(Nat.bit(b), Nat.double(t)), 1n) == LT{} : Cmp}
  {b == False{} : Bool}

def Nat.split_lt_one(b, t, h):
  match b t:
    case False{} _:
      {==}
    case True{} 0n:
      Cmp.eq_lt({True{} == False{} : Bool}, h)
    case True{} 1n+q:
      Cmp.gt_lt({True{} == False{} : Bool}, h)

law Nat.split_lt_one_t:
  for +b: Bool
  for +t: Nat
  for +h: {Nat.cmp(Nat.add(Nat.bit(b), Nat.double(t)), 1n) == LT{} : Cmp}
  {Nat.cmp(t, 1n) == LT{} : Cmp}

def Nat.split_lt_one_t(b, t, h):
  match b t:
    case False{} 0n:
      {==}
    case False{} 1n+q:
      Cmp.gt_lt({Nat.cmp(1n+q, 1n) == LT{} : Cmp}, h)
    case True{} 0n:
      {==}
    case True{} 1n+q:
      Cmp.gt_lt({Nat.cmp(1n+q, 1n) == LT{} : Cmp}, h)

def Nat.split_lt_half(b, t, p, h):
  Nat.split_lt_half.go(b, t, p, Nat.cmp(t, p), {==},
    (%Nat.cmp_split(b, t, False{}, p) : {_ == LT{} : Cmp}
      h))

law Nat.le_zero:
  for +k: Nat
  {Cmp.is_le(Nat.cmp(0n, k)) == True{} : Bool}

def Nat.le_zero(k):
  match k:
    case 0n:
      {==}
    case 1n+q:
      {==}

law Nat.pow2_pos:
  for +p: Nat
  {Nat.cmp(0n, Nat.pow2(p)) == LT{} : Cmp}

law Nat.pos_double:
  for +x: Nat
  for +h: {Nat.cmp(0n, x) == LT{} : Cmp}
  {Nat.cmp(0n, Nat.double(x)) == LT{} : Cmp}

def Nat.pos_double(x, h):
  match x:
    case 0n:
      h
    case 1n+q:
      {==}

def Nat.pow2_pos(p):
  match p:
    case 0n:
      {==}
    case 1n+q:
      Nat.pos_double(Nat.pow2(q), Nat.pow2_pos(q))

law Nat.lt_double:
  for +x: Nat
  for +h: {Nat.cmp(0n, x) == LT{} : Cmp}
  {Nat.cmp(x, Nat.double(x)) == LT{} : Cmp}

# 1 + q < 2 + 2q.
law Nat.lt_double.go:
  for +q: Nat
  {Nat.cmp(q, 1n+Nat.double(q)) == LT{} : Cmp}

def Nat.lt_double.go(q):
  match q:
    case 0n:
      {==}
    case 1n+r:
      Nat.lt_succ_l(r, 2n+Nat.double(r), Nat.lt_double.go(r))

def Nat.lt_double(x, h):
  match x:
    case 0n:
      h
    case 1n+q:
      Nat.lt_double.go(q)

# a < 1 + b gives a <= b.
law Nat.lt_succ_le:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(a, 1n+b) == LT{} : Cmp}
  {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}

# Nothing is below 0.
law Nat.lt_zero:
  for -A: Type
  for +p: Nat
  for +h: {Nat.cmp(p, 0n) == LT{} : Cmp}
  A

def Nat.lt_zero(A, p, h):
  match p:
    case 0n:
      Cmp.eq_lt(A, h)
    case 1n+q:
      Cmp.gt_lt(A, h)

def Nat.lt_succ_le(a, b, h):
  match a b:
    case 0n _:
      Nat.le_zero(b)
    case 1n+p 0n:
      Nat.lt_zero({Cmp.is_le(Nat.cmp(1n+p, 0n)) == True{} : Bool}, p, h)
    case 1n+p 1n+q:
      Nat.lt_succ_le(p, q, h)

law Nat.lt_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h1: {Nat.cmp(a, b) == LT{} : Cmp}
  for +h2: {Cmp.is_le(Nat.cmp(b, c)) == True{} : Bool}
  {Nat.cmp(a, c) == LT{} : Cmp}

def Nat.lt_le_trans(a, b, c, h1, h2):
  match a b c:
    case _ 0n _:
      Nat.lt_zero({Nat.cmp(a, c) == LT{} : Cmp}, a, h1)
    case _ 1n+q 0n:
      Bool.false_true({Nat.cmp(a, 0n) == LT{} : Cmp}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      Nat.lt_le_trans(p, q, r, h1, h2)

law Nat.le_succ_l:
  for +p: Nat
  for +c: Nat
  for +h: {Cmp.is_le(Nat.cmp(1n+p, c)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(p, c)) == True{} : Bool}

def Nat.le_succ_l(p, c, h):
  match p c:
    case 0n _:
      Nat.le_zero(c)
    case 1n+q 0n:
      Bool.false_true({Cmp.is_le(Nat.cmp(1n+q, 0n)) == True{} : Bool}, h)
    case 1n+q 1n+r:
      Nat.le_succ_l(q, r, h)

law Bool.true_false:
  for -A: Type
  for e: {True{} == False{} : Bool}
  A

def Bool.true_false(A, e):
  Bool.false_true(A, Equal.sym(Bool, True{}, False{}, e))

law Cmp.is_lt_lt:
  for +c: Cmp
  for +h: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}

def Cmp.is_lt_lt(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Bool.false_true({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      Bool.false_true({GT{} == LT{} : Cmp}, h)

# b + 2x + 1 = 2y forces b and x + 1 = y.
law Nat.ones_step_b:
  for +b: Bool
  for +x: Nat
  for +y: Nat
  for +e: {Nat.add(Nat.add(Nat.bit(b), Nat.double(x)), 1n) == Nat.double(y) : Nat}
  {b == True{} : Bool}

def Nat.ones_step_b(b, x, y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Bool.true_false({False{} == True{} : Bool},
        (%Nat.odd_double(x) : {Bool.not(_) == False{} : Bool}
          (%Nat.add_one(Nat.double(x)) : {Nat.odd(_) == False{} : Bool}
            (%Equal.sym(Nat, Nat.add(Nat.double(x), 1n), Nat.double(y), e) :
              {Nat.odd(_) == False{} : Bool}
              Nat.odd_double(y)))))

law Nat.ones_step_x:
  for +x: Nat
  for +y: Nat
  for +e: {Nat.add(Nat.add(1n, Nat.double(x)), 1n) == Nat.double(y) : Nat}
  {Nat.add(x, 1n) == y : Nat}

def Nat.ones_step_x(x, y, e):
  %Nat.half_double(y) : {Nat.add(x, 1n) == _ : Nat}
  %e : {Nat.add(x, 1n) == Nat.half(_) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.double(x)), 1n), 1n+Nat.add(1n, Nat.double(x)),
    Nat.add_one(Nat.add(1n, Nat.double(x)))) : {Nat.add(x, 1n) == Nat.half(_) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, Nat.add_one(x)) :
    {_ == Nat.half(2n+Nat.double(x)) : Nat}
  %Equal.sym(Nat, Nat.half(Nat.double(x)), x, Nat.half_double(x)) :
    {1n+x == 1n+_ : Nat}
  {==}

law Nat.lt_of_succ_eq:
  for +x: Nat
  for +y: Nat
  for +e: {Nat.add(x, 1n) == y : Nat}
  {Nat.cmp(x, y) == LT{} : Cmp}

def Nat.lt_of_succ_eq(x, y, e):
  %e : {Nat.cmp(x, _) == LT{} : Cmp}
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, Nat.add_one(x)) : {Nat.cmp(x, _) == LT{} : Cmp}
  Nat.cmp_succ(x)

law Nat.one_le:
  for +x: Nat
  for +h: {Nat.cmp(0n, x) == LT{} : Cmp}
  {Cmp.is_le(Nat.cmp(1n, x)) == True{} : Bool}

def Nat.one_le(x, h):
  match x:
    case 0n:
      Cmp.eq_lt({Cmp.is_le(Nat.cmp(1n, 0n)) == True{} : Bool}, h)
    case 1n+y:
      Nat.le_zero(y)

law Nat.lt_to_le:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(a, b) == LT{} : Cmp}
  {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}

def Nat.lt_to_le(a, b, h):
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, h) : {Cmp.is_le(_) == True{} : Bool}
  {==}

law Nat.le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(b, c)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(a, c)) == True{} : Bool}

def Nat.le_trans(a, b, c, h1, h2):
  match a b c:
    case 0n _ _:
      Nat.le_zero(c)
    case 1n+p 0n _:
      Bool.false_true({Cmp.is_le(Nat.cmp(1n+p, c)) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      Bool.false_true({Cmp.is_le(Nat.cmp(1n+p, 0n)) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      Nat.le_trans(p, q, r, h1, h2)

# k + c < d + c when k < d.
law Nat.add_lt_r:
  for +k: Nat
  for +d: Nat
  for +c: Nat
  for +h: {Nat.cmp(k, d) == LT{} : Cmp}
  {Nat.cmp(Nat.add(k, c), Nat.add(d, c)) == LT{} : Cmp}

def Nat.add_lt_r(k, d, c, h):
  %Equal.sym(Cmp, Nat.cmp(Nat.add(k, c), Nat.add(d, c)), Nat.cmp(k, d), Nat.cmp_add_rr(k, d, c)) :
    {_ == LT{} : Cmp}
  h

# d <= k + d.
law Nat.le_add_l:
  for +k: Nat
  for +d: Nat
  {Cmp.is_le(Nat.cmp(d, Nat.add(k, d))) == True{} : Bool}

def Nat.le_add_l(k, d):
  %Nat.add_comm(d, k) : {Cmp.is_le(Nat.cmp(d, _)) == True{} : Bool}
  Nat.cmp_add_r(d, k)

# k < 8 and x <= 24 give k + x < 32.
law Nat.lt32:
  for +k: Nat
  for +x: Nat
  for +hk: {Nat.cmp(k, 8n) == LT{} : Cmp}
  for +hx: {Cmp.is_le(Nat.cmp(x, 24n)) == True{} : Bool}
  {Nat.cmp(Nat.add(k, x), 32n) == LT{} : Cmp}

def Nat.lt32(k, x, hk, hx):
  Nat.lt_le_trans(Nat.add(k, x), Nat.add(8n, x), 32n, Nat.add_lt_r(k, 8n, x, hk),
    (%Equal.sym(Cmp, Nat.cmp(Nat.add(8n, x), Nat.add(8n, 24n)), Nat.cmp(x, 24n), Nat.cmp_add_l(8n, x, 24n)) :
      {Cmp.is_le(_) == True{} : Bool}
      hx))

# A Cmp that is not LT means the other way round is at most.
law Nat.not_lt_le:
  for +a: Nat
  for +b: Nat
  for +c: Cmp
  for +e: {Nat.cmp(a, b) == c : Cmp}
  for +h: {Cmp.is_lt(c) == False{} : Bool}
  {Cmp.is_le(Nat.cmp(b, a)) == True{} : Bool}

def Nat.not_lt_le(a, b, c, e, h):
  match c:
    case LT{}:
      Bool.true_false({Cmp.is_le(Nat.cmp(b, a)) == True{} : Bool}, h)
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(b, a), Cmp.flip(Nat.cmp(a, b)), Nat.cmp_swap(a, b)) :
        {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(a, b), EQ{}, e) : {Cmp.is_le(Cmp.flip(_)) == True{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(b, a), Cmp.flip(Nat.cmp(a, b)), Nat.cmp_swap(a, b)) :
        {Cmp.is_le(_) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(a, b), GT{}, e) : {Cmp.is_le(Cmp.flip(_)) == True{} : Bool}
      {==}

law Nat.le_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Nat.cmp(b, c) == LT{} : Cmp}
  {Nat.cmp(a, c) == LT{} : Cmp}

def Nat.le_lt_trans(a, b, c, h1, h2):
  match a b c:
    case _ _ 0n:
      Nat.lt_zero({Nat.cmp(a, 0n) == LT{} : Cmp}, b, h2)
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      Bool.false_true({Nat.cmp(1n+p, 1n+r) == LT{} : Cmp}, h1)
    case 1n+p 1n+q 1n+r:
      Nat.le_lt_trans(p, q, r, h1, h2)

# Halving keeps order.
law Nat.half_mono:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.half(a), Nat.half(b))) == True{} : Bool}

def Nat.half_mono(a, b, h):
  match a b:
    case 0n _:
      Nat.le_zero(Nat.half(b))
    case 1n+p 0n:
      Bool.false_true({Cmp.is_le(Nat.cmp(Nat.half(1n+p), Nat.half(0n))) == True{} : Bool}, h)
    case 1n 1n+q:
      Nat.le_zero(Nat.half(1n+q))
    case 2n+x 1n:
      Bool.false_true({Cmp.is_le(Nat.cmp(Nat.half(2n+x), Nat.half(1n))) == True{} : Bool}, h)
    case 2n+x 2n+y:
      Nat.half_mono(x, y, h)

law Nat.lt_le_succ:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(a, b) == LT{} : Cmp}
  {Cmp.is_le(Nat.cmp(1n+a, b)) == True{} : Bool}

def Nat.lt_le_succ(a, b, h):
  match a b:
    case _ 0n:
      Nat.lt_zero({Cmp.is_le(Nat.cmp(1n+a, 0n)) == True{} : Bool}, a, h)
    case 0n 1n+q:
      Nat.le_zero(q)
    case 1n+p 1n+q:
      Nat.lt_le_succ(p, q, h)

law Bool.and_idem_r:
  for +x: Bool
  for +y: Bool
  {Bool.and(Bool.and(x, y), y) == Bool.and(x, y) : Bool}

def Bool.and_idem_r(x, y):
  match x y:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# x < 2y gives x / 2 < y.
law Nat.half_lt:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.cmp(x, Nat.double(y)) == LT{} : Cmp}
  {Nat.cmp(Nat.half(x), y) == LT{} : Cmp}

def Nat.half_lt(x, y, h):
  Nat.split_lt_half(Nat.odd(x), Nat.half(x), y,
    (%Nat.split(x) : {Nat.cmp(_, Nat.double(y)) == LT{} : Cmp}
      h))

# a <= b gives a < 1 + b.
law Nat.le_lt_succ:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Nat.cmp(a, 1n+b) == LT{} : Cmp}

def Nat.le_lt_succ(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.false_true({Nat.cmp(1n+p, 1n) == LT{} : Cmp}, h)
    case 1n+p 1n+q:
      Nat.le_lt_succ(p, q, h)

# a + (1 + b) <= c gives a < c.
law Nat.lt_of_add_succ:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(a, 1n+b), c)) == True{} : Bool}
  {Nat.cmp(a, c) == LT{} : Cmp}

def Nat.lt_of_add_succ(a, b, c, h):
  Nat.lt_le_trans(a, Nat.add(a, 1n+b), c,
    (%Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Nat.add_succ_r(a, b)) :
        {Nat.cmp(a, _) == LT{} : Cmp}
      Nat.le_lt_succ(a, Nat.add(a, b), Nat.cmp_add_r(a, b))),
    h)

def Nat.pred(+n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law Nat.succ_inj:
  for +x: Nat
  for +y: Nat
  for +e: {1n+x == 1n+y : Nat}
  {x == y : Nat}

def Nat.succ_inj(x, y, e):
  %Equal.sym(Nat, 1n+x, 1n+y, e) : {Nat.pred(_) == y : Nat}
  {==}

law Nat.add_cancel_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for +e: {Nat.add(c, a) == Nat.add(c, b) : Nat}
  {a == b : Nat}

def Nat.add_cancel_l(c, a, b, e):
  match c:
    case 0n:
      e
    case 1n+k:
      Nat.add_cancel_l(k, a, b, Nat.succ_inj(Nat.add(k, a), Nat.add(k, b), e))

law Nat.add_cancel_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}
  {a == b : Nat}

def Nat.add_cancel_r(a, b, c, e):
  Nat.add_cancel_l(c, a, b,
    (%Nat.add_comm(a, c) : {_ == Nat.add(c, b) : Nat}
      (%Nat.add_comm(b, c) : {Nat.add(a, c) == _ : Nat}
        e)))

# a < 1 + (c + a).
law Nat.lt_succ_add:
  for +a: Nat
  for +c: Nat
  {Nat.cmp(a, 1n+Nat.add(c, a)) == LT{} : Cmp}

def Nat.lt_succ_add(a, c):
  Nat.le_lt_succ(a, Nat.add(c, a), Nat.le_add_l(c, a))

law Nat.lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h1: {Nat.cmp(a, b) == LT{} : Cmp}
  for +h2: {Nat.cmp(b, c) == LT{} : Cmp}
  {Nat.cmp(a, c) == LT{} : Cmp}

def Nat.lt_trans(a, b, c, h1, h2):
  Nat.lt_le_trans(a, b, c, h1, Nat.lt_to_le(b, c, h2))

law Nat.double_mono:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(a), Nat.double(b))) == True{} : Bool}

def Nat.double_mono(a, b, h):
  match a b:
    case 0n _:
      Nat.le_zero(Nat.double(b))
    case 1n+p 0n:
      Bool.false_true({Cmp.is_le(Nat.cmp(Nat.double(1n+p), 0n)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      Nat.double_mono(p, q, h)

# a < c and b < c give a + b < c + c.
law Nat.add_lt2:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ha: {Nat.cmp(a, c) == LT{} : Cmp}
  for +hb: {Nat.cmp(b, c) == LT{} : Cmp}
  {Nat.cmp(Nat.add(a, b), Nat.add(c, c)) == LT{} : Cmp}

def Nat.add_lt2(a, b, c, ha, hb):
  Nat.le_lt_trans(Nat.add(a, b), Nat.add(a, c), Nat.add(c, c),
    Nat.lt_to_le(Nat.add(a, b), Nat.add(a, c),
      (%Equal.sym(Cmp, Nat.cmp(Nat.add(a, b), Nat.add(a, c)), Nat.cmp(b, c), Nat.cmp_add_l(a, b, c)) :
          {_ == LT{} : Cmp}
        hb)),
    Nat.add_lt_r(a, c, c, ha))

# x <= 4 * ((x + 3) / 4).
law Nat.le_words:
  for +x: Nat
  {Cmp.is_le(Nat.cmp(x, Nat.double(Nat.double(Nat.half(Nat.half(Nat.add(x, 3n))))))) == True{} : Bool}

def Nat.le_words(x):
  match x:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+y:
      Nat.le_words(y)

law Cmp.ge_flip:
  for +c: Cmp
  {Cmp.is_ge(Cmp.flip(c)) == Cmp.is_le(c) : Bool}

def Cmp.ge_flip(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}
