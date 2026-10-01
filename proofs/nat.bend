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
  for e: {Bool.and(a, b) == True{} : Bool}
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
  for e: {Bool.and(a, b) == True{} : Bool}
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
  for e: {False{} == True{} : Bool}
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
  for e: {Nat.cmp(a, b) == EQ{} : Cmp}
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
  for e: {LT{} == EQ{} : Cmp}
  A

def Cmp.lt_eq(A, e):
  Empty.absurd(A, (%e : Cmp.not_eq(_)
    Unit{}))

law Cmp.gt_eq:
  for -A: Type
  for e: {GT{} == EQ{} : Cmp}
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
