import Base
import ./nat.bend as P

# Lemmas about Word(n), the bits under U32, for every width n.
#
# W.fn(n, x) is the word of the low n bits of x. Words add as their values
# do (W.adc_fn), and every word is W.fn of its value (W.fn_N), so U32
# arithmetic follows from Nat arithmetic. The statements never name 2^32:
# the checker writes Nat literals in unary.

# The word of the low n bits of x.
def W.fn(n: Nat, +x: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{P.Nat.odd(x), W.fn(p, P.Nat.half(x))}

law W.fn_N:
  for +n: Nat
  for +w: Word(n)
  {W.fn(n, Word.to_nat(n, w)) == w : Word(n)}

def W.fn_N(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Bool, P.Nat.odd(Nat.double(Word.to_nat(p, t))), False{},
            P.Nat.odd_double(Word.to_nat(p, t))) :
            {WCon{_, W.fn(p, P.Nat.half(Nat.double(Word.to_nat(p, t))))}
              == WCon{False{}, t} : Word(1n+p)}
          %Equal.sym(Nat, P.Nat.half(Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t),
            P.Nat.half_double(Word.to_nat(p, t))) :
            {WCon{False{}, W.fn(p, _)} == WCon{False{}, t} : Word(1n+p)}
          %Equal.sym(Word(p), W.fn(p, Word.to_nat(p, t)), t, W.fn_N(p, t)) :
            {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Bool, P.Nat.odd(Nat.double(Word.to_nat(p, t))), False{},
            P.Nat.odd_double(Word.to_nat(p, t))) :
            {WCon{Bool.not(_), W.fn(p, P.Nat.half(1n+Nat.double(Word.to_nat(p, t))))}
              == WCon{True{}, t} : Word(1n+p)}
          %Equal.sym(Nat, P.Nat.half(1n+Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t),
            P.Nat.half_double1(Word.to_nat(p, t))) :
            {WCon{True{}, W.fn(p, _)} == WCon{True{}, t} : Word(1n+p)}
          %Equal.sym(Word(p), W.fn(p, Word.to_nat(p, t)), t, W.fn_N(p, t)) :
            {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

# Shorthands for the step of W.adc_fn.
def W.fa(+x: Nat, +y: Nat, +c: Bool) -> Bool & Bool:
  Bool.full_add(P.Nat.odd(x), P.Nat.odd(y), c)

def W.fa.s(+x: Nat, +y: Nat, +c: Bool) -> Bool:
  Pair.fst(Bool, Bool, W.fa(x, y, c))

def W.fa.k(+x: Nat, +y: Nat, +c: Bool) -> Bool:
  Pair.snd(Bool, Bool, W.fa(x, y, c))

# The sum's half: the halves' sum and the carry.
def W.fa.m(+x: Nat, +y: Nat, +c: Bool) -> Nat:
  Nat.add(Nat.add(P.Nat.half(x), P.Nat.half(y)), P.Nat.bit(W.fa.k(x, y, c)))

def W.sum(+x: Nat, +y: Nat, +c: Bool) -> Nat:
  Nat.add(Nat.add(x, y), P.Nat.bit(c))

# The sum, split into its low bit and its half.
law W.sum_split:
  for +x: Nat
  for +y: Nat
  for +c: Bool
  {W.sum(x, y, c) == Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c))) : Nat}

def W.sum_split(x, y, c):
  %Equal.sym(Nat, x, Nat.add(P.Nat.bit(P.Nat.odd(x)), Nat.double(P.Nat.half(x))),
    P.Nat.split(x)) :
    {Nat.add(Nat.add(_, y), P.Nat.bit(c))
      == Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c))) : Nat}
  %Equal.sym(Nat, y, Nat.add(P.Nat.bit(P.Nat.odd(y)), Nat.double(P.Nat.half(y))),
    P.Nat.split(y)) :
    {Nat.add(Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(x)), Nat.double(P.Nat.half(x))), _),
      P.Nat.bit(c))
      == Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c))) : Nat}
  P.Nat.add_split(P.Nat.odd(x), P.Nat.half(x), P.Nat.odd(y), P.Nat.half(y), c)

# Words add as their values do.
law W.adc_fn:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  for +c: Bool
  {Word.adc(n, W.fn(n, x), W.fn(n, y), False{}, c) == W.fn(n, W.sum(x, y, c)) : Word(n)}

def W.adc_fn(n, x, y, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, W.sum(x, y, c),
        Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c))),
        W.sum_split(x, y, c)) :
        {Word.adc(1n+p, W.fn(1n+p, x), W.fn(1n+p, y), False{}, c)
          == WCon{P.Nat.odd(_), W.fn(p, P.Nat.half(_))} : Word(1n+p)}
      %Equal.sym(Bool,
        P.Nat.odd(Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c)))),
        W.fa.s(x, y, c),
        P.Nat.odd_bit_double(W.fa.s(x, y, c), W.fa.m(x, y, c))) :
        {Word.adc(1n+p, W.fn(1n+p, x), W.fn(1n+p, y), False{}, c)
          == WCon{_, W.fn(p, P.Nat.half(Nat.add(P.Nat.bit(W.fa.s(x, y, c)),
            Nat.double(W.fa.m(x, y, c)))))} : Word(1n+p)}
      %Equal.sym(Nat,
        P.Nat.half(Nat.add(P.Nat.bit(W.fa.s(x, y, c)), Nat.double(W.fa.m(x, y, c)))),
        W.fa.m(x, y, c),
        P.Nat.half_bit_double(W.fa.s(x, y, c), W.fa.m(x, y, c))) :
        {Word.adc(1n+p, W.fn(1n+p, x), W.fn(1n+p, y), False{}, c)
          == WCon{W.fa.s(x, y, c), W.fn(p, _)} : Word(1n+p)}
      %Equal.sym(Bool & Bool, W.fa(x, y, c),
        (W.fa.s(x, y, c), W.fa.k(x, y, c)), P.Pair.eta_bool(W.fa(x, y, c))) :
        {Word.adc.con(p, W.fn(p, P.Nat.half(x)), W.fn(p, P.Nat.half(y)), False{}, _)
          == WCon{W.fa.s(x, y, c), W.fn(p, W.fa.m(x, y, c))} : Word(1n+p)}
      %Equal.sym(Word(p),
        Word.adc(p, W.fn(p, P.Nat.half(x)), W.fn(p, P.Nat.half(y)), False{}, W.fa.k(x, y, c)),
        W.fn(p, W.fa.m(x, y, c)),
        W.adc_fn(p, P.Nat.half(x), P.Nat.half(y), W.fa.k(x, y, c))) :
        {WCon{W.fa.s(x, y, c), _} == WCon{W.fa.s(x, y, c), W.fn(p, W.fa.m(x, y, c))}
          : Word(1n+p)}
      {==}

# Addition
# ========

law W.add_fn:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  {Word.add(n, W.fn(n, x), W.fn(n, y)) == W.fn(n, Nat.add(x, y)) : Word(n)}

def W.add_fn(n, x, y):
  %Equal.sym(Word(n), Word.adc(n, W.fn(n, x), W.fn(n, y), False{}, False{}),
    W.fn(n, W.sum(x, y, False{})), W.adc_fn(n, x, y, False{})) :
    {_ == W.fn(n, Nat.add(x, y)) : Word(n)}
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), 0n), Nat.add(x, y),
    P.Nat.add_zero_r(Nat.add(x, y))) :
    {W.fn(n, _) == W.fn(n, Nat.add(x, y)) : Word(n)}
  {==}

law W.add_assoc:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  {Word.add(n, Word.add(n, a, b), c) == Word.add(n, a, Word.add(n, b, c)) : Word(n)}

law W.add_assoc.fn:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Word.add(n, Word.add(n, W.fn(n, x), W.fn(n, y)), W.fn(n, z))
    == Word.add(n, W.fn(n, x), Word.add(n, W.fn(n, y), W.fn(n, z))) : Word(n)}

def W.add_assoc.fn(n, x, y, z):
  %Equal.sym(Word(n), Word.add(n, W.fn(n, x), W.fn(n, y)), W.fn(n, Nat.add(x, y)),
    W.add_fn(n, x, y)) :
    {Word.add(n, _, W.fn(n, z)) == Word.add(n, W.fn(n, x), Word.add(n, W.fn(n, y), W.fn(n, z)))
      : Word(n)}
  %Equal.sym(Word(n), Word.add(n, W.fn(n, y), W.fn(n, z)), W.fn(n, Nat.add(y, z)),
    W.add_fn(n, y, z)) :
    {Word.add(n, W.fn(n, Nat.add(x, y)), W.fn(n, z)) == Word.add(n, W.fn(n, x), _) : Word(n)}
  %Equal.sym(Word(n), Word.add(n, W.fn(n, Nat.add(x, y)), W.fn(n, z)),
    W.fn(n, Nat.add(Nat.add(x, y), z)), W.add_fn(n, Nat.add(x, y), z)) :
    {_ == Word.add(n, W.fn(n, x), W.fn(n, Nat.add(y, z))) : Word(n)}
  %Equal.sym(Word(n), Word.add(n, W.fn(n, x), W.fn(n, Nat.add(y, z))),
    W.fn(n, Nat.add(x, Nat.add(y, z))), W.add_fn(n, x, Nat.add(y, z))) :
    {W.fn(n, Nat.add(Nat.add(x, y), z)) == _ : Word(n)}
  %P.Nat.add_assoc(x, y, z) :
    {W.fn(n, Nat.add(Nat.add(x, y), z)) == W.fn(n, _) : Word(n)}
  {==}

def W.add_assoc(n, a, b, c):
  %W.fn_N(n, a) :
    {Word.add(n, Word.add(n, _, b), c) == Word.add(n, _, Word.add(n, b, c)) : Word(n)}
  %W.fn_N(n, b) :
    {Word.add(n, Word.add(n, W.fn(n, Word.to_nat(n, a)), _), c)
      == Word.add(n, W.fn(n, Word.to_nat(n, a)), Word.add(n, _, c)) : Word(n)}
  %W.fn_N(n, c) :
    {Word.add(n, Word.add(n, W.fn(n, Word.to_nat(n, a)), W.fn(n, Word.to_nat(n, b))), _)
      == Word.add(n, W.fn(n, Word.to_nat(n, a)),
        Word.add(n, W.fn(n, Word.to_nat(n, b)), _)) : Word(n)}
  W.add_assoc.fn(n, Word.to_nat(n, a), Word.to_nat(n, b), Word.to_nat(n, c))

law W.N_zero:
  for +n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}

def W.N_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %W.N_zero(p) : {Nat.double(Word.to_nat(p, Word.zero(p))) == Nat.double(_) : Nat}
      {==}

law W.add_zero:
  for +n: Nat
  for +a: Word(n)
  {Word.add(n, a, Word.zero(n)) == a : Word(n)}

def W.add_zero(n, a):
  %W.fn_N(n, a) : {Word.add(n, _, Word.zero(n)) == _ : Word(n)}
  %W.fn_N(n, Word.zero(n)) :
    {Word.add(n, W.fn(n, Word.to_nat(n, a)), _) == W.fn(n, Word.to_nat(n, a)) : Word(n)}
  %Equal.sym(Nat, Word.to_nat(n, Word.zero(n)), 0n, W.N_zero(n)) :
    {Word.add(n, W.fn(n, Word.to_nat(n, a)), W.fn(n, _)) == W.fn(n, Word.to_nat(n, a))
      : Word(n)}
  %Equal.sym(Word(n), Word.add(n, W.fn(n, Word.to_nat(n, a)), W.fn(n, 0n)),
    W.fn(n, Nat.add(Word.to_nat(n, a), 0n)), W.add_fn(n, Word.to_nat(n, a), 0n)) :
    {_ == W.fn(n, Word.to_nat(n, a)) : Word(n)}
  %P.Nat.add_zero_r(Word.to_nat(n, a)) :
    {W.fn(n, Nat.add(Word.to_nat(n, a), 0n)) == W.fn(n, _) : Word(n)}
  {==}

# Subtraction
# ===========

law W.fn_pow:
  for +n: Nat
  for +x: Nat
  {W.fn(n, Nat.add(x, P.Nat.pow2(n))) == W.fn(n, x) : Word(n)}

def W.fn_pow(n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, P.Nat.odd(Nat.add(x, Nat.double(P.Nat.pow2(p)))), P.Nat.odd(x),
        P.Nat.odd_add_double(x, P.Nat.pow2(p))) :
        {WCon{_, W.fn(p, P.Nat.half(Nat.add(x, Nat.double(P.Nat.pow2(p)))))}
          == W.fn(1n+p, x) : Word(1n+p)}
      %Equal.sym(Nat, P.Nat.half(Nat.add(x, Nat.double(P.Nat.pow2(p)))),
        Nat.add(P.Nat.half(x), P.Nat.pow2(p)),
        P.Nat.half_add_double(x, P.Nat.pow2(p))) :
        {WCon{P.Nat.odd(x), W.fn(p, _)} == W.fn(1n+p, x) : Word(1n+p)}
      %Equal.sym(Word(p), W.fn(p, Nat.add(P.Nat.half(x), P.Nat.pow2(p))),
        W.fn(p, P.Nat.half(x)), W.fn_pow(p, P.Nat.half(x))) :
        {WCon{P.Nat.odd(x), _} == W.fn(1n+p, x) : Word(1n+p)}
      {==}

# Subtraction adds the complement: a - b = a + ~b + 1.
law W.adc_flip:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Word.adc(n, a, b, True{}, c) == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}

def W.adc_flip(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %Equal.sym(Bool & Bool, Bool.full_add(ab, Bool.not(bb), c),
            (Pair.fst(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c)),
              Pair.snd(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c))),
            P.Pair.eta_bool(Bool.full_add(ab, Bool.not(bb), c))) :
            {Word.adc.con(p, at, bt, True{}, _)
              == Word.adc.con(p, at, Word.not(p, bt), False{}, _) : Word(1n+p)}
          %W.adc_flip(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c))) :
            {WCon{Pair.fst(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c)),
                Word.adc(p, at, bt, True{},
                  Pair.snd(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c)))}
              == WCon{Pair.fst(Bool, Bool, Bool.full_add(ab, Bool.not(bb), c)), _} : Word(1n+p)}
          {==}

# A word and its complement add up to all ones: ~w + w + 1 = 2^n.
law W.not_sum:
  for +n: Nat
  for +w: Word(n)
  {Nat.add(Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)), 1n)
    == P.Nat.pow2(n) : Nat}

# (1 + 2x) + 2y + 1 = 2((x + y) + 1), given that is 2 * 2^p.
law W.not_sum.step:
  for +x: Nat
  for +y: Nat
  for +q: Nat
  for +e: {Nat.add(Nat.add(x, y), 1n) == q : Nat}
  {Nat.add(Nat.add(1n+Nat.double(x), Nat.double(y)), 1n) == Nat.double(q) : Nat}

def W.not_sum.step(x, y, q, e):
  %e : {Nat.add(Nat.add(1n+Nat.double(x), Nat.double(y)), 1n) == Nat.double(_) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), 1n), 1n+Nat.add(Nat.add(x, y), 0n),
    P.Nat.add_succ_r(Nat.add(x, y), 0n)) :
    {Nat.add(Nat.add(1n+Nat.double(x), Nat.double(y)), 1n) == Nat.double(_) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), 0n), Nat.add(x, y),
    P.Nat.add_zero_r(Nat.add(x, y))) :
    {Nat.add(Nat.add(1n+Nat.double(x), Nat.double(y)), 1n) == 2n+Nat.double(_) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.double(x), Nat.double(y)), 1n),
    1n+Nat.add(Nat.add(Nat.double(x), Nat.double(y)), 0n),
    P.Nat.add_succ_r(Nat.add(Nat.double(x), Nat.double(y)), 0n)) :
    {1n+_ == 2n+Nat.double(Nat.add(x, y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.double(x), Nat.double(y)), 0n),
    Nat.add(Nat.double(x), Nat.double(y)),
    P.Nat.add_zero_r(Nat.add(Nat.double(x), Nat.double(y)))) :
    {2n+_ == 2n+Nat.double(Nat.add(x, y)) : Nat}
  %P.Nat.double_distr(x, y) :
    {2n+_ == 2n+Nat.double(Nat.add(x, y)) : Nat}
  {==}

def W.not_sum(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          W.not_sum.step(Word.to_nat(p, Word.not(p, t)), Word.to_nat(p, t), P.Nat.pow2(p),
            W.not_sum(p, t))
        case WCon{True{}, t}:
          %Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.not(p, t))),
              1n+Nat.double(Word.to_nat(p, t))),
            1n+Nat.add(Nat.double(Word.to_nat(p, Word.not(p, t))), Nat.double(Word.to_nat(p, t))),
            P.Nat.add_succ_r(Nat.double(Word.to_nat(p, Word.not(p, t))),
              Nat.double(Word.to_nat(p, t)))) :
            {Nat.add(_, 1n) == Nat.double(P.Nat.pow2(p)) : Nat}
          W.not_sum.step(Word.to_nat(p, Word.not(p, t)), Word.to_nat(p, t), P.Nat.pow2(p),
            W.not_sum(p, t))

# (a - b) + b = a.
law W.add_sub:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.add(n, Word.sub(n, a, b), b) == a : Word(n)}

law W.add_sub.fn:
  for +n: Nat
  for +x: Nat
  for +nb: Nat
  for +y: Nat
  for +e: {Nat.add(Nat.add(nb, y), 1n) == P.Nat.pow2(n) : Nat}
  {Word.add(n, Word.adc(n, W.fn(n, x), W.fn(n, nb), False{}, True{}), W.fn(n, y))
    == W.fn(n, x) : Word(n)}

def W.add_sub.fn(n, x, nb, y, e):
  %Equal.sym(Word(n), Word.adc(n, W.fn(n, x), W.fn(n, nb), False{}, True{}),
    W.fn(n, W.sum(x, nb, True{})), W.adc_fn(n, x, nb, True{})) :
    {Word.add(n, _, W.fn(n, y)) == W.fn(n, x) : Word(n)}
  %Equal.sym(Word(n), Word.add(n, W.fn(n, W.sum(x, nb, True{})), W.fn(n, y)),
    W.fn(n, Nat.add(W.sum(x, nb, True{}), y)), W.add_fn(n, W.sum(x, nb, True{}), y)) :
    {_ == W.fn(n, x) : Word(n)}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(x, nb), 1n), y), Nat.add(x, Nat.add(Nat.add(nb, y), 1n)),
    P.Nat.rearr_add(x, nb, y)) :
    {W.fn(n, _) == W.fn(n, x) : Word(n)}
  %Equal.sym(Nat, Nat.add(Nat.add(nb, y), 1n), P.Nat.pow2(n), e) :
    {W.fn(n, Nat.add(x, _)) == W.fn(n, x) : Word(n)}
  W.fn_pow(n, x)

def W.add_sub(n, a, b):
  %Equal.sym(Word(n), Word.adc(n, a, b, True{}, True{}),
    Word.adc(n, a, Word.not(n, b), False{}, True{}), W.adc_flip(n, a, b, True{})) :
    {Word.add(n, _, b) == a : Word(n)}
  %W.fn_N(n, Word.not(n, b)) :
    {Word.add(n, Word.adc(n, a, _, False{}, True{}), b) == a : Word(n)}
  %W.fn_N(n, a) :
    {Word.add(n, Word.adc(n, _, W.fn(n, Word.to_nat(n, Word.not(n, b))), False{}, True{}), b)
      == _ : Word(n)}
  %W.fn_N(n, b) :
    {Word.add(n, Word.adc(n, W.fn(n, Word.to_nat(n, a)),
      W.fn(n, Word.to_nat(n, Word.not(n, b))), False{}, True{}), _)
      == W.fn(n, Word.to_nat(n, a)) : Word(n)}
  W.add_sub.fn(n, Word.to_nat(n, a), Word.to_nat(n, Word.not(n, b)), Word.to_nat(n, b),
    W.not_sum(n, b))

# (a + b) - b = a.
law W.sub_add:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.sub(n, Word.add(n, a, b), b) == a : Word(n)}

law W.sub_add.fn:
  for +n: Nat
  for +x: Nat
  for +nb: Nat
  for +y: Nat
  for +e: {Nat.add(Nat.add(nb, y), 1n) == P.Nat.pow2(n) : Nat}
  {Word.adc(n, Word.add(n, W.fn(n, x), W.fn(n, y)), W.fn(n, nb), False{}, True{})
    == W.fn(n, x) : Word(n)}

def W.sub_add.fn(n, x, nb, y, e):
  %Equal.sym(Word(n), Word.add(n, W.fn(n, x), W.fn(n, y)), W.fn(n, Nat.add(x, y)),
    W.add_fn(n, x, y)) :
    {Word.adc(n, _, W.fn(n, nb), False{}, True{}) == W.fn(n, x) : Word(n)}
  %Equal.sym(Word(n), Word.adc(n, W.fn(n, Nat.add(x, y)), W.fn(n, nb), False{}, True{}),
    W.fn(n, W.sum(Nat.add(x, y), nb, True{})), W.adc_fn(n, Nat.add(x, y), nb, True{})) :
    {_ == W.fn(n, x) : Word(n)}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(x, y), nb), 1n), Nat.add(x, Nat.add(Nat.add(nb, y), 1n)),
    P.Nat.rearr_sub(x, y, nb)) :
    {W.fn(n, _) == W.fn(n, x) : Word(n)}
  %Equal.sym(Nat, Nat.add(Nat.add(nb, y), 1n), P.Nat.pow2(n), e) :
    {W.fn(n, Nat.add(x, _)) == W.fn(n, x) : Word(n)}
  W.fn_pow(n, x)

def W.sub_add(n, a, b):
  %Equal.sym(Word(n), Word.adc(n, Word.add(n, a, b), b, True{}, True{}),
    Word.adc(n, Word.add(n, a, b), Word.not(n, b), False{}, True{}),
    W.adc_flip(n, Word.add(n, a, b), b, True{})) :
    {_ == a : Word(n)}
  %W.fn_N(n, Word.not(n, b)) :
    {Word.adc(n, Word.add(n, a, b), _, False{}, True{}) == a : Word(n)}
  %W.fn_N(n, a) :
    {Word.adc(n, Word.add(n, _, b), W.fn(n, Word.to_nat(n, Word.not(n, b))), False{}, True{})
      == _ : Word(n)}
  %W.fn_N(n, b) :
    {Word.adc(n, Word.add(n, W.fn(n, Word.to_nat(n, a)), _),
      W.fn(n, Word.to_nat(n, Word.not(n, b))), False{}, True{})
      == W.fn(n, Word.to_nat(n, a)) : Word(n)}
  W.sub_add.fn(n, Word.to_nat(n, a), Word.to_nat(n, Word.not(n, b)), Word.to_nat(n, b),
    W.not_sum(n, b))

# Order
# =====

# Words compare as their values do.
law W.cmp_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

def W.cmp_nat(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)),
            W.cmp_nat(p, at, bt)) :
            {Word.cmp.fin(False{}, False{}, _) == Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}),
              Word.to_nat(1n+p, WCon{False{}, bt})) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(P.Nat.bit(False{}), Nat.double(Word.to_nat(p, at))),
              Nat.add(P.Nat.bit(False{}), Nat.double(Word.to_nat(p, bt)))),
            Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
            P.Nat.cmp_split(False{}, Word.to_nat(p, at), False{}, Word.to_nat(p, bt)))
        case WCon{False{}, at} WCon{True{}, bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)),
            W.cmp_nat(p, at, bt)) :
            {Word.cmp.fin(False{}, True{}, _) == Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}),
              Word.to_nat(1n+p, WCon{True{}, bt})) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(P.Nat.bit(False{}), Nat.double(Word.to_nat(p, at))),
              Nat.add(P.Nat.bit(True{}), Nat.double(Word.to_nat(p, bt)))),
            Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
            P.Nat.cmp_split(False{}, Word.to_nat(p, at), True{}, Word.to_nat(p, bt)))
        case WCon{True{}, at} WCon{False{}, bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)),
            W.cmp_nat(p, at, bt)) :
            {Word.cmp.fin(True{}, False{}, _) == Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}),
              Word.to_nat(1n+p, WCon{False{}, bt})) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(P.Nat.bit(True{}), Nat.double(Word.to_nat(p, at))),
              Nat.add(P.Nat.bit(False{}), Nat.double(Word.to_nat(p, bt)))),
            Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
            P.Nat.cmp_split(True{}, Word.to_nat(p, at), False{}, Word.to_nat(p, bt)))
        case WCon{True{}, at} WCon{True{}, bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)),
            W.cmp_nat(p, at, bt)) :
            {Word.cmp.fin(True{}, True{}, _) == Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}),
              Word.to_nat(1n+p, WCon{True{}, bt})) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(P.Nat.bit(True{}), Nat.double(Word.to_nat(p, at))),
              Nat.add(P.Nat.bit(True{}), Nat.double(Word.to_nat(p, bt)))),
            Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
            P.Nat.cmp_split(True{}, Word.to_nat(p, at), True{}, Word.to_nat(p, bt)))

# Words with the same value are the same word.
law W.eq_N:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

def W.eq_N(n, a, b, e):
  %W.fn_N(n, a) : {_ == b : Word(n)}
  %W.fn_N(n, b) : {W.fn(n, Word.to_nat(n, a)) == _ : Word(n)}
  %e : {W.fn(n, Word.to_nat(n, a)) == W.fn(n, _) : Word(n)}
  {==}

# Words that compare equal are the same word.
law W.cmp_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def W.cmp_eq(n, a, b, e):
  W.eq_N(n, a, b, P.Nat.cmp_eq(Word.to_nat(n, a), Word.to_nat(n, b),
    (%W.cmp_nat(n, a, b) : {_ == EQ{} : Cmp}
      e)))

# Carries
# =======

# The carry out of adding a, b and c.
def W.carry(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{a0, at} WCon{b0, bt}:
          W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))

# The worth of a carry out of n bits.
def W.cv(n: Nat, k: Bool) -> Nat:
  match k:
    case False{}:
      0n
    case True{}:
      P.Nat.pow2(n)

law W.cv_succ:
  for +p: Nat
  for +k: Bool
  {W.cv(1n+p, k) == Nat.double(W.cv(p, k)) : Nat}

def W.cv_succ(p, k):
  match k:
    case False{}:
      {==}
    case True{}:
      {==}

law W.N_cons:
  for +p: Nat
  for +s: Bool
  for +t: Word(p)
  {Word.to_nat(1n+p, WCon{s, t}) == Nat.add(P.Nat.bit(s), Nat.double(Word.to_nat(p, t))) : Nat}

def W.N_cons(p, s, t):
  match s:
    case False{}:
      {==}
    case True{}:
      {==}

# A sum of words, with its carry out, is the sum of their values.
law W.adc_carry:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), W.cv(n, W.carry(n, a, b, c)))
    == W.sum(Word.to_nat(n, a), Word.to_nat(n, b), c) : Nat}

law W.adc_carry.step:
  for +p: Nat
  for +a0: Bool
  for +at: Word(p)
  for +b0: Bool
  for +bt: Word(p)
  for +c: Bool
  for ih: {Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{},
      Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))),
    W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))
    == W.sum(Word.to_nat(p, at), Word.to_nat(p, bt),
      Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))) : Nat}
  {Nat.add(Word.to_nat(1n+p, Word.adc.con(p, at, bt, False{}, Bool.full_add(a0, b0, c))),
    W.cv(1n+p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))
    == W.sum(Word.to_nat(1n+p, WCon{a0, at}), Word.to_nat(1n+p, WCon{b0, bt}), c) : Nat}

def W.adc_carry.step(p, a0, at, b0, bt, c, ih):
  %Equal.sym(Bool & Bool, Bool.full_add(a0, b0, c), (Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c)), Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))), P.Pair.eta_bool(Bool.full_add(a0, b0, c))) :
    {Nat.add(Word.to_nat(1n+p, Word.adc.con(p, at, bt, False{}, _)), W.cv(1n+p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))) == W.sum(Word.to_nat(1n+p, WCon{a0, at}), Word.to_nat(1n+p, WCon{b0, bt}), c) : Nat}
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c)), Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))}),
    Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))),
    W.N_cons(p, Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c)), Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))) :
    {Nat.add(_, W.cv(1n+p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))) == W.sum(Word.to_nat(1n+p, WCon{a0, at}), Word.to_nat(1n+p, WCon{b0, bt}), c) : Nat}
  %Equal.sym(Nat, W.cv(1n+p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))), W.cv_succ(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))) :
    {Nat.add(Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))), _) == W.sum(Word.to_nat(1n+p, WCon{a0, at}), Word.to_nat(1n+p, WCon{b0, bt}), c) : Nat}
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{a0, at}), Nat.add(P.Nat.bit(a0), Nat.double(Word.to_nat(p, at))),
    W.N_cons(p, a0, at)) :
    {Nat.add(Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))))
      == W.sum(_, Word.to_nat(1n+p, WCon{b0, bt}), c) : Nat}
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b0, bt}), Nat.add(P.Nat.bit(b0), Nat.double(Word.to_nat(p, bt))),
    W.N_cons(p, b0, bt)) :
    {Nat.add(Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))))
      == W.sum(Nat.add(P.Nat.bit(a0), Nat.double(Word.to_nat(p, at))), _, c) : Nat}
  %Equal.sym(Nat, W.sum(Nat.add(P.Nat.bit(a0), Nat.double(Word.to_nat(p, at))), Nat.add(P.Nat.bit(b0), Nat.double(Word.to_nat(p, bt))), c),
    Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Nat.add(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), P.Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))),
    P.Nat.add_split(a0, Word.to_nat(p, at), b0, Word.to_nat(p, bt), c)) :
    {Nat.add(Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))),
    Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.add(Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))))),
    P.Nat.add_assoc(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))), Nat.double(W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))))) :
    {_ == Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Nat.add(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), P.Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))) : Nat}
  %P.Nat.double_distr(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))), W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))) :
    {Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), _)
      == Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Nat.add(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), P.Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))) : Nat}
  %Equal.sym(Nat, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))), W.cv(p, W.carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))), W.sum(Word.to_nat(p, at), Word.to_nat(p, bt), Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))), ih) :
    {Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(_))
      == Nat.add(P.Nat.bit(Pair.fst(Bool, Bool, Bool.full_add(a0, b0, c))), Nat.double(Nat.add(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), P.Nat.bit(Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c)))))) : Nat}
  {==}

def W.adc_carry(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{a0, at} WCon{b0, bt}:
          W.adc_carry.step(p, a0, at, b0, bt, c,
            W.adc_carry(p, at, bt, Pair.snd(Bool, Bool, Bool.full_add(a0, b0, c))))

# A word's value is below 2^n.
law W.N_lt:
  for +n: Nat
  for +w: Word(n)
  {Nat.cmp(Word.to_nat(n, w), P.Nat.pow2(n)) == LT{} : Cmp}

def W.N_lt(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(p, t))), W.N_cons(p, b, t)) :
            {Nat.cmp(_, Nat.double(P.Nat.pow2(p))) == LT{} : Cmp}
          P.Nat.split_lt(b, Word.to_nat(p, t), P.Nat.pow2(p), W.N_lt(p, t))

# A sum that does not wrap (a <= a + b) has the sum of the values.
law W.add_nowrap:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: {Cmp.is_le(Word.cmp(n, a, Word.add(n, a, b))) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law W.add_nowrap.go:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Bool
  for +e: {W.carry(n, a, b, False{}) == k : Bool}
  for +h: {Cmp.is_le(Word.cmp(n, a, Word.add(n, a, b))) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def W.add_nowrap.go(n, a, b, k, e, h):
  match k:
    case False{}:
      %P.Nat.add_zero_r(Word.to_nat(n, Word.add(n, a, b))) : {_ == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}
      %P.Nat.add_zero_r(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) :
        {Nat.add(Word.to_nat(n, Word.add(n, a, b)), 0n) == _ : Nat}
      %e : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.cv(n, _)) == W.sum(Word.to_nat(n, a), Word.to_nat(n, b), False{}) : Nat}
      W.adc_carry(n, a, b, False{})
    case True{}:
      P.Bool.false_true({Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat},
        (%P.Nat.lt_of_sum(Word.to_nat(n, Word.add(n, a, b)), P.Nat.pow2(n), Word.to_nat(n, a), Word.to_nat(n, b),
            (%P.Nat.add_zero_r(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) :
              {Nat.add(Word.to_nat(n, Word.add(n, a, b)), P.Nat.pow2(n)) == _ : Nat}
              (%e : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.cv(n, _)) == W.sum(Word.to_nat(n, a), Word.to_nat(n, b), False{}) : Nat}
                W.adc_carry(n, a, b, False{}))),
            W.N_lt(n, b)) :
          {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
          (%P.Nat.cmp_swap(Word.to_nat(n, Word.add(n, a, b)), Word.to_nat(n, a)) : {Cmp.is_le(_) == True{} : Bool}
            (%W.cmp_nat(n, a, Word.add(n, a, b)) : {Cmp.is_le(_) == True{} : Bool}
              h))))

def W.add_nowrap(n, a, b, h):
  W.add_nowrap.go(n, a, b, W.carry(n, a, b, False{}), {==}, h)

# A difference that does not wrap (b <= a): its value and b's add up to a's.
law W.sub_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: {Cmp.is_le(Word.cmp(n, b, a)) == True{} : Bool}
  {Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) == Word.to_nat(n, a) : Nat}

law W.sub_nat.go:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Bool
  for +e: {W.carry(n, Word.sub(n, a, b), b, False{}) == k : Bool}
  for +h: {Cmp.is_le(Word.cmp(n, b, a)) == True{} : Bool}
  {Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) == Word.to_nat(n, a) : Nat}

def W.sub_nat.go(n, a, b, k, e, h):
  match k:
    case False{}:
      %P.Nat.add_zero_r(Word.to_nat(n, a)) : {Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) == _ : Nat}
      %P.Nat.add_zero_r(Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b))) : {_ == Nat.add(Word.to_nat(n, a), 0n) : Nat}
      Equal.sym(Nat, Nat.add(Word.to_nat(n, a), 0n), Nat.add(Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)), 0n),
        (%e : {Nat.add(Word.to_nat(n, a), W.cv(n, _)) == W.sum(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b), False{}) : Nat}
          (%W.add_sub(n, a, b) : {Nat.add(Word.to_nat(n, _), W.cv(n, W.carry(n, Word.sub(n, a, b), b, False{}))) == W.sum(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b), False{}) : Nat}
        W.adc_carry(n, Word.sub(n, a, b), b, False{}))))
    case True{}:
      P.Bool.false_true({Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) == Word.to_nat(n, a) : Nat},
        (%P.Nat.lt_of_sum(Word.to_nat(n, a), P.Nat.pow2(n), Word.to_nat(n, b), Word.to_nat(n, Word.sub(n, a, b)),
            (%P.Nat.add_comm(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b)) :
              {Nat.add(Word.to_nat(n, a), P.Nat.pow2(n)) == _ : Nat}
              (%P.Nat.add_zero_r(Nat.add(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b))) :
                {Nat.add(Word.to_nat(n, a), P.Nat.pow2(n)) == _ : Nat}
                (%e : {Nat.add(Word.to_nat(n, a), W.cv(n, _)) == W.sum(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b), False{}) : Nat}
                  (%W.add_sub(n, a, b) : {Nat.add(Word.to_nat(n, _), W.cv(n, W.carry(n, Word.sub(n, a, b), b, False{}))) == W.sum(Word.to_nat(n, Word.sub(n, a, b)), Word.to_nat(n, b), False{}) : Nat}
        W.adc_carry(n, Word.sub(n, a, b), b, False{}))))),
            W.N_lt(n, Word.sub(n, a, b))) :
          {Cmp.is_le(P.Cmp.flip(_)) == True{} : Bool}
          (%P.Nat.cmp_swap(Word.to_nat(n, a), Word.to_nat(n, b)) : {Cmp.is_le(_) == True{} : Bool}
            (%W.cmp_nat(n, b, a) : {Cmp.is_le(_) == True{} : Bool}
              h))))

def W.sub_nat(n, a, b, h):
  W.sub_nat.go(n, a, b, W.carry(n, Word.sub(n, a, b), b, False{}), {==}, h)

# Bits
# ====

# Bit i of w (False past the top).
def W.bit(n: Nat, w: Word(n), +i: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match i:
            case 0n:
              b
            case 1n+j:
              W.bit(p, t, j)

# The bits below k of a and b agree: a list of equations (Data, so it can
# be built a bit at a time, then taken apart).
def W.allb(n: Nat, -a: Word(n), -b: Word(n), k: Nat) -> Data:
  match k:
    case 0n:
      Unit
    case 1n+j:
      Sigma<&2, &2, {W.bit(n, a, j) == W.bit(n, b, j) : Bool}, _ => W.allb(n, a, b, j)>

def W.allb.fst(-A: Data, -B: Data, +p: Sigma<&2, &2, A, _ => B>) -> A:
  match p:
    case Tuple{x, y}:
      x

def W.allb.snd(-A: Data, -B: Data, +p: Sigma<&2, &2, A, _ => B>) -> B:
  match p:
    case Tuple{x, y}:
      y

def W.allb.con(-A: Data, -B: Data, +x: A, +y: B) -> Sigma<&2, &2, A, _ => B>:
  Tuple{x, y}

# The low bit's equation and the rest's, from the bits below 1 + k.
law W.allb_tail:
  for +p: Nat
  for +x: Bool
  for +at: Word(p)
  for +y: Bool
  for +bt: Word(p)
  for +k: Nat
  for +h: W.allb(1n+p, WCon{x, at}, WCon{y, bt}, 1n+k)
  Sigma<&2, &2, {x == y : Bool}, _ => W.allb(p, at, bt, k)>

def W.allb_tail.k(-p: Nat, -x: Bool, -at: Word(p), -y: Bool, -bt: Word(p), -j: Nat,
  +e1: {W.bit(p, at, j) == W.bit(p, bt, j) : Bool},
  +r: Sigma<&2, &2, {x == y : Bool}, _ => W.allb(p, at, bt, j)>) ->
  Sigma<&2, &2, {x == y : Bool}, _ => W.allb(p, at, bt, 1n+j)>:
  W.allb.con({x == y : Bool}, W.allb(p, at, bt, 1n+j),
    W.allb.fst({x == y : Bool}, W.allb(p, at, bt, j), r),
    W.allb.con({W.bit(p, at, j) == W.bit(p, bt, j) : Bool}, W.allb(p, at, bt, j), e1,
      W.allb.snd({x == y : Bool}, W.allb(p, at, bt, j), r)))

def W.allb_tail(p, x, at, y, bt, k, h):
  match k:
    case 0n:
      W.allb.con({x == y : Bool}, Unit,
        W.allb.fst({x == y : Bool}, Unit, h), Unit{})
    case 1n+j:
      W.allb_tail.k(p, x, at, y, bt, j,
        W.allb.fst({W.bit(p, at, j) == W.bit(p, bt, j) : Bool},
          W.allb(1n+p, WCon{x, at}, WCon{y, bt}, 1n+j), h),
        W.allb_tail(p, x, at, y, bt, j,
          W.allb.snd({W.bit(p, at, j) == W.bit(p, bt, j) : Bool},
            W.allb(1n+p, WCon{x, at}, WCon{y, bt}, 1n+j), h)))

# Words with the same bits are the same word.
law W.ext:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: W.allb(n, a, b, n)
  {a == b : Word(n)}

law W.ext.con:
  for +p: Nat
  for +x: Bool
  for +at: Word(p)
  for +y: Bool
  for +bt: Word(p)
  for +e: {x == y : Bool}
  for f: {at == bt : Word(p)}
  {WCon{x, at} == WCon{y, bt} : Word(1n+p)}

def W.ext.con(p, x, at, y, bt, e, f):
  %e : {WCon{x, at} == WCon{_, bt} : Word(1n+p)}
  %f : {WCon{x, at} == WCon{x, _} : Word(1n+p)}
  {==}

def W.ext(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          W.ext.con(p, x, at, y, bt,
            W.allb.fst({x == y : Bool}, W.allb(p, at, bt, p), W.allb_tail(p, x, at, y, bt, p, h)),
            W.ext(p, at, bt,
              W.allb.snd({x == y : Bool}, W.allb(p, at, bt, p), W.allb_tail(p, x, at, y, bt, p, h))))

law W.bit_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +i: Nat
  {W.bit(n, Word.and(n, a, b), i) == Bool.and(W.bit(n, a, i), W.bit(n, b, i)) : Bool}

def W.bit_and(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_and(p, at, bt, j)

law W.bit_or:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +i: Nat
  {W.bit(n, Word.or(n, a, b), i) == Bool.or(W.bit(n, a, i), W.bit(n, b, i)) : Bool}

def W.bit_or(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_or(p, at, bt, j)

law W.bit_xor:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +i: Nat
  {W.bit(n, Word.xor(n, a, b), i) == Bool.xor(W.bit(n, a, i), W.bit(n, b, i)) : Bool}

def W.bit_xor(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_xor(p, at, bt, j)

# Below the top, a complement's bits are the complements.
law W.bit_not:
  for +n: Nat
  for +w: Word(n)
  for +i: Nat
  for +h: {Nat.cmp(i, n) == LT{} : Cmp}
  {W.bit(n, Word.not(n, w), i) == Bool.not(W.bit(n, w, i)) : Bool}

def W.bit_not(n, w, i, h):
  match n:
    case 0n:
      match i:
        case 0n:
          P.Cmp.eq_lt({W.bit(0n, Word.not(0n, w), 0n) == Bool.not(W.bit(0n, w, 0n)) : Bool},
            h)
        case 1n+j:
          P.Cmp.gt_lt({W.bit(0n, Word.not(0n, w), 1n+j) == Bool.not(W.bit(0n, w, 1n+j)) : Bool},
            h)
    case 1n+p:
      match w:
        case WCon{x, t}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_not(p, t, j, h)

law W.bit_zero:
  for +n: Nat
  for +i: Nat
  {W.bit(n, Word.zero(n), i) == False{} : Bool}

def W.bit_zero(n, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          {==}
        case 1n+j:
          W.bit_zero(p, j)

law W.bit_pad:
  for +p: Nat
  for +t: Word(p)
  for +i: Nat
  {W.bit(1n+p, Word.shr.pad(p, t), i) == W.bit(p, t, i) : Bool}

def W.bit_pad(p, t, i):
  match p:
    case 0n:
      match t:
        case WNil{}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              {==}
    case 1n+q:
      match t:
        case WCon{b, u}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_pad(q, u, j)

# A shift down moves each bit down one place.
law W.bit_shr:
  for +n: Nat
  for +w: Word(n)
  for +i: Nat
  {W.bit(n, Word.shr(n, w), i) == W.bit(n, w, 1n+i) : Bool}

def W.bit_shr(n, w, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          W.bit_pad(p, t, i)

law W.bit_put:
  for +p: Nat
  for +c: Bool
  for +w: Word(p)
  for +i: Nat
  for +h: {Nat.cmp(i, p) == LT{} : Cmp}
  {W.bit(p, Word.shl.put(p, c, w), i) == W.bit(1n+p, WCon{c, w}, i) : Bool}

def W.bit_put(p, c, w, i, h):
  match p:
    case 0n:
      match i:
        case 0n:
          P.Cmp.eq_lt({W.bit(0n, Word.shl.put(0n, c, w), 0n) == W.bit(1n, WCon{c, w}, 0n) : Bool}, h)
        case 1n+j:
          P.Cmp.gt_lt({W.bit(0n, Word.shl.put(0n, c, w), 1n+j) == W.bit(1n, WCon{c, w}, 1n+j)
            : Bool}, h)
    case 1n+q:
      match w:
        case WCon{b, u}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              W.bit_put(q, b, u, j, h)

# A shift up moves each bit up one place, dropping the top one.
law W.bit_shl0:
  for +n: Nat
  for +w: Word(n)
  {W.bit(n, Word.shl(n, w), 0n) == False{} : Bool}

def W.bit_shl0(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          {==}

law W.bit_shl:
  for +n: Nat
  for +w: Word(n)
  for +i: Nat
  for +h: {Nat.cmp(1n+i, n) == LT{} : Cmp}
  {W.bit(n, Word.shl(n, w), 1n+i) == W.bit(n, w, i) : Bool}

def W.bit_shl(n, w, i, h):
  match n:
    case 0n:
      P.Cmp.gt_lt({W.bit(0n, Word.shl(0n, w), 1n+i) == W.bit(0n, w, i) : Bool}, h)
    case 1n+p:
      match w:
        case WCon{b, t}:
          W.bit_put(p, b, t, i, h)

# Shifts and values
# =================

law W.N_shr:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.shr(n, w)) == P.Nat.half(Word.to_nat(n, w)) : Nat}

law W.N_pad:
  for +p: Nat
  for +t: Word(p)
  {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}

def W.N_pad(p, t):
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{b, u}:
          %Equal.sym(Nat, Word.to_nat(2n+q, WCon{b, Word.shr.pad(q, u)}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, Word.shr.pad(q, u)))),
            W.N_cons(1n+q, b, Word.shr.pad(q, u))) :
            {_ == Word.to_nat(1n+q, WCon{b, u}) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{b, u}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(q, u))), W.N_cons(q, b, u)) :
            {Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, Word.shr.pad(q, u)))) == _ : Nat}
          %W.N_pad(q, u) :
            {Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, Word.shr.pad(q, u))))
              == Nat.add(P.Nat.bit(b), Nat.double(_)) : Nat}
          {==}

def W.N_shr(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(p, t))), W.N_cons(p, b, t)) :
            {Word.to_nat(1n+p, Word.shr.pad(p, t)) == P.Nat.half(_) : Nat}
          %Equal.sym(Nat, P.Nat.half(Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(p, t)))),
            Word.to_nat(p, t), P.Nat.half_bit_double(b, Word.to_nat(p, t))) :
            {Word.to_nat(1n+p, Word.shr.pad(p, t)) == _ : Nat}
          W.N_pad(p, t)

# The top bit of a word of 1 + p bits.
def W.top(+p: Nat, w: Word(1n+p)) -> Bool:
  W.bit(1n+p, w, p)

# Shifting a bit in below a word whose top bit is clear doubles it.
law W.N_put:
  for +p: Nat
  for +c: Bool
  for +w: Word(1n+p)
  for +h: {W.top(p, w) == False{} : Bool}
  {Word.to_nat(1n+p, Word.shl.put(1n+p, c, w))
    == Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(1n+p, w))) : Nat}

def W.N_put(p, c, w, h):
  match p:
    case 0n:
      match w:
        case WCon{b, u}:
          match u:
            case WNil{}:
              %Equal.sym(Bool, b, False{}, h) : {Word.to_nat(1n, Word.shl.put(1n, c, WCon{b, WNil{}}))
                == Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(1n, WCon{_, WNil{}}))) : Nat}
              %Equal.sym(Nat, Word.to_nat(1n, WCon{c, WNil{}}),
                Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(0n, WNil{}))),
                W.N_cons(0n, c, WNil{})) :
                {_ == Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(1n, WCon{False{}, WNil{}})))
                  : Nat}
              {==}
    case 1n+q:
      match w:
        case WCon{b, u}:
          %Equal.sym(Nat, Word.to_nat(2n+q, WCon{c, Word.shl.put(1n+q, b, u)}),
            Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(1n+q, Word.shl.put(1n+q, b, u)))),
            W.N_cons(1n+q, c, Word.shl.put(1n+q, b, u))) :
            {_ == Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(2n+q, WCon{b, u}))) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+q, Word.shl.put(1n+q, b, u)),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u))), W.N_put(q, b, u, h)) :
            {Nat.add(P.Nat.bit(c), Nat.double(_))
              == Nat.add(P.Nat.bit(c), Nat.double(Word.to_nat(2n+q, WCon{b, u}))) : Nat}
          %Equal.sym(Nat, Word.to_nat(2n+q, WCon{b, u}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u))), W.N_cons(1n+q, b, u)) :
            {Nat.add(P.Nat.bit(c), Nat.double(Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u)))))
              == Nat.add(P.Nat.bit(c), Nat.double(_)) : Nat}
          {==}

# Shifting up a word whose top bit is clear doubles it.
law W.N_shl:
  for +p: Nat
  for +w: Word(1n+p)
  for +h: {W.top(p, w) == False{} : Bool}
  {Word.to_nat(1n+p, Word.shl(1n+p, w)) == Nat.double(Word.to_nat(1n+p, w)) : Nat}

def W.N_shl(p, w, h):
  match p:
    case 0n:
      match w:
        case WCon{b, u}:
          match u:
            case WNil{}:
              %Equal.sym(Bool, b, False{}, h) : {Word.to_nat(1n, Word.shl(1n, WCon{b, WNil{}}))
                == Nat.double(Word.to_nat(1n, WCon{_, WNil{}})) : Nat}
              {==}
    case 1n+q:
      match w:
        case WCon{b, u}:
          %Equal.sym(Nat, Word.to_nat(1n+q, Word.shl.put(1n+q, b, u)),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u))), W.N_put(q, b, u, h)) :
            {Nat.double(_) == Nat.double(Word.to_nat(2n+q, WCon{b, u})) : Nat}
          %Equal.sym(Nat, Word.to_nat(2n+q, WCon{b, u}),
            Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u))), W.N_cons(1n+q, b, u)) :
            {Nat.double(Nat.add(P.Nat.bit(b), Nat.double(Word.to_nat(1n+q, u)))) == Nat.double(_)
              : Nat}
          {==}

law W.cmp_refl:
  for +n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def W.cmp_refl(n, a):
  %Equal.sym(Cmp, Word.cmp(n, a, a), Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, a)),
    W.cmp_nat(n, a, a)) : {_ == EQ{} : Cmp}
  P.Nat.cmp_refl(Word.to_nat(n, a))

# A value below 2^p has no bits at p or above.
law W.bit_high:
  for +n: Nat
  for +w: Word(n)
  for +p: Nat
  for +k: Nat
  for +h1: {Nat.cmp(Word.to_nat(n, w), P.Nat.pow2(p)) == LT{} : Cmp}
  for +h2: {Cmp.is_le(Nat.cmp(p, k)) == True{} : Bool}
  {W.bit(n, w, k) == False{} : Bool}

def W.bit_high(n, w, p, k, h1, h2):
  match n:
    case 0n:
      {==}
    case 1n+m:
      match w:
        case WCon{b, t}:
          match p k:
            case 0n 0n:
              P.Nat.split_lt_one(b, Word.to_nat(m, t),
                (%W.N_cons(m, b, t) : {Nat.cmp(_, 1n) == LT{} : Cmp}
                  h1))
            case 0n 1n+j:
              W.bit_high(m, t, 0n, j,
                P.Nat.split_lt_one_t(b, Word.to_nat(m, t),
                  (%W.N_cons(m, b, t) : {Nat.cmp(_, 1n) == LT{} : Cmp}
                    h1)),
                P.Nat.le_zero(j))
            case 1n+q 0n:
              P.Bool.false_true({W.bit(1n+m, WCon{b, t}, 0n) == False{} : Bool}, h2)
            case 1n+q 1n+j:
              W.bit_high(m, t, q, j,
                P.Nat.split_lt_half(b, Word.to_nat(m, t), P.Nat.pow2(q),
                  (%W.N_cons(m, b, t) : {Nat.cmp(_, Nat.double(P.Nat.pow2(q))) == LT{} : Cmp}
                    h1)),
                h2)

# Past the top, every bit is clear.
law W.bit_beyond:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +h: {Cmp.is_le(Nat.cmp(n, k)) == True{} : Bool}
  {W.bit(n, w, k) == False{} : Bool}

def W.bit_beyond(n, w, k, h):
  match n:
    case 0n:
      {==}
    case 1n+m:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              P.Bool.false_true({W.bit(1n+m, WCon{b, t}, 0n) == False{} : Bool}, h)
            case 1n+j:
              W.bit_beyond(m, t, j, h)

# A value one below 2^p has its p low bits set.
law W.bit_ones:
  for +n: Nat
  for +w: Word(n)
  for +p: Nat
  for +k: Nat
  for +e: {Nat.add(Word.to_nat(n, w), 1n) == P.Nat.pow2(p) : Nat}
  for +hk: {Nat.cmp(k, p) == LT{} : Cmp}
  {W.bit(n, w, k) == True{} : Bool}

law W.N_zero0:
  for +w: Word(0n)
  {Word.to_nat(0n, w) == 0n : Nat}

def W.N_zero0(w):
  {==}

# The low bit, for p >= 1.
law W.bit_ones.low:
  for +m: Nat
  for +b: Bool
  for +t: Word(m)
  for +p: Nat
  for +e: {Nat.add(Word.to_nat(1n+m, WCon{b, t}), 1n) == P.Nat.pow2(p) : Nat}
  for +hk: {Nat.cmp(0n, p) == LT{} : Cmp}
  {b == True{} : Bool}

def W.bit_ones.low(m, b, t, p, e, hk):
  match p:
    case 0n:
      P.Nat.lt_zero({b == True{} : Bool}, 0n, hk)
    case 1n+q:
      P.Nat.ones_step_b(b, Word.to_nat(m, t), P.Nat.pow2(q),
        (%W.N_cons(m, b, t) : {Nat.add(_, 1n) == Nat.double(P.Nat.pow2(q)) : Nat}
          e))

def W.bit_ones(n, w, p, k, e, hk):
  match n:
    case 0n:
      match p:
        case 0n:
          P.Nat.lt_zero({W.bit(0n, w, k) == True{} : Bool}, k, hk)
        case 1n+q:
          P.Bool.true_false({W.bit(0n, w, k) == True{} : Bool},
            (%W.N_zero0(w) : {P.Nat.odd(Nat.add(_, 1n)) == False{} : Bool}
              (%Equal.sym(Nat, Nat.add(Word.to_nat(0n, w), 1n), P.Nat.pow2(1n+q), e) :
                {P.Nat.odd(_) == False{} : Bool}
                P.Nat.odd_double(P.Nat.pow2(q)))))
    case 1n+m:
      match w:
        case WCon{b, t}:
          match p k:
            case _ 0n:
              W.bit_ones.low(m, b, t, p, e, hk)
            case 0n 1n+j:
              P.Nat.lt_zero({W.bit(1n+m, WCon{b, t}, 1n+j) == True{} : Bool}, 1n+j, hk)
            case 1n+q 1n+j:
              W.bit_ones(m, t, q, j,
                P.Nat.ones_step_x(Word.to_nat(m, t), P.Nat.pow2(q),
                  (%P.Nat.ones_step_b(b, Word.to_nat(m, t), P.Nat.pow2(q),
                      (%W.N_cons(m, b, t) : {Nat.add(_, 1n) == Nat.double(P.Nat.pow2(q)) : Nat}
                        e)) :
                    {Nat.add(Nat.add(P.Nat.bit(_), Nat.double(Word.to_nat(m, t))), 1n)
                      == Nat.double(P.Nat.pow2(q)) : Nat}
                    (%W.N_cons(m, b, t) : {Nat.add(_, 1n) == Nat.double(P.Nat.pow2(q)) : Nat}
                      e))),
                hk)

law W.and_zero:
  for +n: Nat
  for +r: Word(n)
  {Word.and(n, Word.zero(n), r) == Word.zero(n) : Word(n)}

def W.and_zero(n, r):
  match n:
    case 0n:
      match r:
        case WNil{}:
          {==}
    case 1n+p:
      match r:
        case WCon{b, t}:
          %W.and_zero(p, t) : {WCon{False{}, Word.and(p, Word.zero(p), t)} == WCon{False{}, _} : Word(1n+p)}
          {==}

# A sum below some word's value does not wrap.
law W.add_bound:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: Word(n)
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, e))) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

law W.add_bound.go:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: Word(n)
  for +k: Bool
  for +ek: {W.carry(n, a, b, False{}) == k : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, e))) == True{} : Bool}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def W.add_bound.go(n, a, b, e, k, ek, h):
  match k:
    case False{}:
      %P.Nat.add_zero_r(Word.to_nat(n, Word.add(n, a, b))) : {_ == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}
      %P.Nat.add_zero_r(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) :
        {Nat.add(Word.to_nat(n, Word.add(n, a, b)), 0n) == _ : Nat}
      %ek : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.cv(n, _)) == W.sum(Word.to_nat(n, a), Word.to_nat(n, b), False{}) : Nat}
      W.adc_carry(n, a, b, False{})
    case True{}:
      P.Cmp.eq_lt({Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat},
        (%P.Nat.cmp_refl(P.Nat.pow2(n)) : {_ == LT{} : Cmp}
          P.Nat.le_lt_trans(P.Nat.pow2(n), Word.to_nat(n, e), P.Nat.pow2(n),
            P.Nat.le_trans(P.Nat.pow2(n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, e),
              (%{(%P.Nat.add_zero_r(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) :
                    {Nat.add(Word.to_nat(n, Word.add(n, a, b)), P.Nat.pow2(n)) == _ : Nat}
                    (%ek : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.cv(n, _)) == W.sum(Word.to_nat(n, a), Word.to_nat(n, b), False{}) : Nat}
                      W.adc_carry(n, a, b, False{})))
                  : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), P.Nat.pow2(n)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}} :
                  {Cmp.is_le(Nat.cmp(P.Nat.pow2(n), _)) == True{} : Bool}
                P.Nat.le_add_l(Word.to_nat(n, Word.add(n, a, b)), P.Nat.pow2(n))),
              h),
            W.N_lt(n, e))))

def W.add_bound(n, a, b, e, h):
  W.add_bound.go(n, a, b, e, W.carry(n, a, b, False{}), {==}, h)

law W.and_idem_r:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.and(n, Word.and(n, a, b), b) == Word.and(n, a, b) : Word(n)}

def W.and_idem_r(n, a, b):
  match n a b:
    case 0n _ _:
      {==}
    case 1n+p WCon{x, at} WCon{y, bt}:
      %Equal.sym(Bool, Bool.and(Bool.and(x, y), y), Bool.and(x, y), P.Bool.and_idem_r(x, y)) :
        {WCon{_, Word.and(p, Word.and(p, at, bt), bt)} == WCon{Bool.and(x, y), Word.and(p, at, bt)} : Word(1n+p)}
      %Equal.sym(Word(p), Word.and(p, Word.and(p, at, bt), bt), Word.and(p, at, bt), W.and_idem_r(p, at, bt)) :
        {WCon{Bool.and(x, y), _} == WCon{Bool.and(x, y), Word.and(p, at, bt)} : Word(1n+p)}
      {==}
