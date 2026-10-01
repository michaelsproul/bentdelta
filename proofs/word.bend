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
  for e: {Nat.add(Nat.add(x, y), 1n) == q : Nat}
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
  for e: {Nat.add(Nat.add(nb, y), 1n) == P.Nat.pow2(n) : Nat}
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
  for e: {Nat.add(Nat.add(nb, y), 1n) == P.Nat.pow2(n) : Nat}
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
  for e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
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
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def W.cmp_eq(n, a, b, e):
  W.eq_N(n, a, b, P.Nat.cmp_eq(Word.to_nat(n, a), Word.to_nat(n, b),
    (%W.cmp_nat(n, a, b) : {_ == EQ{} : Cmp}
      e)))
