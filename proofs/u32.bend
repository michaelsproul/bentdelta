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
  for h: {Nat.cmp(i, 32n) == LT{} : Cmp}
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
  for h: {Nat.cmp(1n+i, 32n) == LT{} : Cmp}
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
