import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./word.bend as W

# Lemmas about packed bytes (bytes.bend): a byte written can be read back,
# and a write leaves every other byte as it was.

# Lanes
# =====

# Inserting v's low byte at bit s of w (as B.put does), and extracting the
# byte at bit s (as B.get does).
def BP.ins(+w: U32, +s: Nat, +v: U32) -> U32:
  U32.or(U32.and(w, U32.not(U32.shln(255, s))), U32.shln(U32.and(v, 255), s))

def BP.ext(+w: U32, +s: Nat) -> U32:
  U32.and(U32.shrn(w, s), 255)

law BP.same_lo:
  for +w: U32
  for +s: Nat
  for +v: U32
  for +k: Nat
  for +hk: {Nat.cmp(k, 8n) == LT{} : Cmp}
  for +h32: {Nat.cmp(Nat.add(k, s), 32n) == LT{} : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, s, v), s), k) == V.U.bit(U32.and(v, 255), k) : Bool}

def BP.same_lo(w, s, v, k, hk, h32):
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(BP.ins(w, s, v), s), 255), k), Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(BP.ins(w, s, v), s), 255, k)) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), True{}, V.U.bit_255_lo(k, hk)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), _) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), True{}), V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), P.Bool.and_true(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k))) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), V.U.bit(BP.ins(w, s, v), Nat.add(k, s)), V.U.bit_shrn(BP.ins(w, s, v), s, k)) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(BP.ins(w, s, v), Nat.add(k, s)), Bool.or(V.U.bit(U32.and(w, U32.not(U32.shln(255, s))), Nat.add(k, s)), V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))), V.U.bit_or(U32.and(w, U32.not(U32.shln(255, s))), U32.shln(U32.and(v, 255), s), Nat.add(k, s))) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(w, U32.not(U32.shln(255, s))), Nat.add(k, s)), Bool.and(V.U.bit(w, Nat.add(k, s)), V.U.bit(U32.not(U32.shln(255, s)), Nat.add(k, s))), V.U.bit_and(w, U32.not(U32.shln(255, s)), Nat.add(k, s))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.not(U32.shln(255, s)), Nat.add(k, s)), Bool.not(V.U.bit(U32.shln(255, s), Nat.add(k, s))), V.U.bit_not(U32.shln(255, s), Nat.add(k, s), h32)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, s)), _), V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(255, s), Nat.add(k, s)), V.U.bit(255, k), V.U.bit_shln_hi(255, s, k, h32)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, s)), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), True{}, V.U.bit_255_lo(k, hk)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, s)), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(w, Nat.add(k, s)), Bool.not(True{})), False{}, P.Bool.and_false(V.U.bit(w, Nat.add(k, s)))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s))) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(U32.and(v, 255), s), Nat.add(k, s)), V.U.bit(U32.and(v, 255), k), V.U.bit_shln_hi(U32.and(v, 255), s, k, h32)) :
    {Bool.or(False{}, _) == V.U.bit(U32.and(v, 255), k) : Bool}
  {==}

law BP.same_hi:
  for +w: U32
  for +s: Nat
  for +v: U32
  for +k: Nat
  for +hk: {Cmp.is_le(Nat.cmp(8n, k)) == True{} : Bool}
  {V.U.bit(BP.ext(BP.ins(w, s, v), s), k) == V.U.bit(U32.and(v, 255), k) : Bool}

def BP.same_hi(w, s, v, k, hk):
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(BP.ins(w, s, v), s), 255), k), Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(BP.ins(w, s, v), s), 255, k)) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), False{}, V.U.bit_255_hi(k, hk)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), _) == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k), False{}), False{}, P.Bool.and_false(V.U.bit(U32.shrn(BP.ins(w, s, v), s), k))) :
    {_ == V.U.bit(U32.and(v, 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(v, 255), k), False{}, V.U.bit_low_hi(v, k, hk)) :
    {False{} == _ : Bool}
  {==}

# Bit k < 8 of a byte at s2 lying below the byte written at s1.
law BP.below_lo:
  for +w: U32
  for +d: Nat
  for +s2: Nat
  for +v: U32
  for +k: Nat
  for +hk: {Nat.cmp(k, 8n) == LT{} : Cmp}
  for +hm: {Nat.cmp(Nat.add(k, s2), Nat.add(d, s2)) == LT{} : Cmp}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s2), 32n)) == True{} : Bool}
  for +h32: {Nat.cmp(Nat.add(k, s2), 32n) == LT{} : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), k) == V.U.bit(BP.ext(w, s2), k) : Bool}

def BP.below_lo(w, d, s2, v, k, hk, hm, hs, h32):
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), 255), k), Bool.and(V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), 255, k)) :
    {_ == V.U.bit(U32.and(U32.shrn(w, s2), 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(w, s2), 255), k), Bool.and(V.U.bit(U32.shrn(w, s2), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(w, s2), 255, k)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), V.U.bit(255, k)) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), True{}, V.U.bit_255_lo(k, hk)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), _) == Bool.and(V.U.bit(U32.shrn(w, s2), k), _) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), True{}), V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), P.Bool.and_true(V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k))) :
    {_ == Bool.and(V.U.bit(U32.shrn(w, s2), k), True{}) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(w, s2), k), True{}), V.U.bit(U32.shrn(w, s2), k), P.Bool.and_true(V.U.bit(U32.shrn(w, s2), k))) :
    {V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shrn(BP.ins(w, Nat.add(d, s2), v), s2), k), V.U.bit(BP.ins(w, Nat.add(d, s2), v), Nat.add(k, s2)), V.U.bit_shrn(BP.ins(w, Nat.add(d, s2), v), s2, k)) :
    {_ == V.U.bit(U32.shrn(w, s2), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shrn(w, s2), k), V.U.bit(w, Nat.add(k, s2)), V.U.bit_shrn(w, s2, k)) :
    {V.U.bit(BP.ins(w, Nat.add(d, s2), v), Nat.add(k, s2)) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(BP.ins(w, Nat.add(d, s2), v), Nat.add(k, s2)), Bool.or(V.U.bit(U32.and(w, U32.not(U32.shln(255, Nat.add(d, s2)))), Nat.add(k, s2)), V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))), V.U.bit_or(U32.and(w, U32.not(U32.shln(255, Nat.add(d, s2)))), U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))) :
    {_ == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(w, U32.not(U32.shln(255, Nat.add(d, s2)))), Nat.add(k, s2)), Bool.and(V.U.bit(w, Nat.add(k, s2)), V.U.bit(U32.not(U32.shln(255, Nat.add(d, s2))), Nat.add(k, s2))), V.U.bit_and(w, U32.not(U32.shln(255, Nat.add(d, s2))), Nat.add(k, s2))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))) == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.not(U32.shln(255, Nat.add(d, s2))), Nat.add(k, s2)), Bool.not(V.U.bit(U32.shln(255, Nat.add(d, s2)), Nat.add(k, s2))), V.U.bit_not(U32.shln(255, Nat.add(d, s2)), Nat.add(k, s2), h32)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, s2)), _), V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))) == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(255, Nat.add(d, s2)), Nat.add(k, s2)), False{}, V.U.bit_shln_lo(255, Nat.add(d, s2), Nat.add(k, s2), hm, hs)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, s2)), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))) == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(w, Nat.add(k, s2)), Bool.not(False{})), V.U.bit(w, Nat.add(k, s2)), P.Bool.and_true(V.U.bit(w, Nat.add(k, s2)))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2))) == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(U32.and(v, 255), Nat.add(d, s2)), Nat.add(k, s2)), False{}, V.U.bit_shln_lo(U32.and(v, 255), Nat.add(d, s2), Nat.add(k, s2), hm, hs)) :
    {Bool.or(V.U.bit(w, Nat.add(k, s2)), _) == V.U.bit(w, Nat.add(k, s2)) : Bool}
  %Equal.sym(Bool, Bool.or(V.U.bit(w, Nat.add(k, s2)), False{}), V.U.bit(w, Nat.add(k, s2)), P.Bool.or_false(V.U.bit(w, Nat.add(k, s2)))) :
    {_ == V.U.bit(w, Nat.add(k, s2)) : Bool}
  {==}

# k + (d + s) = (k + d) + s.
law BP.above_idx:
  for +k: Nat
  for +d: Nat
  for +s: Nat
  {Nat.add(k, Nat.add(d, s)) == Nat.add(Nat.add(k, d), s) : Nat}

def BP.above_idx(k, d, s):
  Equal.sym(Nat, Nat.add(Nat.add(k, d), s), Nat.add(k, Nat.add(d, s)), P.Nat.add_assoc(k, d, s))

# Bit k < 8 of a byte at d + s1 lying above the byte written at s1.
law BP.above_lo:
  for +w: U32
  for +s1: Nat
  for +d: Nat
  for +v: U32
  for +k: Nat
  for +hk: {Nat.cmp(k, 8n) == LT{} : Cmp}
  for +hj: {Cmp.is_le(Nat.cmp(8n, Nat.add(k, d))) == True{} : Bool}
  for +h32: {Nat.cmp(Nat.add(k, Nat.add(d, s1)), 32n) == LT{} : Cmp}
  for +hj32: {Nat.cmp(Nat.add(Nat.add(k, d), s1), 32n) == LT{} : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), k) == V.U.bit(BP.ext(w, Nat.add(d, s1)), k) : Bool}

def BP.above_lo(w, s1, d, v, k, hk, hj, h32, hj32):
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), 255), k), Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), 255, k)) :
    {_ == V.U.bit(U32.and(U32.shrn(w, Nat.add(d, s1)), 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(w, Nat.add(d, s1)), 255), k), Bool.and(V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(w, Nat.add(d, s1)), 255, k)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), V.U.bit(255, k)) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), True{}, V.U.bit_255_lo(k, hk)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), _) == Bool.and(V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), _) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), True{}), V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), P.Bool.and_true(V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k))) :
    {_ == Bool.and(V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), True{}) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), True{}), V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), P.Bool.and_true(V.U.bit(U32.shrn(w, Nat.add(d, s1)), k))) :
    {V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shrn(BP.ins(w, s1, v), Nat.add(d, s1)), k), V.U.bit(BP.ins(w, s1, v), Nat.add(k, Nat.add(d, s1))), V.U.bit_shrn(BP.ins(w, s1, v), Nat.add(d, s1), k)) :
    {_ == V.U.bit(U32.shrn(w, Nat.add(d, s1)), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shrn(w, Nat.add(d, s1)), k), V.U.bit(w, Nat.add(k, Nat.add(d, s1))), V.U.bit_shrn(w, Nat.add(d, s1), k)) :
    {V.U.bit(BP.ins(w, s1, v), Nat.add(k, Nat.add(d, s1))) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(BP.ins(w, s1, v), Nat.add(k, Nat.add(d, s1))), Bool.or(V.U.bit(U32.and(w, U32.not(U32.shln(255, s1))), Nat.add(k, Nat.add(d, s1))), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))), V.U.bit_or(U32.and(w, U32.not(U32.shln(255, s1))), U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) :
    {_ == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(w, U32.not(U32.shln(255, s1))), Nat.add(k, Nat.add(d, s1))), Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), V.U.bit(U32.not(U32.shln(255, s1)), Nat.add(k, Nat.add(d, s1)))), V.U.bit_and(w, U32.not(U32.shln(255, s1)), Nat.add(k, Nat.add(d, s1)))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.not(U32.shln(255, s1)), Nat.add(k, Nat.add(d, s1))), Bool.not(V.U.bit(U32.shln(255, s1), Nat.add(k, Nat.add(d, s1)))), V.U.bit_not(U32.shln(255, s1), Nat.add(k, Nat.add(d, s1)), h32)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), _), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(255, s1), Nat.add(k, Nat.add(d, s1))), V.U.bit(U32.shln(255, s1), Nat.add(Nat.add(k, d), s1)), Equal.cong(Nat, Bool, x => V.U.bit(U32.shln(255, s1), x), Nat.add(k, Nat.add(d, s1)), Nat.add(Nat.add(k, d), s1), BP.above_idx(k, d, s1))) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(255, s1), Nat.add(Nat.add(k, d), s1)), V.U.bit(255, Nat.add(k, d)), V.U.bit_shln_hi(255, s1, Nat.add(k, d), hj32)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(255, Nat.add(k, d)), False{}, V.U.bit_255_hi(Nat.add(k, d), hj)) :
    {Bool.or(Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), Bool.not(_)), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), Bool.not(False{})), V.U.bit(w, Nat.add(k, Nat.add(d, s1))), P.Bool.and_true(V.U.bit(w, Nat.add(k, Nat.add(d, s1))))) :
    {Bool.or(_, V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1)))) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(k, Nat.add(d, s1))), V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(Nat.add(k, d), s1)), Equal.cong(Nat, Bool, x => V.U.bit(U32.shln(U32.and(v, 255), s1), x), Nat.add(k, Nat.add(d, s1)), Nat.add(Nat.add(k, d), s1), BP.above_idx(k, d, s1))) :
    {Bool.or(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), _) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.shln(U32.and(v, 255), s1), Nat.add(Nat.add(k, d), s1)), V.U.bit(U32.and(v, 255), Nat.add(k, d)), V.U.bit_shln_hi(U32.and(v, 255), s1, Nat.add(k, d), hj32)) :
    {Bool.or(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), _) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(v, 255), Nat.add(k, d)), False{}, V.U.bit_low_hi(v, Nat.add(k, d), hj)) :
    {Bool.or(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), _) == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  %Equal.sym(Bool, Bool.or(V.U.bit(w, Nat.add(k, Nat.add(d, s1))), False{}), V.U.bit(w, Nat.add(k, Nat.add(d, s1))), P.Bool.or_false(V.U.bit(w, Nat.add(k, Nat.add(d, s1))))) :
    {_ == V.U.bit(w, Nat.add(k, Nat.add(d, s1))) : Bool}
  {==}

law BP.other_hi:
  for +w: U32
  for +s1: Nat
  for +s2: Nat
  for +v: U32
  for +k: Nat
  for +hk: {Cmp.is_le(Nat.cmp(8n, k)) == True{} : Bool}
  {V.U.bit(BP.ext(BP.ins(w, s1, v), s2), k) == V.U.bit(BP.ext(w, s2), k) : Bool}

def BP.other_hi(w, s1, s2, v, k, hk):
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(BP.ins(w, s1, v), s2), 255), k), Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), s2), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(BP.ins(w, s1, v), s2), 255, k)) :
    {_ == V.U.bit(U32.and(U32.shrn(w, s2), 255), k) : Bool}
  %Equal.sym(Bool, V.U.bit(U32.and(U32.shrn(w, s2), 255), k), Bool.and(V.U.bit(U32.shrn(w, s2), k), V.U.bit(255, k)), V.U.bit_and(U32.shrn(w, s2), 255, k)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), s2), k), V.U.bit(255, k)) == _ : Bool}
  %Equal.sym(Bool, V.U.bit(255, k), False{}, V.U.bit_255_hi(k, hk)) :
    {Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), s2), k), _) == Bool.and(V.U.bit(U32.shrn(w, s2), k), _) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(BP.ins(w, s1, v), s2), k), False{}), False{}, P.Bool.and_false(V.U.bit(U32.shrn(BP.ins(w, s1, v), s2), k))) :
    {_ == Bool.and(V.U.bit(U32.shrn(w, s2), k), False{}) : Bool}
  %Equal.sym(Bool, Bool.and(V.U.bit(U32.shrn(w, s2), k), False{}), False{}, P.Bool.and_false(V.U.bit(U32.shrn(w, s2), k))) :
    {False{} == _ : Bool}
  {==}

# Whole lanes
# ===========

law BP.same_bit:
  for +w: U32
  for +s: Nat
  for +v: U32
  for +hs: {Cmp.is_le(Nat.cmp(s, 24n)) == True{} : Bool}
  for +k: Nat
  {V.U.bit(BP.ext(BP.ins(w, s, v), s), k) == V.U.bit(U32.and(v, 255), k) : Bool}

law BP.same_bit.go:
  for +w: U32
  for +s: Nat
  for +v: U32
  for +hs: {Cmp.is_le(Nat.cmp(s, 24n)) == True{} : Bool}
  for +k: Nat
  for +c: Cmp
  for +e: {Nat.cmp(k, 8n) == c : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, s, v), s), k) == V.U.bit(U32.and(v, 255), k) : Bool}

def BP.same_bit.go(w, s, v, hs, k, c, e):
  match c:
    case LT{}:
      BP.same_lo(w, s, v, k, e, P.Nat.lt32(k, s, e, hs))
    case EQ{}:
      BP.same_hi(w, s, v, k, P.Nat.not_lt_le(k, 8n, EQ{}, e, {==}))
    case GT{}:
      BP.same_hi(w, s, v, k, P.Nat.not_lt_le(k, 8n, GT{}, e, {==}))

def BP.same_bit(w, s, v, hs, k):
  BP.same_bit.go(w, s, v, hs, k, Nat.cmp(k, 8n), {==})

def BP.same_all(+w: U32, +s: Nat, +v: U32, +hs: {Cmp.is_le(Nat.cmp(s, 24n)) == True{} : Bool},
  +k: Nat) -> V.U.allb(BP.ext(BP.ins(w, s, v), s), U32.and(v, 255), k):
  match k:
    case 0n:
      Unit{}
    case 1n+j:
      W.W.allb.con({V.U.bit(BP.ext(BP.ins(w, s, v), s), j) == V.U.bit(U32.and(v, 255), j) : Bool},
        V.U.allb(BP.ext(BP.ins(w, s, v), s), U32.and(v, 255), j),
        BP.same_bit(w, s, v, hs, j), BP.same_all(w, s, v, hs, j))

# A byte inserted at bit s reads back as written.
law BP.lane_same:
  for +w: U32
  for +s: Nat
  for +v: U32
  for +hs: {Cmp.is_le(Nat.cmp(s, 24n)) == True{} : Bool}
  {BP.ext(BP.ins(w, s, v), s) == U32.and(v, 255) : U32}

def BP.lane_same(w, s, v, hs):
  V.U.ext(BP.ext(BP.ins(w, s, v), s), U32.and(v, 255), BP.same_all(w, s, v, hs, 32n))

law BP.below_bit:
  for +w: U32
  for +d: Nat
  for +s2: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s2), 24n)) == True{} : Bool}
  for +k: Nat
  {V.U.bit(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), k) == V.U.bit(BP.ext(w, s2), k) : Bool}

law BP.below_bit.go:
  for +w: U32
  for +d: Nat
  for +s2: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s2), 24n)) == True{} : Bool}
  for +k: Nat
  for +c: Cmp
  for +e: {Nat.cmp(k, 8n) == c : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), k) == V.U.bit(BP.ext(w, s2), k) : Bool}

def BP.below_bit.go(w, d, s2, v, hd, hs, k, c, e):
  match c:
    case LT{}:
      BP.below_lo(w, d, s2, v, k, e,
        P.Nat.add_lt_r(k, d, s2, P.Nat.lt_le_trans(k, 8n, d, e, hd)),
        P.Nat.le_trans(Nat.add(d, s2), 24n, 32n, hs, {==}),
        P.Nat.lt_le_trans(Nat.add(k, s2), Nat.add(d, s2), 32n,
          P.Nat.add_lt_r(k, d, s2, P.Nat.lt_le_trans(k, 8n, d, e, hd)),
          P.Nat.le_trans(Nat.add(d, s2), 24n, 32n, hs, {==})))
    case EQ{}:
      BP.other_hi(w, Nat.add(d, s2), s2, v, k, P.Nat.not_lt_le(k, 8n, EQ{}, e, {==}))
    case GT{}:
      BP.other_hi(w, Nat.add(d, s2), s2, v, k, P.Nat.not_lt_le(k, 8n, GT{}, e, {==}))

def BP.below_bit(w, d, s2, v, hd, hs, k):
  BP.below_bit.go(w, d, s2, v, hd, hs, k, Nat.cmp(k, 8n), {==})

def BP.below_all(+w: U32, +d: Nat, +s2: Nat, +v: U32,
  +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool},
  +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s2), 24n)) == True{} : Bool}, +k: Nat) ->
  V.U.allb(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), BP.ext(w, s2), k):
  match k:
    case 0n:
      Unit{}
    case 1n+j:
      W.W.allb.con({V.U.bit(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), j) == V.U.bit(BP.ext(w, s2), j) : Bool},
        V.U.allb(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), BP.ext(w, s2), j),
        BP.below_bit(w, d, s2, v, hd, hs, j), BP.below_all(w, d, s2, v, hd, hs, j))

# Inserting a byte leaves a byte below it.
law BP.lane_below:
  for +w: U32
  for +d: Nat
  for +s2: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s2), 24n)) == True{} : Bool}
  {BP.ext(BP.ins(w, Nat.add(d, s2), v), s2) == BP.ext(w, s2) : U32}

def BP.lane_below(w, d, s2, v, hd, hs):
  V.U.ext(BP.ext(BP.ins(w, Nat.add(d, s2), v), s2), BP.ext(w, s2), BP.below_all(w, d, s2, v, hd, hs, 32n))

law BP.above_bit:
  for +w: U32
  for +s1: Nat
  for +d: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s1), 24n)) == True{} : Bool}
  for +k: Nat
  {V.U.bit(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), k) == V.U.bit(BP.ext(w, Nat.add(d, s1)), k) : Bool}

law BP.above_bit.go:
  for +w: U32
  for +s1: Nat
  for +d: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s1), 24n)) == True{} : Bool}
  for +k: Nat
  for +c: Cmp
  for +e: {Nat.cmp(k, 8n) == c : Cmp}
  {V.U.bit(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), k) == V.U.bit(BP.ext(w, Nat.add(d, s1)), k) : Bool}

def BP.above_bit.go(w, s1, d, v, hd, hs, k, c, e):
  match c:
    case LT{}:
      BP.above_lo(w, s1, d, v, k, e,
        P.Nat.le_trans(8n, d, Nat.add(k, d), hd, P.Nat.le_add_l(k, d)),
        P.Nat.lt32(k, Nat.add(d, s1), e, hs),
        (%BP.above_idx(k, d, s1) : {Nat.cmp(_, 32n) == LT{} : Cmp}
          P.Nat.lt32(k, Nat.add(d, s1), e, hs)))
    case EQ{}:
      BP.other_hi(w, s1, Nat.add(d, s1), v, k, P.Nat.not_lt_le(k, 8n, EQ{}, e, {==}))
    case GT{}:
      BP.other_hi(w, s1, Nat.add(d, s1), v, k, P.Nat.not_lt_le(k, 8n, GT{}, e, {==}))

def BP.above_bit(w, s1, d, v, hd, hs, k):
  BP.above_bit.go(w, s1, d, v, hd, hs, k, Nat.cmp(k, 8n), {==})

def BP.above_all(+w: U32, +s1: Nat, +d: Nat, +v: U32,
  +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool},
  +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s1), 24n)) == True{} : Bool}, +k: Nat) ->
  V.U.allb(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), BP.ext(w, Nat.add(d, s1)), k):
  match k:
    case 0n:
      Unit{}
    case 1n+j:
      W.W.allb.con({V.U.bit(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), j) == V.U.bit(BP.ext(w, Nat.add(d, s1)), j) : Bool},
        V.U.allb(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), BP.ext(w, Nat.add(d, s1)), j),
        BP.above_bit(w, s1, d, v, hd, hs, j), BP.above_all(w, s1, d, v, hd, hs, j))

# Inserting a byte leaves a byte above it.
law BP.lane_above:
  for +w: U32
  for +s1: Nat
  for +d: Nat
  for +v: U32
  for +hd: {Cmp.is_le(Nat.cmp(8n, d)) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(d, s1), 24n)) == True{} : Bool}
  {BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)) == BP.ext(w, Nat.add(d, s1)) : U32}

def BP.lane_above(w, s1, d, v, hd, hs):
  V.U.ext(BP.ext(BP.ins(w, s1, v), Nat.add(d, s1)), BP.ext(w, Nat.add(d, s1)), BP.above_all(w, s1, d, v, hd, hs, 32n))

# Bytes of a tree
# ===============

# The byte at i of A.from(t), and t after writing v there.
def BP.byt(+t: A.Tr, +i: U32) -> U32:
  BP.ext(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i))

def BP.put(+t: A.Tr, +i: U32, +v: U32) -> A.Tr:
  A.T.set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v))

law BP.get_from:
  for +t: A.Tr
  for +i: U32
  {B.B.get(A.A.from(t), i) == (A.A.from(t), BP.byt(t, i)) : Array<U32> & U32}

def BP.get_from(t, i):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.shrn(i, 2n)),
    (A.A.from(t), A.T.word(t, U32.shrn(i, 2n))), A.A.get_from(t, U32.shrn(i, 2n))) :
    {B.B.get.k(i, _) == (A.A.from(t), BP.byt(t, i)) : Array<U32> & U32}
  {==}

law BP.put_from:
  for +t: A.Tr
  for +i: U32
  for +v: U32
  {B.B.put(A.A.from(t), i, v) == A.A.from(BP.put(t, i, v)) : Array<U32>}

def BP.put_from(t, i, v):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.shrn(i, 2n)),
    (A.A.from(t), A.T.word(t, U32.shrn(i, 2n))), A.A.get_from(t, U32.shrn(i, 2n))) :
    {B.B.put.k(i, v, _) == A.A.from(BP.put(t, i, v)) : Array<U32>}
  A.A.set_from(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v))

# The lane of a byte: its bit offset in its word is at most 24.
law BP.sh_le:
  for +i: U32
  {Cmp.is_le(Nat.cmp(B.B.sh(i), 24n)) == True{} : Bool}

law BP.sh_le.go:
  for +b0: Bool
  for +b1: Bool
  {Cmp.is_le(Nat.cmp(U32.to_nat(U32.shln(U32{WCon{b0, WCon{b1, Word.zero(30n)}}}, 3n)), 24n))
    == True{} : Bool}

def BP.sh_le.go(b0, b1):
  match b0 b1:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def BP.sh_le(i):
  match i:
    case U32{WCon{b0, WCon{b1, r}}}:
      %Equal.sym(Word(30n), Word.and(30n, Word.zero(30n), r), Word.zero(30n), W.W.and_zero(30n, r)) :
        {Cmp.is_le(Nat.cmp(U32.to_nat(U32.shln(U32{WCon{Bool.and(True{}, b0), WCon{Bool.and(True{}, b1), _}}}, 3n)), 24n))
          == True{} : Bool}
      BP.sh_le.go(b0, b1)

# A byte written reads back.
law BP.byt_put:
  for +t: A.Tr
  for +i: U32
  for +v: U32
  {BP.byt(BP.put(t, i, v), i) == U32.and(v, 255) : U32}

def BP.byt_put(t, i, v):
  %Equal.sym(U32, A.T.word(BP.put(t, i, v), U32.shrn(i, 2n)),
    BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v),
    A.T.word_set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v))) :
    {BP.ext(_, B.B.sh(i)) == U32.and(v, 255) : U32}
  BP.lane_same(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v, BP.sh_le(i))

# The lane offset of a byte with low bits b0, b1.
def BP.shv(+b0: Bool, +b1: Bool) -> Nat:
  match b0 b1:
    case False{} False{}:
      0n
    case True{} False{}:
      8n
    case False{} True{}:
      16n
    case True{} True{}:
      24n

law BP.sh_val:
  for +b0: Bool
  for +b1: Bool
  for +r: Word(30n)
  {B.B.sh(U32{WCon{b0, WCon{b1, r}}}) == BP.shv(b0, b1) : Nat}

law BP.sh_val.go:
  for +b0: Bool
  for +b1: Bool
  {U32.to_nat(U32.shln(U32{WCon{Bool.and(True{}, b0), WCon{Bool.and(True{}, b1), Word.zero(30n)}}}, 3n))
    == BP.shv(b0, b1) : Nat}

def BP.sh_val.go(b0, b1):
  match b0 b1:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def BP.sh_val(b0, b1, r):
  %Equal.sym(Word(30n), Word.and(30n, Word.zero(30n), r), Word.zero(30n), W.W.and_zero(30n, r)) :
    {U32.to_nat(U32.shln(U32{WCon{Bool.and(True{}, b0), WCon{Bool.and(True{}, b1), _}}}, 3n))
      == BP.shv(b0, b1) : Nat}
  BP.sh_val.go(b0, b1)

# The word index of a byte as a value: the high 30 bits.
law BP.N_hi:
  for +b0: Bool
  for +b1: Bool
  for +r: Word(30n)
  {V.U.N(U32.shrn(U32{WCon{b0, WCon{b1, r}}}, 2n)) == Word.to_nat(30n, r) : Nat}

def BP.N_hi(b0, b1, r):
  %Equal.sym(Nat, Word.to_nat(32n, Word.shr.pad(31n, Word.shr.pad(30n, r))),
    Word.to_nat(31n, Word.shr.pad(30n, r)), W.W.N_pad(31n, Word.shr.pad(30n, r))) :
    {_ == Word.to_nat(30n, r) : Nat}
  W.W.N_pad(30n, r)

# The values of two bytes of one word, whose high bits agree.
law BP.lane_lt.hi:
  for +ri: Word(30n)
  for +rj: Word(30n)
  for +a0: Bool
  for +a1: Bool
  for +c0: Bool
  for +c1: Bool
  for +ew: {U32.shrn(U32{WCon{a0, WCon{a1, ri}}}, 2n) == U32.shrn(U32{WCon{c0, WCon{c1, rj}}}, 2n) : U32}
  {Word.to_nat(30n, ri) == Word.to_nat(30n, rj) : Nat}

def BP.lane_lt.hi(ri, rj, a0, a1, c0, c1, ew):
  %BP.N_hi(a0, a1, ri) :
    {_ == Word.to_nat(30n, rj) : Nat}
  %BP.N_hi(c0, c1, rj) :
    {V.U.N(U32.shrn(U32{WCon{a0, WCon{a1, ri}}}, 2n)) == _ : Nat}
  %Equal.sym(U32, U32.shrn(U32{WCon{a0, WCon{a1, ri}}}, 2n), U32.shrn(U32{WCon{c0, WCon{c1, rj}}}, 2n), ew) :
    {V.U.N(_) == V.U.N(U32.shrn(U32{WCon{c0, WCon{c1, rj}}}, 2n)) : Nat}
  {==}

# Two bytes of one word, the one read below the one written: the write
# leaves it.
law BP.lane_lt:
  for +w: U32
  for +v: U32
  for +i: U32
  for +j: U32
  for +hlt: {U32.is_lt(j, i) == True{} : Bool}
  for +ew: {U32.shrn(i, 2n) == U32.shrn(j, 2n) : U32}
  {BP.ext(BP.ins(w, B.B.sh(i), v), B.B.sh(j)) == BP.ext(w, B.B.sh(j)) : U32}

law BP.lane_lt.go:
  for +w: U32
  for +v: U32
  for +a0: Bool
  for +a1: Bool
  for +ri: Word(30n)
  for +c0: Bool
  for +c1: Bool
  for +rj: Word(30n)
  for +hlt: {U32.is_lt(U32{WCon{c0, WCon{c1, rj}}}, U32{WCon{a0, WCon{a1, ri}}}) == True{} : Bool}
  for +ew: {U32.shrn(U32{WCon{a0, WCon{a1, ri}}}, 2n) == U32.shrn(U32{WCon{c0, WCon{c1, rj}}}, 2n) : U32}
  {BP.ext(BP.ins(w, B.B.sh(U32{WCon{a0, WCon{a1, ri}}}), v), B.B.sh(U32{WCon{c0, WCon{c1, rj}}}))
    == BP.ext(w, B.B.sh(U32{WCon{c0, WCon{c1, rj}}})) : U32}

def BP.lane_lt.go(w, v, a0, a1, ri, c0, c1, rj, hlt, ew):
  match a0 a1 c0 c1:
    case False{} False{} False{} False{}:
      P.Cmp.eq_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(0n, 0n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, False{}, False{}, False{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{False{}, WCon{False{}, rj}}}), Nat.add(0n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{False{}, WCon{False{}, rj}}}, U32{WCon{False{}, WCon{False{}, ri}}}, hlt))))
    case False{} False{} False{} True{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(2n, 0n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, False{}, False{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{False{}, WCon{True{}, rj}}}), Nat.add(0n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{False{}, WCon{True{}, rj}}}, U32{WCon{False{}, WCon{False{}, ri}}}, hlt))))
    case False{} False{} True{} False{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(1n, 0n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, False{}, True{}, False{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{False{}, rj}}}), Nat.add(0n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{False{}, rj}}}, U32{WCon{False{}, WCon{False{}, ri}}}, hlt))))
    case False{} False{} True{} True{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(3n, 0n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, False{}, True{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{True{}, rj}}}), Nat.add(0n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{True{}, rj}}}, U32{WCon{False{}, WCon{False{}, ri}}}, hlt))))
    case False{} True{} False{} False{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{True{}, ri}}}), BP.shv(False{}, True{}), BP.sh_val(False{}, True{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}}), BP.shv(False{}, False{}), BP.sh_val(False{}, False{}, rj)) :
        {BP.ext(BP.ins(w, 16n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 16n, 0n, v, {==}, {==})
    case False{} True{} False{} True{}:
      P.Cmp.eq_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{True{}, ri}}}), v), B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(2n, 2n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, True{}, False{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{False{}, WCon{True{}, rj}}}), Nat.add(2n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{False{}, WCon{True{}, rj}}}, U32{WCon{False{}, WCon{True{}, ri}}}, hlt))))
    case False{} True{} True{} False{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{True{}, ri}}}), BP.shv(False{}, True{}), BP.sh_val(False{}, True{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}}), BP.shv(True{}, False{}), BP.sh_val(True{}, False{}, rj)) :
        {BP.ext(BP.ins(w, 16n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 8n, 8n, v, {==}, {==})
    case False{} True{} True{} True{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{False{}, WCon{True{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(3n, 2n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, False{}, True{}, True{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{True{}, rj}}}), Nat.add(2n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{True{}, rj}}}, U32{WCon{False{}, WCon{True{}, ri}}}, hlt))))
    case True{} False{} False{} False{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{False{}, ri}}}), BP.shv(True{}, False{}), BP.sh_val(True{}, False{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}}), BP.shv(False{}, False{}), BP.sh_val(False{}, False{}, rj)) :
        {BP.ext(BP.ins(w, 8n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 8n, 0n, v, {==}, {==})
    case True{} False{} False{} True{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{True{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(2n, 1n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, True{}, False{}, False{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{False{}, WCon{True{}, rj}}}), Nat.add(1n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{False{}, WCon{True{}, rj}}}, U32{WCon{True{}, WCon{False{}, ri}}}, hlt))))
    case True{} False{} True{} False{}:
      P.Cmp.eq_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{True{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(1n, 1n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, True{}, False{}, True{}, False{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{False{}, rj}}}), Nat.add(1n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{False{}, rj}}}, U32{WCon{True{}, WCon{False{}, ri}}}, hlt))))
    case True{} False{} True{} True{}:
      P.Cmp.gt_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{True{}, WCon{False{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(3n, 1n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, True{}, False{}, True{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{True{}, rj}}}), Nat.add(1n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{True{}, rj}}}, U32{WCon{True{}, WCon{False{}, ri}}}, hlt))))
    case True{} True{} False{} False{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{True{}, ri}}}), BP.shv(True{}, True{}), BP.sh_val(True{}, True{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{False{}, rj}}}), BP.shv(False{}, False{}), BP.sh_val(False{}, False{}, rj)) :
        {BP.ext(BP.ins(w, 24n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 24n, 0n, v, {==}, {==})
    case True{} True{} False{} True{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{True{}, ri}}}), BP.shv(True{}, True{}), BP.sh_val(True{}, True{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{False{}, WCon{True{}, rj}}}), BP.shv(False{}, True{}), BP.sh_val(False{}, True{}, rj)) :
        {BP.ext(BP.ins(w, 24n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 8n, 16n, v, {==}, {==})
    case True{} True{} True{} False{}:
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{True{}, ri}}}), BP.shv(True{}, True{}), BP.sh_val(True{}, True{}, ri)) :
        {BP.ext(BP.ins(w, _, v), B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}})) : U32}
      %Equal.sym(Nat, B.B.sh(U32{WCon{True{}, WCon{False{}, rj}}}), BP.shv(True{}, False{}), BP.sh_val(True{}, False{}, rj)) :
        {BP.ext(BP.ins(w, 24n, v), _) == BP.ext(w, _) : U32}
      BP.lane_below(w, 16n, 8n, v, {==}, {==})
    case True{} True{} True{} True{}:
      P.Cmp.eq_lt({BP.ext(BP.ins(w, B.B.sh(U32{WCon{True{}, WCon{True{}, ri}}}), v), B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) == BP.ext(w, B.B.sh(U32{WCon{True{}, WCon{True{}, rj}}})) : U32},
        (%P.Nat.cmp_add_rr(3n, 3n, Nat.double(Nat.double(Word.to_nat(30n, rj)))) : {_ == LT{} : Cmp}
          (%BP.lane_lt.hi(ri, rj, True{}, True{}, True{}, True{}, ew) :
            {Nat.cmp(V.U.N(U32{WCon{True{}, WCon{True{}, rj}}}), Nat.add(3n, Nat.double(Nat.double(_)))) == LT{} : Cmp}
            V.U.lt_N(U32{WCon{True{}, WCon{True{}, rj}}}, U32{WCon{True{}, WCon{True{}, ri}}}, hlt))))

def BP.lane_lt(w, v, i, j, hlt, ew):
  match i j:
    case U32{WCon{a0, WCon{a1, ri}}} U32{WCon{c0, WCon{c1, rj}}}:
      BP.lane_lt.go(w, v, a0, a1, ri, c0, c1, rj, hlt, ew)

# Frames
# ======

# The word of a byte below one in range is in range.
law BP.wj_lt:
  for +d: Nat
  for +i: U32
  for +j: U32
  for +hi: {U32.is_lt(U32.shrn(i, 2n), U32.shln(1, d)) == True{} : Bool}
  for +hji: {U32.is_lt(j, i) == True{} : Bool}
  {U32.is_lt(U32.shrn(j, 2n), U32.shln(1, d)) == True{} : Bool}

def BP.wj_lt(d, i, j, hi, hji):
  V.U.N_lt(U32.shrn(j, 2n), U32.shln(1, d),
    P.Nat.le_lt_trans(V.U.N(U32.shrn(j, 2n)), V.U.N(U32.shrn(i, 2n)), V.U.N(U32.shln(1, d)),
      (%Equal.sym(Nat, V.U.N(U32.shr(U32.shr(i))), P.Nat.half(V.U.N(U32.shr(i))), V.U.N_shr(U32.shr(i))) :
          {Cmp.is_le(Nat.cmp(V.U.N(U32.shr(U32.shr(j))), _)) == True{} : Bool}
        (%Equal.sym(Nat, V.U.N(U32.shr(U32.shr(j))), P.Nat.half(V.U.N(U32.shr(j))), V.U.N_shr(U32.shr(j))) :
            {Cmp.is_le(Nat.cmp(_, P.Nat.half(V.U.N(U32.shr(i))))) == True{} : Bool}
          (%Equal.sym(Nat, V.U.N(U32.shr(i)), P.Nat.half(V.U.N(i)), V.U.N_shr(i)) :
              {Cmp.is_le(Nat.cmp(P.Nat.half(V.U.N(U32.shr(j))), P.Nat.half(_))) == True{} : Bool}
            (%Equal.sym(Nat, V.U.N(U32.shr(j)), P.Nat.half(V.U.N(j)), V.U.N_shr(j)) :
                {Cmp.is_le(Nat.cmp(P.Nat.half(_), P.Nat.half(P.Nat.half(V.U.N(i))))) == True{} : Bool}
              P.Nat.half_mono(P.Nat.half(V.U.N(j)), P.Nat.half(V.U.N(i)),
                P.Nat.half_mono(V.U.N(j), V.U.N(i), P.Nat.lt_to_le(V.U.N(j), V.U.N(i), V.U.lt_N(j, i, hji)))))))),
      V.U.lt_N(U32.shrn(i, 2n), U32.shln(1, d), hi)))

law BP.byt_put_lt.go:
  for +d: Nat
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +v: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(U32.shrn(i, 2n), U32.shln(1, d)) == True{} : Bool}
  for +hji: {U32.is_lt(j, i) == True{} : Bool}
  for +z: Bool
  for +e: {U32.is_eq(U32.shrn(i, 2n), U32.shrn(j, 2n)) == z : Bool}
  {BP.byt(BP.put(t, i, v), j) == BP.byt(t, j) : U32}

def BP.byt_put_lt.go(d, t, i, j, v, hp, hd, hi, hji, z, e):
  match z:
    case True{}:
      %V.U.is_eq(U32.shrn(i, 2n), U32.shrn(j, 2n), e) :
        {BP.ext(A.T.word(A.T.set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v)), _), B.B.sh(j))
          == BP.ext(A.T.word(t, U32.shrn(j, 2n)), B.B.sh(j)) : U32}
      %Equal.sym(U32, A.T.word(A.T.set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v)), U32.shrn(i, 2n)),
        BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v),
        A.T.word_set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v))) :
        {BP.ext(_, B.B.sh(j)) == BP.ext(A.T.word(t, U32.shrn(j, 2n)), B.B.sh(j)) : U32}
      %V.U.is_eq(U32.shrn(i, 2n), U32.shrn(j, 2n), e) :
        {BP.ext(BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v), B.B.sh(j))
          == BP.ext(A.T.word(t, _), B.B.sh(j)) : U32}
      BP.lane_lt(A.T.word(t, U32.shrn(i, 2n)), v, i, j, hji, V.U.is_eq(U32.shrn(i, 2n), U32.shrn(j, 2n), e))
    case False{}:
      %Equal.sym(U32, A.T.word(A.T.set(t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v)), U32.shrn(j, 2n)),
        A.T.word(t, U32.shrn(j, 2n)),
        A.T.word_other(d, t, U32.shrn(i, 2n), U32.shrn(j, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v),
          hp, hd, hi, BP.wj_lt(d, i, j, hi, hji), e)) :
        {BP.ext(_, B.B.sh(j)) == BP.ext(A.T.word(t, U32.shrn(j, 2n)), B.B.sh(j)) : U32}
      {==}

# A write at i leaves every byte below i (in a perfect tree, i in range).
law BP.byt_put_lt:
  for +d: Nat
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +v: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hi: {U32.is_lt(U32.shrn(i, 2n), U32.shln(1, d)) == True{} : Bool}
  for +hji: {U32.is_lt(j, i) == True{} : Bool}
  {BP.byt(BP.put(t, i, v), j) == BP.byt(t, j) : U32}

def BP.byt_put_lt(d, t, i, j, v, hp, hd, hi, hji):
  BP.byt_put_lt.go(d, t, i, j, v, hp, hd, hi, hji, U32.is_eq(U32.shrn(i, 2n), U32.shrn(j, 2n)), {==})

# A byte write keeps the tree perfect.
law BP.pf_put:
  for +d: Nat
  for +t: A.Tr
  for +i: U32
  for +v: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {A.T.pf(d, BP.put(t, i, v)) == True{} : Bool}

def BP.pf_put(d, t, i, v, hp):
  A.T.pf_set(d, t, U32.shrn(i, 2n), BP.ins(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i), v), hp)

# A byte below e, where e <= 4 * 2^d, is in a tree of depth d.
law BP.in_range:
  for +d: Nat
  for +q: U32
  for +e: U32
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))))) == True{} : Bool}
  for +hq: {Nat.cmp(V.U.N(q), V.U.N(e)) == LT{} : Cmp}
  {U32.is_lt(U32.shrn(q, 2n), U32.shln(1, d)) == True{} : Bool}

def BP.in_range(d, q, e, hd, he, hq):
  V.U.N_lt(U32.shrn(q, 2n), U32.shln(1, d),
    (%Equal.sym(Nat, V.U.N(U32.shln(1, d)), P.Nat.pow2(d), V.U.N_pow(d, hd)) : {Nat.cmp(V.U.N(U32.shr(U32.shr(q))), _) == LT{} : Cmp}
      (%Equal.sym(Nat, V.U.N(U32.shr(U32.shr(q))), P.Nat.half(V.U.N(U32.shr(q))), V.U.N_shr(U32.shr(q))) :
          {Nat.cmp(_, P.Nat.pow2(d)) == LT{} : Cmp}
        (%Equal.sym(Nat, V.U.N(U32.shr(q)), P.Nat.half(V.U.N(q)), V.U.N_shr(q)) :
            {Nat.cmp(P.Nat.half(_), P.Nat.pow2(d)) == LT{} : Cmp}
          P.Nat.half_lt(P.Nat.half(V.U.N(q)), P.Nat.pow2(d),
            P.Nat.half_lt(V.U.N(q), Nat.double(P.Nat.pow2(d)),
              P.Nat.lt_le_trans(V.U.N(q), V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))), hq, he)))))))

# A byte is below 256.
law BP.byt_255:
  for +t: A.Tr
  for +i: U32
  {U32.and(BP.byt(t, i), 255) == BP.byt(t, i) : U32}

def BP.byt_255(t, i):
  V.U.and_idem_r(U32.shrn(A.T.word(t, U32.shrn(i, 2n)), B.B.sh(i)), 255)
