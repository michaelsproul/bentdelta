import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ../encode.bend as N
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./bits.bend as Z
import ./words.bend as K
import ./copy.bend as C
import ./varint.bend as R
import ./spec.bend as Q
import ./sem.bend as M
import ./dec.bend as X

# The encoder's emitter (encode.bend) writes the three sections of a window
# as the spec (proofs/spec) reads them: each emitter step is mirrored by a
# function on trees, and the mirror keeps the sections, the cache and the
# target position in step with the instructions written so far.
#
# Source: proofs/emit.bp (tools/bpp.py writes proofs/emit.bend from it).

# Sections
# ========

law EM.add0:
  for +p: U32
  {U32.add(0, p) == p : U32}

def EM.add0(p):
  %Equal.sym(U32, U32.add(0, p), U32.add(p, 0), V.U.add_comm(0, p)) :
    {_ == p : U32}
  %Equal.sym(U32, U32.add(p, 0), p, V.U.add_zero_r(p)) :
    {_ == p : U32}
  {==}

# Writing ys after the L a tree holds: it holds L then ys.
law EM.sec:
  for +d: Nat
  for +L: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: A.Tr
  for +p: U32
  for +e: U32
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(d))))) == True{} : Bool}
  for +hl: {V.U.N(p) == S.S.len(L) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), S.S.len(ys)), V.U.N(e))) == True{} : Bool}
  for +h: {S.S.has(L, t, 0) == True{} : Bool}
  {S.S.has(K.WD.app(L, ys), S.S.puts(ys, t, p), 0) == True{} : Bool}

def EM.sec(d, L, ys, t, p, e, hp, hd, he, hl, hb, h):
  %Equal.sym(Bool, S.S.has(K.WD.app(L, ys), S.S.puts(ys, t, p), 0), Bool.and(S.S.has(L, S.S.puts(ys, t, p), 0), S.S.has(ys, S.S.puts(ys, t, p), U32.add(0, p))), K.WD.has_app(L, ys, S.S.puts(ys, t, p), 0, p, hl)) :
    {_ == True{} : Bool}
  %Equal.sym(U32, U32.add(0, p), p, EM.add0(p)) :
    {Bool.and(S.S.has(L, S.S.puts(ys, t, p), 0), S.S.has(ys, S.S.puts(ys, t, p), _)) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(L, S.S.puts(ys, t, p), 0), S.S.has(L, t, 0), S.S.has_puts_lt(d, L, t, p, ys, 0, e, hp, hd, he, hb, (%Equal.sym(Nat, V.U.N(p), S.S.len(L), hl) : {Cmp.is_le(Nat.cmp(S.S.len(L), _)) == True{} : Bool}; C.CP.le_refl(S.S.len(L))))) :
    {Bool.and(_, S.S.has(ys, S.S.puts(ys, t, p), p)) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(ys, S.S.puts(ys, t, p), p), True{}, S.S.has_puts(d, ys, t, p, e, hp, hd, he, hb)) :
    {Bool.and(S.S.has(L, t, 0), _) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(L, t, 0), True{}, h) :
    {Bool.and(_, True{}) == True{} : Bool}
  {==}

# Growing
# =======

# The size B.grow doubles to.
def GR.n2(+need: U32) -> U32:
  B.u32.pick((need < 1073741824 : U32), (need << 1n : U32), need)

# B.grow on a tree: the tree, or a bigger one holding its first used bytes.
def GR.t(+t: A.Tr, +used: U32, +need: U32) -> A.Tr:
  Bool.pick(A.Tr, U32.is_le(B.B.words(need), A.T.size(t)), t,
    S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))

# Its depth, when t has depth d.
def GR.d(+t: A.Tr, +used: U32, +need: U32, +d: Nat) -> Nat:
  Bool.pick(Nat, U32.is_le(B.B.words(need), A.T.size(t)), d, B.B.depth(B.B.words(GR.n2(need))))

law GR.b0:
  for +used: U32
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(used), V.U.N(0)), V.U.N(used))) == True{} : Bool}

def GR.b0(used):
  %Equal.sym(Nat, Nat.add(V.U.N(used), 0n), V.U.N(used), P.Nat.add_zero_r(V.U.N(used))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(used))) == True{} : Bool}
  C.CP.le_refl(V.U.N(used))

law GR.code.c:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +c: Bool
  for +ec: {U32.is_le(B.B.words(need), A.T.size(t)) == c : Bool}
  {B.B.grow.if(c, A.A.from(t), used, need) == A.A.from(GR.t(t, used, need)) : Array<U32>}

def GR.code.c(t, used, need, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), True{}, ec) :
        {B.B.grow.if(True{}, A.A.from(t), used, need) == A.A.from(Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))) : Array<U32>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), False{}, ec) :
        {B.B.grow.if(False{}, A.A.from(t), used, need) == A.A.from(Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))) : Array<U32>}
      %Equal.sym(Array<U32>, Array.new(U32, B.B.depth(B.B.words(GR.n2(need))), 0), A.A.from(A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0)), A.A.new_from(B.B.depth(B.B.words(GR.n2(need))), 0)) :
        {B.B.grow.k(B.B.copy(_, 0, A.A.from(t), 0, used)) == A.A.from(S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0)) : Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy(A.A.from(A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0)), 0, A.A.from(t), 0, used), (A.A.from(t), A.A.from(S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))), C.CP.copy(A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0, t, 0, used, used, GR.b0(used), GR.b0(used))) :
        {B.B.grow.k(_) == A.A.from(S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0)) : Array<U32>}
      {==}

law GR.code:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  {B.B.grow(A.A.from(t), used, need) == A.A.from(GR.t(t, used, need)) : Array<U32>}

def GR.code(t, used, need):
  %Equal.sym(Array<U32> & U32, Array.size(U32, A.A.from(t)), (A.A.from(t), A.T.size(t)), A.A.size_from(t)) :
    {B.B.grow.go(used, need, _) == A.A.from(GR.t(t, used, need)) : Array<U32>}
  GR.code.c(t, used, need, U32.is_le(B.B.words(need), A.T.size(t)), {==})

law GR.pf.c:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_le(B.B.words(need), A.T.size(t)) == c : Bool}
  {A.T.pf(GR.d(t, used, need, d), GR.t(t, used, need)) == True{} : Bool}

def GR.pf.c(t, used, need, d, hp, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), True{}, ec) :
        {A.T.pf(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need)))), Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))) == True{} : Bool}
      hp
    case False{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), False{}, ec) :
        {A.T.pf(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need)))), Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0))) == True{} : Bool}
      S.S.pf_puts(B.B.depth(B.B.words(GR.n2(need))), S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0, A.T.pf_new(B.B.depth(B.B.words(GR.n2(need))), 0))

# The grown tree is perfect.
law GR.pf:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  {A.T.pf(GR.d(t, used, need, d), GR.t(t, used, need)) == True{} : Bool}

def GR.pf(t, used, need, d, hp):
  GR.pf.c(t, used, need, d, hp, U32.is_le(B.B.words(need), A.T.size(t)), {==})

law GR.lt.c:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +c: Bool
  for +ec: {U32.is_le(B.B.words(need), A.T.size(t)) == c : Bool}
  {Nat.cmp(GR.d(t, used, need, d), 32n) == LT{} : Cmp}

def GR.lt.c(t, used, need, d, hd, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), True{}, ec) :
        {Nat.cmp(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need)))), 32n) == LT{} : Cmp}
      hd
    case False{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), False{}, ec) :
        {Nat.cmp(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need)))), 32n) == LT{} : Cmp}
      Y.BD.lt(B.B.words(GR.n2(need)))

law GR.lt:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  {Nat.cmp(GR.d(t, used, need, d), 32n) == LT{} : Cmp}

def GR.lt(t, used, need, d, hd):
  GR.lt.c(t, used, need, d, hd, U32.is_le(B.B.words(need), A.T.size(t)), {==})

# The words of n bytes, as a value.
law GR.Nw:
  for +n: U32
  for +hn: {U32.is_lt(n, 2147483648) == True{} : Bool}
  {V.U.N(B.B.words(n)) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(n), 3n))) : Nat}

def GR.Nw(n, hn):
  %Equal.sym(Nat, V.U.N(U32.shr(U32.shr((n + 3 : U32)))), P.Nat.half(V.U.N(U32.shr((n + 3 : U32)))),
    V.U.N_shr(U32.shr((n + 3 : U32)))) :
    {_ == P.Nat.half(P.Nat.half(Nat.add(V.U.N(n), 3n))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shr((n + 3 : U32))), P.Nat.half(V.U.N((n + 3 : U32))), V.U.N_shr((n + 3 : U32))) :
    {P.Nat.half(_) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(n), 3n))) : Nat}
  %Equal.sym(Nat, V.U.N((n + 3 : U32)), Nat.add(V.U.N(n), V.U.N(3)),
    V.U.add_top(n, 3, V.U.bit_lt_pow(n, 31n, 31n, hn, {==}, {==}), {==})) :
    {P.Nat.half(P.Nat.half(_)) == P.Nat.half(P.Nat.half(Nat.add(V.U.N(n), 3n))) : Nat}
  {==}

law GR.lw:
  for +n: U32
  for +hn: {U32.is_lt(n, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(n), Nat.double(Nat.double(V.U.N(B.B.words(n)))))) == True{} : Bool}

def GR.lw(n, hn):
  %Equal.sym(Nat, V.U.N(B.B.words(n)), P.Nat.half(P.Nat.half(Nat.add(V.U.N(n), 3n))), GR.Nw(n, hn)) :
    {Cmp.is_le(Nat.cmp(V.U.N(n), Nat.double(Nat.double(_)))) == True{} : Bool}
  P.Nat.le_words(V.U.N(n))

law GR.le_dbl:
  for +x: Nat
  {Cmp.is_le(Nat.cmp(x, Nat.double(x))) == True{} : Bool}

def GR.le_dbl(x):
  %Equal.sym(Nat, Nat.double(x), Nat.add(x, x), P.Nat.double_add(x)) :
    {Cmp.is_le(Nat.cmp(x, _)) == True{} : Bool}
  P.Nat.cmp_add_r(x, x)

# Words are below 2^30.
law GR.wb:
  for +n: U32
  {U32.is_le(B.B.words(n), U32.shln(1, 31n)) == True{} : Bool}

def GR.wb(n):
  V.U.lt_to_le(B.B.words(n), U32.shln(1, 31n),
    V.U.lt_of_top(B.B.words(n), U32.shln(1, 31n),
      (%Equal.sym(Bool, V.U.bit(U32.shr(U32.shr((n + 3 : U32))), 31n),
          V.U.bit(U32.shr((n + 3 : U32)), 32n), V.U.bit_shr(U32.shr((n + 3 : U32)), 31n)) :
          {_ == False{} : Bool}
        V.U.bit_beyond(U32.shr((n + 3 : U32)), 32n, {==})),
      {==}))

law GR.n2.c:
  for +need: U32
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(need, 1073741824) == c : Bool}
  {Bool.and(Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(GR.n2(need)))), U32.is_lt(GR.n2(need), 2147483648)) == True{} : Bool}

def GR.n2.c(need, hn, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_lt(need, 1073741824), True{}, ec) :
        {Bool.and(Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(B.u32.pick(_, U32.shln(need, 1n), need)))), U32.is_lt(B.u32.pick(_, U32.shln(need, 1n), need), 2147483648)) == True{} : Bool}
      %Equal.sym(Nat, V.U.N(U32.shl(need)), Nat.double(V.U.N(need)), V.U.N_shl(need, V.U.bit_lt_pow(need, 30n, 31n, ec, {==}, {==}))) :
        {Bool.and(Cmp.is_le(Nat.cmp(V.U.N(need), _)), U32.is_lt(U32.shl(need), 2147483648)) == True{} : Bool}
      %Equal.sym(Bool, Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(V.U.N(need)))), True{}, GR.le_dbl(V.U.N(need))) :
        {Bool.and(_, U32.is_lt(U32.shl(need), 2147483648)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(U32.shl(need), 2147483648), True{}, V.U.lt_of_top(U32.shl(need), U32.shln(1, 31n), (%Equal.sym(Bool, V.U.bit(U32.shl(need), 31n), V.U.bit(need, 30n), V.U.bit_shl(need, 30n, {==})) : {_ == False{} : Bool}; V.U.bit_lt_pow(need, 30n, 30n, ec, {==}, {==})), {==})) :
        {Bool.and(True{}, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_lt(need, 1073741824), False{}, ec) :
        {Bool.and(Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(B.u32.pick(_, U32.shln(need, 1n), need)))), U32.is_lt(B.u32.pick(_, U32.shln(need, 1n), need), 2147483648)) == True{} : Bool}
      %Equal.sym(Bool, Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(need))), True{}, C.CP.le_refl(V.U.N(need))) :
        {Bool.and(_, U32.is_lt(need, 2147483648)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(need, 2147483648), True{}, hn) :
        {Bool.and(True{}, _) == True{} : Bool}
      {==}

law GR.n2_ge:
  for +need: U32
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(GR.n2(need)))) == True{} : Bool}

def GR.n2_ge(need, hn):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(GR.n2(need)))), U32.is_lt(GR.n2(need), 2147483648), GR.n2.c(need, hn, U32.is_lt(need, 1073741824), {==}))

law GR.n2_lt:
  for +need: U32
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  {U32.is_lt(GR.n2(need), 2147483648) == True{} : Bool}

def GR.n2_lt(need, hn):
  P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(need), V.U.N(GR.n2(need)))), U32.is_lt(GR.n2(need), 2147483648), GR.n2.c(need, hn, U32.is_lt(need, 1073741824), {==}))

law GR.dd2:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(a)), Nat.double(Nat.double(b)))) == True{} : Bool}

def GR.dd2(a, b, h):
  P.Nat.double_mono(Nat.double(a), Nat.double(b), P.Nat.double_mono(a, b, h))

# A new tree of the doubled size holds need bytes.
law GR.capF:
  for +need: U32
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(Nat.double(P.Nat.pow2(B.B.depth(B.B.words(GR.n2(need)))))))) == True{} : Bool}

def GR.capF(need, hn):
  P.Nat.le_trans(V.U.N(need), V.U.N(GR.n2(need)), Nat.double(Nat.double(P.Nat.pow2(B.B.depth(B.B.words(GR.n2(need)))))), GR.n2_ge(need, hn),
    P.Nat.le_trans(V.U.N(GR.n2(need)), Nat.double(Nat.double(V.U.N(B.B.words(GR.n2(need))))), Nat.double(Nat.double(P.Nat.pow2(B.B.depth(B.B.words(GR.n2(need)))))),
      GR.lw(GR.n2(need), GR.n2_lt(need, hn)),
      GR.dd2(V.U.N(B.B.words(GR.n2(need))), P.Nat.pow2(B.B.depth(B.B.words(GR.n2(need)))),
        (%V.U.N_pow(B.B.depth(B.B.words(GR.n2(need))), Y.BD.lt(B.B.words(GR.n2(need)))) : {Cmp.is_le(Nat.cmp(V.U.N(B.B.words(GR.n2(need))), _)) == True{} : Bool};
          V.U.le_N(B.B.words(GR.n2(need)), U32.shln(1, B.B.depth(B.B.words(GR.n2(need)))), Y.BD.le(B.B.words(GR.n2(need)), GR.wb(GR.n2(need))))))))

law GR.cap.c:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_le(B.B.words(need), A.T.size(t)) == c : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(Nat.double(P.Nat.pow2(GR.d(t, used, need, d)))))) == True{} : Bool}

def GR.cap.c(t, used, need, d, hp, hd, hn, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), True{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(Nat.double(P.Nat.pow2(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need))))))))) == True{} : Bool}
      P.Nat.le_trans(V.U.N(need), Nat.double(Nat.double(V.U.N(B.B.words(need)))), Nat.double(Nat.double(P.Nat.pow2(d))), GR.lw(need, hn),
        GR.dd2(V.U.N(B.B.words(need)), P.Nat.pow2(d),
          (%V.U.N_pow(d, hd) : {Cmp.is_le(Nat.cmp(V.U.N(B.B.words(need)), _)) == True{} : Bool};
            (%A.T.size_pf(d, t, hp) : {Cmp.is_le(Nat.cmp(V.U.N(B.B.words(need)), V.U.N(_))) == True{} : Bool};
              V.U.le_N(B.B.words(need), A.T.size(t), ec)))))
    case False{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), False{}, ec) :
        {Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(Nat.double(P.Nat.pow2(Bool.pick(Nat, _, d, B.B.depth(B.B.words(GR.n2(need))))))))) == True{} : Bool}
      GR.capF(need, hn)

# The grown tree holds need bytes.
law GR.cap:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(need), Nat.double(Nat.double(P.Nat.pow2(GR.d(t, used, need, d)))))) == True{} : Bool}

def GR.cap(t, used, need, d, hp, hd, hn):
  GR.cap.c(t, used, need, d, hp, hd, hn, U32.is_le(B.B.words(need), A.T.size(t)), {==})

law GR.keep.c:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +L: List<&2, U32>
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  for +hl: {S.S.len(L) == V.U.N(used) : Nat}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(need))) == True{} : Bool}
  for +h: {S.S.has(L, t, 0) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_le(B.B.words(need), A.T.size(t)) == c : Bool}
  {S.S.has(L, GR.t(t, used, need), 0) == True{} : Bool}

def GR.keep.c(t, used, need, L, hn, hl, hu, h, c, ec):
  match c:
    case True{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), True{}, ec) :
        {S.S.has(L, Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0)), 0) == True{} : Bool}
      h
    case False{}:
      %Equal.sym(Bool, U32.is_le(B.B.words(need), A.T.size(t)), False{}, ec) :
        {S.S.has(L, Bool.pick(A.Tr, _, t, S.S.puts(S.S.sl(V.U.N(used), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0)), 0) == True{} : Bool}
      %hl :
        {S.S.has(L, S.S.puts(S.S.sl(_, t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0), 0) == True{} : Bool}
      %Equal.sym(A.Tr, S.S.puts(S.S.sl(S.S.len(L), t, 0), A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0), S.S.puts(L, A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0), X.DX.puts_held(L, [], t, 0, A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0, (%Equal.sym(List<&2, U32>, K.WD.app(L, []), L, K.WD.app_nil(L)) : {S.S.has(_, t, 0) == True{} : Bool}; h))) :
        {S.S.has(L, _, 0) == True{} : Bool}
      S.S.has_puts(B.B.depth(B.B.words(GR.n2(need))), L, A.T.new(B.B.depth(B.B.words(GR.n2(need))), 0), 0, need, A.T.pf_new(B.B.depth(B.B.words(GR.n2(need))), 0), Y.BD.lt(B.B.words(GR.n2(need))), GR.capF(need, hn),
        (%Equal.sym(Nat, S.S.len(L), V.U.N(used), hl) : {Cmp.is_le(Nat.cmp(_, V.U.N(need))) == True{} : Bool}; hu))

# The grown tree keeps the bytes it held.
law GR.keep:
  for +t: A.Tr
  for +used: U32
  for +need: U32
  for +L: List<&2, U32>
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  for +hl: {S.S.len(L) == V.U.N(used) : Nat}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(need))) == True{} : Bool}
  for +h: {S.S.has(L, t, 0) == True{} : Bool}
  {S.S.has(L, GR.t(t, used, need), 0) == True{} : Bool}

def GR.keep(t, used, need, L, hn, hl, hu, h):
  GR.keep.c(t, used, need, L, hn, hl, hu, h, U32.is_le(B.B.words(need), A.T.size(t)), {==})
