import Base
import ../bytes.bend as B
import ../check.bend as C
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S

# The plain encoding (check.bend's fallback) writes a fixed list of bytes:
# the header, then nine bytes for each target byte (or one empty window).

# The bytes
# =========

# The window for the target byte x, before r.
def F.win(+x: U32, +r: List<&2, U32>) -> List<&2, U32>:
  0 <> 7 <> 1 <> 0 <> 1 <> 1 <> 0 <> x <> 2 <> r

def F.wins(+xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case []:
      []
    case x <> r:
      F.win(x, F.wins(r))

# The file header, before r.
def F.hdr(+r: List<&2, U32>) -> List<&2, U32>:
  214 <> 195 <> 196 <> 0 <> 0 <> r

# The window of an empty target.
def F.empty() -> List<&2, U32>:
  0 <> 5 <> 0 <> 0 <> 0 <> 0 <> 0 <> []

# The writes
# ==========

# Writing the bytes xs, a wr.byte each.
def F.wrs(+xs: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & U32:
  match xs:
    case []:
      r
    case x <> t:
      F.wrs(t, C.wr.byte(x, r))

law F.wr1:
  for +v: U32
  for +t: A.Tr
  for +p: U32
  {C.wr.byte(v, (A.A.from(t), p)) == (A.A.from(Y.BP.put(t, p, v)), (p + 1 : U32)) : Array<U32> & U32}

def F.wr1(v, t, p):
  %Equal.sym(Array<U32>, B.B.put(A.A.from(t), p, v), A.A.from(Y.BP.put(t, p, v)), Y.BP.put_from(t, p, v)) :
    {(_, (p + 1 : U32)) == (A.A.from(Y.BP.put(t, p, v)), (p + 1 : U32)) : Array<U32> & U32}
  {==}

law F.wrs_from:
  for +xs: List<&2, U32>
  for +t: A.Tr
  for +p: U32
  {F.wrs(xs, (A.A.from(t), p)) == (A.A.from(S.S.puts(xs, t, p)), S.S.adv(xs, p)) : Array<U32> & U32}

def F.wrs_from(xs, t, p):
  match xs:
    case []:
      {==}
    case x <> r:
      %Equal.sym(Array<U32> & U32, C.wr.byte(x, (A.A.from(t), p)), (A.A.from(Y.BP.put(t, p, x)), (p + 1 : U32)),
        F.wr1(x, t, p)) :
        {F.wrs(r, _) == (A.A.from(S.S.puts(r, Y.BP.put(t, p, x), (p + 1 : U32))), S.S.adv(r, (p + 1 : U32)))
          : Array<U32> & U32}
      F.wrs_from(r, Y.BP.put(t, p, x), (p + 1 : U32))

# The windows for k target bytes from w.
law F.loop_from:
  for +k: Nat
  for +tt: A.Tr
  for +w: U32
  for +td: A.Tr
  for +p: U32
  {C.fb.loop(k, w, (A.A.from(tt), (A.A.from(td), p)))
    == (A.A.from(tt), (A.A.from(S.S.puts(F.wins(S.S.sl(k, tt, w)), td, p)), S.S.adv(F.wins(S.S.sl(k, tt, w)), p)))
    : Array<U32> & (Array<U32> & U32)}

def F.loop_from(k, tt, w, td, p):
  match k:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), w), (A.A.from(tt), Y.BP.byt(tt, w)), Y.BP.get_from(tt, w)) :
        {C.fb.loop(m, (w + 1 : U32), C.fb.win.k((A.A.from(td), p), _))
          == (A.A.from(tt), (A.A.from(S.S.puts(F.wins(S.S.sl(1n+m, tt, w)), td, p)), S.S.adv(F.wins(S.S.sl(1n+m, tt, w)), p)))
          : Array<U32> & (Array<U32> & U32)}
      %Equal.sym(Array<U32> & U32, F.wrs(F.win(Y.BP.byt(tt, w), []), (A.A.from(td), p)),
        (A.A.from(S.S.puts(F.win(Y.BP.byt(tt, w), []), td, p)), S.S.adv(F.win(Y.BP.byt(tt, w), []), p)),
        F.wrs_from(F.win(Y.BP.byt(tt, w), []), td, p)) :
        {C.fb.loop(m, (w + 1 : U32), (A.A.from(tt), _))
          == (A.A.from(tt), (A.A.from(S.S.puts(F.wins(S.S.sl(1n+m, tt, w)), td, p)), S.S.adv(F.wins(S.S.sl(1n+m, tt, w)), p)))
          : Array<U32> & (Array<U32> & U32)}
      F.loop_from(m, tt, (w + 1 : U32), S.S.puts(F.win(Y.BP.byt(tt, w), []), td, p),
        S.S.adv(F.win(Y.BP.byt(tt, w), []), p))

# The whole encoding
# ==================

# The delta's capacity in bytes, its depth and the empty tree it starts from.
def F.cap(+len: U32) -> U32:
  ((len + 1 : U32) << 4n : U32)

def F.dep(+len: U32) -> Nat:
  B.B.depth(((len + 1 : U32) << 2n : U32))

def F.t0(+len: U32) -> A.Tr:
  A.T.new(F.dep(len), 0)

law F.spec:
  for +len: U32
  for +tt: A.Tr
  {C.fallback(B.Bytes{len, A.A.from(tt)})
    == C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt),
      (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)))
    : B.Bytes & B.Bytes}

def F.spec(len, tt):
  %Equal.sym(Array<U32>, Array.new(U32, F.dep(len), 0), A.A.from(F.t0(len)), A.A.new_from(F.dep(len), 0)) :
    {C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt), F.wrs(F.hdr([]), (_, 0))))
      == C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt),
        (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)))
      : B.Bytes & B.Bytes}
  %Equal.sym(Array<U32> & U32, F.wrs(F.hdr([]), (A.A.from(F.t0(len)), 0)),
    (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), S.S.adv(F.hdr([]), 0)),
    F.wrs_from(F.hdr([]), F.t0(len), 0)) :
    {C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt), _))
      == C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt),
        (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)))
      : B.Bytes & B.Bytes}
  {==}

# A nonempty target: a window per byte.
law F.spec1:
  for +len: U32
  for +tt: A.Tr
  for +z: {U32.is_eq(len, 0) == False{} : Bool}
  {C.fallback(B.Bytes{len, A.A.from(tt)})
    == (B.Bytes{len, A.A.from(tt)},
      B.Bytes{S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5),
        A.A.from(S.S.puts(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0))})
    : B.Bytes & B.Bytes}

def F.spec1(len, tt, z):
  %Equal.sym(B.Bytes & B.Bytes, C.fallback(B.Bytes{len, A.A.from(tt)}),
    C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5))),
    F.spec(len, tt)) :
    {_ == (B.Bytes{len, A.A.from(tt)},
      B.Bytes{S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5),
        A.A.from(S.S.puts(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  %Equal.sym(Bool, U32.is_eq(len, 0), False{}, z) :
    {C.fb.done(len, C.fb.body(_, len, A.A.from(tt), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)))
      == (B.Bytes{len, A.A.from(tt)},
        B.Bytes{S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5),
          A.A.from(S.S.puts(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  %Equal.sym(Array<U32> & (Array<U32> & U32),
    C.fb.loop(U32.to_nat(len), 0, (A.A.from(tt), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5))),
    (A.A.from(tt), (A.A.from(S.S.puts(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), S.S.puts(F.hdr([]), F.t0(len), 0), 5)),
      S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5))),
    F.loop_from(U32.to_nat(len), tt, 0, S.S.puts(F.hdr([]), F.t0(len), 0), 5)) :
    {C.fb.done(len, _)
      == (B.Bytes{len, A.A.from(tt)},
        B.Bytes{S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5),
          A.A.from(S.S.puts(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  {==}

# An empty target: one empty window.
law F.spec0:
  for +len: U32
  for +tt: A.Tr
  for +z: {U32.is_eq(len, 0) == True{} : Bool}
  {C.fallback(B.Bytes{len, A.A.from(tt)})
    == (B.Bytes{len, A.A.from(tt)}, B.Bytes{12, A.A.from(S.S.puts(F.hdr(F.empty()), F.t0(len), 0))})
    : B.Bytes & B.Bytes}

def F.spec0(len, tt, z):
  %Equal.sym(B.Bytes & B.Bytes, C.fallback(B.Bytes{len, A.A.from(tt)}),
    C.fb.done(len, C.fb.body(U32.is_eq(len, 0), len, A.A.from(tt), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5))),
    F.spec(len, tt)) :
    {_ == (B.Bytes{len, A.A.from(tt)}, B.Bytes{12, A.A.from(S.S.puts(F.hdr(F.empty()), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  %Equal.sym(Bool, U32.is_eq(len, 0), True{}, z) :
    {C.fb.done(len, C.fb.body(_, len, A.A.from(tt), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)))
      == (B.Bytes{len, A.A.from(tt)}, B.Bytes{12, A.A.from(S.S.puts(F.hdr(F.empty()), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  %Equal.sym(Array<U32> & U32, F.wrs(F.empty(), (A.A.from(S.S.puts(F.hdr([]), F.t0(len), 0)), 5)),
    (A.A.from(S.S.puts(F.empty(), S.S.puts(F.hdr([]), F.t0(len), 0), 5)), S.S.adv(F.empty(), 5)),
    F.wrs_from(F.empty(), S.S.puts(F.hdr([]), F.t0(len), 0), 5)) :
    {C.fb.done(len, (A.A.from(tt), _))
      == (B.Bytes{len, A.A.from(tt)}, B.Bytes{12, A.A.from(S.S.puts(F.hdr(F.empty()), F.t0(len), 0))})
      : B.Bytes & B.Bytes}
  {==}

# Sizes
# =====

def F.d4(+n: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(n))))

# Nine bytes per byte are at most sixteen.
law F.len_wins:
  for +n: Nat
  for +tt: A.Tr
  for +w: U32
  {Cmp.is_le(Nat.cmp(S.S.len(F.wins(S.S.sl(n, tt, w))), F.d4(n))) == True{} : Bool}

def F.len_wins(n, tt, w):
  match n:
    case 0n:
      {==}
    case 1n+m:
      P.Nat.le_trans(S.S.len(F.wins(S.S.sl(m, tt, (w + 1 : U32)))), F.d4(m), Nat.add(7n, F.d4(m)),
        F.len_wins(m, tt, (w + 1 : U32)), P.Nat.le_add_l(7n, F.d4(m)))

law F.len_le:
  for +n: Nat
  for +tt: A.Tr
  for +w: U32
  {Cmp.is_le(Nat.cmp(Nat.add(5n, S.S.len(F.wins(S.S.sl(n, tt, w)))), F.d4(1n+n))) == True{} : Bool}

def F.len_le(n, tt, w):
  P.Nat.le_trans(S.S.len(F.wins(S.S.sl(n, tt, w))), F.d4(n), Nat.add(11n, F.d4(n)),
    F.len_wins(n, tt, w), P.Nat.le_add_l(11n, F.d4(n)))

# At least one byte per byte.
law F.len_ge:
  for +n: Nat
  for +tt: A.Tr
  for +w: U32
  {Cmp.is_le(Nat.cmp(n, S.S.len(F.wins(S.S.sl(n, tt, w))))) == True{} : Bool}

def F.len_ge(n, tt, w):
  match n:
    case 0n:
      {==}
    case 1n+m:
      P.Nat.le_trans(m, S.S.len(F.wins(S.S.sl(m, tt, (w + 1 : U32)))),
        Nat.add(8n, S.S.len(F.wins(S.S.sl(m, tt, (w + 1 : U32))))),
        F.len_ge(m, tt, (w + 1 : U32)), P.Nat.le_add_l(8n, S.S.len(F.wins(S.S.sl(m, tt, (w + 1 : U32))))))

# len + 1 (len < 2^27) is below 2^28.
law F.x1_lt:
  for +len: U32
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {U32.is_lt((len + 1 : U32), U32.shln(1, 28n)) == True{} : Bool}

def F.x1_lt(len, hlen):
  V.U.le_lt_trans((len + 1 : U32), 134217728, U32.shln(1, 28n), V.U.lt_succ_le(len, 134217728, hlen), {==})

law F.x1_bit:
  for +len: U32
  for +k: Nat
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(28n, k)) == True{} : Bool}
  {V.U.bit((len + 1 : U32), k) == False{} : Bool}

def F.x1_bit(len, k, hlen, hk):
  V.U.bit_lt_pow((len + 1 : U32), 28n, k, F.x1_lt(len, hlen), {==}, hk)

# The value of a U32 shifted up once, then twice, with the bits it loses clear.
law F.N_shl2:
  for +x: U32
  for +h31: {V.U.bit(x, 31n) == False{} : Bool}
  for +h30: {V.U.bit(x, 30n) == False{} : Bool}
  {V.U.N(U32.shl(U32.shl(x))) == Nat.double(Nat.double(V.U.N(x))) : Nat}

def F.N_shl2(x, h31, h30):
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shl(x))), Nat.double(V.U.N(U32.shl(x))),
    V.U.N_shl(U32.shl(x), (%Equal.sym(Bool, V.U.bit(U32.shl(x), 31n), V.U.bit(x, 30n), V.U.bit_shl(x, 30n, {==})) :
        {_ == False{} : Bool}
      h30))) :
    {_ == Nat.double(Nat.double(V.U.N(x))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(x)), Nat.double(V.U.N(x)), V.U.N_shl(x, h31)) :
    {Nat.double(_) == Nat.double(Nat.double(V.U.N(x))) : Nat}
  {==}

# The words of the delta: 4 (len + 1).
def F.w(+len: U32) -> U32:
  ((len + 1 : U32) << 2n : U32)

law F.Nw:
  for +len: U32
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {V.U.N(F.w(len)) == Nat.double(Nat.double(1n+V.U.N(len))) : Nat}

def F.Nw(len, hlen):
  %V.U.succ_lt(len, 134217728, hlen) :
    {V.U.N(F.w(len)) == Nat.double(Nat.double(_)) : Nat}
  F.N_shl2((len + 1 : U32), F.x1_bit(len, 31n, hlen, {==}), F.x1_bit(len, 30n, hlen, {==}))

law F.Ncap:
  for +len: U32
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {V.U.N(F.cap(len)) == F.d4(1n+V.U.N(len)) : Nat}

def F.Ncap(len, hlen):
  %F.Nw(len, hlen) :
    {V.U.N(F.cap(len)) == Nat.double(Nat.double(_)) : Nat}
  F.N_shl2(F.w(len),
    (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shl((len + 1 : U32))), 31n), V.U.bit((len + 1 : U32), 29n),
        V.U.bit_shln_hi((len + 1 : U32), 2n, 29n, {==})) : {_ == False{} : Bool}
      F.x1_bit(len, 29n, hlen, {==})),
    (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shl((len + 1 : U32))), 30n), V.U.bit((len + 1 : U32), 28n),
        V.U.bit_shln_hi((len + 1 : U32), 2n, 28n, {==})) : {_ == False{} : Bool}
      F.x1_bit(len, 28n, hlen, {==})))

law F.w_le:
  for +len: U32
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {U32.is_le(F.w(len), U32.shln(1, 31n)) == True{} : Bool}

def F.w_le(len, hlen):
  V.U.lt_to_le(F.w(len), U32.shln(1, 31n),
    V.U.lt_of_top(F.w(len), U32.shln(1, 31n),
      (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shl((len + 1 : U32))), 31n), V.U.bit((len + 1 : U32), 29n),
          V.U.bit_shln_hi((len + 1 : U32), 2n, 29n, {==})) : {_ == False{} : Bool}
        F.x1_bit(len, 29n, hlen, {==})),
      {==}))

# The capacity fits the tree.
law F.he:
  for +len: U32
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(F.cap(len)), Nat.double(Nat.double(P.Nat.pow2(F.dep(len)))))) == True{} : Bool}

def F.he(len, hlen):
  %Equal.sym(Nat, V.U.N(F.cap(len)), Nat.double(Nat.double(V.U.N(F.w(len)))),
    F.N_shl2(F.w(len),
      (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shl((len + 1 : U32))), 31n), V.U.bit((len + 1 : U32), 29n),
          V.U.bit_shln_hi((len + 1 : U32), 2n, 29n, {==})) : {_ == False{} : Bool}
        F.x1_bit(len, 29n, hlen, {==})),
      (%Equal.sym(Bool, V.U.bit(U32.shl(U32.shl((len + 1 : U32))), 30n), V.U.bit((len + 1 : U32), 28n),
          V.U.bit_shln_hi((len + 1 : U32), 2n, 28n, {==})) : {_ == False{} : Bool}
        F.x1_bit(len, 28n, hlen, {==})))) :
    {Cmp.is_le(Nat.cmp(_, Nat.double(Nat.double(P.Nat.pow2(F.dep(len)))))) == True{} : Bool}
  P.Nat.double_mono(Nat.double(V.U.N(F.w(len))), Nat.double(P.Nat.pow2(F.dep(len))),
    P.Nat.double_mono(V.U.N(F.w(len)), P.Nat.pow2(F.dep(len)),
      (%V.U.N_pow(F.dep(len), Y.BD.lt(F.w(len))) : {Cmp.is_le(Nat.cmp(V.U.N(F.w(len)), _)) == True{} : Bool}
        V.U.le_N(F.w(len), U32.shln(1, F.dep(len)), Y.BD.le(F.w(len), F.w_le(len, hlen))))))

# The plain encoding fits its capacity.
law F.hb:
  for +len: U32
  for +tt: A.Tr
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(0), S.S.len(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))))), V.U.N(F.cap(len))))
    == True{} : Bool}

def F.hb(len, tt, hlen):
  %Equal.sym(Nat, V.U.N(F.cap(len)), F.d4(1n+V.U.N(len)), F.Ncap(len, hlen)) :
    {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(0), S.S.len(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))))), _)) == True{} : Bool}
  F.len_le(U32.to_nat(len), tt, 0)

# The delta holds the plain encoding.
law F.has:
  for +len: U32
  for +tt: A.Tr
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {S.S.has(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))),
    S.S.puts(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0), 0) == True{} : Bool}

def F.has(len, tt, hlen):
  S.S.has_puts(F.dep(len), F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), F.t0(len), 0, F.cap(len),
    A.T.pf_new(F.dep(len), 0), Y.BD.lt(F.w(len)), F.he(len, hlen), F.hb(len, tt, hlen))

# Its length.
law F.dl:
  for +len: U32
  for +tt: A.Tr
  for +hlen: {U32.is_lt(len, 134217728) == True{} : Bool}
  {V.U.N(S.S.adv(F.wins(S.S.sl(U32.to_nat(len), tt, 0)), 5))
    == Nat.add(5n, S.S.len(F.wins(S.S.sl(U32.to_nat(len), tt, 0)))) : Nat}

def F.dl(len, tt, hlen):
  S.S.adv_N(F.hdr(F.wins(S.S.sl(U32.to_nat(len), tt, 0))), 0, F.cap(len), F.hb(len, tt, hlen))
