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

# The delta's capacity, its depth and the empty tree it starts from.
def F.cap(+len: U32) -> U32:
  ((len + 1 : U32) << 4n : U32)

def F.dep(+len: U32) -> Nat:
  B.B.depth(B.B.words(F.cap(len)))

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
