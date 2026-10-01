import Base
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V

# U32.mod (Base's long division) leaves a remainder below the divisor, for
# divisors below 2^31.
#
# Source: proofs/umod.bp (tools/bpp.py writes proofs/umod.bend from it).

# Shifting a bit in: the top bit out, and the word shifted.
law UM.shlo:
  for +p: Nat
  for +c: Bool
  for +w: Word(1n+p)
  {Word.shl.out(1n+p, c, w) == (W.W.top(p, w), Word.shl.put(1n+p, c, w)) : Bool & Word(1n+p)}

def UM.shlo(p, c, w):
  match p w:
    case 0n WCon{b, t}:
      {==}
    case 1n+q WCon{b, t}:
      %Equal.sym(Bool & Word(1n+q), Word.shl.out(1n+q, b, t), (W.W.top(q, t), Word.shl.put(1n+q, b, t)), UM.shlo(q, b, t)) :
        {Word.shl.out.con(1n+q, c, _) == (W.W.top(1n+q, WCon{b, t}), WCon{c, Word.shl.put(1n+q, b, t)}) : Bool & Word.Con<1n+q>}
      {==}

law UM.rec:
  for +p: Nat
  for +a0: Bool
  for +b: U32
  for qr: Word(p) & U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hr: {Nat.cmp(V.U.N(Pair.snd(Word(p), U32, qr)), V.U.N(b)) == LT{} : Cmp}
  {Nat.cmp(V.U.N(Pair.snd(Word(1n+p), U32, U32.divmod.go.rec(p, a0, b, qr))), V.U.N(b)) == LT{} : Cmp}

law UM.rec.r:
  for +p: Nat
  for +a0: Bool
  for +b: U32
  for +q: Word(p)
  for +r: U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hr: {Nat.cmp(V.U.N(r), V.U.N(b)) == LT{} : Cmp}
  {Nat.cmp(V.U.N(Pair.snd(Word(1n+p), U32, U32.divmod.go.rec(p, a0, b, (q, r)))), V.U.N(b)) == LT{} : Cmp}

# A remainder below b < 2^31 has its top bit clear.
law UM.top0:
  for +rw: Word(32n)
  for +b: U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hr: {Nat.cmp(V.U.N(U32{rw}), V.U.N(b)) == LT{} : Cmp}
  {W.W.top(31n, rw) == False{} : Bool}

def UM.top0(rw, b, hb, hr):
  V.U.bit_lt_pow(U32{rw}, 31n, 31n, V.U.N_lt(U32{rw}, 2147483648, P.Nat.lt_trans(V.U.N(U32{rw}), V.U.N(b), V.U.N(2147483648), hr, V.U.lt_N(b, 2147483648, hb))), {==}, {==})

law UM.fin:
  for +p: Nat
  for +q: Word(p)
  for +a0: Bool
  for +rw: Word(32n)
  for +b: U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hr: {Nat.cmp(V.U.N(U32{rw}), V.U.N(b)) == LT{} : Cmp}
  for +c: Bool
  for +ec: {U32.is_ge(U32{Word.shl.put(32n, a0, rw)}, b) == c : Bool}
  {Nat.cmp(V.U.N(Pair.snd(Word(1n+p), U32, U32.divmod.go.fin(p, q, U32{Word.shl.put(32n, a0, rw)}, b, c))), V.U.N(b)) == LT{} : Cmp}

law UM.cge:
  for +c: Cmp
  for +h: {Cmp.is_ge(c) == False{} : Bool}
  {Cmp.is_lt(c) == True{} : Bool}

def UM.cge(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      P.Bool.true_false({Cmp.is_lt(EQ{}) == True{} : Bool}, h)
    case GT{}:
      P.Bool.true_false({Cmp.is_lt(GT{}) == True{} : Bool}, h)

# A bit shifted in below x < y stays below 2y.
law UM.dl:
  for +x: Nat
  for +y: Nat
  for +c: Bool
  for +h: {Nat.cmp(x, y) == LT{} : Cmp}
  {Nat.cmp(Nat.add(P.Nat.bit(c), Nat.double(x)), Nat.double(y)) == LT{} : Cmp}

def UM.dl(x, y, c, h):
  match x y c:
    case _ 0n _:
      P.Nat.lt_zero({Nat.cmp(Nat.add(P.Nat.bit(c), Nat.double(x)), Nat.double(0n)) == LT{} : Cmp}, x, h)
    case 0n 1n+q True{}:
      {==}
    case 0n 1n+q False{}:
      {==}
    case 1n+p 1n+q True{}:
      UM.dl(p, q, True{}, h)
    case 1n+p 1n+q False{}:
      UM.dl(p, q, False{}, h)

def UM.fin(p, q, a0, rw, b, hb, hr, c, ec):
  match c:
    case True{}:
      %P.Nat.cmp_add_rr(V.U.N(U32.sub(U32{Word.shl.put(32n, a0, rw)}, b)), V.U.N(b), V.U.N(b)) :
        {_ == LT{} : Cmp}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(U32{Word.shl.put(32n, a0, rw)}, b)), V.U.N(b)), V.U.N(U32{Word.shl.put(32n, a0, rw)}), V.U.sub_nat(U32{Word.shl.put(32n, a0, rw)}, b, V.U.ge_le(U32{Word.shl.put(32n, a0, rw)}, b, ec))) :
        {Nat.cmp(_, Nat.add(V.U.N(b), V.U.N(b))) == LT{} : Cmp}
      %Equal.sym(Nat, Word.to_nat(32n, Word.shl.put(32n, a0, rw)), Nat.add(P.Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), W.W.N_put(31n, a0, rw, UM.top0(rw, b, hb, hr))) :
        {Nat.cmp(_, Nat.add(V.U.N(b), V.U.N(b))) == LT{} : Cmp}
      %P.Nat.double_add(V.U.N(b)) :
        {Nat.cmp(Nat.add(P.Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), _) == LT{} : Cmp}
      UM.dl(Word.to_nat(32n, rw), V.U.N(b), a0, hr)
    case False{}:
      V.U.lt_N(U32{Word.shl.put(32n, a0, rw)}, b, UM.cge(U32.cmp(U32{Word.shl.put(32n, a0, rw)}, b), ec))

def UM.rec.r(p, a0, b, q, r, hb, hr):
  match r:
    case U32{rw}:
      %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (W.W.top(31n, rw), Word.shl.put(32n, a0, rw)), UM.shlo(31n, a0, rw)) :
        {Nat.cmp(V.U.N(Pair.snd(Word(1n+p), U32, U32.divmod.go.shl(p, q, b, _))), V.U.N(b)) == LT{} : Cmp}
      %Equal.sym(Bool, W.W.top(31n, rw), False{}, UM.top0(rw, b, hb, hr)) :
        {Nat.cmp(V.U.N(Pair.snd(Word(1n+p), U32, U32.divmod.go.fin(p, q, U32{Word.shl.put(32n, a0, rw)}, b, Bool.or(_, U32.is_ge(U32{Word.shl.put(32n, a0, rw)}, b))))), V.U.N(b)) == LT{} : Cmp}
      UM.fin(p, q, a0, rw, b, hb, hr, U32.is_ge(U32{Word.shl.put(32n, a0, rw)}, b), {==})

def UM.rec(p, a0, b, qr, hb, hr):
  match qr:
    case Tuple{q, r}:
      UM.rec.r(p, a0, b, q, r, hb, hr)

law UM.go:
  for +m: Nat
  for +a: Word(m)
  for +b: U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hb0: {Nat.cmp(0n, V.U.N(b)) == LT{} : Cmp}
  {Nat.cmp(V.U.N(Pair.snd(Word(m), U32, U32.divmod.go(m, a, b))), V.U.N(b)) == LT{} : Cmp}

def UM.go(m, a, b, hb, hb0):
  match m a:
    case 0n WNil{}:
      hb0
    case 1n+p WCon{a0, hi}:
      UM.rec(p, a0, b, U32.divmod.go(p, hi, b), hb, UM.go(p, hi, b, hb, hb0))

law UM.fin_snd:
  for qr: Word(32n) & U32
  {U32.mod.fin(qr) == Pair.snd(Word(32n), U32, qr) : U32}

def UM.fin_snd(qr):
  match qr:
    case Tuple{q, r}:
      {==}

law UM.nz:
  for +b: U32
  for +hb0: {Nat.cmp(0n, V.U.N(b)) == LT{} : Cmp}
  for +c: Bool
  for +ec: {U32.is_eq(b, 0) == c : Bool}
  {U32.is_eq(b, 0) == False{} : Bool}

def UM.nz(b, hb0, c, ec):
  match c:
    case True{}:
      P.Bool.false_true({U32.is_eq(b, 0) == False{} : Bool}, (%V.U.is_eq(b, 0, ec) : {Cmp.is_lt(Nat.cmp(0n, V.U.N(_))) == True{} : Bool}; (%Equal.sym(Cmp, Nat.cmp(0n, V.U.N(b)), LT{}, hb0) : {Cmp.is_lt(_) == True{} : Bool}; {==})))
    case False{}:
      ec

# The remainder of a division by 0 < b < 2^31 is below b.
law UM.mod:
  for +a: U32
  for +b: U32
  for +hb: {U32.is_lt(b, 2147483648) == True{} : Bool}
  for +hb0: {Nat.cmp(0n, V.U.N(b)) == LT{} : Cmp}
  {Nat.cmp(V.U.N(U32.mod(a, b)), V.U.N(b)) == LT{} : Cmp}

def UM.mod(a, b, hb, hb0):
  match a b:
    case U32{aw} U32{bw}:
      %Equal.sym(Bool, U32.is_eq(U32{bw}, 0), False{}, UM.nz(U32{bw}, hb0, U32.is_eq(U32{bw}, 0), {==})) :
        {Nat.cmp(V.U.N(U32.mod.if(aw, U32{bw}, _)), V.U.N(U32{bw})) == LT{} : Cmp}
      %Equal.sym(U32, U32.mod.fin(U32.divmod.go(32n, aw, U32{bw})), Pair.snd(Word(32n), U32, U32.divmod.go(32n, aw, U32{bw})), UM.fin_snd(U32.divmod.go(32n, aw, U32{bw}))) :
        {Nat.cmp(V.U.N(_), V.U.N(U32{bw})) == LT{} : Cmp}
      UM.go(32n, aw, U32{bw}, hb, hb0)
