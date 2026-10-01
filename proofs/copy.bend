import Base
import ../bytes.bend as B
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./bits.bend as Z
import ./words.bend as D

# Copying, filling and moving bytes (bytes.bend), as lists of bytes written
# into trees: B.copy writes the source's bytes, B.fill copies of a byte,
# and B.move a forward copy within one array.
#
# Source: proofs/copy.bp (tools/bpp.py writes proofs/copy.bend from it).

# A byte at a time
# ================

law CP.bytes:
  for +k: Nat
  for +t: A.Tr
  for +d: U32
  for +u: A.Tr
  for +s: U32
  {B.B.copy.bytes(k, A.A.from(t), d, s, (A.A.from(u), Y.BP.byt(u, s))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(k, u, s), t, d))) : Array<U32> & Array<U32>}

def CP.bytes(k, t, d, u, s):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, B.B.put(A.A.from(t), d, Y.BP.byt(u, s)), A.A.from(Y.BP.put(t, d, Y.BP.byt(u, s))), Y.BP.put_from(t, d, Y.BP.byt(u, s))) :
        {B.B.copy.bytes(p, _, U32.add(d, 1), U32.add(s, 1), B.B.get(A.A.from(u), U32.add(s, 1))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(p, u, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1)))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(u), U32.add(s, 1)), (A.A.from(u), Y.BP.byt(u, U32.add(s, 1))), Y.BP.get_from(u, U32.add(s, 1))) :
        {B.B.copy.bytes(p, A.A.from(Y.BP.put(t, d, Y.BP.byt(u, s))), U32.add(d, 1), U32.add(s, 1), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(p, u, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1)))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.bytes(p, A.A.from(Y.BP.put(t, d, Y.BP.byt(u, s))), U32.add(d, 1), U32.add(s, 1), (A.A.from(u), Y.BP.byt(u, U32.add(s, 1)))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(p, u, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1)))), CP.bytes(p, Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), u, U32.add(s, 1))) :
        {_ == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(p, u, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1)))) : Array<U32> & Array<U32>}
      {==}

# A word at a time
# ================

# The four bytes of the word read at s, s = m + 4 sw.
law CP.join:
  for +u: A.Tr
  for +s: U32
  for +sw: U32
  for +m: Nat
  for +E: U32
  for +es: {V.U.N(s) == Nat.add(m, Nat.double(Nat.double(V.U.N(sw)))) : Nat}
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {D.WD.w4(B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))))) == S.S.sl(4n, u, s) : List<&2, U32>}

def CP.join(u, s, sw, m, E, es, hm, hb):
  %D.WD.lane(s, sw, m, es, hm) :
    {D.WD.w4(B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), _)) == S.S.sl(4n, u, s) : List<&2, U32>}
  %D.WD.at(s, sw, m, es, hm) :
    {D.WD.w4(B.B.join(A.T.word(u, _), A.T.word(u, U32.add(_, 1)), B.B.sh(s))) == S.S.sl(4n, u, s) : List<&2, U32>}
  D.WD.join(u, s, E, hb)

law CP.le4:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Cmp.is_le(Nat.cmp(4n+Nat.add(a, b), c)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(4n, b), c)) == True{} : Bool}

def CP.le4(a, b, c, h):
  P.Nat.le_trans(Nat.add(4n, b), 4n+Nat.add(a, b), c, P.Nat.le_add_l(a, b), h)

# A word's index is below a bound past its byte position.
law CP.word_lt:
  for +x: U32
  for +w: U32
  for +E: U32
  for +m: Nat
  for +e: {V.U.N(x) == Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(x)), V.U.N(E))) == True{} : Bool}
  {Nat.cmp(V.U.N(w), V.U.N(E)) == LT{} : Cmp}

def CP.word_lt(x, w, E, m, e, hb):
  P.Nat.le_lt_trans(V.U.N(w), V.U.N(x), V.U.N(E),
    (%Equal.sym(Nat, V.U.N(x), Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), e) :
        {Cmp.is_le(Nat.cmp(V.U.N(w), _)) == True{} : Bool};
      D.WD.le_quad(m, V.U.N(w))),
    D.WD.lt4(V.U.N(x), V.U.N(E), 0n, {==}, hb))

# The next word's position: four bytes on, one word on.
law CP.next:
  for +x: U32
  for +w: U32
  for +E: U32
  for +m: Nat
  for +e: {V.U.N(x) == Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(x)), V.U.N(E))) == True{} : Bool}
  {V.U.N(D.WD.step(4n, x)) == Nat.add(m, Nat.double(Nat.double(V.U.N(U32.add(w, 1))))) : Nat}

def CP.next(x, w, E, m, e, hb):
  %Equal.sym(Nat, V.U.N(U32.add(w, 1)), 1n+V.U.N(w), V.U.succ_N(w, E, CP.word_lt(x, w, E, m, e, hb))) :
    {V.U.N(D.WD.step(4n, x)) == Nat.add(m, Nat.double(Nat.double(_))) : Nat}
  %Equal.sym(Nat, V.U.N(D.WD.step(4n, x)), 4n+V.U.N(x), D.WD.pos_4(x, E, hb)) :
    {_ == Nat.add(m, Nat.double(Nat.double(1n+V.U.N(w)))) : Nat}
  %Equal.sym(Nat, V.U.N(x), Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), e) :
    {4n+_ == Nat.add(m, Nat.double(Nat.double(1n+V.U.N(w)))) : Nat}
  %Equal.sym(Nat, Nat.add(m, 4n+Nat.double(Nat.double(V.U.N(w)))), 4n+Nat.add(m, Nat.double(Nat.double(V.U.N(w)))), D.WD.add4r(m, Nat.double(Nat.double(V.U.N(w))))) :
    {4n+Nat.add(m, Nat.double(Nat.double(V.U.N(w)))) == _ : Nat}
  {==}

# Whole words: n words from s (lane m of word sw) to the aligned position
# d (word dw).
law CP.words:
  for +n: Nat
  for +t: A.Tr
  for +dw: U32
  for +d: U32
  for +u: A.Tr
  for +sw: U32
  for +s: U32
  for +m: Nat
  for +E: U32
  for +ed: {V.U.N(d) == Nat.double(Nat.double(V.U.N(dw))) : Nat}
  for +es: {V.U.N(s) == Nat.add(m, Nat.double(Nat.double(V.U.N(sw)))) : Nat}
  for +hm: {Nat.cmp(m, 4n) == LT{} : Cmp}
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(n)), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(n)), V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {B.B.copy.words(n, A.A.from(t), dw, sw, Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), A.T.word(u, sw), (A.A.from(u), A.T.word(u, U32.add(sw, 1)))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(n)), u, s), t, d))) : Array<U32> & Array<U32>}

def CP.words(n, t, dw, d, u, sw, s, m, E, ed, es, hm, hd, hs):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(t), dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))))), A.A.from(A.T.set(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))))), A.A.set_from(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))))) :
        {B.B.copy.words(p, _, U32.add(dw, 1), U32.add(sw, 1), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), A.T.word(u, U32.add(sw, 1)), Array.get(U32, A.A.from(u), U32.add(U32.add(sw, 1), 1))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), Y.BP.byt(u, U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(u, U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(u, U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1)))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(u), U32.add(U32.add(sw, 1), 1)), (A.A.from(u), A.T.word(u, U32.add(U32.add(sw, 1), 1))), A.A.get_from(u, U32.add(U32.add(sw, 1), 1))) :
        {B.B.copy.words(p, A.A.from(A.T.set(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))))), U32.add(dw, 1), U32.add(sw, 1), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), A.T.word(u, U32.add(sw, 1)), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), Y.BP.byt(u, U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(u, U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(u, U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1)))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.words(p, A.A.from(A.T.set(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))))), U32.add(dw, 1), U32.add(sw, 1), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))), A.T.word(u, U32.add(sw, 1)), (A.A.from(u), A.T.word(u, U32.add(U32.add(sw, 1), 1)))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, D.WD.step(4n, s)), A.T.set(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))))), D.WD.step(4n, d)))), CP.words(p, A.T.set(t, dw, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))))), U32.add(dw, 1), D.WD.step(4n, d), u, U32.add(sw, 1), D.WD.step(4n, s), m, E, CP.next(d, dw, E, 0n, ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd)), CP.next(s, sw, E, m, es, CP.le4(Nat.double(Nat.double(p)), V.U.N(s), V.U.N(E), hs)), hm, (%Equal.sym(Nat, V.U.N(D.WD.step(4n, d)), 4n+V.U.N(d), D.WD.pos_4(d, E, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(p)), _), V.U.N(E))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.double(Nat.double(p)), 4n+V.U.N(d)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), D.WD.add4r(Nat.double(Nat.double(p)), V.U.N(d))) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hd)), (%Equal.sym(Nat, V.U.N(D.WD.step(4n, s)), 4n+V.U.N(s), D.WD.pos_4(s, E, CP.le4(Nat.double(Nat.double(p)), V.U.N(s), V.U.N(E), hs))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(p)), _), V.U.N(E))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.double(Nat.double(p)), 4n+V.U.N(s)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(s)), D.WD.add4r(Nat.double(Nat.double(p)), V.U.N(s))) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hs)))) :
        {_ == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), Y.BP.byt(u, U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(u, U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(u, U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1)))) : Array<U32> & Array<U32>}
      %D.WD.put4(t, d, dw, E, B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m)))), ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd)) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, D.WD.step(4n, s)), _, D.WD.step(4n, d)))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), Y.BP.byt(u, U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(u, U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(u, U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1)))) : Array<U32> & Array<U32>}
      %Equal.sym(List<&2, U32>, D.WD.w4(B.B.join(A.T.word(u, sw), A.T.word(u, U32.add(sw, 1)), Y.BP.shv(P.Nat.odd(m), P.Nat.odd(P.Nat.half(m))))), S.S.sl(4n, u, s), CP.join(u, s, sw, m, E, es, hm, CP.le4(Nat.double(Nat.double(p)), V.U.N(s), V.U.N(E), hs))) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, D.WD.step(4n, s)), S.S.puts(_, t, d), D.WD.step(4n, d)))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(p)), u, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(u, s)), U32.add(d, 1), Y.BP.byt(u, U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(u, U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(u, U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1)))) : Array<U32> & Array<U32>}
      {==}

# Alignment
# =========

# Nat sums: A + (d + X) <= E when A <= n', n' + X = n and n + d <= E.
law CP.bnd:
  for +A: Nat
  for +n1: Nat
  for +X: Nat
  for +n: Nat
  for +d: Nat
  for +E: Nat
  for +h1: {Cmp.is_le(Nat.cmp(A, n1)) == True{} : Bool}
  for +e: {Nat.add(n1, X) == n : Nat}
  for +h2: {Cmp.is_le(Nat.cmp(Nat.add(n, d), E)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(A, Nat.add(d, X)), E)) == True{} : Bool}

law CP.le_add_r:
  for +A: Nat
  for +n1: Nat
  for +Y: Nat
  for +h1: {Cmp.is_le(Nat.cmp(A, n1)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(A, Y), Nat.add(n1, Y))) == True{} : Bool}

def CP.le_add_r(A, n1, Y, h1):
  %Equal.sym(Nat, Nat.add(A, Y), Nat.add(Y, A), P.Nat.add_comm(A, Y)) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(n1, Y))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(n1, Y), Nat.add(Y, n1), P.Nat.add_comm(n1, Y)) :
    {Cmp.is_le(Nat.cmp(Nat.add(Y, A), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(Y, A), Nat.add(Y, n1)), Nat.cmp(A, n1), P.Nat.cmp_add_l(Y, A, n1)) :
    {Cmp.is_le(_) == True{} : Bool}
  h1

law CP.sum3:
  for +n1: Nat
  for +X: Nat
  for +n: Nat
  for +d: Nat
  for +e: {Nat.add(n1, X) == n : Nat}
  {Nat.add(n1, Nat.add(d, X)) == Nat.add(n, d) : Nat}

def CP.sum3(n1, X, n, d, e):
  %Equal.sym(Nat, Nat.add(d, X), Nat.add(X, d), P.Nat.add_comm(d, X)) :
    {Nat.add(n1, _) == Nat.add(n, d) : Nat}
  %P.Nat.add_assoc(n1, X, d) :
    {_ == Nat.add(n, d) : Nat}
  %Equal.sym(Nat, Nat.add(n1, X), n, e) :
    {Nat.add(_, d) == Nat.add(n, d) : Nat}
  {==}

law CP.bnd.r:
  for +n1: Nat
  for +X: Nat
  for +n: Nat
  for +d: Nat
  for +E: Nat
  for +e: {Nat.add(n1, X) == n : Nat}
  for +h2: {Cmp.is_le(Nat.cmp(Nat.add(n, d), E)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(n1, Nat.add(d, X)), E)) == True{} : Bool}

def CP.bnd.r(n1, X, n, d, E, e, h2):
  %Equal.sym(Nat, Nat.add(n1, Nat.add(d, X)), Nat.add(n, d), CP.sum3(n1, X, n, d, e)) :
    {Cmp.is_le(Nat.cmp(_, E)) == True{} : Bool}
  h2

def CP.bnd(A, n1, X, n, d, E, h1, e, h2):
  P.Nat.le_trans(Nat.add(A, Nat.add(d, X)), Nat.add(n1, Nat.add(d, X)), E,
    CP.le_add_r(A, n1, Nat.add(d, X), h1), CP.bnd.r(n1, X, n, d, E, e, h2))

law CP.align.k0:
  for +K: Nat
  {Nat.add(Nat.add(0n, Nat.double(Nat.double(K))), 0n) == Nat.double(Nat.double(K)) : Nat}

def CP.align.k0(K):
  P.Nat.add_zero_r(Nat.double(Nat.double(K)))

law CP.align.k1:
  for +K: Nat
  {Nat.add(Nat.add(1n, Nat.double(Nat.double(K))), 3n) == Nat.double(Nat.double(1n+K)) : Nat}

def CP.align.k1(K):
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 3n), 1n+Nat.add(Nat.double(Nat.double(K)), 2n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 2n)) :
    {1n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 2n), 1n+Nat.add(Nat.double(Nat.double(K)), 1n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 1n)) :
    {2n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 1n), 1n+Nat.add(Nat.double(Nat.double(K)), 0n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 0n)) :
    {3n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 0n), Nat.double(Nat.double(K)), P.Nat.add_zero_r(Nat.double(Nat.double(K)))) :
    {4n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  {==}

law CP.align.k2:
  for +K: Nat
  {Nat.add(Nat.add(2n, Nat.double(Nat.double(K))), 2n) == Nat.double(Nat.double(1n+K)) : Nat}

def CP.align.k2(K):
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 2n), 1n+Nat.add(Nat.double(Nat.double(K)), 1n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 1n)) :
    {2n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 1n), 1n+Nat.add(Nat.double(Nat.double(K)), 0n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 0n)) :
    {3n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 0n), Nat.double(Nat.double(K)), P.Nat.add_zero_r(Nat.double(Nat.double(K)))) :
    {4n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  {==}

law CP.align.k3:
  for +K: Nat
  {Nat.add(Nat.add(3n, Nat.double(Nat.double(K))), 1n) == Nat.double(Nat.double(1n+K)) : Nat}

def CP.align.k3(K):
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 1n), 1n+Nat.add(Nat.double(Nat.double(K)), 0n), P.Nat.add_succ_r(Nat.double(Nat.double(K)), 0n)) :
    {3n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(K)), 0n), Nat.double(Nat.double(K)), P.Nat.add_zero_r(Nat.double(Nat.double(K)))) :
    {4n+_ == 4n+Nat.double(Nat.double(K)) : Nat}
  {==}

# d + X, where X = (4 - (d & 3)) & 3 brings d up to a whole word.
law CP.align.go:
  for +d: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(E))) == True{} : Bool}
  for +o0: Bool
  for +o1: Bool
  for +eo0: {P.Nat.odd(V.U.N(d)) == o0 : Bool}
  for +eo1: {P.Nat.odd(P.Nat.half(V.U.N(d))) == o1 : Bool}
  {V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))) == Nat.double(Nat.double(V.U.N(U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))) : Nat}

def CP.align.go(d, E, hb, o0, o1, eo0, eo1):
  match o0 o1:
    case False{} False{}:
      D.WD.aligned(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.shrn(d, 2n)),
        (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, hb)) : {_ == Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(U32, U32.and(d, 3), 0, V.U.eq_N(U32.and(d, 3), 0, (%eo0 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(False{}))) : Nat}; (%eo1 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))) : Nat}; D.WD.lane_N(d))))) : {Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, _), 3))) == Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(Nat, V.U.N(d), Nat.add(Nat.add(P.Nat.bit(False{}), Nat.double(P.Nat.bit(False{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))), (%eo0 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(False{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; (%eo1 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; D.WD.split_lane(d)))) : {Nat.add(_, 0n) == Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n)))) : Nat}; CP.align.k0(V.U.N(U32.shrn(d, 2n)))))))
    case True{} False{}:
      D.WD.aligned(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 1n+V.U.N(U32.shrn(d, 2n)),
        (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, hb)) : {_ == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(U32, U32.and(d, 3), 1, V.U.eq_N(U32.and(d, 3), 1, (%eo0 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(False{}))) : Nat}; (%eo1 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))) : Nat}; D.WD.lane_N(d))))) : {Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, _), 3))) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(Nat, V.U.N(d), Nat.add(Nat.add(P.Nat.bit(True{}), Nat.double(P.Nat.bit(False{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))), (%eo0 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(False{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; (%eo1 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; D.WD.split_lane(d)))) : {Nat.add(_, 3n) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; CP.align.k1(V.U.N(U32.shrn(d, 2n)))))))
    case False{} True{}:
      D.WD.aligned(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 1n+V.U.N(U32.shrn(d, 2n)),
        (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, hb)) : {_ == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(U32, U32.and(d, 3), 2, V.U.eq_N(U32.and(d, 3), 2, (%eo0 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(True{}))) : Nat}; (%eo1 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))) : Nat}; D.WD.lane_N(d))))) : {Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, _), 3))) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(Nat, V.U.N(d), Nat.add(Nat.add(P.Nat.bit(False{}), Nat.double(P.Nat.bit(True{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))), (%eo0 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(True{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; (%eo1 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; D.WD.split_lane(d)))) : {Nat.add(_, 2n) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; CP.align.k2(V.U.N(U32.shrn(d, 2n)))))))
    case True{} True{}:
      D.WD.aligned(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 1n+V.U.N(U32.shrn(d, 2n)),
        (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, hb)) : {_ == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(U32, U32.and(d, 3), 3, V.U.eq_N(U32.and(d, 3), 3, (%eo0 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(True{}))) : Nat}; (%eo1 : {V.U.N(U32.and(d, 3)) == Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))) : Nat}; D.WD.lane_N(d))))) : {Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, _), 3))) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; (%Equal.sym(Nat, V.U.N(d), Nat.add(Nat.add(P.Nat.bit(True{}), Nat.double(P.Nat.bit(True{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))), (%eo0 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(_), Nat.double(P.Nat.bit(True{}))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; (%eo1 : {V.U.N(d) == Nat.add(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(d))), Nat.double(P.Nat.bit(_))), Nat.double(Nat.double(V.U.N(U32.shrn(d, 2n))))) : Nat}; D.WD.split_lane(d)))) : {Nat.add(_, 1n) == Nat.double(Nat.double(1n+V.U.N(U32.shrn(d, 2n)))) : Nat}; CP.align.k3(V.U.N(U32.shrn(d, 2n)))))))

law CP.align:
  for +d: U32
  for +E: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))) == Nat.double(Nat.double(V.U.N(U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))) : Nat}

def CP.align(d, E, hb):
  CP.align.go(d, E, hb, P.Nat.odd(V.U.N(d)), P.Nat.odd(P.Nat.half(V.U.N(d))), {==}, {==})

# Copying
# =======

# a + x <= e when a + n <= e and x <= n (as values).
law CP.le_part:
  for +a: Nat
  for +x: Nat
  for +n: Nat
  for +e: Nat
  for +h: {Cmp.is_le(Nat.cmp(x, n)) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(n, a), e)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(a, x), e)) == True{} : Bool}

def CP.le_part(a, x, n, e, h, hb):
  P.Nat.le_trans(Nat.add(a, x), Nat.add(n, a), e,
    (%P.Nat.add_comm(x, a) : {Cmp.is_le(Nat.cmp(_, Nat.add(n, a))) == True{} : Bool};
      CP.le_add_r(x, n, a, h)),
    hb)

law CP.copy.go:
  for +t: A.Tr
  for +d: U32
  for +u: A.Tr
  for +s: U32
  for +n: U32
  for +E: U32
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(s)), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)) == c : Bool}
  {B.B.copy(A.A.from(t), d, A.A.from(u), s, n) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}

def CP.copy.go(t, d, u, s, n, E, hd, hs, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.copy.body(U32.sub(n, _), U32.add(d, _), U32.add(s, _), B.B.copy.bytes(U32.to_nat(_), A.A.from(t), d, s, B.B.get(A.A.from(u), s))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), True{}, ec) :
        {B.B.copy.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(s, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), B.B.copy.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), A.A.from(t), d, s, B.B.get(A.A.from(u), s))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(u), s), (A.A.from(u), Y.BP.byt(u, s)), Y.BP.get_from(u, s)) :
        {B.B.copy.body(U32.sub(n, n), U32.add(d, n), U32.add(s, n), B.B.copy.bytes(V.U.N(n), A.A.from(t), d, s, _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.bytes(V.U.N(n), A.A.from(t), d, s, (A.A.from(u), Y.BP.byt(u, s))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))), CP.bytes(V.U.N(n), t, d, u, s)) :
        {B.B.copy.body(U32.sub(n, n), U32.add(d, n), U32.add(s, n), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(U32, U32.sub(n, n), 0, D.WD.sub_self(n)) :
        {B.B.copy.body(_, U32.add(d, n), U32.add(s, n), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d)))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(u), U32.shrn(U32.add(s, n), 2n)), (A.A.from(u), A.T.word(u, U32.shrn(U32.add(s, n), 2n))), A.A.get_from(u, U32.shrn(U32.add(s, n), 2n))) :
        {B.B.copy.tail(U32.and(0, 3), U32.add(U32.add(d, n), U32.shln(U32.shrn(0, 2n), 2n)), U32.add(U32.add(s, n), U32.shln(U32.shrn(0, 2n), 2n)), B.B.copy.body.k(U32.shrn(0, 2n), U32.add(d, n), U32.add(s, n), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d)), _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(u), U32.add(U32.shrn(U32.add(s, n), 2n), 1)), (A.A.from(u), A.T.word(u, U32.add(U32.shrn(U32.add(s, n), 2n), 1))), A.A.get_from(u, U32.add(U32.shrn(U32.add(s, n), 2n), 1))) :
        {B.B.copy.tail(U32.and(0, 3), U32.add(U32.add(d, n), U32.shln(U32.shrn(0, 2n), 2n)), U32.add(U32.add(s, n), U32.shln(U32.shrn(0, 2n), 2n)), B.B.copy.words(V.U.N(U32.shrn(0, 2n)), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d)), U32.shrn(U32.add(d, n), 2n), U32.shrn(U32.add(s, n), 2n), B.B.sh(U32.add(s, n)), A.T.word(u, U32.shrn(U32.add(s, n), 2n)), _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(u), U32.add(U32.add(s, n), 0)), (A.A.from(u), Y.BP.byt(u, U32.add(U32.add(s, n), 0))), Y.BP.get_from(u, U32.add(U32.add(s, n), 0))) :
        {B.B.copy.bytes(0n, A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d)), U32.add(U32.add(d, n), 0), U32.add(U32.add(s, n), 0), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      {==}
    case False{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.copy.body(U32.sub(n, _), U32.add(d, _), U32.add(s, _), B.B.copy.bytes(U32.to_nat(_), A.A.from(t), d, s, B.B.get(A.A.from(u), s))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), False{}, ec) :
        {B.B.copy.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(s, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), B.B.copy.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), A.A.from(t), d, s, B.B.get(A.A.from(u), s))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(u), s), (A.A.from(u), Y.BP.byt(u, s)), Y.BP.get_from(u, s)) :
        {B.B.copy.body(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), B.B.copy.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), A.A.from(t), d, s, _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), A.A.from(t), d, s, (A.A.from(u), Y.BP.byt(u, s))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d))), CP.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, u, s)) :
        {B.B.copy.body(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(u), U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), (A.A.from(u), A.T.word(u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))), A.A.get_from(u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))) :
        {B.B.copy.tail(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), B.B.copy.body.k(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d)), _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(u), U32.add(U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 1)), (A.A.from(u), A.T.word(u, U32.add(U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 1))), A.A.get_from(u, U32.add(U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 1))) :
        {B.B.copy.tail(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), B.B.copy.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d)), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), B.B.sh(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), A.T.word(u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), _)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Nat, B.B.sh(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))))))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))))))))), D.WD.sh_lane(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) :
        {B.B.copy.tail(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), B.B.copy.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d)), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), _, A.T.word(u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), (A.A.from(u), A.T.word(u, U32.add(U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 1))))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d)), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), Y.BP.shv(P.Nat.odd(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))))))), P.Nat.odd(P.Nat.half(Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))))))))), A.T.word(u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), (A.A.from(u), A.T.word(u, U32.add(U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 1)))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), CP.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, U32.shrn(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Nat.add(P.Nat.bit(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))))), Nat.double(P.Nat.bit(P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))))))), E, CP.align(d, E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd)), D.WD.split_lane(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), D.WD.lane_lt(P.Nat.odd(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), P.Nat.odd(P.Nat.half(V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))))), (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _), V.U.N(E))) == True{} : Bool}; CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(d), V.U.N(E), (%Equal.sym(Nat, V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _)) == True{} : Bool}; P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))))), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd)), (%Equal.sym(Nat, V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(s), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(s, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, CP.le_part(V.U.N(s), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hs))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _), V.U.N(E))) == True{} : Bool}; CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(s), V.U.N(E), (%Equal.sym(Nat, V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _)) == True{} : Bool}; P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))))), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hs)))) :
        {B.B.copy.tail(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(u), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))), (A.A.from(u), Y.BP.byt(u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))), Y.BP.get_from(u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))) :
        {B.B.copy.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), _) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), A.A.from(S.S.puts(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), (A.A.from(u), Y.BP.byt(u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))))), (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))), S.S.puts(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))))), CP.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), S.S.puts(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))) :
        {_ == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %D.WD.puts_app(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.sl(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))), S.S.puts(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n), (%Equal.sym(Nat, S.S.len(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), S.S.len_sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) : {V.U.N(U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)) == _ : Nat}; D.WD.shl2(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) :
        {(A.A.from(u), A.A.from(_)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %D.WD.puts_app(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), D.WD.app(S.S.sl(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), S.S.sl(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), u, U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))), t, d, U32.and(U32.sub(4, U32.and(d, 3)), 3), Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s)), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), S.S.len_sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s))) :
        {(A.A.from(u), A.A.from(_)) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %D.WD.sl_app(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), u, U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n), D.WD.shl2(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) :
        {(A.A.from(u), A.A.from(S.S.puts(D.WD.app(S.S.sl(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), u, s), _), t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %D.WD.sl_app(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), u, s, U32.and(U32.sub(4, U32.and(d, 3)), 3), {==}) :
        {(A.A.from(u), A.A.from(S.S.puts(_, t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), P.Nat.add_comm(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)))) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), u, s), t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), u, s), t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), P.Nat.add_comm(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(_, u, s), t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(n), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec))) :
        {(A.A.from(u), A.A.from(S.S.puts(S.S.sl(_, u, s), t, d))) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}
      {==}

# Copying n bytes from s in one array to d in another writes them there.
law CP.copy:
  for +t: A.Tr
  for +d: U32
  for +u: A.Tr
  for +s: U32
  for +n: U32
  for +E: U32
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(s)), V.U.N(E))) == True{} : Bool}
  {B.B.copy(A.A.from(t), d, A.A.from(u), s, n) == (A.A.from(u), A.A.from(S.S.puts(S.S.sl(V.U.N(n), u, s), t, d))) : Array<U32> & Array<U32>}

def CP.copy(t, d, u, s, n, E, hd, hs):
  CP.copy.go(t, d, u, s, n, E, hd, hs, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), {==})

# Filling
# =======

# n copies of v.
def CP.rep(+n: Nat, +v: U32) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      v <> CP.rep(p, v)

law CP.len_rep:
  for +n: Nat
  for +v: U32
  {S.S.len(CP.rep(n, v)) == n : Nat}

def CP.len_rep(n, v):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, S.S.len(CP.rep(p, v)), p, CP.len_rep(p, v)) :
        {1n+_ == 1n+p : Nat}
      {==}

law CP.rep_app:
  for +a: Nat
  for +b: Nat
  for +v: U32
  {CP.rep(Nat.add(a, b), v) == D.WD.app(CP.rep(a, v), CP.rep(b, v)) : List<&2, U32>}

def CP.rep_app(a, b, v):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, U32>, CP.rep(Nat.add(p, b), v), D.WD.app(CP.rep(p, v), CP.rep(b, v)), CP.rep_app(p, b, v)) :
        {v <> _ == v <> D.WD.app(CP.rep(p, v), CP.rep(b, v)) : List<&2, U32>}
      {==}

# A byte is written as its low eight bits.
law CP.put_mask:
  for +t: A.Tr
  for +i: U32
  for +v: U32
  {Y.BP.put(t, i, U32.and(v, 255)) == Y.BP.put(t, i, v) : A.Tr}

def CP.put_mask(t, i, v):
  %Equal.sym(U32, U32.and(U32.and(v, 255), 255), U32.and(v, 255), Z.BB.and255(v)) :
    {A.T.set(t, U32.shrn(i, 2n), U32.or(U32.and(A.T.word(t, U32.shrn(i, 2n)), U32.not(U32.shln(255, B.B.sh(i)))), U32.shln(_, B.B.sh(i)))) == A.T.set(t, U32.shrn(i, 2n), U32.or(U32.and(A.T.word(t, U32.shrn(i, 2n)), U32.not(U32.shln(255, B.B.sh(i)))), U32.shln(U32.and(v, 255), B.B.sh(i)))) : A.Tr}
  {==}

law CP.fbytes:
  for +k: Nat
  for +t: A.Tr
  for +d: U32
  for +v: U32
  {B.B.fill.bytes(k, A.A.from(t), d, v) == A.A.from(S.S.puts(CP.rep(k, v), t, d)) : Array<U32>}

def CP.fbytes(k, t, d, v):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, B.B.put(A.A.from(t), d, v), A.A.from(Y.BP.put(t, d, v)), Y.BP.put_from(t, d, v)) :
        {B.B.fill.bytes(p, _, U32.add(d, 1), v) == A.A.from(S.S.puts(CP.rep(p, v), Y.BP.put(t, d, v), U32.add(d, 1))) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.bytes(p, A.A.from(Y.BP.put(t, d, v)), U32.add(d, 1), v), A.A.from(S.S.puts(CP.rep(p, v), Y.BP.put(t, d, v), U32.add(d, 1))), CP.fbytes(p, Y.BP.put(t, d, v), U32.add(d, 1), v)) :
        {_ == A.A.from(S.S.puts(CP.rep(p, v), Y.BP.put(t, d, v), U32.add(d, 1))) : Array<U32>}
      {==}

# The four bytes of a word of copies of v, written, are copies of v.
law CP.rep4_put:
  for +t: A.Tr
  for +d: U32
  for +v: U32
  {S.S.puts(D.WD.w4(B.B.rep4(v)), t, d) == S.S.puts(CP.rep(4n, v), t, d) : A.Tr}

def CP.rep4_put(t, d, v):
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(v), 0n), U32.and(v, 255), Z.BB.rep4_0(v)) :
    {S.S.puts(_ <> Y.BP.ext(B.B.rep4(v), 8n) <> Y.BP.ext(B.B.rep4(v), 16n) <> Y.BP.ext(B.B.rep4(v), 24n) <> [], t, d) == S.S.puts(CP.rep(4n, v), t, d) : A.Tr}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(v), 8n), U32.and(v, 255), Z.BB.rep4_1(v)) :
    {S.S.puts(U32.and(v, 255) <> _ <> Y.BP.ext(B.B.rep4(v), 16n) <> Y.BP.ext(B.B.rep4(v), 24n) <> [], t, d) == S.S.puts(CP.rep(4n, v), t, d) : A.Tr}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(v), 16n), U32.and(v, 255), Z.BB.rep4_2(v)) :
    {S.S.puts(U32.and(v, 255) <> U32.and(v, 255) <> _ <> Y.BP.ext(B.B.rep4(v), 24n) <> [], t, d) == S.S.puts(CP.rep(4n, v), t, d) : A.Tr}
  %Equal.sym(U32, Y.BP.ext(B.B.rep4(v), 24n), U32.and(v, 255), Z.BB.rep4_3(v)) :
    {S.S.puts(U32.and(v, 255) <> U32.and(v, 255) <> U32.and(v, 255) <> _ <> [], t, d) == S.S.puts(CP.rep(4n, v), t, d) : A.Tr}
  %Equal.sym(A.Tr, Y.BP.put(t, d, U32.and(v, 255)), Y.BP.put(t, d, v), CP.put_mask(t, d, v)) :
    {Y.BP.put(Y.BP.put(Y.BP.put(_, U32.add(d, 1), U32.and(v, 255)), U32.add(U32.add(d, 1), 1), U32.and(v, 255)), U32.add(U32.add(U32.add(d, 1), 1), 1), U32.and(v, 255)) == Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v) : A.Tr}
  %Equal.sym(A.Tr, Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), U32.and(v, 255)), Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), CP.put_mask(Y.BP.put(t, d, v), U32.add(d, 1), v)) :
    {Y.BP.put(Y.BP.put(_, U32.add(U32.add(d, 1), 1), U32.and(v, 255)), U32.add(U32.add(U32.add(d, 1), 1), 1), U32.and(v, 255)) == Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v) : A.Tr}
  %Equal.sym(A.Tr, Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), U32.and(v, 255)), Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), CP.put_mask(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v)) :
    {Y.BP.put(_, U32.add(U32.add(U32.add(d, 1), 1), 1), U32.and(v, 255)) == Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v) : A.Tr}
  %Equal.sym(A.Tr, Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), U32.and(v, 255)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v), CP.put_mask(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v)) :
    {_ == Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v) : A.Tr}
  {==}

law CP.fwords:
  for +n: Nat
  for +t: A.Tr
  for +dw: U32
  for +d: U32
  for +v: U32
  for +E: U32
  for +ed: {V.U.N(d) == Nat.double(Nat.double(V.U.N(dw))) : Nat}
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(n)), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  {B.B.fill.words(n, A.A.from(t), dw, B.B.rep4(v)) == A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(n)), v), t, d)) : Array<U32>}

def CP.fwords(n, t, dw, d, v, E, ed, hd):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(t), dw, B.B.rep4(v)), A.A.from(A.T.set(t, dw, B.B.rep4(v))), A.A.set_from(t, dw, B.B.rep4(v))) :
        {B.B.fill.words(p, _, U32.add(dw, 1), B.B.rep4(v)) == A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.words(p, A.A.from(A.T.set(t, dw, B.B.rep4(v))), U32.add(dw, 1), B.B.rep4(v)), A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), A.T.set(t, dw, B.B.rep4(v)), D.WD.step(4n, d))), CP.fwords(p, A.T.set(t, dw, B.B.rep4(v)), U32.add(dw, 1), D.WD.step(4n, d), v, E, CP.next(d, dw, E, 0n, ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd)), (%Equal.sym(Nat, V.U.N(D.WD.step(4n, d)), 4n+V.U.N(d), D.WD.pos_4(d, E, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(p)), _), V.U.N(E))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.double(Nat.double(p)), 4n+V.U.N(d)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), D.WD.add4r(Nat.double(Nat.double(p)), V.U.N(d))) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hd)))) :
        {_ == A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1))) : Array<U32>}
      %D.WD.put4(t, d, dw, E, B.B.rep4(v), ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hd)) :
        {A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), _, D.WD.step(4n, d))) == A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(A.Tr, S.S.puts(D.WD.w4(B.B.rep4(v)), t, d), S.S.puts(CP.rep(4n, v), t, d), CP.rep4_put(t, d, v)) :
        {A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), _, D.WD.step(4n, d))) == A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(p)), v), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, v), U32.add(d, 1), v), U32.add(U32.add(d, 1), 1), v), U32.add(U32.add(U32.add(d, 1), 1), 1), v), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1))) : Array<U32>}
      {==}

law CP.fill.go:
  for +t: A.Tr
  for +d: U32
  for +v: U32
  for +n: U32
  for +E: U32
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)) == c : Bool}
  {B.B.fill(A.A.from(t), d, v, n) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}

def CP.fill.go(t, d, v, n, E, hd, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.fill.body(U32.sub(n, _), U32.add(d, _), v, B.B.fill.bytes(U32.to_nat(_), A.A.from(t), d, v)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), True{}, ec) :
        {B.B.fill.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), v, B.B.fill.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), A.A.from(t), d, v)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.bytes(V.U.N(n), A.A.from(t), d, v), A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)), CP.fbytes(V.U.N(n), t, d, v)) :
        {B.B.fill.body(U32.sub(n, n), U32.add(d, n), v, _) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(U32, U32.sub(n, n), 0, D.WD.sub_self(n)) :
        {B.B.fill.body(_, U32.add(d, n), v, A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d))) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      {==}
    case False{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.fill.body(U32.sub(n, _), U32.add(d, _), v, B.B.fill.bytes(U32.to_nat(_), A.A.from(t), d, v)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), False{}, ec) :
        {B.B.fill.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), v, B.B.fill.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), A.A.from(t), d, v)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), A.A.from(t), d, v), A.A.from(S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d)), CP.fbytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, v)) :
        {B.B.fill.body(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), v, _) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), A.A.from(S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d)), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), B.B.rep4(v)), A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), CP.fwords(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), v, E, CP.align(d, E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd)), (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _), V.U.N(E))) == True{} : Bool}; CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(d), V.U.N(E), (%Equal.sym(Nat, V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _)) == True{} : Bool}; P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))))), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hd)))) :
        {B.B.fill.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), _, U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), v) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.fill.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), A.A.from(S.S.puts(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), v), A.A.from(S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), v), S.S.puts(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))), CP.fbytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), S.S.puts(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), v)) :
        {_ == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %D.WD.puts_app(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), CP.rep(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), v), S.S.puts(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), t, d), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n), (%Equal.sym(Nat, S.S.len(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.len_rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v)) : {V.U.N(U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)) == _ : Nat}; D.WD.shl2(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) :
        {A.A.from(_) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %D.WD.puts_app(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), D.WD.app(CP.rep(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), v), CP.rep(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), v)), t, d, U32.and(U32.sub(4, U32.and(d, 3)), 3), Equal.sym(Nat, S.S.len(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v)), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), CP.len_rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v))) :
        {A.A.from(_) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %CP.rep_app(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), v) :
        {A.A.from(S.S.puts(D.WD.app(CP.rep(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), v), _), t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %CP.rep_app(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), v) :
        {A.A.from(S.S.puts(_, t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), P.Nat.add_comm(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)))) :
        {A.A.from(S.S.puts(CP.rep(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), v), t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {A.A.from(S.S.puts(CP.rep(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), v), t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), P.Nat.add_comm(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) :
        {A.A.from(S.S.puts(CP.rep(_, v), t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(n), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec))) :
        {A.A.from(S.S.puts(CP.rep(_, v), t, d)) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}
      {==}

# Filling n bytes from d with v writes n copies of v there.
law CP.fill:
  for +t: A.Tr
  for +d: U32
  for +v: U32
  for +n: U32
  for +E: U32
  for +hd: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  {B.B.fill(A.A.from(t), d, v, n) == A.A.from(S.S.puts(CP.rep(V.U.N(n), v), t, d)) : Array<U32>}

def CP.fill(t, d, v, n, E, hd):
  CP.fill.go(t, d, v, n, E, hd, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), {==})

# Moving
# ======

law CP.le_refl:
  for +a: Nat
  {Cmp.is_le(Nat.cmp(a, a)) == True{} : Bool}

def CP.le_refl(a):
  %Equal.sym(Cmp, Nat.cmp(a, a), EQ{}, P.Nat.cmp_refl(a)) :
    {Cmp.is_le(_) == True{} : Bool}
  {==}

# Copying n bytes from s to d within one tree, a byte at a time and in
# order: a byte copied may be read again.
def CP.mv(+n: Nat, +t: A.Tr, +d: U32, +s: U32) -> A.Tr:
  match n:
    case 0n:
      t
    case 1n+p:
      CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))

law CP.pf_mv:
  for +k: Nat
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +dp: Nat
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  {A.T.pf(dp, CP.mv(k, t, d, s)) == True{} : Bool}

def CP.pf_mv(k, t, d, s, dp, hp):
  match k:
    case 0n:
      hp
    case 1n+q:
      CP.pf_mv(q, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1), dp, Y.BP.pf_put(dp, t, d, Y.BP.byt(t, s), hp))

law CP.mbytes:
  for +k: Nat
  for +t: A.Tr
  for +d: U32
  for +s: U32
  {B.B.move.bytes(k, d, s, (A.A.from(t), Y.BP.byt(t, s))) == A.A.from(CP.mv(k, t, d, s)) : Array<U32>}

def CP.mbytes(k, t, d, s):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, B.B.put(A.A.from(t), d, Y.BP.byt(t, s)), A.A.from(Y.BP.put(t, d, Y.BP.byt(t, s))), Y.BP.put_from(t, d, Y.BP.byt(t, s))) :
        {B.B.move.bytes(p, U32.add(d, 1), U32.add(s, 1), B.B.get(_, U32.add(s, 1))) == A.A.from(CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(Y.BP.put(t, d, Y.BP.byt(t, s))), U32.add(s, 1)), (A.A.from(Y.BP.put(t, d, Y.BP.byt(t, s))), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), Y.BP.get_from(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))) :
        {B.B.move.bytes(p, U32.add(d, 1), U32.add(s, 1), _) == A.A.from(CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.bytes(p, U32.add(d, 1), U32.add(s, 1), (A.A.from(Y.BP.put(t, d, Y.BP.byt(t, s))), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1)))), A.A.from(CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))), CP.mbytes(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))) :
        {_ == A.A.from(CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1))) : Array<U32>}
      {==}

# A write at d leaves the p bytes from s when s + p <= d.
law CP.sl_put:
  for +p: Nat
  for +t: A.Tr
  for +d: U32
  for +x: U32
  for +s: U32
  for +dp: Nat
  for +e: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(d), 1n), V.U.N(e))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(p, V.U.N(s)), V.U.N(d))) == True{} : Bool}
  {S.S.sl(p, Y.BP.put(t, d, x), s) == S.S.sl(p, t, s) : List<&2, U32>}

def CP.sl_put(p, t, d, x, s, dp, e, hp, hd, he, hb, hs):
  match p:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(List<&2, U32>, S.S.sl(q, Y.BP.put(t, d, x), U32.add(s, 1)), S.S.sl(q, t, U32.add(s, 1)), CP.sl_put(q, t, d, x, U32.add(s, 1), dp, e, hp, hd, he, hb, (%Equal.sym(Nat, V.U.N(U32.add(s, 1)), 1n+V.U.N(s), V.U.succ_N(s, d, D.WD.lt_of_succ_le(V.U.N(s), V.U.N(d), P.Nat.le_trans(1n+V.U.N(s), 1n+Nat.add(q, V.U.N(s)), V.U.N(d), P.Nat.le_add_l(q, V.U.N(s)), hs)))) : {Cmp.is_le(Nat.cmp(Nat.add(q, _), V.U.N(d))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(q, 1n+V.U.N(s)), 1n+Nat.add(q, V.U.N(s)), P.Nat.add_succ_r(q, V.U.N(s))) : {Cmp.is_le(Nat.cmp(_, V.U.N(d))) == True{} : Bool}; hs)))) :
        {Y.BP.byt(Y.BP.put(t, d, x), s) <> _ == Y.BP.byt(t, s) <> S.S.sl(q, t, U32.add(s, 1)) : List<&2, U32>}
      %Equal.sym(U32, Y.BP.byt(S.S.puts(x <> [], t, d), s), Y.BP.byt(t, s), S.S.byt_puts_lt(dp, x <> [], t, d, s, e, hp, hd, he, hb, D.WD.lt_of_succ_le(V.U.N(s), V.U.N(d), P.Nat.le_trans(1n+V.U.N(s), 1n+Nat.add(q, V.U.N(s)), V.U.N(d), P.Nat.le_add_l(q, V.U.N(s)), hs)))) :
        {_ <> S.S.sl(q, t, U32.add(s, 1)) == Y.BP.byt(t, s) <> S.S.sl(q, t, U32.add(s, 1)) : List<&2, U32>}
      {==}

# A copy whose source ends before its destination writes the source's bytes.
law CP.mv_far:
  for +k: Nat
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +dp: Nat
  for +e: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(e), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(k, V.U.N(d)), V.U.N(e))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(k, V.U.N(s)), V.U.N(d))) == True{} : Bool}
  {CP.mv(k, t, d, s) == S.S.puts(S.S.sl(k, t, s), t, d) : A.Tr}

def CP.mv_far(k, t, d, s, dp, e, hp, hd, he, hb, hs):
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(A.Tr, CP.mv(q, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), S.S.puts(S.S.sl(q, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1)), CP.mv_far(q, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1), dp, e, Y.BP.pf_put(dp, t, d, Y.BP.byt(t, s), hp), hd, he, (%Equal.sym(Nat, V.U.N(U32.add(d, 1)), 1n+V.U.N(d), V.U.succ_N(d, e, D.WD.lt_of_succ_le(V.U.N(d), V.U.N(e), P.Nat.le_trans(1n+V.U.N(d), 1n+Nat.add(q, V.U.N(d)), V.U.N(e), P.Nat.le_add_l(q, V.U.N(d)), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(q, _), V.U.N(e))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(q, 1n+V.U.N(d)), 1n+Nat.add(q, V.U.N(d)), P.Nat.add_succ_r(q, V.U.N(d))) : {Cmp.is_le(Nat.cmp(_, V.U.N(e))) == True{} : Bool}; hb)), (%Equal.sym(Nat, V.U.N(U32.add(s, 1)), 1n+V.U.N(s), V.U.succ_N(s, d, D.WD.lt_of_succ_le(V.U.N(s), V.U.N(d), P.Nat.le_trans(1n+V.U.N(s), 1n+Nat.add(q, V.U.N(s)), V.U.N(d), P.Nat.le_add_l(q, V.U.N(s)), hs)))) : {Cmp.is_le(Nat.cmp(Nat.add(q, _), V.U.N(U32.add(d, 1)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(d, 1)), 1n+V.U.N(d), V.U.succ_N(d, e, D.WD.lt_of_succ_le(V.U.N(d), V.U.N(e), P.Nat.le_trans(1n+V.U.N(d), 1n+Nat.add(q, V.U.N(d)), V.U.N(e), P.Nat.le_add_l(q, V.U.N(d)), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(q, 1n+V.U.N(s)), _)) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(q, 1n+V.U.N(s)), 1n+Nat.add(q, V.U.N(s)), P.Nat.add_succ_r(q, V.U.N(s))) : {Cmp.is_le(Nat.cmp(_, 1n+V.U.N(d))) == True{} : Bool}; P.Nat.le_succ_l(Nat.add(q, V.U.N(s)), V.U.N(d), hs)))))) :
        {_ == S.S.puts(S.S.sl(q, t, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1)) : A.Tr}
      %Equal.sym(List<&2, U32>, S.S.sl(q, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1)), S.S.sl(q, t, U32.add(s, 1)), CP.sl_put(q, t, d, Y.BP.byt(t, s), U32.add(s, 1), dp, e, hp, hd, he, P.Nat.le_trans(Nat.add(V.U.N(d), 1n), 1n+Nat.add(q, V.U.N(d)), V.U.N(e), (%Equal.sym(Nat, Nat.add(V.U.N(d), 1n), 1n+V.U.N(d), P.Nat.add_one(V.U.N(d))) : {Cmp.is_le(Nat.cmp(_, 1n+Nat.add(q, V.U.N(d)))) == True{} : Bool}; P.Nat.le_add_l(q, V.U.N(d))), hb), P.Nat.le_trans(Nat.add(q, V.U.N(U32.add(s, 1))), 1n+Nat.add(q, V.U.N(s)), V.U.N(d), (%Equal.sym(Nat, V.U.N(U32.add(s, 1)), 1n+V.U.N(s), V.U.succ_N(s, d, D.WD.lt_of_succ_le(V.U.N(s), V.U.N(d), P.Nat.le_trans(1n+V.U.N(s), 1n+Nat.add(q, V.U.N(s)), V.U.N(d), P.Nat.le_add_l(q, V.U.N(s)), hs)))) : {Cmp.is_le(Nat.cmp(Nat.add(q, _), 1n+Nat.add(q, V.U.N(s)))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(q, 1n+V.U.N(s)), 1n+Nat.add(q, V.U.N(s)), P.Nat.add_succ_r(q, V.U.N(s))) : {Cmp.is_le(Nat.cmp(_, 1n+Nat.add(q, V.U.N(s)))) == True{} : Bool}; CP.le_refl(1n+Nat.add(q, V.U.N(s))))), hs))) :
        {S.S.puts(_, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1)) == S.S.puts(S.S.sl(q, t, U32.add(s, 1)), Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1)) : A.Tr}
      {==}

law CP.mv_app:
  for +a: Nat
  for +b: Nat
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +x: U32
  for +e: {V.U.N(x) == a : Nat}
  {CP.mv(Nat.add(a, b), t, d, s) == CP.mv(b, CP.mv(a, t, d, s), U32.add(d, x), U32.add(s, x)) : A.Tr}

def CP.mv_app(a, b, t, d, s, x, e):
  match a:
    case 0n:
      %Equal.sym(U32, x, 0, D.WD.zero_of(x, e)) :
        {CP.mv(b, t, d, s) == CP.mv(b, t, U32.add(d, _), U32.add(s, _)) : A.Tr}
      %Equal.sym(U32, U32.add(d, 0), d, V.U.add_zero_r(d)) :
        {CP.mv(b, t, d, s) == CP.mv(b, t, _, U32.add(s, 0)) : A.Tr}
      %Equal.sym(U32, U32.add(s, 0), s, V.U.add_zero_r(s)) :
        {CP.mv(b, t, d, s) == CP.mv(b, t, d, _) : A.Tr}
      {==}
    case 1n+p:
      %Equal.sym(A.Tr, CP.mv(Nat.add(p, b), Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), U32.add(U32.add(d, 1), U32.sub(x, 1)), U32.add(U32.add(s, 1), U32.sub(x, 1))), CP.mv_app(p, b, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1), U32.sub(x, 1), D.WD.pred_N(x, p, e))) :
        {_ == CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), U32.add(d, x), U32.add(s, x)) : A.Tr}
      %Equal.sym(U32, U32.add(U32.add(d, 1), U32.sub(x, 1)), U32.add(d, x), D.WD.add_shift(d, x)) :
        {CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), _, U32.add(U32.add(s, 1), U32.sub(x, 1))) == CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), U32.add(d, x), U32.add(s, x)) : A.Tr}
      %Equal.sym(U32, U32.add(U32.add(s, 1), U32.sub(x, 1)), U32.add(s, x), D.WD.add_shift(s, x)) :
        {CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), U32.add(d, x), _) == CP.mv(b, CP.mv(p, Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), U32.add(s, 1)), U32.add(d, x), U32.add(s, x)) : A.Tr}
      {==}

law CP.word_from:
  for +t: A.Tr
  for +s: U32
  {B.B.word(A.A.from(t), s) == (A.A.from(t), B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))) : Array<U32> & U32}

def CP.word_from(t, s):
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.shrn(s, 2n)), (A.A.from(t), A.T.word(t, U32.shrn(s, 2n))), A.A.get_from(t, U32.shrn(s, 2n))) :
    {B.B.word.k1(s, _) == (A.A.from(t), B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(t), U32.add(U32.shrn(s, 2n), 1)), (A.A.from(t), A.T.word(t, U32.add(U32.shrn(s, 2n), 1))), A.A.get_from(t, U32.add(U32.shrn(s, 2n), 1))) :
    {B.B.word.k2(B.B.sh(s), A.T.word(t, U32.shrn(s, 2n)), _) == (A.A.from(t), B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))) : Array<U32> & U32}
  {==}

# Whole words of a forward copy at least four bytes behind.
law CP.mwords:
  for +n: Nat
  for +t: A.Tr
  for +dw: U32
  for +d: U32
  for +s: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +ed: {V.U.N(d) == Nat.double(Nat.double(V.U.N(dw))) : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(n)), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(d))) == True{} : Bool}
  {B.B.move.words(n, dw, s, B.B.word(A.A.from(t), s)) == A.A.from(CP.mv(Nat.double(Nat.double(n)), t, d, s)) : Array<U32>}

def CP.mwords(n, t, dw, d, s, dp, E, hp, hd, he, ed, hb, hs):
  match n:
    case 0n:
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), s), (A.A.from(t), B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))), CP.word_from(t, s)) :
        {B.B.move.words(0n, dw, s, _) == A.A.from(CP.mv(Nat.double(Nat.double(0n)), t, d, s)) : Array<U32>}
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(t), s), (A.A.from(t), B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))), CP.word_from(t, s)) :
        {B.B.move.words(1n+p, dw, s, _) == A.A.from(CP.mv(Nat.double(Nat.double(1n+p)), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(t), dw, B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))), A.A.from(A.T.set(t, dw, B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s)))), A.A.set_from(t, dw, B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s)))) :
        {B.B.move.words(p, U32.add(dw, 1), U32.add(s, 4), B.B.word(_, U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %D.WD.put4(t, d, dw, E, B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s)), ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hb)) :
        {B.B.move.words(p, U32.add(dw, 1), U32.add(s, 4), B.B.word(A.A.from(_), U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(List<&2, U32>, D.WD.w4(B.B.join(A.T.word(t, U32.shrn(s, 2n)), A.T.word(t, U32.add(U32.shrn(s, 2n), 1)), B.B.sh(s))), S.S.sl(4n, t, s), D.WD.join(t, s, E, P.Nat.le_trans(Nat.add(4n, V.U.N(s)), V.U.N(d), V.U.N(E), hs, P.Nat.le_trans(V.U.N(d), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), V.U.N(E), P.Nat.le_trans(V.U.N(d), Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), P.Nat.le_add_l(Nat.double(Nat.double(p)), V.U.N(d)), P.Nat.le_add_l(4n, Nat.add(Nat.double(Nat.double(p)), V.U.N(d)))), hb)))) :
        {B.B.move.words(p, U32.add(dw, 1), U32.add(s, 4), B.B.word(A.A.from(S.S.puts(_, t, d)), U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %CP.mv_far(4n, t, d, s, dp, E, hp, hd, he, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hb), hs) :
        {B.B.move.words(p, U32.add(dw, 1), U32.add(s, 4), B.B.word(A.A.from(_), U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.words(p, U32.add(dw, 1), U32.add(s, 4), B.B.word(A.A.from(CP.mv(4n, t, d, s)), U32.add(s, 4))), A.A.from(CP.mv(Nat.double(Nat.double(p)), CP.mv(4n, t, d, s), U32.add(d, 4), U32.add(s, 4))), CP.mwords(p, CP.mv(4n, t, d, s), U32.add(dw, 1), U32.add(d, 4), U32.add(s, 4), dp, E, CP.pf_mv(4n, t, d, s, dp, hp), hd, he, (%D.WD.step4(d) : {V.U.N(_) == Nat.add(0n, Nat.double(Nat.double(V.U.N(U32.add(dw, 1))))) : Nat}; CP.next(d, dw, E, 0n, ed, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hb))), (%Equal.sym(Nat, V.U.N(U32.add(d, 4)), 4n+V.U.N(d), (%D.WD.step4(d) : {V.U.N(_) == 4n+V.U.N(d) : Nat}; D.WD.pos_4(d, E, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(p)), _), V.U.N(E))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.double(Nat.double(p)), 4n+V.U.N(d)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), D.WD.add4r(Nat.double(Nat.double(p)), V.U.N(d))) : {Cmp.is_le(Nat.cmp(_, V.U.N(E))) == True{} : Bool}; hb)), (%Equal.sym(Nat, V.U.N(U32.add(s, 4)), 4n+V.U.N(s), (%D.WD.step4(s) : {V.U.N(_) == 4n+V.U.N(s) : Nat}; D.WD.pos_4(s, E, P.Nat.le_trans(Nat.add(4n, V.U.N(s)), V.U.N(d), V.U.N(E), hs, P.Nat.le_trans(V.U.N(d), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), V.U.N(E), P.Nat.le_trans(V.U.N(d), Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), 4n+Nat.add(Nat.double(Nat.double(p)), V.U.N(d)), P.Nat.le_add_l(Nat.double(Nat.double(p)), V.U.N(d)), P.Nat.le_add_l(4n, Nat.add(Nat.double(Nat.double(p)), V.U.N(d)))), hb))))) : {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(U32.add(d, 4)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(d, 4)), 4n+V.U.N(d), (%D.WD.step4(d) : {V.U.N(_) == 4n+V.U.N(d) : Nat}; D.WD.pos_4(d, E, CP.le4(Nat.double(Nat.double(p)), V.U.N(d), V.U.N(E), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(4n, 4n+V.U.N(s)), _)) == True{} : Bool}; hs)))) :
        {_ == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(d, 1), 1), 1), 1), U32.add(d, 4), D.WD.step4(d)) :
        {A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(d, 4), U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), _, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1))) : Array<U32>}
      %Equal.sym(U32, U32.add(U32.add(U32.add(U32.add(s, 1), 1), 1), 1), U32.add(s, 4), D.WD.step4(s)) :
        {A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(d, 4), U32.add(s, 4))) == A.A.from(CP.mv(Nat.double(Nat.double(p)), Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(d, 1), 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(d, 1), 1), Y.BP.byt(Y.BP.put(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(d, 1), Y.BP.byt(Y.BP.put(t, d, Y.BP.byt(t, s)), U32.add(s, 1))), U32.add(U32.add(s, 1), 1))), U32.add(U32.add(U32.add(s, 1), 1), 1))), U32.add(d, 4), _)) : Array<U32>}
      {==}

law CP.move.fast:
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +n: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +far: {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), V.U.N(d))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)) == c : Bool}
  {B.B.move.go(True{}, A.A.from(t), d, s, n) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}

def CP.move.fast(t, d, s, n, dp, E, hp, hd, he, hb, far, c, ec):
  match c:
    case True{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.move.body(U32.sub(n, _), U32.add(d, _), U32.add(s, _), B.B.move.bytes(U32.to_nat(_), d, s, B.B.get(A.A.from(t), s))) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), True{}, ec) :
        {B.B.move.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(s, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), B.B.move.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), d, s, B.B.get(A.A.from(t), s))) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), s), (A.A.from(t), Y.BP.byt(t, s)), Y.BP.get_from(t, s)) :
        {B.B.move.body(U32.sub(n, n), U32.add(d, n), U32.add(s, n), B.B.move.bytes(V.U.N(n), d, s, _)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.bytes(V.U.N(n), d, s, (A.A.from(t), Y.BP.byt(t, s))), A.A.from(CP.mv(V.U.N(n), t, d, s)), CP.mbytes(V.U.N(n), t, d, s)) :
        {B.B.move.body(U32.sub(n, n), U32.add(d, n), U32.add(s, n), _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(U32, U32.sub(n, n), 0, D.WD.sub_self(n)) :
        {B.B.move.body(_, U32.add(d, n), U32.add(s, n), A.A.from(CP.mv(V.U.N(n), t, d, s))) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(CP.mv(V.U.N(n), t, d, s)), U32.add(s, n)), (A.A.from(CP.mv(V.U.N(n), t, d, s)), B.B.join(A.T.word(CP.mv(V.U.N(n), t, d, s), U32.shrn(U32.add(s, n), 2n)), A.T.word(CP.mv(V.U.N(n), t, d, s), U32.add(U32.shrn(U32.add(s, n), 2n), 1)), B.B.sh(U32.add(s, n)))), CP.word_from(CP.mv(V.U.N(n), t, d, s), U32.add(s, n))) :
        {B.B.move.tail(U32.and(0, 3), U32.add(U32.add(d, n), U32.shln(U32.shrn(0, 2n), 2n)), U32.add(U32.add(s, n), U32.shln(U32.shrn(0, 2n), 2n)), B.B.move.words(U32.to_nat(U32.shrn(0, 2n)), U32.shrn(U32.add(d, n), 2n), U32.add(s, n), _)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(CP.mv(V.U.N(n), t, d, s)), U32.add(U32.add(s, n), 0)), (A.A.from(CP.mv(V.U.N(n), t, d, s)), Y.BP.byt(CP.mv(V.U.N(n), t, d, s), U32.add(U32.add(s, n), 0))), Y.BP.get_from(CP.mv(V.U.N(n), t, d, s), U32.add(U32.add(s, n), 0))) :
        {B.B.move.bytes(0n, U32.add(U32.add(d, n), 0), U32.add(U32.add(s, n), 0), _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      {==}
    case False{}:
      %Equal.sym(U32, U32.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), Bool.pick(U32, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), D.WD.min(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {B.B.move.body(U32.sub(n, _), U32.add(d, _), U32.add(s, _), B.B.move.bytes(U32.to_nat(_), d, s, B.B.get(A.A.from(t), s))) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Bool, U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), False{}, ec) :
        {B.B.move.body(U32.sub(n, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(d, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(s, Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), B.B.move.bytes(U32.to_nat(Bool.pick(U32, _, n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), d, s, B.B.get(A.A.from(t), s))) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), s), (A.A.from(t), Y.BP.byt(t, s)), Y.BP.get_from(t, s)) :
        {B.B.move.body(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), B.B.move.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), d, s, _)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.bytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), d, s, (A.A.from(t), Y.BP.byt(t, s))), A.A.from(CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s)), CP.mbytes(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s)) :
        {B.B.move.body(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.words(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), B.B.word(A.A.from(CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), A.A.from(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), CP.mwords(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.shrn(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), dp, E, CP.pf_mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s, dp, hp), hd, he, CP.align(d, E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hb)), (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hb))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _), V.U.N(E))) == True{} : Bool}; CP.bnd(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(d), V.U.N(E), (%Equal.sym(Nat, V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), _)) == True{} : Bool}; P.Nat.le_add_l(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))))), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hb)), (%Equal.sym(Nat, V.U.N(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(s), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(s, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, P.Nat.le_trans(Nat.add(V.U.N(s), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(E), CP.le_add_r(V.U.N(s), V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), P.Nat.lt_to_le(V.U.N(s), V.U.N(d), P.Nat.lt_le_trans(V.U.N(s), Nat.add(4n, V.U.N(s)), V.U.N(d), P.Nat.lt_of_add_succ(V.U.N(s), 3n, Nat.add(4n, V.U.N(s)), (%P.Nat.add_comm(4n, V.U.N(s)) : {Cmp.is_le(Nat.cmp(_, Nat.add(4n, V.U.N(s)))) == True{} : Bool}; CP.le_refl(Nat.add(4n, V.U.N(s))))), far))), CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hb)))) : {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3))), Nat.add(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.add_N(d, U32.and(U32.sub(4, U32.and(d, 3)), 3), E, CP.le_part(V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(n), V.U.N(E), V.U.le_N(U32.and(U32.sub(4, U32.and(d, 3)), 3), n, V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec)), hb))) : {Cmp.is_le(Nat.cmp(Nat.add(4n, Nat.add(V.U.N(s), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)))), _)) == True{} : Bool}; CP.le_add_r(Nat.add(4n, V.U.N(s)), V.U.N(d), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), far))))) :
        {B.B.move.tail(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))), (A.A.from(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Y.BP.byt(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))), Y.BP.get_from(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))) :
        {B.B.move.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32>, B.B.move.bytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), (A.A.from(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Y.BP.byt(CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n))))), A.A.from(CP.mv(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))), CP.mbytes(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), CP.mv(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3))), U32.add(U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)), U32.add(U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n)))) :
        {_ == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %CP.mv_app(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), CP.mv(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), t, d, s), U32.add(d, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.add(s, U32.and(U32.sub(4, U32.and(d, 3)), 3)), U32.shln(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n), 2n), D.WD.shl2(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))) :
        {A.A.from(_) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %CP.mv_app(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), t, d, s, U32.and(U32.sub(4, U32.and(d, 3)), 3), {==}) :
        {A.A.from(_) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3))), Nat.add(V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)), Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n))))), P.Nat.add_comm(Nat.double(Nat.double(V.U.N(U32.shrn(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 2n)))), V.U.N(U32.and(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), 3)))) :
        {A.A.from(CP.mv(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), t, d, s)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %D.WD.mod4(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))) :
        {A.A.from(CP.mv(Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), _), t, d, s)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)))), Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), P.Nat.add_comm(V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3)), V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))))) :
        {A.A.from(CP.mv(_, t, d, s)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(n, U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(U32.and(U32.sub(4, U32.and(d, 3)), 3))), V.U.N(n), V.U.sub_nat(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), V.U.not_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3), ec))) :
        {A.A.from(CP.mv(_, t, d, s)) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      {==}

law CP.move.go:
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +n: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Nat.cmp(V.U.N(s), V.U.N(d)) == LT{} : Cmp}
  for +f: Bool
  for +ef: {U32.is_ge(U32.sub(d, s), 4) == f : Bool}
  {B.B.move(A.A.from(t), d, s, n) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}

def CP.move.go(t, d, s, n, dp, E, hp, hd, he, hb, hs, f, ef):
  match f:
    case False{}:
      %Equal.sym(Bool, U32.is_ge(U32.sub(d, s), 4), False{}, ef) :
        {B.B.move.go(_, A.A.from(t), d, s, n) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(t), s), (A.A.from(t), Y.BP.byt(t, s)), Y.BP.get_from(t, s)) :
        {B.B.move.bytes(V.U.N(n), d, s, _) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      CP.mbytes(V.U.N(n), t, d, s)
    case True{}:
      %Equal.sym(Bool, U32.is_ge(U32.sub(d, s), 4), True{}, ef) :
        {B.B.move.go(_, A.A.from(t), d, s, n) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}
      CP.move.fast(t, d, s, n, dp, E, hp, hd, he, hb, (%V.U.sub_nat(d, s, V.U.lt_to_le(s, d, V.U.N_lt(s, d, hs))) : {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(s)), _)) == True{} : Bool}; CP.le_add_r(4n, V.U.N(U32.sub(d, s)), V.U.N(s), V.U.le_N(4, U32.sub(d, s), V.U.ge_le(U32.sub(d, s), 4, ef)))), U32.is_lt(n, U32.and(U32.sub(4, U32.and(d, 3)), 3)), {==})

# Moving n bytes from s to d (s before d) in one tree is the forward copy.
law CP.move:
  for +t: A.Tr
  for +d: U32
  for +s: U32
  for +n: U32
  for +dp: Nat
  for +E: U32
  for +hp: {A.T.pf(dp, t) == True{} : Bool}
  for +hd: {Nat.cmp(dp, 32n) == LT{} : Cmp}
  for +he: {Cmp.is_le(Nat.cmp(V.U.N(E), Nat.double(Nat.double(P.Nat.pow2(dp))))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(n), V.U.N(d)), V.U.N(E))) == True{} : Bool}
  for +hs: {Nat.cmp(V.U.N(s), V.U.N(d)) == LT{} : Cmp}
  {B.B.move(A.A.from(t), d, s, n) == A.A.from(CP.mv(V.U.N(n), t, d, s)) : Array<U32>}

def CP.move(t, d, s, n, dp, E, hp, hd, he, hb, hs):
  CP.move.go(t, d, s, n, dp, E, hp, hd, he, hb, hs, U32.is_ge(U32.sub(d, s), 4), {==})
