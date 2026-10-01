import Base
import ./nat.bend as P
import ./u32.bend as V

# Lemmas about Base's Array<U32>.
#
# An array is Type: a proof may hand one to a lemma only once. So proofs
# work with Tr, a Data copy of the tree under an array, and A.from(t), the
# array it stands for: any array is A.from(A.to(a)) (A.from_to), and reads
# and writes of A.from(t) are A.from of reads and writes of t.

type Tr is Data:
  TL{v: U32}
  TN{l: Tr, r: Tr}

def A.from(+t: Tr) -> Array<U32>:
  match t:
    case TL{v}:
      ALeaf{v}
    case TN{l, r}:
      ANode{A.from(l), A.from(r)}

def A.to(a: Array<U32>) -> Tr:
  match a:
    case ALeaf{v}:
      TL{v}
    case ANode{xs, ys}:
      TN{A.to(xs), A.to(ys)}

law A.from_to:
  for a: Array<U32>
  {A.from(A.to(a)) == a : Array<U32>}

def A.from_to(a):
  match a:
    case ALeaf{v}:
      {==}
    case ANode{xs, ys}:
      %A.from_to(xs) : {ANode{A.from(A.to(xs)), A.from(A.to(ys))} == ANode{_, ys} : Array<U32>}
      %A.from_to(ys) : {ANode{A.from(A.to(xs)), A.from(A.to(ys))} == ANode{A.from(A.to(xs)), _}
        : Array<U32>}
      {==}

# The tree side of Array.size, Array.get and Array.swap.

def T.size(+t: Tr) -> U32:
  match t:
    case TL{v}:
      1
    case TN{l, r}:
      U32.shl(T.size(l))

def T.get.go(+t: Tr, +n: U32, +i: U32, +z: Bool) -> U32:
  match t z:
    case TL{v} _:
      v
    case TN{l, r} True{}:
      T.get.go(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))
    case TN{l, r} False{}:
      T.get.go(r, U32.shr(n), U32.sub(i, U32.shr(n)),
        U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

def T.swap.go(+t: Tr, +n: U32, +i: U32, +v: U32, +z: Bool) -> Tr:
  match t z:
    case TL{w} _:
      TL{v}
    case TN{l, r} True{}:
      TN{T.swap.go(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), r}
    case TN{l, r} False{}:
      TN{l, T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
        U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))}

# The slot of index i in an array of n slots, and which half it is in.
def T.mask(+n: U32, +i: U32) -> U32:
  U32.and(i, U32.sub(n, 1))

def T.half(+n: U32, +i: U32) -> Bool:
  U32.is_lt(T.mask(n, i), U32.shr(n))

# The word at i.
def T.word(+t: Tr, +i: U32) -> U32:
  T.get.go(t, T.size(t), T.mask(T.size(t), i), T.half(T.size(t), i))

# The tree after writing v at i.
def T.set(+t: Tr, +i: U32, +v: U32) -> Tr:
  T.swap.go(t, T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i))

law A.size_from:
  for +t: Tr
  {Array.size(U32, A.from(t)) == (A.from(t), T.size(t)) : Array<U32> & U32}

def A.size_from(t):
  match t:
    case TL{v}:
      {==}
    case TN{l, r}:
      %Equal.sym(Array<U32> & U32, Array.size(U32, A.from(l)), (A.from(l), T.size(l)),
        A.size_from(l)) :
        {Array.size.node(U32, A.from(r), _) == (ANode{A.from(l), A.from(r)}, U32.shl(T.size(l)))
          : Array<U32> & U32}
      {==}

law A.go_from:
  for +t: Tr
  for +n: U32
  for +i: U32
  for +z: Bool
  {Array.get.go(U32, A.from(t), n, i, z) == (A.from(t), T.get.go(t, n, i, z))
    : Array<U32> & U32}

def A.go_from(t, n, i, z):
  match t z:
    case TL{v} _:
      {==}
    case TN{l, r} True{}:
      %Equal.sym(Array<U32> & U32,
        Array.get.go(U32, A.from(l), U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))),
        (A.from(l), T.get.go(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))),
        A.go_from(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))) :
        {Array.swap.lo(U32, A.from(r), _)
          == (A.from(TN{l, r}), T.get.go(TN{l, r}, n, i, True{})) : Array<U32> & U32}
      {==}
    case TN{l, r} False{}:
      %Equal.sym(Array<U32> & U32,
        Array.get.go(U32, A.from(r), U32.shr(n), U32.sub(i, U32.shr(n)),
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))),
        (A.from(r), T.get.go(r, U32.shr(n), U32.sub(i, U32.shr(n)),
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))),
        A.go_from(r, U32.shr(n), U32.sub(i, U32.shr(n)),
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) :
        {Array.swap.hi(U32, A.from(l), _)
          == (A.from(TN{l, r}), T.get.go(TN{l, r}, n, i, False{})) : Array<U32> & U32}
      {==}

law A.swap_from:
  for +t: Tr
  for +n: U32
  for +i: U32
  for +v: U32
  for +z: Bool
  {Array.swap.go(U32, A.from(t), n, i, v, z)
    == (A.from(T.swap.go(t, n, i, v, z)), T.get.go(t, n, i, z)) : Array<U32> & U32}

def A.swap_from(t, n, i, v, z):
  match t z:
    case TL{w} _:
      {==}
    case TN{l, r} True{}:
      %Equal.sym(Array<U32> & U32,
        Array.swap.go(U32, A.from(l), U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))),
        (A.from(T.swap.go(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))),
          T.get.go(l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))),
        A.swap_from(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))) :
        {Array.swap.lo(U32, A.from(r), _)
          == (A.from(T.swap.go(TN{l, r}, n, i, v, True{})), T.get.go(TN{l, r}, n, i, True{}))
          : Array<U32> & U32}
      {==}
    case TN{l, r} False{}:
      %Equal.sym(Array<U32> & U32,
        Array.swap.go(U32, A.from(r), U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))),
        (A.from(T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))),
          T.get.go(r, U32.shr(n), U32.sub(i, U32.shr(n)),
            U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))),
        A.swap_from(r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) :
        {Array.swap.hi(U32, A.from(l), _)
          == (A.from(T.swap.go(TN{l, r}, n, i, v, False{})), T.get.go(TN{l, r}, n, i, False{}))
          : Array<U32> & U32}
      {==}

# A read of A.from(t) hands it back with the word at i.
law A.get_from:
  for +t: Tr
  for +i: U32
  {Array.get(U32, A.from(t), i) == (A.from(t), T.word(t, i)) : Array<U32> & U32}

def A.get_from(t, i):
  %Equal.sym(Array<U32> & U32, Array.size(U32, A.from(t)), (A.from(t), T.size(t)),
    A.size_from(t)) :
    {Array.get.at(U32, i, _) == (A.from(t), T.word(t, i)) : Array<U32> & U32}
  A.go_from(t, T.size(t), T.mask(T.size(t), i), T.half(T.size(t), i))

# A write to A.from(t) is A.from of the write to t.
law A.set_from:
  for +t: Tr
  for +i: U32
  for +v: U32
  {Array.set(U32, A.from(t), i, v) == A.from(T.set(t, i, v)) : Array<U32>}

def A.set_from(t, i, v):
  %Equal.sym(Array<U32> & U32, Array.size(U32, A.from(t)), (A.from(t), T.size(t)),
    A.size_from(t)) :
    {Array.set.fin(U32, Array.swap.at(U32, i, v, _)) == A.from(T.set(t, i, v)) : Array<U32>}
  %Equal.sym(Array<U32> & U32,
    Array.swap.go(U32, A.from(t), T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i)),
    (A.from(T.set(t, i, v)), T.get.go(t, T.size(t), T.mask(T.size(t), i), T.half(T.size(t), i))),
    A.swap_from(t, T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i))) :
    {Array.set.fin(U32, _) == A.from(T.set(t, i, v)) : Array<U32>}
  {==}

# A write keeps the slot count.
law T.size_swap:
  for +t: Tr
  for +n: U32
  for +i: U32
  for +v: U32
  for +z: Bool
  {T.size(T.swap.go(t, n, i, v, z)) == T.size(t) : U32}

def T.size_swap(t, n, i, v, z):
  match t z:
    case TL{w} _:
      {==}
    case TN{l, r} True{}:
      %T.size_swap(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))) :
        {U32.shl(T.size(T.swap.go(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))))
          == U32.shl(_) : U32}
      {==}
    case TN{l, r} False{}:
      {==}

law T.get_swap:
  for +t: Tr
  for +n: U32
  for +i: U32
  for +v: U32
  for +z: Bool
  {T.get.go(T.swap.go(t, n, i, v, z), n, i, z) == v : U32}

def T.get_swap(t, n, i, v, z):
  match t z:
    case TL{w} _:
      {==}
    case TN{l, r} True{}:
      T.get_swap(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))
    case TN{l, r} False{}:
      T.get_swap(r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
        U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

# A read of the slot just written answers what was written.
law T.word_set:
  for +t: Tr
  for +i: U32
  for +v: U32
  {T.word(T.set(t, i, v), i) == v : U32}

def T.word_set(t, i, v):
  %Equal.sym(U32, T.size(T.set(t, i, v)), T.size(t),
    T.size_swap(t, T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i))) :
    {T.get.go(T.set(t, i, v), _, T.mask(_, i), T.half(_, i)) == v : U32}
  T.get_swap(t, T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i))

# The tree is perfect of depth d: every leaf d levels down.
def T.pf(+d: Nat, +t: Tr) -> Bool:
  match d t:
    case 0n TL{v}:
      True{}
    case 0n TN{l, r}:
      False{}
    case 1n+p TL{v}:
      False{}
    case 1n+p TN{l, r}:
      Bool.and(T.pf(p, l), T.pf(p, r))

law T.size_pf:
  for +d: Nat
  for +t: Tr
  for +hp: {T.pf(d, t) == True{} : Bool}
  {T.size(t) == U32.shln(1, d) : U32}

def T.size_pf(d, t, hp):
  match d t:
    case 0n TL{v}:
      {==}
    case 0n TN{l, r}:
      P.Bool.false_true({T.size(TN{l, r}) == U32.shln(1, 0n) : U32}, hp)
    case 1n+p TL{v}:
      P.Bool.false_true({T.size(TL{v}) == U32.shln(1, 1n+p) : U32}, hp)
    case 1n+p TN{l, r}:
      %T.size_pf(p, l, P.Bool.and_l(T.pf(p, l), T.pf(p, r), hp)) :
        {U32.shl(T.size(l)) == U32.shl(_) : U32}
      {==}

# In a perfect tree, writing slot j1 leaves slot j2 as it was.
law T.go_other:
  for +p: Nat
  for +t: Tr
  for +n: U32
  for +j1: U32
  for +j2: U32
  for +v: U32
  for +hp: {T.pf(p, t) == True{} : Bool}
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +hn: {n == U32.shln(1, p) : U32}
  for +h1: {U32.is_lt(j1, n) == True{} : Bool}
  for +h2: {U32.is_lt(j2, n) == True{} : Bool}
  for +ne: {U32.is_eq(j1, j2) == False{} : Bool}
  for +z1: Bool
  for +e1: {U32.is_lt(j1, U32.shr(n)) == z1 : Bool}
  for +z2: Bool
  for +e2: {U32.is_lt(j2, U32.shr(n)) == z2 : Bool}
  {T.get.go(T.swap.go(t, n, j1, v, z1), n, j2, z2) == T.get.go(t, n, j2, z2) : U32}

# j - n/2 is below n/2 in the upper half.
law T.go_other.half:
  for +q: Nat
  for +n: U32
  for +j: U32
  for +hd: {Nat.cmp(1n+q, 32n) == LT{} : Cmp}
  for +hn: {n == U32.shln(1, 1n+q) : U32}
  for +hj: {U32.is_lt(j, n) == True{} : Bool}
  for +hz: {U32.is_lt(j, U32.shr(n)) == False{} : Bool}
  {U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(n)) == True{} : Bool}

def T.go_other.half(q, n, j, hd, hn, hj, hz):
  %Equal.sym(U32, n, U32.shln(1, 1n+q), hn) :
    {U32.is_lt(U32.sub(j, U32.shr(_)), U32.shr(_)) == True{} : Bool}
  %Equal.sym(U32, U32.shr(U32.shln(1, 1n+q)), U32.shln(1, q), V.U.shr_pow(q, hd)) :
    {U32.is_lt(U32.sub(j, _), _) == True{} : Bool}
  V.U.sub_half(j, q, hd,
    (%hn : {U32.is_lt(j, _) == True{} : Bool}
      hj),
    (%V.U.shr_pow(q, hd) : {U32.is_lt(j, _) == False{} : Bool}
      (%hn : {U32.is_lt(j, U32.shr(_)) == False{} : Bool}
        hz)))

def T.go_other(p, t, n, j1, j2, v, hp, hd, hn, h1, h2, ne, z1, e1, z2, e2):
  match p t z1 z2:
    case 0n TL{w} _ _:
      P.Bool.true_false({T.get.go(T.swap.go(TL{w}, n, j1, v, z1), n, j2, z2)
        == T.get.go(TL{w}, n, j2, z2) : U32},
        (%V.U.lt_one(j2, (%hn : {U32.is_lt(j2, _) == True{} : Bool}
            h2)) : {U32.is_eq(0, _) == False{} : Bool}
          (%V.U.lt_one(j1, (%hn : {U32.is_lt(j1, _) == True{} : Bool}
              h1)) : {U32.is_eq(_, j2) == False{} : Bool}
            ne)))
    case 0n TN{l, r} _ _:
      P.Bool.false_true({T.get.go(T.swap.go(TN{l, r}, n, j1, v, z1), n, j2, z2)
        == T.get.go(TN{l, r}, n, j2, z2) : U32}, hp)
    case 1n+q TL{w} _ _:
      P.Bool.false_true({T.get.go(T.swap.go(TL{w}, n, j1, v, z1), n, j2, z2)
        == T.get.go(TL{w}, n, j2, z2) : U32}, hp)
    case 1n+q TN{l, r} True{} True{}:
      T.go_other(q, l, U32.shr(n), j1, j2, v, P.Bool.and_l(T.pf(q, l), T.pf(q, r), hp),
        P.Nat.lt_succ_l(q, 32n, hd),
        (%Equal.sym(U32, n, U32.shln(1, 1n+q), hn) : {U32.shr(_) == U32.shln(1, q) : U32}
            V.U.shr_pow(q, hd)),
        e1, e2, ne, U32.is_lt(j1, U32.shr(U32.shr(n))), {==}, U32.is_lt(j2, U32.shr(U32.shr(n))), {==})
    case 1n+q TN{l, r} False{} False{}:
      T.go_other(q, r, U32.shr(n), U32.sub(j1, U32.shr(n)), U32.sub(j2, U32.shr(n)), v, P.Bool.and_r(T.pf(q, l), T.pf(q, r), hp),
        P.Nat.lt_succ_l(q, 32n, hd),
        (%Equal.sym(U32, n, U32.shln(1, 1n+q), hn) : {U32.shr(_) == U32.shln(1, q) : U32}
            V.U.shr_pow(q, hd)),
        T.go_other.half(q, n, j1, hd, hn, h1, e1),
        T.go_other.half(q, n, j2, hd, hn, h2, e2),
        V.U.sub_ne(j1, j2, U32.shr(n), ne), U32.is_lt(U32.sub(j1, U32.shr(n)), U32.shr(U32.shr(n))), {==}, U32.is_lt(U32.sub(j2, U32.shr(n)), U32.shr(U32.shr(n))), {==})
    case 1n+q TN{l, r} True{} False{}:
      {==}
    case 1n+q TN{l, r} False{} True{}:
      {==}

# In a perfect tree, a write at i1 leaves the word at i2 (both in range).
law T.word_other:
  for +p: Nat
  for +t: Tr
  for +i1: U32
  for +i2: U32
  for +v: U32
  for +hp: {T.pf(p, t) == True{} : Bool}
  for +hd: {Nat.cmp(p, 32n) == LT{} : Cmp}
  for +h1: {U32.is_lt(i1, U32.shln(1, p)) == True{} : Bool}
  for +h2: {U32.is_lt(i2, U32.shln(1, p)) == True{} : Bool}
  for +ne: {U32.is_eq(i1, i2) == False{} : Bool}
  {T.word(T.set(t, i1, v), i2) == T.word(t, i2) : U32}

def T.word_other(p, t, i1, i2, v, hp, hd, h1, h2, ne):
  %Equal.sym(U32, T.size(T.swap.go(t, T.size(t), T.mask(T.size(t), i1), v, T.half(T.size(t), i1))), T.size(t), T.size_swap(t, T.size(t), T.mask(T.size(t), i1), v, T.half(T.size(t), i1))) :
    {T.get.go(T.swap.go(t, T.size(t), T.mask(T.size(t), i1), v, T.half(T.size(t), i1)), _, T.mask(_, i2), T.half(_, i2))
      == T.get.go(t, T.size(t), T.mask(T.size(t), i2), T.half(T.size(t), i2)) : U32}
  %Equal.sym(U32, T.size(t), U32.shln(1, p), T.size_pf(p, t, hp)) :
    {T.get.go(T.swap.go(t, _, T.mask(_, i1), v, T.half(_, i1)), _, T.mask(_, i2), T.half(_, i2))
      == T.get.go(t, _, T.mask(_, i2), T.half(_, i2)) : U32}
  %Equal.sym(U32, U32.and(i1, U32.sub(U32.shln(1, p), 1)), i1, V.U.mask_id(i1, p, hd, h1)) :
    {T.get.go(T.swap.go(t, U32.shln(1, p), _, v, U32.is_lt(_, U32.shr(U32.shln(1, p)))), U32.shln(1, p), T.mask(U32.shln(1, p), i2),
      T.half(U32.shln(1, p), i2)) == T.get.go(t, U32.shln(1, p), T.mask(U32.shln(1, p), i2), T.half(U32.shln(1, p), i2)) : U32}
  %Equal.sym(U32, U32.and(i2, U32.sub(U32.shln(1, p), 1)), i2, V.U.mask_id(i2, p, hd, h2)) :
    {T.get.go(T.swap.go(t, U32.shln(1, p), i1, v, U32.is_lt(i1, U32.shr(U32.shln(1, p)))), U32.shln(1, p), _,
      U32.is_lt(_, U32.shr(U32.shln(1, p)))) == T.get.go(t, U32.shln(1, p), _, U32.is_lt(_, U32.shr(U32.shln(1, p)))) : U32}
  T.go_other(p, t, U32.shln(1, p), i1, i2, v, hp, hd, {==}, h1, h2, ne,
    U32.is_lt(i1, U32.shr(U32.shln(1, p))), {==}, U32.is_lt(i2, U32.shr(U32.shln(1, p))), {==})

# A new array, as a tree.
def T.new(+d: Nat, +v: U32) -> Tr:
  match d:
    case 0n:
      TL{v}
    case 1n+p:
      TN{T.new(p, v), T.new(p, v)}

law A.new_from:
  for +d: Nat
  for +v: U32
  {Array.new(U32, d, v) == A.from(T.new(d, v)) : Array<U32>}

def A.new_from(d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, Array.new(U32, p, v), A.from(T.new(p, v)), A.new_from(p, v)) :
        {ANode{_, _} == A.from(T.new(1n+p, v)) : Array<U32>}
      {==}

law T.pf_new:
  for +d: Nat
  for +v: U32
  {T.pf(d, T.new(d, v)) == True{} : Bool}

def T.pf_new(d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, T.pf(p, T.new(p, v)), True{}, T.pf_new(p, v)) :
        {Bool.and(_, _) == True{} : Bool}
      {==}

# Every word of a new tree is its fill value.
law T.go_new:
  for +d: Nat
  for +v: U32
  for +n: U32
  for +i: U32
  for +z: Bool
  {T.get.go(T.new(d, v), n, i, z) == v : U32}

def T.go_new(d, v, n, i, z):
  match d z:
    case 0n _:
      {==}
    case 1n+p True{}:
      T.go_new(p, v, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))
    case 1n+p False{}:
      T.go_new(p, v, U32.shr(n), U32.sub(i, U32.shr(n)),
        U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

law T.word_new:
  for +d: Nat
  for +v: U32
  for +i: U32
  {T.word(T.new(d, v), i) == v : U32}

def T.word_new(d, v, i):
  T.go_new(d, v, T.size(T.new(d, v)), T.mask(T.size(T.new(d, v)), i),
    T.half(T.size(T.new(d, v)), i))

# A clone of A.from(t) is two of it.
law A.clone_from:
  for +t: Tr
  {Array.clone(U32, A.from(t)) == (A.from(t), A.from(t)) : Array<U32> & Array<U32>}

def A.clone_from(t):
  match t:
    case TL{v}:
      {==}
    case TN{l, r}:
      %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.from(l)), (A.from(l), A.from(l)),
        A.clone_from(l)) :
        {Array.clone.node(U32, _, Array.clone(U32, A.from(r))) == (A.from(TN{l, r}), A.from(TN{l, r}))
          : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.from(r)), (A.from(r), A.from(r)),
        A.clone_from(r)) :
        {Array.clone.node(U32, (A.from(l), A.from(l)), _) == (A.from(TN{l, r}), A.from(TN{l, r}))
          : Array<U32> & Array<U32>}
      {==}

# A write keeps the tree's shape.
law T.pf_swap:
  for +d: Nat
  for +t: Tr
  for +n: U32
  for +i: U32
  for +v: U32
  for +z: Bool
  {T.pf(d, T.swap.go(t, n, i, v, z)) == T.pf(d, t) : Bool}

def T.pf_swap(d, t, n, i, v, z):
  match d t z:
    case 0n TL{w} _:
      {==}
    case 0n TN{l, r} True{}:
      {==}
    case 0n TN{l, r} False{}:
      {==}
    case 1n+p TL{w} _:
      {==}
    case 1n+p TN{l, r} True{}:
      %Equal.sym(Bool, T.pf(p, T.swap.go(l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))), T.pf(p, l),
        T.pf_swap(p, l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))) :
        {Bool.and(_, T.pf(p, r)) == Bool.and(T.pf(p, l), T.pf(p, r)) : Bool}
      {==}
    case 1n+p TN{l, r} False{}:
      %Equal.sym(Bool, T.pf(p, T.swap.go(r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))), T.pf(p, r),
        T.pf_swap(p, r, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) :
        {Bool.and(T.pf(p, l), _) == Bool.and(T.pf(p, l), T.pf(p, r)) : Bool}
      {==}

law T.pf_set:
  for +d: Nat
  for +t: Tr
  for +i: U32
  for +v: U32
  for +hp: {T.pf(d, t) == True{} : Bool}
  {T.pf(d, T.set(t, i, v)) == True{} : Bool}

def T.pf_set(d, t, i, v, hp):
  %Equal.sym(Bool, T.pf(d, T.set(t, i, v)), T.pf(d, t),
    T.pf_swap(d, t, T.size(t), T.mask(T.size(t), i), v, T.half(T.size(t), i))) :
    {_ == True{} : Bool}
  hp
