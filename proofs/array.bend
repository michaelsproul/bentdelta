import Base
import ./nat.bend as P

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
