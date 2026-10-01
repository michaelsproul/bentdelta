import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ../encode.bend as N
import ../check.bend as C
import ./array.bend as A
import ./decode.bend as R
import ./eq.bend as Q

# The round trip: the check either keeps a delta that decoded to the target
# (and decoding is a function, so it decodes so again) or falls back to the
# plain encoding, which always decodes to the target (proofs/decode.bend).

# Views
# =====

# Every array is the array of some tree, and every byte string is a length
# and a tree; proofs then work with the Data side, free to reuse it.

law T.av.k:
  for -l: Array<U32>
  for -r: Array<U32>
  for vl: &tl:A.Tr -> {l == A.A.from(tl) : Array<U32>}
  for vr: &tr:A.Tr -> {r == A.A.from(tr) : Array<U32>}
  exs t: A.Tr
  {ANode{l, r} == A.A.from(t) : Array<U32>}

def T.av.k(l, r, vl, vr):
  match vl vr:
    case Tuple{tl, el} Tuple{tr, er}:
      (A.TN{tl, tr}, (%Equal.sym(Array<U32>, l, A.A.from(tl), el) :
          {ANode{_, r} == ANode{A.A.from(tl), A.A.from(tr)} : Array<U32>}
        (%Equal.sym(Array<U32>, r, A.A.from(tr), er) :
            {ANode{A.A.from(tl), _} == ANode{A.A.from(tl), A.A.from(tr)} : Array<U32>}
          {==})))

law T.av:
  for a: Array<U32>
  exs t: A.Tr
  {a == A.A.from(t) : Array<U32>}

def T.av(a):
  match a:
    case ALeaf{v}:
      (A.TL{v}, {==})
    case ANode{l, r}:
      T.av.k(l, r, T.av(l), T.av(r))

type BV is Data:
  BV{len: U32, t: A.Tr}

def T.bytes(+v: BV) -> B.Bytes:
  match v:
    case BV{len, t}:
      B.Bytes{len, A.A.from(t)}

law T.bv.k:
  for +len: U32
  for -buf: Array<U32>
  for vb: &t:A.Tr -> {buf == A.A.from(t) : Array<U32>}
  exs v: BV
  {B.Bytes{len, buf} == T.bytes(v) : B.Bytes}

def T.bv.k(len, buf, vb):
  match vb:
    case Tuple{t, e}:
      (BV{len, t}, (%Equal.sym(Array<U32>, buf, A.A.from(t), e) : {B.Bytes{len, _} == B.Bytes{len, A.A.from(t)} : B.Bytes}
        {==}))

law T.bv:
  for b: B.Bytes
  exs v: BV
  {b == T.bytes(v) : B.Bytes}

def T.bv(b):
  match b:
    case B.Bytes{+len, buf}:
      T.bv.k(len, buf, T.av(buf))

law T.clone:
  for +len: U32
  for +t: A.Tr
  {B.B.clone(B.Bytes{len, A.A.from(t)}) == (B.Bytes{len, A.A.from(t)}, B.Bytes{len, A.A.from(t)}) : B.Bytes & B.Bytes}

def T.clone(len, t):
  %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.A.from(t)), (A.A.from(t), A.A.from(t)), A.A.clone_from(t)) :
    {B.B.clone.k(len, _) == (B.Bytes{len, A.A.from(t)}, B.Bytes{len, A.A.from(t)}) : B.Bytes & B.Bytes}
  {==}

# The check
# =========

def T.S(+sl: U32, +st: A.Tr) -> B.Bytes:
  B.Bytes{sl, A.A.from(st)}

law T.res.z:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +dl: U32
  for +dt: A.Tr
  for +xl: U32
  for +xt: A.Tr
  for +hl: {U32.is_lt(tl, 134217728) == True{} : Bool}
  for -s: B.Bytes
  for -d1: B.Bytes
  for er: {D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}) == (s, (d1, Done{B.Bytes{xl, A.A.from(xt)}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
  for +z: Bool
  for +ez: {Q.E.w(U32.to_nat(B.B.words(xl)), 0, xt, tt, U32.is_eq(xl, tl)) == z : Bool}
  {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.ok(z, B.Bytes{tl, A.A.from(tt)}, B.Bytes{dl, A.A.from(dt)})) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.res.z(sl, st, tl, tt, dl, dt, xl, xt, hl, s, d1, er, z, ez):
  match z:
    case True{}:
      %Equal.sym(B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>), D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}), (s, (d1, Done{B.Bytes{xl, A.A.from(xt)}})), er) :
        {C.restore.k(_) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, B.B.list(B.Bytes{xl, A.A.from(xt)}), B.B.list(B.Bytes{tl, A.A.from(tt)}), Q.E.sound(xl, xt, tl, tt, hl, ez)) :
        {Done{_} == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      {==}
    case False{}:
      R.FB.ok(B.Bytes{sl, A.A.from(st)}, tl, tt, hl)

law T.res.done:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +dl: U32
  for +dt: A.Tr
  for +hl: {U32.is_lt(tl, 134217728) == True{} : Bool}
  for -s: B.Bytes
  for -d1: B.Bytes
  for -x: B.Bytes
  for vx: &v:BV -> {x == T.bytes(v) : B.Bytes}
  {D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}) == (s, (d1, Done{x})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
    -> {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.cmp(B.Bytes{tl, A.A.from(tt)}, B.Bytes{dl, A.A.from(dt)}, B.B.eq(x, B.Bytes{tl, A.A.from(tt)}))) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.res.done(sl, st, tl, tt, dl, dt, hl, s, d1, x, vx):
  match vx:
    case Tuple{BV{+xl, +xt}, ex}:
      %Equal.sym(B.Bytes, x, B.Bytes{xl, A.A.from(xt)}, ex) :
        {D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}) == (s, (d1, Done{_})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
          -> {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.cmp(B.Bytes{tl, A.A.from(tt)}, B.Bytes{dl, A.A.from(dt)}, B.B.eq(_, B.Bytes{tl, A.A.from(tt)}))) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      er =>
        %Equal.sym((Array<U32> & Array<U32>) & Bool, B.B.eq.words(U32.to_nat(B.B.words(xl)), 0, (U32.is_eq(xl, tl), (A.A.from(xt), A.A.from(tt)))), ((A.A.from(xt), A.A.from(tt)), Q.E.w(U32.to_nat(B.B.words(xl)), 0, xt, tt, U32.is_eq(xl, tl))),
          Q.E.loop(U32.to_nat(B.B.words(xl)), 0, xt, tt, U32.is_eq(xl, tl))) :
          {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.cmp(B.Bytes{tl, A.A.from(tt)}, B.Bytes{dl, A.A.from(dt)}, B.B.eq.fin(xl, tl, _))) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
        T.res.z(sl, st, tl, tt, dl, dt, xl, xt, hl, s, d1, er, Q.E.w(U32.to_nat(B.B.words(xl)), 0, xt, tt, U32.is_eq(xl, tl)), {==})

# What decoding the candidate gave: the target (kept) or anything else
# (the plain encoding instead).
law T.res:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +dl: U32
  for +dt: A.Tr
  for +hl: {U32.is_lt(tl, 134217728) == True{} : Bool}
  for r: B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)
  for er: {D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}) == r : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}
  {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.res(B.Bytes{tl, A.A.from(tt)}, B.Bytes{tl, A.A.from(tt)}, B.Bytes{dl, A.A.from(dt)}, r)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.res(sl, st, tl, tt, dl, dt, hl, r, er):
  match r:
    case Tuple{s, Tuple{d1, Done{x}}}:
      T.res.done(sl, st, tl, tt, dl, dt, hl, s, d1, x, T.bv(x))(er)
    case Tuple{s, Tuple{d1, Fail{e}}}:
      R.FB.ok(B.Bytes{sl, A.A.from(st)}, tl, tt, hl)

law T.chk:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +hl: {U32.is_lt(tl, 134217728) == True{} : Bool}
  for -d: B.Bytes
  for vd: &v:BV -> {d == T.bytes(v) : B.Bytes}
  {C.restore(B.Bytes{sl, A.A.from(st)}, C.check(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)}, d)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.chk(sl, st, tl, tt, hl, d, vd):
  match vd:
    case Tuple{BV{+dl, +dt}, ed}:
      %Equal.sym(B.Bytes, d, B.Bytes{dl, A.A.from(dt)}, ed) : {C.restore(B.Bytes{sl, A.A.from(st)}, C.check(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)}, _)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      %Equal.sym(B.Bytes & B.Bytes, B.B.clone(B.Bytes{tl, A.A.from(tt)}), (B.Bytes{tl, A.A.from(tt)}, B.Bytes{tl, A.A.from(tt)}), T.clone(tl, tt)) :
        {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.go(B.Bytes{sl, A.A.from(st)}, _, B.B.clone(B.Bytes{dl, A.A.from(dt)}))) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      %Equal.sym(B.Bytes & B.Bytes, B.B.clone(B.Bytes{dl, A.A.from(dt)}), (B.Bytes{dl, A.A.from(dt)}, B.Bytes{dl, A.A.from(dt)}), T.clone(dl, dt)) :
        {C.restore(B.Bytes{sl, A.A.from(st)}, C.chk.go(B.Bytes{sl, A.A.from(st)}, (B.Bytes{tl, A.A.from(tt)}, B.Bytes{tl, A.A.from(tt)}), _)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
      T.res(sl, st, tl, tt, dl, dt, hl, D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{dl, A.A.from(dt)}), {==})

law T.enc:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +hl: {U32.is_lt(tl, 134217728) == True{} : Bool}
  {C.restore(B.Bytes{sl, A.A.from(st)}, C.encode(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)})) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.enc(sl, st, tl, tt, hl):
  %Equal.sym(B.Bytes & B.Bytes, B.B.clone(B.Bytes{sl, A.A.from(st)}), (B.Bytes{sl, A.A.from(st)}, B.Bytes{sl, A.A.from(st)}), T.clone(sl, st)) :
    {C.restore(B.Bytes{sl, A.A.from(st)}, C.enc.go(_, B.B.clone(B.Bytes{tl, A.A.from(tt)}))) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
  %Equal.sym(B.Bytes & B.Bytes, B.B.clone(B.Bytes{tl, A.A.from(tt)}), (B.Bytes{tl, A.A.from(tt)}, B.Bytes{tl, A.A.from(tt)}), T.clone(tl, tt)) :
    {C.restore(B.Bytes{sl, A.A.from(st)}, C.enc.go((B.Bytes{sl, A.A.from(st)}, B.Bytes{sl, A.A.from(st)}), _)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
  T.chk(sl, st, tl, tt, hl, Pair.snd(B.Bytes & B.Bytes, B.Bytes, N.encode(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)})),
    T.bv(Pair.snd(B.Bytes & B.Bytes, B.Bytes, N.encode(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)}))))

# The round trip
# ==============

law T.main.v:
  for -src: B.Bytes
  for -tgt: B.Bytes
  for vs: &v:BV -> {src == T.bytes(v) : B.Bytes}
  for vt: &v:BV -> {tgt == T.bytes(v) : B.Bytes}
  {U32.is_lt(B.B.len(tgt), 134217728) == True{} : Bool}
    -> {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}

def T.main.v(src, tgt, vs, vt):
  match vs vt:
    case Tuple{BV{+sl, +st}, es} Tuple{BV{+tl, +tt}, et}:
      %Equal.sym(B.Bytes, src, B.Bytes{sl, A.A.from(st)}, es) :
        {U32.is_lt(B.B.len(tgt), 134217728) == True{} : Bool}
          -> {C.restore(_, C.encode(_, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}
      %Equal.sym(B.Bytes, tgt, B.Bytes{tl, A.A.from(tt)}, et) :
        {U32.is_lt(B.B.len(_), 134217728) == True{} : Bool}
          -> {C.restore(B.Bytes{sl, A.A.from(st)}, C.encode(B.Bytes{sl, A.A.from(st)}, _)) == Done{B.B.list(_)} : Result<&1, &1, U32, List<&2, U32>>}
      small => T.enc(sl, st, tl, tt, small)

law T.main:
  for src: B.Bytes
  for tgt: B.Bytes
  for small: {U32.is_lt(B.B.len(tgt), 134217728) == True{} : Bool}
  {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}

def T.main(src, tgt, small):
  T.main.v(src, tgt, T.bv(src), T.bv(tgt))(small)
