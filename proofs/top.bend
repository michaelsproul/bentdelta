import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ../encode.bend as N
import ../codec.bend as C
import ./array.bend as A
import ./spec.bend as Q
import ./wstart.bend as WS_
import ./dtop.bend as DT_
import ./etop.bend as TP_

# The round trip: the encoder's delta is the output of its run of windows
# (proofs/etop.bp), which the decoder turns back into the target
# (proofs/dtop.bp).

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

# The encoder
# ===========

law T.enc:
  for +sl: U32
  for +st: A.Tr
  for +tl: U32
  for +tt: A.Tr
  for +hl: {U32.is_lt(tl, 2146435072) == True{} : Bool}
  {C.restore(B.Bytes{sl, A.A.from(st)}, C.encode(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)})) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}

def T.enc(sl, st, tl, tt, hl):
  %Equal.sym((B.Bytes & B.Bytes) & B.Bytes, N.encode(B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)}), ((B.Bytes{sl, A.A.from(st)}, B.Bytes{tl, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP_.TP.FF(sl, tl, st, tt)), A.A.from(WS_.WS.to(TP_.TP.FF(sl, tl, st, tt)))}), TP_.TP.enc_code(sl, tl, st, tt, hl)) :
    {C.restore(B.Bytes{sl, A.A.from(st)}, Pair.snd(B.Bytes & B.Bytes, B.Bytes, _)) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
  %Equal.sym(B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>), D.decode(B.Bytes{sl, A.A.from(st)}, B.Bytes{WS_.WS.olen(TP_.TP.FF(sl, tl, st, tt)), A.A.from(WS_.WS.to(TP_.TP.FF(sl, tl, st, tt)))}), (B.Bytes{sl, A.A.from(st)}, (B.Bytes{WS_.WS.olen(TP_.TP.FF(sl, tl, st, tt)), A.A.from(WS_.WS.to(TP_.TP.FF(sl, tl, st, tt)))}, Done{B.Bytes{tl, A.A.from(Q.SP.wto(TP_.TP.WW(sl, tl, st, tt), st, tt, A.T.new(DT_.O.dep(tl), 0), 0))}})), TP_.TP.dec(sl, tl, st, tt, hl)) :
    {C.restore.k(_) == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, B.B.list(B.Bytes{tl, A.A.from(Q.SP.wto(TP_.TP.WW(sl, tl, st, tt), st, tt, A.T.new(DT_.O.dep(tl), 0), 0))}), B.B.list(B.Bytes{tl, A.A.from(tt)}), TP_.TP.list(sl, tl, st, tt, hl)) :
    {Done{_} == Done{B.B.list(B.Bytes{tl, A.A.from(tt)})} : Result<&1, &1, U32, List<&2, U32>>}
  {==}

# The round trip
# ==============

law T.main.v:
  for -src: B.Bytes
  for -tgt: B.Bytes
  for vs: &v:BV -> {src == T.bytes(v) : B.Bytes}
  for vt: &v:BV -> {tgt == T.bytes(v) : B.Bytes}
  {U32.is_lt(B.B.len(tgt), 2146435072) == True{} : Bool}
    -> {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}

def T.main.v(src, tgt, vs, vt):
  match vs vt:
    case Tuple{BV{+sl, +st}, es} Tuple{BV{+tl, +tt}, et}:
      %Equal.sym(B.Bytes, src, B.Bytes{sl, A.A.from(st)}, es) :
        {U32.is_lt(B.B.len(tgt), 2146435072) == True{} : Bool}
          -> {C.restore(_, C.encode(_, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}
      %Equal.sym(B.Bytes, tgt, B.Bytes{tl, A.A.from(tt)}, et) :
        {U32.is_lt(B.B.len(_), 2146435072) == True{} : Bool}
          -> {C.restore(B.Bytes{sl, A.A.from(st)}, C.encode(B.Bytes{sl, A.A.from(st)}, _)) == Done{B.B.list(_)} : Result<&1, &1, U32, List<&2, U32>>}
      small => T.enc(sl, st, tl, tt, small)

law T.main:
  for src: B.Bytes
  for tgt: B.Bytes
  for small: {U32.is_lt(B.B.len(tgt), 2146435072) == True{} : Bool}
  {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)} : Result<&1, &1, U32, List<&2, U32>>}

def T.main(src, tgt, small):
  T.main.v(src, tgt, T.bv(src), T.bv(tgt))(small)
