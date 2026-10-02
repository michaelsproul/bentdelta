import Base
import ./bytes.bend as B
import ./vcdiff.bend as V
import ./encode.bend as N

# The encoder and decoder the law in LAWS.bend is about: encode.bend makes
# the delta and vcdiff.bend decodes it. PROOF.bend proves that decoding the
# delta gives back the target.

# A delta that turns src into tgt.
def encode(src: B.Bytes, tgt: B.Bytes) -> B.Bytes:
  Pair.snd(B.Bytes & B.Bytes, B.Bytes, N.encode(src, tgt))

# What decoding d against src gives, as a list of bytes.
def restore.k(r: B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)) ->
  Result<&1, &1, U32, List<&2, U32>>:
  match r:
    case Tuple{s, Tuple{d, Done{x}}}:
      Done{B.B.list(x)}
    case Tuple{s, Tuple{d, Fail{e}}}:
      Fail{e}

def restore(src: B.Bytes, d: B.Bytes) -> Result<&1, &1, U32, List<&2, U32>>:
  restore.k(V.decode(src, d))
