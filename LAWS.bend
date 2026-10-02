import Base
import ./bytes.bend as B
import ./codec.bend as C

# The laws bentdelta keeps. PROOF.bend proves each one.

# Round trip: for any source and any target under 2 GiB less 1 MiB
# (2^31 - 2^20 bytes), the delta that bentdelta's encoder makes, decoded
# against the same source by bentdelta's decoder, gives back exactly the
# bytes of the target.
law roundtrip:
  for src: B.Bytes
  for tgt: B.Bytes
  for small: {U32.is_lt(B.B.len(tgt), 2146435072) == True{} : Bool}
  {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)}
    : Result<&1, &1, U32, List<&2, U32>>}
