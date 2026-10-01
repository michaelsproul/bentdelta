import Base
import ./LAWS.bend as L
import ./proofs/top.bend as T

# The proofs are in proofs/: top.bend states the round trip from the
# pieces below it.
def L.roundtrip(src, tgt, small):
  T.T.main(src, tgt, small)
