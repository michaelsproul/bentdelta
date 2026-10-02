import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ../encode.bend as N
import ./nat.bend as P
import ./word.bend as W
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./words.bend as K
import ./copy.bend as C
import ./spec.bend as Q
import ./bits.bend as Z
import ./match.bend as MT_
import ./emit.bend as EM_
import ./settle.bend as SE_
import ./segm.bend as SG_

# The scan
import ./scan.bend as SC_
import ./wstart.bend as WS_
import ./wspec.bend as WP_
import ./wloop.bend as WL_
import ./wwrite.bend as WW_
import ./wfin.bend as WF_
import ./einst.bend as EI_
import ./adler.bend as H
import ./varint.bend as R
import ./dwin.bend as J



# Tasks
# =====
#
# enc.par: the windows split between tasks, each with copies of the source,
# the target and the index and its own emitter and output; the outputs
# joined in order.
#
# Source: proofs/wpar.bp (tools/bpp.py writes proofs/wpar.bend from it).

law WR.lit0:
  {[0 : U32^0n] == A.A.from(A.TL{0}) : Array<U32>}

def WR.lit0():
  {==}

# A task's fresh state, with its copy of the index.
def WR.fresh(+tl: A.Tr, +ocap: U32, +lidx: U32, +cont: U32) -> WS_.EST:
  WS_.EST{tl, A.TL{0}, A.TL{0}, A.T.new(17n, 0), EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.T.new(B.B.depth(B.B.words(ocap)), 0), 0, lidx, cont}

law WR.fresh_code:
  for +sbits: Nat
  for +wb: U32
  for +ocap: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +tl: A.Tr
  for +lidx: U32
  for +cont: U32
  {N.es.fresh(sbits, wb, ocap, A.A.from(ts), A.A.from(tt), A.A.from(tl), lidx, cont) == WS_.WS.es(ts, tt, WR.fresh(tl, ocap, lidx, cont)) : N.ES}

def WR.fresh_code(sbits, wb, ocap, ts, tt, tl, lidx, cont):
  %Equal.sym(Array<U32>, Array.new(U32, 17n, 0), A.A.from(A.T.new(17n, 0)), A.A.new_from(17n, 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), [0 : U32^0n], [0 : U32^0n], _, N.Em{Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, Array.new(U32, B.B.depth(B.B.words(ocap)), 0), 0, lidx, cont} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(A.T.new(B.B.depth(B.B.words(ocap)), 0)), 0, lidx, cont} : N.ES}
  %Equal.sym(Array<U32>, Array.new(U32, B.B.depth(B.B.words(65536)), 0), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.new_from(B.B.depth(B.B.words(65536)), 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), [0 : U32^0n], [0 : U32^0n], A.A.from(A.T.new(17n, 0)), N.Em{_, _, _, Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, Array.new(U32, B.B.depth(B.B.words(ocap)), 0), 0, lidx, cont} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(A.T.new(B.B.depth(B.B.words(ocap)), 0)), 0, lidx, cont} : N.ES}
  %Equal.sym(Array<U32>, Array.new(U32, 10n, 0), A.A.from(A.T.new(10n, 0)), A.A.new_from(10n, 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), [0 : U32^0n], [0 : U32^0n], A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), _, 0, 0, 0, 0, 0, 0, 0, 0, 0}, Array.new(U32, B.B.depth(B.B.words(ocap)), 0), 0, lidx, cont} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(A.T.new(B.B.depth(B.B.words(ocap)), 0)), 0, lidx, cont} : N.ES}
  %Equal.sym(Array<U32>, Array.new(U32, B.B.depth(B.B.words(ocap)), 0), A.A.from(A.T.new(B.B.depth(B.B.words(ocap)), 0)), A.A.new_from(B.B.depth(B.B.words(ocap)), 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), [0 : U32^0n], [0 : U32^0n], A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, _, 0, lidx, cont} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(A.T.new(B.B.depth(B.B.words(ocap)), 0)), 0, lidx, cont} : N.ES}
  {==}

# The run's bounds
# ----------------
#
# What every window needs of the bounds, from facts about the source and
# target lengths and the window size (Et and Ea are the target's length).
def WR.G(+E: N.EK, +Eb: U32, +BIGs: U32, +BIGe: U32, +HB: U32, +Es: U32, +S: U32, +Eo: U32) -> Bool:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))))

law WR.G.r1:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))) == True{} : Bool}

def WR.G.r1(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)

law WR.G.r2:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))) == True{} : Bool}

def WR.G.r2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))

law WR.G.r3a:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_le(slen, U32.add(slen, wsz)) == True{} : Bool}

def WR.G.r3a(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)))

law WR.G.r3b:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))) == True{} : Bool}

def WR.G.r3b(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))

law WR.G.r4:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))) == True{} : Bool}

def WR.G.r4(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)))))

law WR.G.r5:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_lt(BIGs, 2147483648) == True{} : Bool}

def WR.G.r5(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))))

law WR.G.r6:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))) == True{} : Bool}

def WR.G.r6(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)))))))

law WR.G.r7:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_lt(BIGe, 2147483648) == True{} : Bool}

def WR.G.r7(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))))))

law WR.G.r8:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))) == True{} : Bool}

def WR.G.r8(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)))))))))

law WR.G.r9:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))) == True{} : Bool}

def WR.G.r9(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))))))))

law WR.G.r10:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_le(slen, S) == True{} : Bool}

def WR.G.r10(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h)))))))))))

law WR.G.r11:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_le(tlen, 2147483648) == True{} : Bool}

def WR.G.r11(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_l(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648), P.Bool.and_r(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))))))))))

law WR.G.r12:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  {U32.is_lt(Eo, 2147483648) == True{} : Bool}

def WR.G.r12(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h):
  P.Bool.and_r(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648), P.Bool.and_r(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(Eb))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe))), Bool.and(U32.is_lt(BIGe, 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(Eo, 2147483648)))))))))))), h))))))))))))

law WR.le_trans_u:
  for +a: U32
  for +b: U32
  for +c: U32
  for +h1: {U32.is_le(a, b) == True{} : Bool}
  for +h2: {U32.is_le(b, c) == True{} : Bool}
  {U32.is_le(a, c) == True{} : Bool}

def WR.le_trans_u(a, b, c, h1, h2):
  V.U.N_le(a, c, P.Nat.le_trans(V.U.N(a), V.U.N(b), V.U.N(c), V.U.le_N(a, b, h1), V.U.le_N(b, c, h2)))

# x - z <= y - z, for z <= x <= y.
law WR.sub_mono:
  for +x: U32
  for +y: U32
  for +z: U32
  for +hxy: {U32.is_le(x, y) == True{} : Bool}
  for +hz: {U32.is_le(z, x) == True{} : Bool}
  {U32.is_le(U32.sub(x, z), U32.sub(y, z)) == True{} : Bool}

def WR.sub_mono(x, y, z, hxy, hz):
  V.U.N_le(U32.sub(x, z), U32.sub(y, z), SC_.SC.nd(V.U.N(U32.sub(x, z)), V.U.N(z), V.U.N(x), V.U.N(U32.sub(y, z)), V.U.N(y), V.U.sub_nat(x, z, hz), V.U.sub_nat(y, z, WR.le_trans_u(z, x, y, hz, hxy)), V.U.le_N(x, y, hxy)))

# A difference is at most the larger value.
law WR.sub_le:
  for +x: U32
  for +z: U32
  for +hz: {U32.is_le(z, x) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(x, z)), V.U.N(x))) == True{} : Bool}

def WR.sub_le(x, z, hz):
  (%V.U.sub_nat(x, z, hz) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(x, z)), _)) == True{} : Bool};
    P.Nat.cmp_add_r(V.U.N(U32.sub(x, z)), V.U.N(z)))

# A window's facts, from the run's bounds: it starts in the target.
law WR.wh_of:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ha: {U32.is_le(w0, tlen) == True{} : Bool}
  for +hb: {U32.is_le(w0, U32.add(w0, wsz)) == True{} : Bool}
  {WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo) == True{} : Bool}

def WR.wh_of(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, Eb, BIGs, BIGe, HB, Es, S, Eo, h, ha, hb):
  SC_.SC.and_tt(U32.is_le(w0, WL_.WL.w1(tlen, w0, wsz)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WL_.WL.w1(tlen, w0, wsz)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), WL_.WL.w01(tlen, w0, wsz, ha, hb), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WL_.WL.w1(tlen, w0, wsz)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), WR.G.r1(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WL_.WL.w1(tlen, w0, wsz)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Nat.le_trans(Nat.add(V.U.N(WL_.WL.w1(tlen, w0, wsz)), 9n), Nat.add(V.U.N(tlen), 9n), V.U.N(Eb), MT_.MT.add_le(V.U.N(WL_.WL.w1(tlen, w0, wsz)), V.U.N(tlen), 9n, 9n, WL_.WL.w1T(tlen, w0, wsz), C.CP.le_refl(9n)), WR.G.r2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Nat.le_trans(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(U32.add(slen, wsz)), V.U.N(Eb), (%Equal.sym(Nat, V.U.N(U32.add(slen, wsz)), Nat.add(V.U.N(slen), V.U.N(wsz)), V.U.add_nowrap(slen, wsz, WR.G.r3a(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(slen), V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(wsz), C.CP.le_refl(V.U.N(slen)), WL_.WL.wk(tlen, w0, wsz, ha, hb))), WR.G.r3b(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Nat.le_trans(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(BIGs), P.Nat.double_mono(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)))), Nat.double(SG_.SG.tri(1n+V.U.N(wsz))), P.Nat.double_mono(SG_.SG.tri(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), SG_.SG.tri(1n+V.U.N(wsz)), SG_.SG.tri_mono(1n+V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), 1n+V.U.N(wsz), WL_.WL.wk(tlen, w0, wsz, ha, hb)))), WR.G.r4(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), SC_.SC.and_tt(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), WR.G.r5(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h), SC_.SC.and_tt(WS_.WS.wokv(w0, WL_.WL.w1(tlen, w0, wsz), tlen, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), SC_.SC.and_tt(U32.is_le(w0, WL_.WL.w1(tlen, w0, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WL_.WL.w1(tlen, w0, wsz)), V.U.N(tlen))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), 16n), V.U.N(BIGe))))), WL_.WL.w01(tlen, w0, wsz, ha, hb), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(V.U.N(WL_.WL.w1(tlen, w0, wsz)), V.U.N(tlen))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), 16n), V.U.N(BIGe)))), WL_.WL.w1T(tlen, w0, wsz), SC_.SC.and_tt(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), 16n), V.U.N(BIGe))), WR.G.r7(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h), P.Nat.le_trans(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), 16n), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(BIGe), MT_.MT.add_le(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))))), Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n, 16n, P.Nat.double_mono(Nat.double(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)))), Nat.double(Nat.double(V.U.N(wsz))), P.Nat.double_mono(Nat.double(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), Nat.double(V.U.N(wsz)), P.Nat.double_mono(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(wsz), WL_.WL.wk(tlen, w0, wsz, ha, hb)))), C.CP.le_refl(16n)), WR.G.r6(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h))))), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Nat.le_trans(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), V.U.N(U32.add(slen, wsz)), V.U.N(HB), (%Equal.sym(Nat, V.U.N(U32.add(slen, wsz)), Nat.add(V.U.N(slen), V.U.N(wsz)), V.U.add_nowrap(slen, wsz, WR.G.r3a(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(slen), V.U.N(slen), V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(wsz), C.CP.le_refl(V.U.N(slen)), WL_.WL.wk(tlen, w0, wsz, ha, hb))), WR.G.r8(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), WR.G.r9(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(tlen))), Bool.and(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(WL_.WL.w1(tlen, w0, wsz)), V.U.sub_nat(WL_.WL.w1(tlen, w0, wsz), w0, WL_.WL.w01(tlen, w0, wsz, ha, hb))) : {Cmp.is_le(Nat.cmp(_, V.U.N(tlen))) == True{} : Bool}; WL_.WL.w1T(tlen, w0, wsz)), SC_.SC.and_tt(U32.is_le(slen, S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))), WR.G.r10(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h), SC_.SC.and_tt(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)), WR.le_trans_u(w0, tlen, 2147483648, ha, WR.G.r11(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), SC_.SC.and_tt(U32.is_le(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648), WR.sub_mono(WL_.WL.w1(tlen, w0, wsz), 2147483648, w0, WR.le_trans_u(WL_.WL.w1(tlen, w0, wsz), tlen, 2147483648, V.U.N_le(WL_.WL.w1(tlen, w0, wsz), tlen, WL_.WL.w1T(tlen, w0, wsz)), WR.G.r11(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h)), WL_.WL.w01(tlen, w0, wsz, ha, hb)), WR.G.r12(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, h))))))))))))))

# Splitting the windows
# ---------------------

# Twice half n is n at most.
law WR.hh:
  for +n: Nat
  {Cmp.is_le(Nat.cmp(Nat.double(P.Nat.half(n)), n)) == True{} : Bool}

def WR.hh(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          WR.hh(q)

law WR.nl_le:
  for +nw: U32
  {U32.is_le(U32.shrn(nw, 1n), nw) == True{} : Bool}

def WR.nl_le(nw):
  V.U.N_le(U32.shrn(nw, 1n), nw, (%Equal.sym(Nat, V.U.N(U32.shr(nw)), P.Nat.half(V.U.N(nw)), V.U.N_shr(nw)) : {Cmp.is_le(Nat.cmp(_, V.U.N(nw))) == True{} : Bool};
    P.Nat.le_trans(P.Nat.half(V.U.N(nw)), Nat.double(P.Nat.half(V.U.N(nw))), V.U.N(nw), (%Equal.sym(Nat, Nat.double(P.Nat.half(V.U.N(nw))), Nat.add(P.Nat.half(V.U.N(nw)), P.Nat.half(V.U.N(nw))), P.Nat.double_add(P.Nat.half(V.U.N(nw)))) : {Cmp.is_le(Nat.cmp(P.Nat.half(V.U.N(nw)), _)) == True{} : Bool};
      P.Nat.cmp_add_r(P.Nat.half(V.U.N(nw)), P.Nat.half(V.U.N(nw)))), WR.hh(V.U.N(nw)))))

# Of nw >= 2m windows, each half has m at least.
law WR.halfL:
  for +nw: U32
  for +m: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.double(m), V.U.N(nw))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(m, V.U.N(U32.shrn(nw, 1n)))) == True{} : Bool}

def WR.halfL(nw, m, h):
  (%Equal.sym(Nat, V.U.N(U32.shr(nw)), P.Nat.half(V.U.N(nw)), V.U.N_shr(nw)) : {Cmp.is_le(Nat.cmp(m, _)) == True{} : Bool};
    (%P.Nat.half_double(m) : {Cmp.is_le(Nat.cmp(_, P.Nat.half(V.U.N(nw)))) == True{} : Bool};
      P.Nat.half_mono(Nat.double(m), V.U.N(nw), h)))

law WR.halfR:
  for +nw: U32
  for +m: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.double(m), V.U.N(nw))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(m, V.U.N(U32.sub(nw, U32.shrn(nw, 1n))))) == True{} : Bool}

def WR.halfR(nw, m, h):
  P.Nat.le_trans(m, V.U.N(U32.shrn(nw, 1n)), V.U.N(U32.sub(nw, U32.shrn(nw, 1n))), WR.halfL(nw, m, h),
    (%P.Nat.cmp_add_rr(V.U.N(U32.shrn(nw, 1n)), V.U.N(U32.sub(nw, U32.shrn(nw, 1n))), V.U.N(U32.shrn(nw, 1n))) : {Cmp.is_le(_) == True{} : Bool};
      (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(nw, U32.shrn(nw, 1n))), V.U.N(U32.shrn(nw, 1n))), V.U.N(nw), V.U.sub_nat(nw, U32.shrn(nw, 1n), WR.nl_le(nw))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.shrn(nw, 1n)), V.U.N(U32.shrn(nw, 1n))), _)) == True{} : Bool};
        (%P.Nat.double_add(V.U.N(U32.shrn(nw, 1n))) : {Cmp.is_le(Nat.cmp(_, V.U.N(nw))) == True{} : Bool};
          (%Equal.sym(Nat, V.U.N(U32.shr(nw)), P.Nat.half(V.U.N(nw)), V.U.N_shr(nw)) : {Cmp.is_le(Nat.cmp(Nat.double(_), V.U.N(nw))) == True{} : Bool};
            WR.hh(V.U.N(nw)))))))

law WR.pos_add:
  for +a: Nat
  for +c: Nat
  for +hc: {Cmp.is_le(Nat.cmp(1n, c)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(1n, Nat.add(a, c))) == True{} : Bool}

def WR.pos_add(a, c, hc):
  match a:
    case 0n:
      hc
    case 1n+r:
      SE_.SE.le0(Nat.add(r, c))

# A window with more after it is whole.
law WR.lastw:
  for +n: Nat
  for +w: U32
  for +cend: U32
  for +T: U32
  for +wsz: U32
  for +hn: {Cmp.is_le(Nat.cmp(1n, n)) == True{} : Bool}
  for +h: {WL_.WL.last(n, w, cend, T, wsz) == True{} : Bool}
  {U32.is_le(U32.add(w, wsz), T) == True{} : Bool}

def WR.lastw(n, w, cend, T, wsz, hn, h):
  match n:
    case 0n:
      P.Bool.false_true({U32.is_le(U32.add(w, wsz), T) == True{} : Bool}, hn)
    case 1n+r:
      h

# A whole window ends where the windows after it start.
law WR.last_mid:
  for +p: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  for +hle: {U32.is_le(U32.add(w, wsz), T) == True{} : Bool}
  {WL_.WL.last(p, w, N.adv(p, U32.add(w, wsz), wsz), T, wsz) == True{} : Bool}

def WR.last_mid(p, w, T, wsz, hle):
  match p:
    case 0n:
      %Equal.sym(U32, WL_.WL.w1(T, w, wsz), U32.add(w, wsz), WL_.WL.wnext(T, w, wsz, hle)) : {U32.is_eq(_, U32.add(w, wsz)) == True{} : Bool}
      V.U.is_eq_refl(U32.add(w, wsz))
    case 1n+r:
      hle

# a + c windows from w, c of them at least one: the first a, to where they
# end, and the c from there.
law WR.tile_split:
  for +a: Nat
  for +c: Nat
  for +w: U32
  for +cend: U32
  for +T: U32
  for +wsz: U32
  for +hc: {Cmp.is_le(Nat.cmp(1n, c)) == True{} : Bool}
  for +h: {WL_.WL.tile(Nat.add(a, c), w, cend, T, wsz) == True{} : Bool}
  {Bool.and(WL_.WL.tile(a, w, N.adv(a, w, wsz), T, wsz), WL_.WL.tile(c, N.adv(a, w, wsz), cend, T, wsz)) == True{} : Bool}

def WR.tile_split(a, c, w, cend, T, wsz, hc, h):
  match a:
    case 0n:
      SC_.SC.and_tt(True{}, WL_.WL.tile(c, w, cend, T, wsz), {==}, h)
    case 1n+p:
      +ih = WR.tile_split(p, c, U32.add(w, wsz), cend, T, wsz, hc, P.Bool.and_r(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz), P.Bool.and_r(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz)), P.Bool.and_r(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz))), h))))
      SC_.SC.and_tt(WL_.WL.tile(1n+p, w, N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(c, N.adv(p, U32.add(w, wsz), wsz), cend, T, wsz), SC_.SC.and_tt(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(p, w, N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(p, U32.add(w, wsz), N.adv(p, U32.add(w, wsz), wsz), T, wsz))), P.Bool.and_l(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz))), h), SC_.SC.and_tt(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(p, w, N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(p, U32.add(w, wsz), N.adv(p, U32.add(w, wsz), wsz), T, wsz)), P.Bool.and_l(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz)), P.Bool.and_r(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz))), h)), SC_.SC.and_tt(WL_.WL.last(p, w, N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(p, U32.add(w, wsz), N.adv(p, U32.add(w, wsz), wsz), T, wsz), WR.last_mid(p, w, T, wsz, WR.lastw(Nat.add(p, c), w, cend, T, wsz, WR.pos_add(p, c, hc), P.Bool.and_l(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz), P.Bool.and_r(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz)), P.Bool.and_r(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL_.WL.last(Nat.add(p, c), w, cend, T, wsz), WL_.WL.tile(Nat.add(p, c), U32.add(w, wsz), cend, T, wsz))), h))))), P.Bool.and_l(WL_.WL.tile(p, U32.add(w, wsz), N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(c, N.adv(p, U32.add(w, wsz), wsz), cend, T, wsz), ih)))), P.Bool.and_r(WL_.WL.tile(p, U32.add(w, wsz), N.adv(p, U32.add(w, wsz), wsz), T, wsz), WL_.WL.tile(c, N.adv(p, U32.add(w, wsz), wsz), cend, T, wsz), ih))

# The facts of each of k windows, from the run's bounds.
law WR.whs_of:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +cend: U32
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +h: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(k, w0, cend, tlen, wsz) == True{} : Bool}
  {WL_.WL.whs(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo) == True{} : Bool}

def WR.whs_of(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, h, ht):
  match k:
    case 0n:
      {==}
    case 1n+q:
      SC_.SC.and_tt(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo), WL_.WL.whs(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo), WR.wh_of(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, Eb, BIGs, BIGe, HB, Es, S, Eo, h, P.Bool.and_l(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz))), ht), P.Bool.and_l(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz))), ht))), WR.whs_of(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, U32.add(w0, wsz), cend, Eb, BIGs, BIGe, HB, Es, S, Eo, h, P.Bool.and_r(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(q, w0, cend, tlen, wsz), WL_.WL.tile(q, U32.add(w0, wsz), cend, tlen, wsz))), ht)))))

# Splitting a task
# ----------------

def WR.tl(+s: WS_.EST) -> A.Tr:
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      tl

def WR.lidx(+s: WS_.EST) -> U32:
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      lidx

# The first of the halves of nw windows, and where the second starts.
def WR.nl(+nw: U32) -> U32:
  U32.shrn(nw, 1n)

def WR.nr(+nw: U32) -> U32:
  U32.sub(nw, U32.shrn(nw, 1n))

def WR.wm(+nw: U32, +w0: U32, +wsz: U32) -> U32:
  N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)

def WR.ocap(+nw: U32, +wsz: U32) -> U32:
  N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096)

# The second half's task.
def WR.sp(+nw: U32, +w0: U32, +wsz: U32, +s: WS_.EST) -> WS_.EST:
  WR.fresh(WR.tl(s), WR.ocap(nw, wsz), WR.lidx(s), WR.wm(nw, w0, wsz))

law WR.split_code:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +sbits: Nat
  for +wb: U32
  for +w0: U32
  for +nw: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {N.es.split(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, nw, WS_.WS.es(ts, tt, s)) == (WS_.WS.es(ts, tt, s), WS_.WS.es(ts, tt, WR.sp(nw, w0, wsz, s))) : N.ES & N.ES}

def WR.split_code(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, w0, nw, ts, tt, s):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.A.from(ts)), (A.A.from(ts), A.A.from(ts)), A.A.clone_from(ts)) :
        {N.es.split.k(sbits, wb, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz), N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), _, Array.clone(U32, A.A.from(tt)), Array.clone(U32, A.A.from(tl)), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont) == (N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}, WS_.WS.es(ts, tt, WR.fresh(tl, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)))) : N.ES & N.ES}
      %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.A.from(tt)), (A.A.from(tt), A.A.from(tt)), A.A.clone_from(tt)) :
        {N.es.split.k(sbits, wb, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz), N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), (A.A.from(ts), A.A.from(ts)), _, Array.clone(U32, A.A.from(tl)), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont) == (N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}, WS_.WS.es(ts, tt, WR.fresh(tl, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)))) : N.ES & N.ES}
      %Equal.sym(Array<U32> & Array<U32>, Array.clone(U32, A.A.from(tl)), (A.A.from(tl), A.A.from(tl)), A.A.clone_from(tl)) :
        {N.es.split.k(sbits, wb, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz), N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), (A.A.from(ts), A.A.from(ts)), (A.A.from(tt), A.A.from(tt)), _, A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont) == (N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}, WS_.WS.es(ts, tt, WR.fresh(tl, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)))) : N.ES & N.ES}
      %Equal.sym(N.ES, N.es.fresh(sbits, wb, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), A.A.from(ts), A.A.from(tt), A.A.from(tl), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)), WS_.WS.es(ts, tt, WR.fresh(tl, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz))), WR.fresh_code(sbits, wb, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), ts, tt, tl, lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz))) :
        {(N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}, _) == (N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}, WS_.WS.es(ts, tt, WR.fresh(tl, N.u32.max(U32.shrn(U32.mul(U32.sub(nw, U32.shrn(nw, 1n)), wsz), 3n), 4096), lidx, N.adv(U32.to_nat(U32.shrn(nw, 1n)), w0, wsz)))) : N.ES & N.ES}
      {==}

# Joining two tasks
# -----------------

def WR.tb(+s: WS_.EST) -> A.Tr:
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      tb

def WR.tv(+s: WS_.EST) -> A.Tr:
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      tv

def WR.cont(+s: WS_.EST) -> U32:
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      cont

# The output of l, then r's bytes copied after it.
def WR.jt(+TL: A.Tr, +OL: U32, +TR: A.Tr, +OR: U32) -> A.Tr:
  S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL)

def WR.join(+l: WS_.EST, +r: WS_.EST) -> WS_.EST:
  WS_.EST{WR.tl(l), WR.tb(l), WR.tv(l), WS_.WS.tio(l), WS_.WS.ee(l), WR.jt(WS_.WS.to(l), WS_.WS.olen(l), WS_.WS.to(r), WS_.WS.olen(r)), U32.add(WS_.WS.olen(l), WS_.WS.olen(r)), WR.lidx(r), WR.cont(r)}

law WR.join_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +ts2: A.Tr
  for +tt2: A.Tr
  for +l: WS_.EST
  for +r: WS_.EST
  for +Eo: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(l)), V.U.N(WS_.WS.olen(r))), V.U.N(Eo))) == True{} : Bool}
  {N.es.join(WS_.WS.es(ts, tt, l), WS_.WS.es(ts2, tt2, r)) == WS_.WS.es(ts, tt, WR.join(l, r)) : N.ES}

def WR.join_code(ts, tt, ts2, tt2, l, r, Eo, hb):
  match l r:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont} WS_.EST{rtl, rtb, rtv, rtio, re, rto, rolen, rlidx, rcont}:
      %Equal.sym(Array<U32>, B.B.grow(A.A.from(to), olen, U32.add(olen, rolen)), A.A.from(EM_.GR.t(to, olen, U32.add(olen, rolen))), EM_.GR.code(to, olen, U32.add(olen, rolen))) :
        {N.es.join.k(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), U32.add(olen, rolen), rlidx, rcont, B.B.copy(_, olen, A.A.from(rto), 0, rolen)) == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(S.S.puts(S.S.sl(V.U.N(rolen), rto, 0), EM_.GR.t(to, olen, U32.add(olen, rolen)), olen)), U32.add(olen, rolen), rlidx, rcont} : N.ES}
      %Equal.sym(Array<U32> & Array<U32>, B.B.copy(A.A.from(EM_.GR.t(to, olen, U32.add(olen, rolen))), olen, A.A.from(rto), 0, rolen), (A.A.from(rto), A.A.from(S.S.puts(S.S.sl(V.U.N(rolen), rto, 0), EM_.GR.t(to, olen, U32.add(olen, rolen)), olen))), C.CP.copy(EM_.GR.t(to, olen, U32.add(olen, rolen)), olen, rto, 0, rolen, Eo, (%P.Nat.add_comm(V.U.N(olen), V.U.N(rolen)) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; hb), (%Equal.sym(Nat, Nat.add(V.U.N(rolen), 0n), V.U.N(rolen), P.Nat.add_zero_r(V.U.N(rolen))) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(V.U.N(rolen), Nat.add(V.U.N(rolen), V.U.N(olen)), V.U.N(Eo), P.Nat.cmp_add_r(V.U.N(rolen), V.U.N(olen)), (%P.Nat.add_comm(V.U.N(olen), V.U.N(rolen)) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; hb))))) :
        {N.es.join.k(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), U32.add(olen, rolen), rlidx, rcont, _) == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(S.S.puts(S.S.sl(V.U.N(rolen), rto, 0), EM_.GR.t(to, olen, U32.add(olen, rolen)), olen)), U32.add(olen, rolen), rlidx, rcont} : N.ES}
      {==}

# The joined output holds l's bytes, then r's.
law WR.jhas:
  for +TL: A.Tr
  for +OL: U32
  for +TR: A.Tr
  for +OR: U32
  for +Eo: U32
  for +hpf: {WP_.WP.ook(TL) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), V.U.N(OR)), V.U.N(Eo))) == True{} : Bool}
  for +hEo: {U32.is_lt(Eo, 2147483648) == True{} : Bool}
  for +OUTL: List<&2, U32>
  for +R: List<&2, U32>
  for +hO: {S.S.has(OUTL, TL, 0) == True{} : Bool}
  for +hOl: {S.S.len(OUTL) == V.U.N(OL) : Nat}
  for +hR: {S.S.has(R, TR, 0) == True{} : Bool}
  for +hRl: {S.S.len(R) == V.U.N(OR) : Nat}
  {S.S.has(K.WD.app(OUTL, R), WR.jt(TL, OL, TR, OR), 0) == True{} : Bool}

def WR.jhas(TL, OL, TR, OR, Eo, hpf, hb, hEo, OUTL, R, hO, hOl, hR, hRl):
  WW_.WW.has_cons(OUTL, R, S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL), 0, OL, Equal.sym(Nat, S.S.len(OUTL), V.U.N(OL), hOl), (%Equal.sym(Bool, S.S.has(OUTL, S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL), 0), S.S.has(OUTL, EM_.GR.t(TL, OL, U32.add(OL, OR)), 0), S.S.has_puts_lt(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), OUTL, EM_.GR.t(TL, OL, U32.add(OL, OR)), OL, S.S.sl(V.U.N(OR), TR, 0), 0, U32.add(OL, OR), EM_.GR.pf(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf)), EM_.GR.lt(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(TL), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf))), EM_.GR.cap(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(TL), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf)), V.U.le_lt_trans(U32.add(OL, OR), Eo, 2147483648, V.U.N_le(U32.add(OL, OR), Eo, (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; hb)), hEo)), (%Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(OR), TR, 0)), V.U.N(OR), S.S.len_sl(V.U.N(OR), TR, 0)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), _), V.U.N(U32.add(OL, OR)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), V.U.N(OR)), _)) == True{} : Bool}; C.CP.le_refl(Nat.add(V.U.N(OL), V.U.N(OR))))), (%Equal.sym(Nat, S.S.len(OUTL), V.U.N(OL), hOl) : {Cmp.is_le(Nat.cmp(_, V.U.N(OL))) == True{} : Bool}; C.CP.le_refl(V.U.N(OL))))) : {_ == True{} : Bool}; EM_.GR.keep(TL, OL, U32.add(OL, OR), OUTL, V.U.le_lt_trans(U32.add(OL, OR), Eo, 2147483648, V.U.N_le(U32.add(OL, OR), Eo, (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; hb)), hEo), hOl, (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(V.U.N(OL), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(OL), V.U.N(OR))), hO)), WW_.WW.has_tr(R, TR, 0, S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL), OL, hR, (%Equal.sym(Nat, S.S.len(R), V.U.N(OR), hRl) : {S.S.has(S.S.sl(_, TR, 0), S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL), OL) == True{} : Bool}; S.S.has_puts(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL, U32.add(OL, OR), EM_.GR.pf(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf)), EM_.GR.lt(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(TL), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf))), EM_.GR.cap(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(TL), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf)), V.U.le_lt_trans(U32.add(OL, OR), Eo, 2147483648, V.U.N_le(U32.add(OL, OR), Eo, (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(_, V.U.N(Eo))) == True{} : Bool}; hb)), hEo)), (%Equal.sym(Nat, S.S.len(S.S.sl(V.U.N(OR), TR, 0)), V.U.N(OR), S.S.len_sl(V.U.N(OR), TR, 0)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), _), V.U.N(U32.add(OL, OR)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), V.U.N(OR)), _)) == True{} : Bool}; C.CP.le_refl(Nat.add(V.U.N(OL), V.U.N(OR)))))))))

law WR.jook:
  for +TL: A.Tr
  for +OL: U32
  for +TR: A.Tr
  for +OR: U32
  for +Eo: U32
  for +hpf: {WP_.WP.ook(TL) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), V.U.N(OR)), V.U.N(Eo))) == True{} : Bool}
  for +hEo: {U32.is_lt(Eo, 2147483648) == True{} : Bool}
  {WP_.WP.ook(WR.jt(TL, OL, TR, OR)) == True{} : Bool}

def WR.jook(TL, OL, TR, OR, Eo, hpf, hb, hEo):
  (%Equal.sym(Nat, SC_.SC.dep(S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL)), EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), SC_.SC.dep_pf(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL), S.S.pf_puts(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL, EM_.GR.pf(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf))))) : {Bool.and(A.T.pf(_, S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL)), Cmp.is_lt(Nat.cmp(_, 32n))) == True{} : Bool}; SC_.SC.and_tt(A.T.pf(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), S.S.puts(S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL)), Cmp.is_lt(Nat.cmp(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), 32n)), S.S.pf_puts(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), S.S.sl(V.U.N(OR), TR, 0), EM_.GR.t(TL, OL, U32.add(OL, OR)), OL, EM_.GR.pf(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), P.Bool.and_l(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf))), (%Equal.sym(Cmp, Nat.cmp(EM_.GR.d(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL)), 32n), LT{}, EM_.GR.lt(TL, OL, U32.add(OL, OR), SC_.SC.dep(TL), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(TL), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(TL), TL), Cmp.is_lt(Nat.cmp(SC_.SC.dep(TL), 32n)), hpf)))) : {Cmp.is_lt(_) == True{} : Bool}; {==})))

law WR.jlen:
  for +OL: U32
  for +OR: U32
  for +Eo: U32
  for +OUTL: List<&2, U32>
  for +R: List<&2, U32>
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(OL), V.U.N(OR)), V.U.N(Eo))) == True{} : Bool}
  for +hOl: {S.S.len(OUTL) == V.U.N(OL) : Nat}
  for +hRl: {S.S.len(R) == V.U.N(OR) : Nat}
  {S.S.len(K.WD.app(OUTL, R)) == V.U.N(U32.add(OL, OR)) : Nat}

def WR.jlen(OL, OR, Eo, OUTL, R, hb, hOl, hRl):
  %Equal.sym(Nat, S.S.len(K.WD.app(OUTL, R)), Nat.add(S.S.len(OUTL), S.S.len(R)), K.WD.len_app(OUTL, R)) :
    {_ == V.U.N(U32.add(OL, OR)) : Nat}
  %Equal.sym(Nat, S.S.len(OUTL), V.U.N(OL), hOl) :
    {Nat.add(_, S.S.len(R)) == V.U.N(U32.add(OL, OR)) : Nat}
  %Equal.sym(Nat, S.S.len(R), V.U.N(OR), hRl) :
    {Nat.add(V.U.N(OL), _) == V.U.N(U32.add(OL, OR)) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(OL, OR)), Nat.add(V.U.N(OL), V.U.N(OR)), V.U.add_N(OL, OR, Eo, hb)) :
    {Nat.add(V.U.N(OL), V.U.N(OR)) == _ : Nat}
  {==}

# A fresh task's state is sound.
law WR.esok_fresh:
  for +tl: A.Tr
  for +ocap: U32
  for +lidx: U32
  for +cont: U32
  {WP_.WP.esok(WR.fresh(tl, ocap, lidx, cont)) == True{} : Bool}

def WR.esok_fresh(tl, ocap, lidx, cont):
  %Equal.sym(Nat, SC_.SC.dep(A.T.new(B.B.depth(B.B.words(ocap)), 0)), B.B.depth(B.B.words(ocap)), SC_.SC.dep_pf(B.B.depth(B.B.words(ocap)), A.T.new(B.B.depth(B.B.words(ocap)), 0), A.T.pf_new(B.B.depth(B.B.words(ocap)), 0))) :
    {Bool.and(WS_.WS.eok(EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}), Bool.and(WP_.WP.bok(A.T.new(17n, 0)), Bool.and(A.T.pf(_, A.T.new(B.B.depth(B.B.words(ocap)), 0)), Cmp.is_lt(Nat.cmp(_, 32n))))) == True{} : Bool}
  %Equal.sym(Bool, A.T.pf(B.B.depth(B.B.words(ocap)), A.T.new(B.B.depth(B.B.words(ocap)), 0)), True{}, A.T.pf_new(B.B.depth(B.B.words(ocap)), 0)) :
    {Bool.and(WS_.WS.eok(EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}), Bool.and(WP_.WP.bok(A.T.new(17n, 0)), Bool.and(_, Cmp.is_lt(Nat.cmp(B.B.depth(B.B.words(ocap)), 32n))))) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(B.B.depth(B.B.words(ocap)), 32n), LT{}, Y.BD.lt(B.B.words(ocap))) :
    {Bool.and(WS_.WS.eok(EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}), Bool.and(WP_.WP.bok(A.T.new(17n, 0)), Bool.and(True{}, Cmp.is_lt(_)))) == True{} : Bool}
  {==}

# Windows one after another
# -------------------------

def WR.wapp(+xs: List<&2, Q.AW>, +ys: List<&2, Q.AW>) -> List<&2, Q.AW>:
  match xs:
    case []:
      ys
    case w <> r:
      w <> WR.wapp(r, ys)

law WR.wbs_app:
  for +xs: List<&2, Q.AW>
  for +ys: List<&2, Q.AW>
  {Q.SP.wbs(WR.wapp(xs, ys)) == K.WD.app(Q.SP.wbs(xs), Q.SP.wbs(ys)) : List<&2, U32>}

def WR.wbs_app(xs, ys):
  match xs:
    case []:
      {==}
    case w <> r:
      %Equal.sym(List<&2, U32>, Q.SP.wbs(WR.wapp(r, ys)), K.WD.app(Q.SP.wbs(r), Q.SP.wbs(ys)), WR.wbs_app(r, ys)) :
        {K.WD.app(Q.SP.wb(w), _) == K.WD.app(K.WD.app(Q.SP.wb(w), Q.SP.wbs(r)), Q.SP.wbs(ys)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, K.WD.app(K.WD.app(Q.SP.wb(w), Q.SP.wbs(r)), Q.SP.wbs(ys)), K.WD.app(Q.SP.wb(w), K.WD.app(Q.SP.wbs(r), Q.SP.wbs(ys))), K.WD.app_assoc(Q.SP.wb(w), Q.SP.wbs(r), Q.SP.wbs(ys))) :
        {K.WD.app(Q.SP.wb(w), K.WD.app(Q.SP.wbs(r), Q.SP.wbs(ys))) == _ : List<&2, U32>}
      {==}

law WR.wop_app:
  for +xs: List<&2, Q.AW>
  for +ys: List<&2, Q.AW>
  for +p: U32
  {Q.SP.wop(WR.wapp(xs, ys), p) == Q.SP.wop(ys, Q.SP.wop(xs, p)) : U32}

def WR.wop_app(xs, ys, p):
  match xs:
    case []:
      {==}
    case w <> r:
      WR.wop_app(r, ys, U32.add(p, Q.SP.wtl(w)))

law WR.wsok_app:
  for +xs: List<&2, Q.AW>
  for +ys: List<&2, Q.AW>
  for +ts: A.Tr
  for +tt: A.Tr
  for +S: U32
  for +p: U32
  for +tb: A.Tr
  for +Et: U32
  for +Es: U32
  {Q.SP.wsok(WR.wapp(xs, ys), ts, tt, S, p, tb, Et, Es) == Bool.and(Q.SP.wsok(xs, ts, tt, S, p, tb, Et, Es), Q.SP.wsok(ys, ts, tt, S, Q.SP.wop(xs, p), tb, Et, Es)) : Bool}

def WR.wsok_app(xs, ys, ts, tt, S, p, tb, Et, Es):
  match xs:
    case []:
      {==}
    case w <> r:
      %Equal.sym(Bool, Q.SP.wsok(WR.wapp(r, ys), ts, tt, S, U32.add(p, Q.SP.wtl(w)), tb, Et, Es), Bool.and(Q.SP.wsok(r, ts, tt, S, U32.add(p, Q.SP.wtl(w)), tb, Et, Es), Q.SP.wsok(ys, ts, tt, S, Q.SP.wop(r, U32.add(p, Q.SP.wtl(w))), tb, Et, Es)), WR.wsok_app(r, ys, ts, tt, S, U32.add(p, Q.SP.wtl(w)), tb, Et, Es)) :
        {Bool.and(Q.SP.wok(w, ts, tt, S, p, tb, Et, Es), _) == Bool.and(Bool.and(Q.SP.wok(w, ts, tt, S, p, tb, Et, Es), Q.SP.wsok(r, ts, tt, S, U32.add(p, Q.SP.wtl(w)), tb, Et, Es)), Q.SP.wsok(ys, ts, tt, S, Q.SP.wop(r, U32.add(p, Q.SP.wtl(w))), tb, Et, Es)) : Bool}
      K.WD.and_assoc(Q.SP.wok(w, ts, tt, S, p, tb, Et, Es), Q.SP.wsok(r, ts, tt, S, U32.add(p, Q.SP.wtl(w)), tb, Et, Es), Q.SP.wsok(ys, ts, tt, S, Q.SP.wop(r, U32.add(p, Q.SP.wtl(w))), tb, Et, Es))

# A run's output grows by its budget at most.
law WR.loop_ob:
  for +k: Nat
  for +E: N.EK
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hws: {WL_.WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL_.WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WL_.WL.loop(k, E, w0, ts, tt, s))), Nat.add(V.U.N(WS_.WS.olen(s)), WL_.WL.rb(k, E, w0)))) == True{} : Bool}

def WR.loop_ob(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      P.Nat.cmp_add_r(V.U.N(WS_.WS.olen(s)), 0n)
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      P.Nat.le_trans(V.U.N(WS_.WS.olen(WL_.WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))), Nat.add(V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))), WR.loop_ob(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL_.WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL_.WL.bud1(V.U.N(WS_.WS.olen(s)), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL_.WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL_.WL.olen_next(OUT, Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL_.WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL_.WL.bud1(V.U.N(WS_.WS.olen(s)), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL_.WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL_.WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL_.WL.bud1(V.U.N(WS_.WS.olen(s)), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL_.WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL_.WL.bud1(V.U.N(WS_.WS.olen(s)), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), (%Equal.sym(Nat, V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), Nat.add(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))), WL_.WL.olen_next(OUT, Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL_.WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL_.WL.bud1(V.U.N(WS_.WS.olen(s)), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))) : {Cmp.is_le(Nat.cmp(Nat.add(_, WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))))) == True{} : Bool}; (%Equal.sym(Nat, Nat.add(Nat.add(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))), P.Nat.add_assoc(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))) : {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))))) == True{} : Bool}; MT_.MT.add_le(V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(s)), Nat.add(S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), C.CP.le_refl(V.U.N(WS_.WS.olen(s))), MT_.MT.add_le(S.S.len(Q.SP.wb(WL_.WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), WL_.WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL_.WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL_.WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), C.CP.le_refl(WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))))))))

# The tasks
# ---------

law WR.rb_split:
  for +a: Nat
  for +c: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w: U32
  {WL_.WL.rb(Nat.add(a, c), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w) == Nat.add(WL_.WL.rb(a, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(a, w, wsz))) : Nat}

def WR.rb_split(a, c, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, WL_.WL.rb(Nat.add(p, c), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz)), Nat.add(WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz)), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz))), WR.rb_split(p, c, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, U32.add(w, wsz))) :
        {Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), _) == Nat.add(Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz))), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz))), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz))), Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), Nat.add(WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz)), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz)))), P.Nat.add_assoc(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz)), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz)))) :
        {Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w), Nat.add(WL_.WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w, wsz)), WL_.WL.rb(c, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.adv(p, U32.add(w, wsz), wsz)))) == _ : Nat}
      {==}

law WR.nsplit:
  for +nw: U32
  {V.U.N(nw) == Nat.add(V.U.N(WR.nl(nw)), V.U.N(WR.nr(nw))) : Nat}

def WR.nsplit(nw):
  Equal.sym(Nat, Nat.add(V.U.N(WR.nl(nw)), V.U.N(WR.nr(nw))), V.U.N(nw), (%P.Nat.add_comm(V.U.N(WR.nr(nw)), V.U.N(WR.nl(nw))) : {_ == V.U.N(nw) : Nat}; V.U.sub_nat(nw, U32.shrn(nw, 1n), WR.nl_le(nw))))

law WR.rb2:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  {WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0) == Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))) : Nat}

def WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw):
  %Equal.sym(Nat, V.U.N(nw), Nat.add(V.U.N(WR.nl(nw)), V.U.N(WR.nr(nw))), WR.nsplit(nw)) : {WL_.WL.rb(_, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0) == Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))) : Nat}
  WR.rb_split(V.U.N(WR.nl(nw)), V.U.N(WR.nr(nw)), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0)

law WR.p2pos:
  for +q: Nat
  {Cmp.is_le(Nat.cmp(1n, P.Nat.pow2(q))) == True{} : Bool}

def WR.p2pos(q):
  match q:
    case 0n:
      {==}
    case 1n+p:
      P.Nat.le_trans(1n, P.Nat.pow2(p), Nat.double(P.Nat.pow2(p)), WR.p2pos(p), EM_.GR.le_dbl(P.Nat.pow2(p)))

# The windows of the two halves.
law WR.tile2:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +q: Nat
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(1n+q), V.U.N(nw))) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  {Bool.and(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz)) == True{} : Bool}

def WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht):
  WR.tile_split(V.U.N(WR.nl(nw)), V.U.N(WR.nr(nw)), w0, cend, tlen, wsz, P.Nat.le_trans(1n, P.Nat.pow2(q), V.U.N(WR.nr(nw)), WR.p2pos(q), WR.halfR(nw, P.Nat.pow2(q), hk)), (%WR.nsplit(nw) : {WL_.WL.tile(_, w0, cend, tlen, wsz) == True{} : Bool}; ht))

law WR.le_r3:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Cmp.is_le(Nat.cmp(c, Nat.add(a, Nat.add(b, c)))) == True{} : Bool}

def WR.le_r3(a, b, c):
  %P.Nat.add_assoc(a, b, c) : {Cmp.is_le(Nat.cmp(c, _)) == True{} : Bool}
  %P.Nat.add_comm(c, Nat.add(a, b)) : {Cmp.is_le(Nat.cmp(c, _)) == True{} : Bool}
  P.Nat.cmp_add_r(c, Nat.add(a, b))

law WR.sum_le:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  for +l: Nat
  for +r: Nat
  for +eo: Nat
  for +hl: {Cmp.is_le(Nat.cmp(a, Nat.add(x, l))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(b, r)) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(x, Nat.add(l, r)), eo)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(a, b), eo)) == True{} : Bool}

def WR.sum_le(a, b, x, l, r, eo, hl, hr, h):
  P.Nat.le_trans(Nat.add(a, b), Nat.add(Nat.add(x, l), r), eo, MT_.MT.add_le(a, Nat.add(x, l), b, r, hl, hr), (%Equal.sym(Nat, Nat.add(Nat.add(x, l), r), Nat.add(x, Nat.add(l, r)), P.Nat.add_assoc(x, l, r)) : {Cmp.is_le(Nat.cmp(_, eo)) == True{} : Bool}; h))

# nw windows in a tree of 2^k tasks.
def WR.par(k: Nat, +E: N.EK, +w0: U32, +nw: U32, +ts: A.Tr, +tt: A.Tr, +sl: WS_.EST, +sr: WS_.EST) -> WS_.EST:
  match k E:
    case 0n e:
      WL_.WL.loop(U32.to_nat(nw), e, w0, ts, tt, sl)
    case 1n+q0 N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      +q = {q0 : Nat}
      WR.join(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))

def WR.pws(k: Nat, +E: N.EK, +w0: U32, +nw: U32, +ts: A.Tr, +tt: A.Tr, +sl: WS_.EST, +sr: WS_.EST) -> List<&2, Q.AW>:
  match k E:
    case 0n e:
      WL_.WL.ws(U32.to_nat(nw), e, w0, ts, tt, sl)
    case 1n+q0 N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      +q = {q0 : Nat}
      WR.wapp(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))

# The tasks' output grows by the windows' budget at most.
law WR.par_ob:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr))), Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)))) == True{} : Bool}

def WR.par_ob(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WR.loop_ob(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl)
    case 1n+q:
      (%Equal.sym(Nat, V.U.N(U32.add(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))), Nat.add(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))), V.U.add_N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), Eo, WR.sum_le(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)))) : {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)))) == True{} : Bool}; (%Equal.sym(Nat, WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))), Nat.add(V.U.N(WS_.WS.olen(sl)), _))) == True{} : Bool}; WR.sum_le(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), C.CP.le_refl(Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))))))

law WR.loop_wop1:
  for +n: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +cend: U32
  for +hn: {Cmp.is_le(Nat.cmp(1n, n)) == True{} : Bool}
  for +ht: {WL_.WL.tile(n, w0, cend, tlen, wsz) == True{} : Bool}
  {Q.SP.wop(WL_.WL.ws(n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), w0) == cend : U32}

def WR.loop_wop1(n, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, ts, tt, s, cend, hn, ht):
  match n:
    case 0n:
      P.Bool.false_true({Q.SP.wop(WL_.WL.ws(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), w0) == cend : U32}, hn)
    case 1n+q:
      WL_.WL.loop_wop(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, cend, ht)

# The tasks' output tree is sound.
law WR.par_ook:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {WP_.WP.ook(WS_.WS.to(WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr))) == True{} : Bool}

def WR.par_ook(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.es_o(WL_.WL.loop(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl), WL_.WL.loop_es(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl))
    case 1n+q:
      WR.jook(WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), Eo, WR.par_ook(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), WR.sum_le(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), WR.G.r12(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, hG))

# The tasks' windows end where the run does.
law WR.par_wop:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {Q.SP.wop(WR.pws(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr), w0) == cend : U32}

def WR.par_wop(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WR.loop_wop1(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, ts, tt, sl, cend, hk, ht)
    case 1n+q:
      %Equal.sym(U32, Q.SP.wop(WR.wapp(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), w0), Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), w0)), WR.wop_app(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), w0)) : {_ == cend : U32}
      %Equal.sym(U32, Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), w0), WR.wm(nw, w0, wsz), WR.par_wop(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl)) : {Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), _) == cend : U32}
      WR.par_wop(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))

# The tasks' output is as long as the bytes of their windows.
law WR.par_len:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {S.S.len(K.WD.app(OUT, Q.SP.wbs(WR.pws(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr)))) == V.U.N(WS_.WS.olen(WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr))) : Nat}

def WR.par_len(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.loop_len(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl)
    case 1n+q:
      %Equal.sym(List<&2, U32>, Q.SP.wbs(WR.wapp(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), K.WD.app(Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), WR.wbs_app(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : {S.S.len(K.WD.app(OUT, _)) == V.U.N(U32.add(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))) : Nat}
      %K.WD.app_assoc(OUT, Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : {S.S.len(_) == V.U.N(U32.add(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))) : Nat}
      WR.jlen(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), Eo, K.WD.app(OUT, Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WR.sum_le(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), WR.par_len(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), WR.par_len(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==})))

# The tasks' output holds the bytes of their windows.
law WR.par_out:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {S.S.has(K.WD.app(OUT, Q.SP.wbs(WR.pws(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr))), WS_.WS.to(WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr)), 0) == True{} : Bool}

def WR.par_out(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.loop_out(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl)
    case 1n+q:
      %Equal.sym(List<&2, U32>, Q.SP.wbs(WR.wapp(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), K.WD.app(Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), WR.wbs_app(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : {S.S.has(K.WD.app(OUT, _), WR.jt(WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), 0) == True{} : Bool}
      %K.WD.app_assoc(OUT, Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : {S.S.has(_, WR.jt(WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), 0) == True{} : Bool}
      WR.jhas(WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WS_.WS.to(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), Eo, WR.par_ook(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), WR.sum_le(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), WR.G.r12(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, Eb, BIGs, BIGe, HB, Es, S, Eo, hG), K.WD.app(OUT, Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), Q.SP.wbs(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WR.par_out(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), WR.par_len(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), WR.par_out(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==})), WR.par_len(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==})))

# Every window of the tasks rebuilds its part of the target.
law WR.par_wsok:
  for +k: Nat
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {Q.SP.wsok(WR.pws(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr), ts, tt, S, w0, A.A.to(D.ct.table()), tlen, Es) == True{} : Bool}

def WR.par_wsok(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.loop_wsok(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, cend, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl, ht)
    case 1n+q:
      %Equal.sym(Bool, Q.SP.wsok(WR.wapp(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), ts, tt, S, w0, A.A.to(D.ct.table()), tlen, Es), Bool.and(Q.SP.wsok(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), ts, tt, S, w0, A.A.to(D.ct.table()), tlen, Es), Q.SP.wsok(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), ts, tt, S, Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), w0), A.A.to(D.ct.table()), tlen, Es)), WR.wsok_app(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), ts, tt, S, w0, A.A.to(D.ct.table()), tlen, Es)) : {_ == True{} : Bool}
      SC_.SC.and_tt(Q.SP.wsok(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), ts, tt, S, w0, A.A.to(D.ct.table()), tlen, Es), Q.SP.wsok(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), ts, tt, S, Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), w0), A.A.to(D.ct.table()), tlen, Es), WR.par_wsok(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%Equal.sym(U32, Q.SP.wop(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), w0), WR.wm(nw, w0, wsz), WR.par_wop(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl)) : {Q.SP.wsok(WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), ts, tt, S, _, A.A.to(D.ct.table()), tlen, Es) == True{} : Bool}; WR.par_wsok(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))))

# The tasks' code.
law WR.par_code:
  for +k: Nat
  for +sbits: Nat
  for +wb: U32
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +w0: U32
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +sl: WS_.EST
  for +sr: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {N.enc.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, nw, (WS_.WS.es(ts, tt, sl), WS_.WS.es(ts, tt, sr))) == WS_.WS.es(ts, tt, WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr)) : N.ES}

def WR.par_code(k, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.loop_code(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl)
    case 1n+q:
      match q:
        case 0n:
        %Equal.sym(N.ES, N.win.loop(U32.to_nat(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WS_.WS.es(ts, tt, sl)), WS_.WS.es(ts, tt, WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WR.par_code(0n, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 0n, hk, ht)), WR.halfL(nw, P.Nat.pow2(0n), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl)) : {N.es.join(_, N.win.loop(U32.to_nat(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WS_.WS.es(ts, tt, sr))) == WS_.WS.es(ts, tt, WR.join(WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        %Equal.sym(N.ES, N.win.loop(U32.to_nat(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WS_.WS.es(ts, tt, sr)), WS_.WS.es(ts, tt, WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WR.par_code(0n, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 0n, hk, ht)), WR.halfR(nw, P.Nat.pow2(0n), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))) : {N.es.join(WS_.WS.es(ts, tt, WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), _) == WS_.WS.es(ts, tt, WR.join(WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        WR.join_code(ts, tt, ts, tt, WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), Eo, WR.sum_le(V.U.N(WS_.WS.olen(WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(0n, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 0n, hk, ht)), WR.halfL(nw, P.Nat.pow2(0n), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(0n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(0n, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 0n, hk, ht)), WR.halfR(nw, P.Nat.pow2(0n), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)))
        case 1n+p:
        %Equal.sym(N.ES & N.ES, N.es.split(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, WR.nl(nw), WS_.WS.es(ts, tt, sl)), (WS_.WS.es(ts, tt, sl), WS_.WS.es(ts, tt, WR.sp(WR.nl(nw), w0, wsz, sl))), WR.split_code(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, w0, WR.nl(nw), ts, tt, sl)) : {N.es.join(N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, WR.nl(nw), _), N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), N.es.split(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), WS_.WS.es(ts, tt, sr)))) == WS_.WS.es(ts, tt, WR.join(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        %Equal.sym(N.ES & N.ES, N.es.split(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), WS_.WS.es(ts, tt, sr)), (WS_.WS.es(ts, tt, sr), WS_.WS.es(ts, tt, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WR.split_code(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr)) : {N.es.join(N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, WR.nl(nw), (WS_.WS.es(ts, tt, sl), WS_.WS.es(ts, tt, WR.sp(WR.nl(nw), w0, wsz, sl)))), N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), _)) == WS_.WS.es(ts, tt, WR.join(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        %Equal.sym(N.ES, N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, w0, WR.nl(nw), (WS_.WS.es(ts, tt, sl), WS_.WS.es(ts, tt, WR.sp(WR.nl(nw), w0, wsz, sl)))), WS_.WS.es(ts, tt, WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), WR.par_code(1n+p, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 1n+p, hk, ht)), WR.halfL(nw, P.Nat.pow2(1n+p), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl)) : {N.es.join(_, N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), (WS_.WS.es(ts, tt, sr), WS_.WS.es(ts, tt, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))))) == WS_.WS.es(ts, tt, WR.join(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        %Equal.sym(N.ES, N.enc.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, WR.wm(nw, w0, wsz), WR.nr(nw), (WS_.WS.es(ts, tt, sr), WS_.WS.es(ts, tt, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), WS_.WS.es(ts, tt, WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr))), WR.par_code(1n+p, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 1n+p, hk, ht)), WR.halfR(nw, P.Nat.pow2(1n+p), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))) : {N.es.join(WS_.WS.es(ts, tt, WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl))), _) == WS_.WS.es(ts, tt, WR.join(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))) : N.ES}
        WR.join_code(ts, tt, ts, tt, WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)), WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)), Eo, WR.sum_le(V.U.N(WS_.WS.olen(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR.nl(nw), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl)))), V.U.N(WS_.WS.olen(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), WR.par_ob(1n+p, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR.nl(nw), WR.wm(nw, w0, wsz), ts, tt, sl, WR.sp(WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 1n+p, hk, ht)), WR.halfL(nw, P.Nat.pow2(1n+p), hk), hesl, WR.esok_fresh(WR.tl(sl), WR.ocap(WR.nl(nw), wsz), WR.lidx(sl), WR.wm(WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl), (%hr0 : {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.olen(WR.par(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz), WR.nr(nw), ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr)))), Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))))) == True{} : Bool}; WR.par_ob(1n+p, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR.wm(nw, w0, wsz), WR.nr(nw), cend, ts, tt, sr, WR.sp(WR.nr(nw), WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR.nl(nw)), w0, N.adv(V.U.N(WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR.nr(nw)), N.adv(V.U.N(WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, 1n+p, hk, ht)), WR.halfR(nw, P.Nat.pow2(1n+p), hk), hesr, WR.esok_fresh(WR.tl(sr), WR.ocap(WR.nr(nw), wsz), WR.lidx(sr), WR.wm(WR.nr(nw), WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR.wm(nw, w0, wsz))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==}))), (%WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)))
