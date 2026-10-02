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
import ./wwrite.bend as WW_
import ./wfin.bend as WF_
import ./einst.bend as EI_
import ./adler.bend as H
import ./varint.bend as R

# A window's start
# ================
#
# win.start: the source match that reached the last window's end tried
# first (MATCH_TARGET), the source indexed as far as the window needs, the
# tables made, the emitter reset; then the scan.
#
# Source: proofs/wstart.bp (tools/bpp.py writes proofs/wstart.bend from it).

# The state between windows, its arrays as trees; the source and the target
# are fixed.
type EST is Data:
  EST{tl: A.Tr, tb: A.Tr, tv: A.Tr, tio: A.Tr, e: EM_.ET, to: A.Tr, olen: U32, lidx: U32, cont: U32}

def WS.es(+ts: A.Tr, +tt: A.Tr, +s: EST) -> N.ES:
  match s:
    case EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      N.ES{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, lidx, cont}

# The source index
# ----------------

def WS.ixgo(n: Nat, +tl: A.Tr, +q: U32, +sh: Nat, +mask: U32, +h: U32, +ts: A.Tr) -> A.Tr:
  match n:
    case 0n:
      tl
    case 1n+p:
      WS.ixgo(p, A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1)), U32.sub(q, 8), sh, mask, SC_.SC.hl(ts, U32.sub(q, 8)), ts)

law WS.ixgo_code:
  for +n: Nat
  for +tl: A.Tr
  for +q: U32
  for +sh: Nat
  for +mask: U32
  for +h: U32
  for +ts: A.Tr
  {N.ix.go(n, A.A.from(tl), q, sh, mask, (A.A.from(ts), h)) == (A.A.from(ts), A.A.from(WS.ixgo(n, tl, q, sh, mask, h, ts))) : Array<U32> & Array<U32>}

def WS.ixgo_code(n, tl, q, sh, mask, h, ts):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(tl), N.H.slot(h, sh, mask), U32.add(q, 1)), A.A.from(A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1))), A.A.set_from(tl, N.H.slot(h, sh, mask), U32.add(q, 1))) :
        {N.ix.go(p, _, U32.sub(q, 8), sh, mask, N.H.large(A.A.from(ts), U32.sub(q, 8))) == (A.A.from(ts), A.A.from(WS.ixgo(p, A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1)), U32.sub(q, 8), sh, mask, SC_.SC.hl(ts, U32.sub(q, 8)), ts))) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & U32, N.H.large(A.A.from(ts), U32.sub(q, 8)), (A.A.from(ts), SC_.SC.hl(ts, U32.sub(q, 8))), SC_.SC.hl_code(ts, U32.sub(q, 8))) :
        {N.ix.go(p, A.A.from(A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1))), U32.sub(q, 8), sh, mask, _) == (A.A.from(ts), A.A.from(WS.ixgo(p, A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1)), U32.sub(q, 8), sh, mask, SC_.SC.hl(ts, U32.sub(q, 8)), ts))) : Array<U32> & Array<U32>}
      WS.ixgo_code(p, A.T.set(tl, N.H.slot(h, sh, mask), U32.add(q, 1)), U32.sub(q, 8), sh, mask, SC_.SC.hl(ts, U32.sub(q, 8)), ts)

def WS.ixblk.if(+z: Bool, +tl: A.Tr, +b0: U32, +len: U32, +sh: Nat, +mask: U32, +ts: A.Tr) -> A.Tr:
  match z:
    case False{}:
      tl
    case True{}:
      WS.ixgo(U32.to_nat(U32.add(U32.shrn(U32.sub(len, 9), 3n), 1)), tl, U32.add(b0, U32.sub(len, 9)), sh, mask, SC_.SC.hl(ts, U32.add(b0, U32.sub(len, 9))), ts)

def WS.ixblk(+tl: A.Tr, +b0: U32, +len: U32, +sh: Nat, +mask: U32, +ts: A.Tr) -> A.Tr:
  WS.ixblk.if(U32.is_le(9, len), tl, b0, len, sh, mask, ts)

law WS.ixblk.if_code:
  for +z: Bool
  for +ts: A.Tr
  for +tl: A.Tr
  for +b0: U32
  for +len: U32
  for +sh: Nat
  for +mask: U32
  {N.ix.block.if(z, A.A.from(ts), A.A.from(tl), b0, len, sh, mask) == (A.A.from(ts), A.A.from(WS.ixblk.if(z, tl, b0, len, sh, mask, ts))) : Array<U32> & Array<U32>}

def WS.ixblk.if_code(z, ts, tl, b0, len, sh, mask):
  match z:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Array<U32> & U32, N.H.large(A.A.from(ts), U32.add(b0, U32.sub(len, 9))), (A.A.from(ts), SC_.SC.hl(ts, U32.add(b0, U32.sub(len, 9)))), SC_.SC.hl_code(ts, U32.add(b0, U32.sub(len, 9)))) :
        {N.ix.go(U32.to_nat(U32.add(U32.shrn(U32.sub(len, 9), 3n), 1)), A.A.from(tl), U32.add(b0, U32.sub(len, 9)), sh, mask, _) == (A.A.from(ts), A.A.from(WS.ixgo(U32.to_nat(U32.add(U32.shrn(U32.sub(len, 9), 3n), 1)), tl, U32.add(b0, U32.sub(len, 9)), sh, mask, SC_.SC.hl(ts, U32.add(b0, U32.sub(len, 9))), ts))) : Array<U32> & Array<U32>}
      WS.ixgo_code(U32.to_nat(U32.add(U32.shrn(U32.sub(len, 9), 3n), 1)), tl, U32.add(b0, U32.sub(len, 9)), sh, mask, SC_.SC.hl(ts, U32.add(b0, U32.sub(len, 9))), ts)

def WS.ixblks(n: Nat, +b0: U32, +slen: U32, +blk: U32, +sh: Nat, +mask: U32, +tl: A.Tr, +ts: A.Tr) -> A.Tr:
  match n:
    case 0n:
      tl
    case 1n+p:
      WS.ixblks(p, U32.add(b0, blk), slen, blk, sh, mask, WS.ixblk(tl, b0, U32.min(blk, U32.sub(slen, b0)), sh, mask, ts), ts)

law WS.ixblks_code:
  for +n: Nat
  for +b0: U32
  for +slen: U32
  for +blk: U32
  for +sh: Nat
  for +mask: U32
  for +tl: A.Tr
  for +ts: A.Tr
  {N.ix.blocks(n, b0, slen, blk, sh, mask, (A.A.from(ts), A.A.from(tl))) == (A.A.from(ts), A.A.from(WS.ixblks(n, b0, slen, blk, sh, mask, tl, ts))) : Array<U32> & Array<U32>}

def WS.ixblks_code(n, b0, slen, blk, sh, mask, tl, ts):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<U32> & Array<U32>, N.ix.block.if(U32.is_le(9, U32.min(blk, U32.sub(slen, b0))), A.A.from(ts), A.A.from(tl), b0, U32.min(blk, U32.sub(slen, b0)), sh, mask), (A.A.from(ts), A.A.from(WS.ixblk.if(U32.is_le(9, U32.min(blk, U32.sub(slen, b0))), tl, b0, U32.min(blk, U32.sub(slen, b0)), sh, mask, ts))), WS.ixblk.if_code(U32.is_le(9, U32.min(blk, U32.sub(slen, b0))), ts, tl, b0, U32.min(blk, U32.sub(slen, b0)), sh, mask)) :
        {N.ix.blocks(p, U32.add(b0, blk), slen, blk, sh, mask, _) == (A.A.from(ts), A.A.from(WS.ixblks(p, U32.add(b0, blk), slen, blk, sh, mask, WS.ixblk.if(U32.is_le(9, U32.min(blk, U32.sub(slen, b0))), tl, b0, U32.min(blk, U32.sub(slen, b0)), sh, mask, ts), ts))) : Array<U32> & Array<U32>}
      WS.ixblks_code(p, U32.add(b0, blk), slen, blk, sh, mask, WS.ixblk.if(U32.is_le(9, U32.min(blk, U32.sub(slen, b0))), tl, b0, U32.min(blk, U32.sub(slen, b0)), sh, mask, ts), ts)

# A table of 2^d slots at least.
def WS.need.if(+z: Bool, +d: Nat, +t: A.Tr) -> A.Tr:
  match z:
    case True{}:
      A.T.new(d, 0)
    case False{}:
      t

def WS.need(+d: Nat, +t: A.Tr) -> A.Tr:
  WS.need.if(U32.is_lt(A.T.size(t), U32.shln(1, d)), d, t)

law WS.need_code:
  for +d: Nat
  for +t: A.Tr
  {N.tab.need(d, A.A.from(t)) == A.A.from(WS.need(d, t)) : Array<U32>}

law WS.need_code.if:
  for +z: Bool
  for +d: Nat
  for +t: A.Tr
  {N.tab.need.if(z, d, A.A.from(t)) == A.A.from(WS.need.if(z, d, t)) : Array<U32>}

def WS.need_code.if(z, d, t):
  match z:
    case True{}:
      A.A.new_from(d, 0)
    case False{}:
      {==}

def WS.need_code(d, t):
  %Equal.sym(Array<U32> & U32, Array.size(U32, A.A.from(t)), (A.A.from(t), A.T.size(t)), A.A.size_from(t)) :
    {N.tab.need.k(d, _) == A.A.from(WS.need.if(U32.is_lt(A.T.size(t), U32.shln(1, d)), d, t)) : Array<U32>}
  WS.need_code.if(U32.is_lt(A.T.size(t), U32.shln(1, d)), d, t)

def WS.needw(+z: Bool, +d: Nat, +t: A.Tr) -> A.Tr:
  match z:
    case True{}:
      WS.need(d, t)
    case False{}:
      t

law WS.needw_code:
  for +z: Bool
  for +d: Nat
  for +t: A.Tr
  {N.tab.need.when(z, d, A.A.from(t)) == A.A.from(WS.needw(z, d, t)) : Array<U32>}

def WS.needw_code(z, d, t):
  match z:
    case True{}:
      WS.need_code(d, t)
    case False{}:
      {==}

# Indexing as far as the window needs
def WS.want(+slen: U32, +w1: U32) -> U32:
  U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))

def WS.nb(+slen: U32, +blk: U32, +w1: U32, +lidx: U32) -> U32:
  N.u32.pick(U32.is_lt(lidx, WS.want(slen, w1)), U32.div(U32.sub(U32.add(U32.sub(WS.want(slen, w1), lidx), blk), 1), blk), 0)

def WS.uptol(+E: N.EK, +w1: U32, +lidx: U32) -> U32:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      U32.add(lidx, U32.mul(WS.nb(slen, blk, w1, lidx), blk))

def WS.uptot(+E: N.EK, +w1: U32, +lidx: U32, +tl: A.Tr, +ts: A.Tr) -> A.Tr:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      WS.ixblks(U32.to_nat(WS.nb(slen, blk, w1, lidx)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)

law WS.upto_code:
  for +E: N.EK
  for +w1: U32
  for +lidx: U32
  for +ts: A.Tr
  for +tl: A.Tr
  {N.ix.upto(E, w1, lidx, A.A.from(ts), A.A.from(tl)) == (WS.uptol(E, w1, lidx), (A.A.from(ts), A.A.from(WS.uptot(E, w1, lidx, tl, ts)))) : U32 & (Array<U32> & Array<U32>)}

def WS.upto_code(E, w1, lidx, ts, tl):
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(Array<U32>, N.tab.need(U32.to_nat(U32.sub(32, lsh)), A.A.from(tl)), A.A.from(WS.need(U32.to_nat(U32.sub(32, lsh)), tl)), WS.need_code(U32.to_nat(U32.sub(32, lsh)), tl)) :
        {(U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), N.ix.blocks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, (A.A.from(ts), _))) == (U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), (A.A.from(ts), A.A.from(WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)))) : U32 & Array<U32> & Array<U32>}
      %Equal.sym(Array<U32> & Array<U32>, N.ix.blocks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, (A.A.from(ts), A.A.from(WS.need(U32.to_nat(U32.sub(32, lsh)), tl)))), (A.A.from(ts), A.A.from(WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts))), WS.ixblks_code(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)) :
        {(U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), _) == (U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), (A.A.from(ts), A.A.from(WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)))) : U32 & Array<U32> & Array<U32>}
      {==}

def WS.sil(+z: Bool, +E: N.EK, +w1: U32, +lidx: U32) -> U32:
  match z:
    case True{}:
      WS.uptol(E, w1, lidx)
    case False{}:
      lidx

def WS.sit(+z: Bool, +E: N.EK, +w1: U32, +lidx: U32, +tl: A.Tr, +ts: A.Tr) -> A.Tr:
  match z:
    case True{}:
      WS.uptot(E, w1, lidx, tl, ts)
    case False{}:
      tl

law WS.si_code:
  for +z: Bool
  for +E: N.EK
  for +w1: U32
  for +lidx: U32
  for +ts: A.Tr
  for +tl: A.Tr
  {N.win.start.i(z, E, w1, lidx, A.A.from(ts), A.A.from(tl)) == (WS.sil(z, E, w1, lidx), (A.A.from(ts), A.A.from(WS.sit(z, E, w1, lidx, tl, ts)))) : U32 & (Array<U32> & Array<U32>)}

def WS.si_code(z, E, w1, lidx, ts, tl):
  match z:
    case True{}:
      WS.upto_code(E, w1, lidx, ts, tl)
    case False{}:
      {==}

# MATCH_TARGET's match, buffered first.
def WS.putif(+z: Bool, +tio: A.Tr, +pos: U32, +len: U32, +val: U32) -> A.Tr:
  match z:
    case True{}:
      SG_.SG.put(tio, 0, pos, len, val)
    case False{}:
      tio

law WS.putif_code:
  for +z: Bool
  for +tio: A.Tr
  for +pos: U32
  for +len: U32
  for +val: U32
  {N.io.put.if(z, A.A.from(tio), pos, len, val) == A.A.from(WS.putif(z, tio, pos, len, val)) : Array<U32>}

def WS.putif_code(z, tio, pos, len, val):
  match z:
    case True{}:
      SG_.SG.put_code(tio, 0, pos, len, val)
    case False{}:
      {==}

# Where MATCH_TARGET tries the source: where the last window's match went
# on, if within the source.
def WS.at(+slen: U32, +cont: U32) -> U32:
  N.u32.pick(U32.is_lt(cont, slen), cont, slen)

# Its length.
def WS.fwd(+slen: U32, +w0: U32, +w1: U32, +ts: A.Tr, +tt: A.Tr, +cont: U32) -> U32:
  SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))

# Where the scan starts.
def WS.p0(+slen: U32, +w0: U32, +w1: U32, +ts: A.Tr, +tt: A.Tr, +cont: U32) -> U32:
  N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.add(w0, WS.fwd(slen, w0, w1, ts, tt, cont)), w0)

def WS.ee(+s: EST) -> EM_.ET:
  match s:
    case EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      e

# The scan's first state.
def WS.st0(+E: N.EK, +w0: U32, +w1: U32, +ts: A.Tr, +tt: A.Tr, +s: EST) -> SC_.ST:
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      +at = WS.at(slen, cont)
      +fwd = WS.fwd(slen, w0, w1, ts, tt, cont)
      +ok = U32.is_le(4, fwd)
      +p = WS.p0(slen, w0, w1, ts, tt, cont)
      SC_.ST{WS.sit(U32.is_lt(p, w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts), WS.needw(U32.is_lt(p, w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), tb), WS.needw(U32.is_lt(p, w1), 18n, tv), WS.putif(ok, tio, w0, fwd, at), p, 4, 0, 0, 0, N.NONE(), N.u32.pick(ok, 1, 0), N.u32.pick(Bool.and(ok, U32.is_eq(p, w1)), U32.add(at, fwd), N.NONE())}

# Where the index stands after the start.
def WS.lid0(+E: N.EK, +w0: U32, +w1: U32, +ts: A.Tr, +tt: A.Tr, +s: EST) -> U32:
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx)

def WS.to(+s: EST) -> A.Tr:
  match s:
    case EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      to

def WS.olen(+s: EST) -> U32:
  match s:
    case EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      olen

def WS.slen(+E: N.EK) -> U32:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      slen

law WS.at_le.go:
  for +slen: U32
  for +cont: U32
  for +c: Bool
  for +ec: {U32.is_lt(cont, slen) == c : Bool}
  {U32.is_le(N.u32.pick(c, cont, slen), slen) == True{} : Bool}

def WS.at_le.go(slen, cont, c, ec):
  match c:
    case True{}:
      V.U.lt_to_le(cont, slen, ec)
    case False{}:
      V.U.N_le(slen, slen, C.CP.le_refl(V.U.N(slen)))

law WS.at_le:
  for +slen: U32
  for +cont: U32
  {U32.is_le(WS.at(slen, cont), slen) == True{} : Bool}

def WS.at_le(slen, cont):
  WS.at_le.go(slen, cont, U32.is_lt(cont, slen), {==})

law WS.start_code:
  for +E: N.EK
  for +K: N.SK
  for +w0: U32
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: EST
  for +Eb: U32
  for +hpf: {A.T.pf(10n, EM_.EM.tc(WS.ee(s))) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +hS: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.slen(E)), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hW: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(Eb))) == True{} : Bool}
  {N.win.start(E, K, w0, w1, WS.es(ts, tt, s)) == N.win.scan(E, K, w0, w1, A.A.from(WS.to(s)), WS.olen(s), WS.lid0(E, w0, w1, ts, tt, s), SC_.SC.sc(ts, tt, EM_.EM.reset(w0, WS.ee(s)), WS.st0(E, w0, w1, ts, tt, s))) : N.ES}

def WS.start_code(E, K, w0, w1, ts, tt, s, Eb, hpf, hw, hS, hW):
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      %Equal.sym(N.Em, N.em.reset(w0, EM_.EM.em(e)), EM_.EM.em(EM_.EM.reset(w0, e)), EM_.EM.reset_code(w0, e, hpf)) :
        {N.win.start.k(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, N.u32.pick(U32.is_lt(cont, slen), cont, slen), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), _, A.A.from(to), olen, lidx, B.B.fwd(A.A.from(ts), N.u32.pick(U32.is_lt(cont, slen), cont, slen), A.A.from(tt), w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.fwd(A.A.from(ts), N.u32.pick(U32.is_lt(cont, slen), cont, slen), A.A.from(tt), w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), ((A.A.from(ts), A.A.from(tt)), MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), 2n), 1)), ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), MT_.MT.cf(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), 0), MT_.MT.cn(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), MT_.MW{tt, w0}, 0))), MT_.MT.fwd(ts, tt, N.u32.pick(U32.is_lt(cont, slen), cont, slen), w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), Eb, SC_.SC.fb(N.u32.pick(U32.is_lt(cont, slen), cont, slen), slen, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), Eb, WS.at_le(slen, cont), MT_.MT.min_le_r(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), hS), SC_.SC.fb(w0, w1, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), Eb, hw, MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))), hW))) :
        {N.win.start.k(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, N.u32.pick(U32.is_lt(cont, slen), cont, slen), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(EM_.EM.reset(w0, e)), A.A.from(to), olen, lidx, _) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      %Equal.sym(U32 & Array<U32> & Array<U32>, N.win.start.i(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, A.A.from(ts), A.A.from(tl)), (WS.sil(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), (A.A.from(ts), A.A.from(WS.sit(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)))), WS.si_code(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, ts, tl)) :
        {N.win.start.s(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, N.u32.pick(U32.is_lt(cont, slen), cont, slen), SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), A.A.from(tt), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(EM_.EM.reset(w0, e)), A.A.from(to), olen, _) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      %Equal.sym(Array<U32>, N.tab.need.when(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), A.A.from(tb)), A.A.from(WS.needw(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), tb)), WS.needw_code(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), tb)) :
        {N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), _, N.tab.need.when(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), 18n, A.A.from(tv)), N.io.put.if(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), A.A.from(tio), w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), N.u32.pick(U32.is_lt(cont, slen), cont, slen)), EM_.EM.em(EM_.EM.reset(w0, e)), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.is_eq(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1)), U32.add(N.u32.pick(U32.is_lt(cont, slen), cont, slen), SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), N.NONE())}) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      %Equal.sym(Array<U32>, N.tab.need.when(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), 18n, A.A.from(tv)), A.A.from(WS.needw(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), 18n, tv)), WS.needw_code(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), 18n, tv)) :
        {N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), tb)), _, N.io.put.if(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), A.A.from(tio), w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), N.u32.pick(U32.is_lt(cont, slen), cont, slen)), EM_.EM.em(EM_.EM.reset(w0, e)), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.is_eq(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1)), U32.add(N.u32.pick(U32.is_lt(cont, slen), cont, slen), SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), N.NONE())}) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      %Equal.sym(Array<U32>, N.io.put.if(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), A.A.from(tio), w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), N.u32.pick(U32.is_lt(cont, slen), cont, slen)), A.A.from(WS.putif(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), tio, w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), N.u32.pick(U32.is_lt(cont, slen), cont, slen))), WS.putif_code(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), tio, w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen)))), N.u32.pick(U32.is_lt(cont, slen), cont, slen))) :
        {N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), N.EK.sbits(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}), tb)), A.A.from(WS.needw(U32.is_lt(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1), 18n, tv)), _, EM_.EM.em(EM_.EM.reset(w0, e)), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.is_eq(N.u32.pick(U32.is_le(4, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), U32.add(w0, SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), w0), w1)), U32.add(N.u32.pick(U32.is_lt(cont, slen), cont, slen), SC_.SC.flen(ts, N.u32.pick(U32.is_lt(cont, slen), cont, slen), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, N.u32.pick(U32.is_lt(cont, slen), cont, slen))))), N.NONE())}) == N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, K, w0, w1, A.A.from(to), olen, WS.sil(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(WS.sit(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w1, lidx, tl, ts)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), U32.to_nat(U32.sub(32, ssh)), tb)), A.A.from(WS.needw(U32.is_lt(WS.p0(slen, w0, w1, ts, tt, cont), w1), 18n, tv)), A.A.from(WS.putif(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), tio, w0, WS.fwd(slen, w0, w1, ts, tt, cont), WS.at(slen, cont))), EM_.EM.em(EM_.EM.reset(w0, e)), WS.p0(slen, w0, w1, ts, tt, cont), 4, 0, 0, 0, N.NONE(), N.u32.pick(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), 1, 0), N.u32.pick(Bool.and(U32.is_le(4, WS.fwd(slen, w0, w1, ts, tt, cont)), U32.is_eq(WS.p0(slen, w0, w1, ts, tt, cont), w1)), U32.add(WS.at(slen, cont), WS.fwd(slen, w0, w1, ts, tt, cont)), N.NONE())}) : N.ES}
      {==}

law WS.lt_pos:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.cmp(0n, b) == LT{} : Cmp}
  {Nat.cmp(a, Nat.add(a, b)) == LT{} : Cmp}

def WS.lt_pos(a, b, h):
  match b:
    case 0n:
      P.Cmp.eq_lt({Nat.cmp(a, Nat.add(a, 0n)) == LT{} : Cmp}, h)
    case 1n+q:
      SC_.SC.lt_addk(a, q)

law WS.lerefl:
  for +x: U32
  {U32.is_le(x, x) == True{} : Bool}

def WS.lerefl(x):
  V.U.N_le(x, x, C.CP.le_refl(V.U.N(x)))

# MATCH_TARGET's match holds.
law WS.mt_ok0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +BIG: U32
  for +at: U32
  for +hat: {U32.is_le(at, slen) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +hE4: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))) == True{} : Bool}
  for +h4: {U32.is_le(4, SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{w0, U32.and(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 2147483647), at, N.ent.run(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))}) == True{} : Bool}

def WS.mt_ok0(ts, tt, slen, w0, w1, E, BIG, at, hat, hw, hE4, hEs, h4, hk, hB):
  %Equal.sym(U32, U32.and(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 2147483647), SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), SC_.SC.m31(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), SC_.SC.w31(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), U32.sub(w1, w0), BIG, P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, at))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), MT_.MT.cf(ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 0), MT_.MT.cn(ts, at, MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, at))), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{w0, _, at, N.ent.run(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))}) == True{} : Bool}
  %Equal.sym(Bool, N.ent.run(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), False{}, SC_.SC.run0(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), SC_.SC.w31(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), U32.sub(w1, w0), BIG, P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, at))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), MT_.MT.cf(ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 0), MT_.MT.cn(ts, at, MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, at))), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{w0, SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), at, _}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, w0), True{}, WS.lerefl(w0)) :
    {Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(w1))), Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, U32.is_lt(at, slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), ts, at), tt, w0)), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(w1))), True{}, P.Nat.le_trans(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), Nat.add(V.U.N(w0), V.U.N(U32.sub(w1, w0))), V.U.N(w1), MT_.MT.add_le(V.U.N(w0), V.U.N(w0), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(w0)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, at))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), MT_.MT.cf(ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 0), MT_.MT.cn(ts, at, MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, at)))), SC_.SC.fb1(w0, w1, hw))) :
    {Bool.and(True{}, Bool.and(_, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, U32.is_lt(at, slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), ts, at), tt, w0)), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(at, slen), True{}, V.U.N_lt(at, slen, P.Nat.lt_le_trans(V.U.N(at), Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(slen), WS.lt_pos(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), P.Nat.lt_le_trans(0n, 4n, V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), {==}, V.U.le_N(4, SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), h4))), P.Nat.le_trans(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), Nat.add(V.U.N(at), V.U.N(U32.sub(slen, at))), V.U.N(slen), MT_.MT.add_le(V.U.N(at), V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.sub(slen, at)), C.CP.le_refl(V.U.N(at)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, at))), V.U.N(U32.sub(slen, at)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), MT_.MT.cf(ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 0), MT_.MT.cn(ts, at, MT_.MW{tt, w0}, 0)), MT_.MT.min_le_r(U32.sub(w1, w0), U32.sub(slen, at)))), SC_.SC.fb1(at, slen, hat))))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), ts, at), tt, w0)), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), V.U.N(slen))), True{}, P.Nat.le_trans(Nat.add(V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))))), Nat.add(V.U.N(at), V.U.N(U32.sub(slen, at))), V.U.N(slen), MT_.MT.add_le(V.U.N(at), V.U.N(at), V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.sub(slen, at)), C.CP.le_refl(V.U.N(at)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, at))), V.U.N(U32.sub(slen, at)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), MT_.MT.cf(ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 0), MT_.MT.cn(ts, at, MT_.MW{tt, w0}, 0)), MT_.MT.min_le_r(U32.sub(w1, w0), U32.sub(slen, at)))), SC_.SC.fb1(at, slen, hat))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, True{}, Bool.and(_, S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), ts, at), tt, w0)), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), ts, at), S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, w0), MT_.MT.cs0_ok(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, at)), 2n), 1)), ts, at, MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), E, SC_.SC.fb(at, slen, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), E, hat, MT_.MT.min_le_r(U32.sub(w1, w0), U32.sub(slen, at)), hEs), SC_.SC.fb(w0, w1, U32.min(U32.sub(w1, w0), U32.sub(slen, at)), E, hw, MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, at)), hE4))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, True{}, Bool.and(True{}, S.S.has(_, tt, w0)), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, w0), tt, w0), True{}, EM_.EM.has_sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, w0)) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), Bool.pick(Bool, True{}, Bool.and(True{}, _), Bool.and(U32.is_lt(U32.sub(at, slen), U32.sub(w0, w0)), S.S.has(S.S.sl(V.U.N(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at)))), tt, U32.add(w0, U32.sub(at, slen))), tt, w0)))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0), True{}), True{}, P.Bool.or_true(U32.is_eq(SC_.SC.flen(ts, at, tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, at))), 0))) :
    {_ == True{} : Bool}
  {==}

def WS.tio(+s: EST) -> A.Tr:
  match s:
    case EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      tio

# The scan's facts: the window, the copy segment the whole source.
def WS.sk(+E: N.EK, +w0: U32, +w1: U32) -> N.SK:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      N.SK{slen, w0, w1, slen, lsh, lmask, ssh, smask, cap}

law WS.inv0.go:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +tio: A.Tr
  for +cont: U32
  for +Eb: U32
  for +BIG: U32
  for +c: Bool
  for +ec: {U32.is_le(4, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))) == c : Bool}
  for +hpf: {A.T.pf(SC_.SC.dep(tio), tio) == True{} : Bool}
  for +hd: {Nat.cmp(SC_.SC.dep(tio), 32n) == LT{} : Cmp}
  for +h3: {Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(tio)))) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +hE4: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SC_.SC.Iv(ts, tt, slen, w0, w1, 0n, WS.putif(c, tio, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), N.u32.pick(c, U32.add(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), w0), 4, N.u32.pick(c, 1, 0)) == True{} : Bool}

def WS.inv0.go(ts, tt, slen, w0, w1, tio, cont, Eb, BIG, c, ec, hpf, hd, h3, hw, hE4, hEs, hk, hB):
  match c:
    case True{}:
      SC_.SC.Iv.mk(ts, tt, slen, w0, w1, 0n, SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), U32.add(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), 4, 1,
        SC_.SC.and_tt(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), 0)), True{}, (%Equal.sym(N.Ent, SE_.SE.ent(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), 0), N.Ent{w0, U32.and(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), 2147483647), WS.at(slen, cont), N.ent.run(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))}, SG_.SG.get_same(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf, hd, h3)) : {SG_.SG.ok0(ts, tt, slen, w0, w1, _) == True{} : Bool}; WS.mt_ok0(ts, tt, slen, w0, w1, Eb, BIG, WS.at(slen, cont), WS.at_le(slen, cont), hw, hE4, hEs, ec, hk, hB)), {==}),
        (%Equal.sym(Nat, SC_.SC.dep(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont))), SC_.SC.dep(tio), SC_.SC.dep_pf(SC_.SC.dep(tio), SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), SG_.SG.pf_put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf))) : {A.T.pf(_, SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont))) == True{} : Bool}; SG_.SG.pf_put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf)),
        (%Equal.sym(Nat, SC_.SC.dep(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont))), SC_.SC.dep(tio), SC_.SC.dep_pf(SC_.SC.dep(tio), SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), SG_.SG.pf_put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf))) : {Nat.cmp(_, 32n) == LT{} : Cmp}; hd),
        (%Equal.sym(Nat, SC_.SC.dep(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont))), SC_.SC.dep(tio), SC_.SC.dep_pf(SC_.SC.dep(tio), SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), SG_.SG.pf_put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf))) : {Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(_))) == True{} : Bool}; h3),
        (%Equal.sym(Nat, V.U.N(U32.add(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), V.U.add_N(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), w1, P.Nat.le_trans(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(U32.sub(w1, w0))), V.U.N(w1), MT_.MT.add_le(V.U.N(w0), V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(w0)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), 2n), 1)), ts, WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), MT_.MT.cf(ts, WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), 0), MT_.MT.cn(ts, WS.at(slen, cont), MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), SC_.SC.fb1(w0, w1, hw)))) : {Cmp.is_le(Nat.cmp(1n+V.U.N(w0), Nat.add(_, 0n))) == True{} : Bool};
          (%Equal.sym(Nat, Nat.add(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), 0n), Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), P.Nat.add_zero_r(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))))) : {Cmp.is_le(Nat.cmp(1n+V.U.N(w0), _)) == True{} : Bool};
            (%Equal.sym(Nat, Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), Nat.add(V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(w0)), P.Nat.add_comm(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))))) : {Cmp.is_le(Nat.cmp(1n+V.U.N(w0), _)) == True{} : Bool}; MT_.MT.add_le(1n, V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(w0), V.U.N(w0), P.Nat.le_trans(1n, 4n, V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), {==}, V.U.le_N(4, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), ec)), C.CP.le_refl(V.U.N(w0)))))),
        V.U.N_le(w0, U32.add(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), (%Equal.sym(Nat, V.U.N(U32.add(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), V.U.add_N(w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), w1, P.Nat.le_trans(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(U32.sub(w1, w0))), V.U.N(w1), MT_.MT.add_le(V.U.N(w0), V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(w0)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), 2n), 1)), ts, WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), MT_.MT.cf(ts, WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))), 0), MT_.MT.cn(ts, WS.at(slen, cont), MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), SC_.SC.fb1(w0, w1, hw)))) : {Cmp.is_le(Nat.cmp(V.U.N(w0), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))))))),
        {==}, (%Equal.sym(Nat, SC_.SC.dep(SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont))), SC_.SC.dep(tio), SC_.SC.dep_pf(SC_.SC.dep(tio), SG_.SG.put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont)), SG_.SG.pf_put(tio, 0, w0, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont)))), WS.at(slen, cont), SC_.SC.dep(tio), hpf))) : {Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(_))) == True{} : Bool}; h3))
    case False{}:
      SC_.SC.Iv.mk(ts, tt, slen, w0, w1, 0n, tio, w0, 4, 0, {==}, hpf, hd, P.Nat.le_zero(P.Nat.pow2(SC_.SC.dep(tio))), (%Equal.sym(Nat, Nat.add(V.U.N(w0), 0n), V.U.N(w0), P.Nat.add_zero_r(V.U.N(w0))) : {Cmp.is_le(Nat.cmp(V.U.N(w0), _)) == True{} : Bool}; C.CP.le_refl(V.U.N(w0))), WS.lerefl(w0), {==}, h3)

law WS.inv0:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: EST
  for +Eb: U32
  for +BIG: U32
  for +hpf: {A.T.pf(SC_.SC.dep(WS.tio(s)), WS.tio(s)) == True{} : Bool}
  for +hd: {Nat.cmp(SC_.SC.dep(WS.tio(s)), 32n) == LT{} : Cmp}
  for +h3: {Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(WS.tio(s))))) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +hE4: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.slen(E)), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SC_.SC.Is(WS.sk(E, w0, w1), ts, tt, 0n, WS.st0(E, w0, w1, ts, tt, s)) == True{} : Bool}

def WS.inv0(E, w0, w1, ts, tt, s, Eb, BIG, hpf, hd, h3, hw, hE4, hEs, hk, hB):
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      WS.inv0.go(ts, tt, slen, w0, w1, tio, cont, Eb, BIG, U32.is_le(4, SC_.SC.flen(ts, WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS.at(slen, cont))))), {==}, hpf, hd, h3, hw, hE4, hEs, hk, hB)

# The scan, as code.
law WS.scan_code:
  for +E: N.EK
  for +K: N.SK
  for +w0: U32
  for +w1: U32
  for +to: A.Tr
  for +olen: U32
  for +lidx: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: SC_.ST
  for +Eb: U32
  for +BIG: U32
  for +hk: {SC_.SC.kf(K, e, Eb, BIG) == True{} : Bool}
  for +hI: {SC_.SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC_.SC.pp(st), SC_.SC.w1(K)) == True{} : Bool}
  {N.win.scan(E, K, w0, w1, A.A.from(to), olen, lidx, SC_.SC.sc(ts, tt, e, st)) == N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, SC_.SC.sc(ts, tt, e, SC_.SC.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, ts, tt, e, SC_.SC.restart(K, tt, st)))) : N.ES}

def WS.scan_code(E, K, w0, w1, to, olen, lidx, ts, tt, e, st, Eb, BIG, hk, hI, hp):
  %Equal.sym(Bool & N.Sc, N.sc.restart(K, SC_.SC.sc(ts, tt, e, st)), SC_.SC.b(ts, tt, e, SC_.SC.restart(K, tt, st)), SC_.SC.restart_code(ts, tt, e, K, st)) :
    {N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, N.sc.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, _)) == N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, SC_.SC.sc(ts, tt, e, SC_.SC.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, ts, tt, e, SC_.SC.restart(K, tt, st)))) : N.ES}
  %Equal.sym(N.Sc, N.sc.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, SC_.SC.b(ts, tt, e, SC_.SC.restart(K, tt, st))), SC_.SC.sc(ts, tt, e, SC_.SC.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, ts, tt, e, SC_.SC.restart(K, tt, st))), SC_.SC.loop_code(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), ts, tt, e, K, Eb, BIG, SC_.SC.restart(K, tt, st), hk, SC_.SC.restart_inv(ts, tt, e, K, Eb, BIG, st, hk, hI, hp))) :
    {N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, _) == N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, SC_.SC.sc(ts, tt, e, SC_.SC.loop(U32.to_nat(U32.add(U32.sub(w1, w0), 2)), K, ts, tt, e, SC_.SC.restart(K, tt, st)))) : N.ES}
  {==}

# Writing the window
# ------------------

def WS.wto(+to: A.Tr, +olen: U32, +tt: A.Tr, +w0: U32, +tlen: U32, +cpl: U32, +off: U32, +e: EM_.ET) -> A.Tr:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      S.S.puts(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(N.u32.pick(U32.is_lt(0, cpl), 5, 4) <> [], WW_.WW.sb(U32.is_lt(0, cpl), cpl, off)), R.VI.var(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al))), R.VI.var(tlen)), 0 <> []), R.VI.var(dl)), R.VI.var(il)), R.VI.var(al)), U32.shrn(H.AD.T(tt, w0, tlen), 24n) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 16n), 255) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 8n), 255) <> []), U32.and(H.AD.T(tt, w0, tlen), 255) <> []), S.S.sl(V.U.N(dl), td, 0)), S.S.sl(V.U.N(il), ti, 0)), S.S.sl(V.U.N(al), ta, 0)), EM_.GR.t(to, olen, U32.add(olen, U32.add(U32.add(U32.add(1, N.u32.pick(U32.is_lt(0, cpl), U32.add(B.B.var.len(cpl), B.B.var.len(off)), 0)), B.B.var.len(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al))), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al)))), olen)

def WS.wol(+olen: U32, +tt: A.Tr, +w0: U32, +tlen: U32, +cpl: U32, +off: U32, +e: EM_.ET) -> U32:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(WW_.WW.sp(U32.is_lt(0, cpl), cpl, off, U32.add(olen, 1)), B.B.var.len(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al))), B.B.var.len(tlen)), 1), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 1), 1), 1), 1), dl), il), al)

# The window's bytes fit below Eo.
def WS.hbv(+olen: U32, +tt: A.Tr, +w0: U32, +tlen: U32, +cpl: U32, +off: U32, +e: EM_.ET, +Eo: U32) -> Bool:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      Cmp.is_le(Nat.cmp(Nat.add(V.U.N(olen), S.S.len(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(N.u32.pick(U32.is_lt(0, cpl), 5, 4) <> [], WW_.WW.sb(U32.is_lt(0, cpl), cpl, off)), R.VI.var(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al))), R.VI.var(tlen)), 0 <> []), R.VI.var(dl)), R.VI.var(il)), R.VI.var(al)), U32.shrn(H.AD.T(tt, w0, tlen), 24n) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 16n), 255) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 8n), 255) <> []), U32.and(H.AD.T(tt, w0, tlen), 255) <> []), S.S.sl(V.U.N(dl), td, 0)), S.S.sl(V.U.N(il), ti, 0)), S.S.sl(V.U.N(al), ta, 0)))), V.U.N(Eo)))

# The emitter after the write: its sections kept, its counts cleared.
def WS.ez(+e: EM_.ET) -> EM_.ET:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      EM_.ET{td, ti, ta, tc, 0, 0, 0, 0, 0, 0, 0, 0, 0}

law WS.write:
  for +to: A.Tr
  for +olen: U32
  for +tt: A.Tr
  for +w0: U32
  for +tlen: U32
  for +cpl: U32
  for +off: U32
  for +e: EM_.ET
  for +Eo: U32
  for +Ea: U32
  for +ha: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}
  for +hb: {WS.hbv(olen, tt, w0, tlen, cpl, off, e, Eo) == True{} : Bool}
  {N.win.write(A.A.from(to), olen, A.A.from(tt), w0, tlen, cpl, off, EM_.EM.em(e)) == ((A.A.from(WS.wto(to, olen, tt, w0, tlen, cpl, off, e)), WS.wol(olen, tt, w0, tlen, cpl, off, e)), (A.A.from(tt), EM_.EM.em(WS.ez(e)))) : (Array<U32> & U32) & (Array<U32> & N.Em)}

def WS.write(to, olen, tt, w0, tlen, cpl, off, e, Eo, Ea, ha, hb):
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      WW_.WW.write(to, olen, tt, w0, tlen, cpl, off, td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc, Eo, Ea, ha, hb)

# The emitter at a window's start
# -------------------------------

def WS.td(+e: EM_.ET) -> A.Tr:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      td

def WS.ti(+e: EM_.ET) -> A.Tr:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      ti

def WS.ta(+e: EM_.ET) -> A.Tr:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      ta

# Its ghost: nothing written, the sections' depths.
def WS.g0(+e: EM_.ET) -> EM_.EG:
  EM_.EG{[], Q.HN{}, SC_.SC.dep(WS.td(e)), SC_.SC.dep(WS.ti(e)), SC_.SC.dep(WS.ta(e))}

# The sections' shapes, and room for an instruction.
def WS.eok(+e: EM_.ET) -> Bool:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      Bool.and(Bool.and(A.T.pf(SC_.SC.dep(td), td), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(td), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ti), ti), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ti), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ta), ta), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ta), 32n)), Cmp.is_le(Nat.cmp(6n, EM_.EM.cap(SC_.SC.dep(ti)))))))))), A.T.pf(10n, tc))

law WS.einv0:
  for +e: EM_.ET
  for +ts: A.Tr
  for +tt: A.Tr
  for +seg: U32
  for +cpl: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +Es: U32
  for +BIG: U32
  for +he: {WS.eok(e) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  {EM_.EM.inv(EM_.EM.reset(w0, e), WS.g0(e), EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}) == True{} : Bool}

def WS.einv0(e, ts, tt, seg, cpl, w0, w1, E, Es, BIG, he, hw):
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      %Equal.sym(Bool, Bool.and(A.T.pf(SC_.SC.dep(td), td), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(td), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ti), ti), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ti), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ta), ta), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ta), 32n)), Cmp.is_le(Nat.cmp(6n, EM_.EM.cap(SC_.SC.dep(ti)))))))))), True{}, P.Bool.and_l(Bool.and(A.T.pf(SC_.SC.dep(td), td), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(td), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ti), ti), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ti), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ta), ta), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ta), 32n)), Cmp.is_le(Nat.cmp(6n, EM_.EM.cap(SC_.SC.dep(ti)))))))))), A.T.pf(10n, tc), he)) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(_, Bool.and(Bool.and(U32.is_eq(w0, Q.SP.so(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(U32.is_le(w0, w0), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(0n, V.U.N(U32.sub(w0, w0)))), Bool.and(Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(w0, Q.SP.so(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), True{}, V.U.is_eq_refl(w0)) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(_, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(U32.is_le(w0, w0), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(0n, V.U.N(U32.sub(w0, w0)))), Bool.and(Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_le(w0, w0), True{}, WS.lerefl(w0)) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(True{}, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(_, Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(0n, V.U.N(U32.sub(w0, w0)))), Bool.and(Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_le(w0, w1), True{}, hw) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(True{}, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(True{}, Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(0n, V.U.N(U32.sub(w0, w0)))), Bool.and(Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, Cmp.is_le(Nat.cmp(0n, V.U.N(U32.sub(w0, w0)))), True{}, P.Nat.le_zero(V.U.N(U32.sub(w0, w0)))) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(True{}, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(True{}, Bool.and(True{}, Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, Cmp.is_le(Nat.cmp(0n, Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))), True{}, P.Nat.le_zero(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w0, w0))))))) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(True{}, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(_, Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))))))))), True{})))))) == True{} : Bool}
      %Equal.sym(Bool, Cmp.is_le(Nat.cmp(0n, EM_.EM.k5(V.U.N(U32.sub(w0, w0))))), True{}, P.Nat.le_zero(EM_.EM.k5(V.U.N(U32.sub(w0, w0))))) :
        {Bool.and(Bool.and(S.S.has(Q.SP.datl(EM_.EM.hs([], Q.HN{})), td, 0), Q.SP.lenis(Q.SP.datl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Q.SP.lenis([], 0), Bool.and(Bool.and(S.S.has(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), ta, 0), Q.SP.lenis(Q.SP.adrl(EM_.EM.hs([], Q.HN{})), 0)), Bool.and(Bool.and(Q.SP.vhs(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})), Bool.and(Q.SP.bnds(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG}), E, Es), Bool.and(Q.SP.doks(EM_.EM.hs([], Q.HN{})), True{}))), Bool.and(True{}, Bool.and(Bool.and(True{}, Bool.and(U32.is_eq(0, Q.SP.ss(Q.SP.run(EM_.EM.hs([], Q.HN{}), Q.XC{ts, tt, seg, cpl, w0, w1}, EM_.EM.s0(EM_.EW{Q.XC{ts, tt, seg, cpl, w0, w1}, E, Es, A.A.to(D.ct.table()), BIG})))), Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, _)))))), True{})))))) == True{} : Bool}
      {==}

# The window's end
# ----------------

# The emitter after the settling, the gap and the flush.
def WS.e3(+E: N.EK, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET, +st: SC_.ST) -> EM_.ET:
  match E e st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))

def WS.cc(+E: N.EK, +st: SC_.ST) -> U32:
  match E st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SG_.SG.cC(True{}, slen, nio, tio)

def WS.co(+E: N.EK, +st: SC_.ST) -> U32:
  match E st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SG_.SG.cO(True{}, slen, nio, tio)

# The window's choice
# -------------------

# Its sections' bytes.
def WS.secs(+e: EM_.ET) -> U32:
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      U32.add(U32.add(dl, il), al)

# Whether the window is written as an ADD of its bytes instead (win.out).
def WS.big(+w0: U32, +w1: U32, +e: EM_.ET) -> Bool:
  U32.is_lt(N.raw.secs(U32.sub(w1, w0)), WS.secs(e))

# win.out, as the mirror's choice.
law WS.out_if:
  for +to: A.Tr
  for +olen: U32
  for +tt: A.Tr
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +off: U32
  for +e: EM_.ET
  {N.win.out(A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)) == N.win.out.if(WS.big(w0, w1, e), A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)) : (Array<U32> & U32) & (Array<U32> & N.Em)}

def WS.out_if(to, olen, tt, w0, w1, cpl, off, e):
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      {==}

# The emitter that writes it: a fresh one with the ADD, or e.
def WS.pe(+z: Bool, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET) -> EM_.ET:
  match z:
    case True{}:
      EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e)))
    case False{}:
      e

# Its copy segment's fields: none for the ADD.
def WS.pz(+z: Bool, +c: U32) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      c

law WS.out_code.go:
  for +to: A.Tr
  for +olen: U32
  for +tt: A.Tr
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +off: U32
  for +e: EM_.ET
  for +Eo: U32
  for +Ea: U32
  for +z: Bool
  for +he: {WS.eok(e) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +ha: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(w1, w0)), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}
  for +hb: {WS.hbv(olen, tt, w0, U32.sub(w1, w0), WS.pz(z, cpl), WS.pz(z, off), WS.pe(z, w0, w1, tt, e), Eo) == True{} : Bool}
  {N.win.out.if(z, A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)) == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS.pz(z, cpl), WS.pz(z, off), WS.pe(z, w0, w1, tt, e))), WS.wol(olen, tt, w0, U32.sub(w1, w0), WS.pz(z, cpl), WS.pz(z, off), WS.pe(z, w0, w1, tt, e))), (A.A.from(tt), EM_.EM.em(WS.ez(WS.pe(z, w0, w1, tt, e))))) : (Array<U32> & U32) & (Array<U32> & N.Em)}

# The window's write, as code: the instructions, or the ADD.
law WS.out_code:
  for +to: A.Tr
  for +olen: U32
  for +tt: A.Tr
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +off: U32
  for +e: EM_.ET
  for +Eo: U32
  for +Ea: U32
  for +he: {WS.eok(e) == True{} : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +ha: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(w1, w0)), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}
  for +hb: {WS.hbv(olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, e), cpl), WS.pz(WS.big(w0, w1, e), off), WS.pe(WS.big(w0, w1, e), w0, w1, tt, e), Eo) == True{} : Bool}
  {N.win.out(A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)) == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, e), cpl), WS.pz(WS.big(w0, w1, e), off), WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))), WS.wol(olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, e), cpl), WS.pz(WS.big(w0, w1, e), off), WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))), (A.A.from(tt), EM_.EM.em(WS.ez(WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))))) : (Array<U32> & U32) & (Array<U32> & N.Em)}

def WS.e4(+E: N.EK, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET, +st: SC_.ST) -> EM_.ET:
  WS.pe(WS.big(w0, w1, WS.e3(E, w0, w1, tt, e, st)), w0, w1, tt, WS.e3(E, w0, w1, tt, e, st))

def WS.c4(+E: N.EK, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET, +st: SC_.ST) -> U32:
  WS.pz(WS.big(w0, w1, WS.e3(E, w0, w1, tt, e, st)), WS.cc(E, st))

def WS.o4(+E: N.EK, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET, +st: SC_.ST) -> U32:
  WS.pz(WS.big(w0, w1, WS.e3(E, w0, w1, tt, e, st)), WS.co(E, st))

def WS.fin(+E: N.EK, +w0: U32, +w1: U32, +tt: A.Tr, +e: EM_.ET, +st: SC_.ST, +to: A.Tr, +olen: U32, +lidx: U32) -> EST:
  match E st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      EST{tl, tb, tv, SG_.SG.cT(True{}, slen, nio, tio), WS.ez(WS.e4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS.c4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), WS.o4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), WS.e4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), WS.wol(olen, tt, w0, U32.sub(w1, w0), WS.c4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), WS.o4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), WS.e4(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, e, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), lidx, cont}

# The window's facts the emitter needs.
def WS.wokv(+w0: U32, +w1: U32, +Et: U32, +BIGe: U32) -> Bool:
  Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(w1), V.U.N(Et))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w1, w0))))), 16n), V.U.N(BIGe))))))

law WS.fin_code:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: SC_.ST
  for +to: A.Tr
  for +olen: U32
  for +lidx: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Eo: U32
  for +Ea: U32
  for +he: {WS.eok(e) == True{} : Bool}
  for +hI: {SC_.SC.Is(WS.sk(E, w0, w1), ts, tt, 0n, st) == True{} : Bool}
  for +hwok: {WS.wokv(w0, w1, Et, BIGe) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.slen(E)), V.U.N(U32.sub(w1, w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(WS.slen(E)), V.U.N(Es))) == True{} : Bool}
  for +ha: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(w1, w0)), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}
  for +he3: {WS.eok(WS.e3(E, w0, w1, tt, e, st)) == True{} : Bool}
  for +hb: {WS.hbv(olen, tt, w0, U32.sub(w1, w0), WS.c4(E, w0, w1, tt, e, st), WS.o4(E, w0, w1, tt, e, st), WS.e4(E, w0, w1, tt, e, st), Eo) == True{} : Bool}
  {N.win.fin(E, w0, w1, A.A.from(to), olen, lidx, SC_.SC.sc(ts, tt, EM_.EM.reset(w0, e), st)) == WS.es(ts, tt, WS.fin(E, w0, w1, tt, e, st, to, olen, lidx)) : N.ES}

# A window
# --------

def WS.w1(+E: N.EK, +w0: U32) -> U32:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      U32.min(tlen, U32.add(w0, wsz))

# The scan's last state.
def WS.stF(+E: N.EK, +w0: U32, +ts: A.Tr, +tt: A.Tr, +s: EST) -> SC_.ST:
  SC_.SC.loop(U32.to_nat(U32.add(U32.sub(WS.w1(E, w0), w0), 2)), WS.sk(E, w0, WS.w1(E, w0)), ts, tt, EM_.EM.reset(w0, WS.ee(s)), SC_.SC.restart(WS.sk(E, w0, WS.w1(E, w0)), tt, WS.st0(E, w0, WS.w1(E, w0), ts, tt, s)))

def WS.enc(+E: N.EK, +w0: U32, +ts: A.Tr, +tt: A.Tr, +s: EST) -> EST:
  WS.fin(E, w0, WS.w1(E, w0), tt, WS.ee(s), WS.stF(E, w0, ts, tt, s), WS.to(s), WS.olen(s), WS.lid0(E, w0, WS.w1(E, w0), ts, tt, s))

law WS.enc_code:
  for +E: N.EK
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: EST
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Eo: U32
  for +Ea: U32
  for +he: {WS.eok(WS.ee(s)) == True{} : Bool}
  for +hk: {SC_.SC.kf(WS.sk(E, w0, WS.w1(E, w0)), EM_.EM.reset(w0, WS.ee(s)), Eb, BIGs) == True{} : Bool}
  for +hI: {SC_.SC.Is(WS.sk(E, w0, WS.w1(E, w0)), ts, tt, 0n, WS.st0(E, w0, WS.w1(E, w0), ts, tt, s)) == True{} : Bool}
  for +hp: {U32.is_le(SC_.SC.pp(WS.st0(E, w0, WS.w1(E, w0), ts, tt, s)), WS.w1(E, w0)) == True{} : Bool}
  for +hS: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.slen(E)), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hW: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.w1(E, w0)), 4n), V.U.N(Eb))) == True{} : Bool}
  for +hwok: {WS.wokv(w0, WS.w1(E, w0), Et, BIGe) == True{} : Bool}
  for +hH: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS.slen(E)), V.U.N(U32.sub(WS.w1(E, w0), w0))), V.U.N(HB))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(V.U.N(WS.slen(E)), V.U.N(Es))) == True{} : Bool}
  for +ha: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}
  for +he3: {WS.eok(WS.e3(E, w0, WS.w1(E, w0), tt, WS.ee(s), WS.stF(E, w0, ts, tt, s))) == True{} : Bool}
  for +hb: {WS.hbv(WS.olen(s), tt, w0, U32.sub(WS.w1(E, w0), w0), WS.c4(E, w0, WS.w1(E, w0), tt, WS.ee(s), WS.stF(E, w0, ts, tt, s)), WS.o4(E, w0, WS.w1(E, w0), tt, WS.ee(s), WS.stF(E, w0, ts, tt, s)), WS.e4(E, w0, WS.w1(E, w0), tt, WS.ee(s), WS.stF(E, w0, ts, tt, s)), Eo) == True{} : Bool}
  {N.win.enc(E, w0, WS.es(ts, tt, s)) == WS.es(ts, tt, WS.enc(E, w0, ts, tt, s)) : N.ES}

# The window's first steps keep the emitter's cache a 10-deep tree.
law WS.eok_tc:
  for +e: EM_.ET
  for +h: {WS.eok(e) == True{} : Bool}
  {A.T.pf(10n, EM_.EM.tc(e)) == True{} : Bool}

def WS.eok_tc(e, h):
  match e:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      P.Bool.and_r(Bool.and(A.T.pf(SC_.SC.dep(td), td), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(td), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ti), ti), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ti), 32n)), Bool.and(A.T.pf(SC_.SC.dep(ta), ta), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(ta), 32n)), Cmp.is_le(Nat.cmp(6n, EM_.EM.cap(SC_.SC.dep(ti)))))))))), A.T.pf(10n, tc), h)

def WS.out_code.go(to, olen, tt, w0, w1, cpl, off, e, Eo, Ea, z, he, hw, ha, hb):
  match z:
    case True{}:
      %Equal.sym(N.Em, N.em.reset(w0, EM_.EM.em(e)), EM_.EM.em(EM_.EM.reset(w0, e)), EM_.EM.reset_code(w0, e, WS.eok_tc(e, he))) :
        {N.win.raw(A.A.from(to), olen, w0, w1, N.em.gap(A.A.from(tt), w1, _)) == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), (A.A.from(tt), EM_.EM.em(WS.ez(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))))) : (Array<U32> & U32) & Array<U32> & N.Em}
      %Equal.sym(Array<U32> & N.Em, N.em.gap(A.A.from(tt), w1, EM_.EM.em(EM_.EM.reset(w0, e))), (A.A.from(tt), EM_.EM.em(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e)))), WF_.WF.gap_code(EM_.EM.reset(w0, e), WS.g0(e), tt, tt, 0, 0, w0, w1, w1, 0, 0, WS.einv0(e, tt, tt, 0, 0, w0, w1, w1, 0, 0, he, hw))) :
        {N.win.raw(A.A.from(to), olen, w0, w1, _) == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), (A.A.from(tt), EM_.EM.em(WS.ez(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))))) : (Array<U32> & U32) & Array<U32> & N.Em}
      %Equal.sym(N.Em, N.em.flush(EM_.EM.em(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e)))), EM_.EM.em(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e)))), EM_.EM.fl_code(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e)))) :
        {N.win.write(A.A.from(to), olen, A.A.from(tt), w0, U32.sub(w1, w0), 0, 0, _) == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), (A.A.from(tt), EM_.EM.em(WS.ez(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))))) : (Array<U32> & U32) & Array<U32> & N.Em}
      %Equal.sym((Array<U32> & U32) & Array<U32> & N.Em, N.win.write(A.A.from(to), olen, A.A.from(tt), w0, U32.sub(w1, w0), 0, 0, EM_.EM.em(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), (A.A.from(tt), EM_.EM.em(WS.ez(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))))), WS.write(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))), Eo, Ea, ha, hb)) :
        {_ == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), 0, 0, EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))), (A.A.from(tt), EM_.EM.em(WS.ez(EM_.EM.fl(EM_.EM.gap(tt, w1, EM_.EM.reset(w0, e))))))) : (Array<U32> & U32) & Array<U32> & N.Em}
      {==}
    case False{}:
      %Equal.sym((Array<U32> & U32) & Array<U32> & N.Em, N.win.write(A.A.from(to), olen, A.A.from(tt), w0, U32.sub(w1, w0), cpl, off, EM_.EM.em(e)), ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), cpl, off, e)), WS.wol(olen, tt, w0, U32.sub(w1, w0), cpl, off, e)), (A.A.from(tt), EM_.EM.em(WS.ez(e)))), WS.write(to, olen, tt, w0, U32.sub(w1, w0), cpl, off, e, Eo, Ea, ha, hb)) :
        {_ == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), cpl, off, e)), WS.wol(olen, tt, w0, U32.sub(w1, w0), cpl, off, e)), (A.A.from(tt), EM_.EM.em(WS.ez(e)))) : (Array<U32> & U32) & Array<U32> & N.Em}
      {==}

def WS.out_code(to, olen, tt, w0, w1, cpl, off, e, Eo, Ea, he, hw, ha, hb):
  %Equal.sym((Array<U32> & U32) & Array<U32> & N.Em, N.win.out(A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)), N.win.out.if(WS.big(w0, w1, e), A.A.from(to), olen, A.A.from(tt), w0, w1, cpl, off, EM_.EM.em(e)), WS.out_if(to, olen, tt, w0, w1, cpl, off, e)) :
    {_ == ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, e), cpl), WS.pz(WS.big(w0, w1, e), off), WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))), WS.wol(olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, e), cpl), WS.pz(WS.big(w0, w1, e), off), WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))), (A.A.from(tt), EM_.EM.em(WS.ez(WS.pe(WS.big(w0, w1, e), w0, w1, tt, e))))) : (Array<U32> & U32) & Array<U32> & N.Em}
  WS.out_code.go(to, olen, tt, w0, w1, cpl, off, e, Eo, Ea, WS.big(w0, w1, e), he, hw, ha, hb)

law WS.w01:
  for +w0: U32
  for +w1: U32
  for +Et: U32
  for +BIGe: U32
  for +h: {WS.wokv(w0, w1, Et, BIGe) == True{} : Bool}
  {U32.is_le(w0, w1) == True{} : Bool}

def WS.w01(w0, w1, Et, BIGe, h):
  P.Bool.and_l(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(w1), V.U.N(Et))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w1, w0))))), 16n), V.U.N(BIGe))))), h)

def WS.fin_code(E, w0, w1, ts, tt, e, st, to, olen, lidx, Et, Es, BIGe, HB, Eo, Ea, he, hI, hwok, hH, hEs, ha, he3, hb):
  match E e st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32 & U32, N.seg.choose(True{}, slen, nio, A.A.from(tio)), (A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), (SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio))), SG_.SG.choose_code(True{}, slen, nio, tio)) :
        {N.win.fin.seg(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), EM_.EM.em(EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc})), A.A.from(to), olen, lidx, nio, cont, _) == WS.es(ts, tt, WS.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, to, olen, lidx)) : N.ES}
      %Equal.sym(Array<U32> & Array<U32> & N.Em, N.io.flush(A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, A.A.from(tt), EM_.EM.em(EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}))), (A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), (A.A.from(tt), EM_.EM.em(SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), WF_.WF.em_code(EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), ts, tt, Q.SP.wseg(SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio)), SG_.SG.cC(True{}, slen, nio, tio), w0, w1, Et, Es, BIGe, HB, nio, SG_.SG.cT(True{}, slen, nio, tio), WS.einv0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, ts, tt, Q.SP.wseg(SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio)), SG_.SG.cC(True{}, slen, nio, tio), w0, w1, Et, Es, BIGe, he, P.Bool.and_l(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(w1), V.U.N(Et))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w1, w0))))), 16n), V.U.N(BIGe))))), hwok)), {==}, hwok, P.Nat.le_trans(Nat.add(V.U.N(SG_.SG.cC(True{}, slen, nio, tio)), V.U.N(U32.sub(w1, w0))), Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(HB), MT_.MT.add_le(V.U.N(SG_.SG.cC(True{}, slen, nio, tio)), V.U.N(slen), V.U.N(U32.sub(w1, w0)), V.U.N(U32.sub(w1, w0)), V.U.le_N(SG_.SG.cC(True{}, slen, nio, tio), slen, SG_.SG.cC_le(True{}, ts, tt, slen, w0, w1, nio, tio, SC_.SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI))), C.CP.le_refl(V.U.N(U32.sub(w1, w0)))), hH), SG_.SG.choose_oks(True{}, ts, tt, slen, w0, w1, Es, HB, nio, tio, SC_.SC.dep(tio), SC_.SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(tio), 32n), SC_.SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC_.SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), hH, hEs, SC_.SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)))) :
        {N.win.fin.k1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio), A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(to), olen, lidx, cont, _) == WS.es(ts, tt, WS.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, to, olen, lidx)) : N.ES}
      %Equal.sym(Array<U32> & N.Em, N.em.gap(A.A.from(tt), w1, EM_.EM.em(SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)}))))), (A.A.from(tt), EM_.EM.em(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), WF_.WF.gap1_code(EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), ts, tt, Q.SP.wseg(SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio)), SG_.SG.cC(True{}, slen, nio, tio), w0, w1, Et, Es, BIGe, HB, nio, SG_.SG.cT(True{}, slen, nio, tio), WS.einv0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, ts, tt, Q.SP.wseg(SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio)), SG_.SG.cC(True{}, slen, nio, tio), w0, w1, Et, Es, BIGe, he, P.Bool.and_l(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(w1), V.U.N(Et))), Bool.and(U32.is_lt(BIGe, 2147483648), Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w1, w0))))), 16n), V.U.N(BIGe))))), hwok)), {==}, hwok, P.Nat.le_trans(Nat.add(V.U.N(SG_.SG.cC(True{}, slen, nio, tio)), V.U.N(U32.sub(w1, w0))), Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(HB), MT_.MT.add_le(V.U.N(SG_.SG.cC(True{}, slen, nio, tio)), V.U.N(slen), V.U.N(U32.sub(w1, w0)), V.U.N(U32.sub(w1, w0)), V.U.le_N(SG_.SG.cC(True{}, slen, nio, tio), slen, SG_.SG.cC_le(True{}, ts, tt, slen, w0, w1, nio, tio, SC_.SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI))), C.CP.le_refl(V.U.N(U32.sub(w1, w0)))), hH), SG_.SG.choose_oks(True{}, ts, tt, slen, w0, w1, Es, HB, nio, tio, SC_.SC.dep(tio), SC_.SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC_.SC.ltc(Nat.cmp(SC_.SC.dep(tio), 32n), SC_.SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC_.SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), hH, hEs, SC_.SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)))) :
        {N.win.fin.k2(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio), A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), A.A.from(to), olen, lidx, cont, _) == WS.es(ts, tt, WS.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, to, olen, lidx)) : N.ES}
      %Equal.sym(N.Em, N.em.flush(EM_.EM.em(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), EM_.EM.em(EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), EM_.EM.fl_code(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))) :
        {N.win.fin.k3(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), lidx, cont, N.win.out(A.A.from(to), olen, A.A.from(tt), w0, w1, SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio), _)) == WS.es(ts, tt, WS.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, to, olen, lidx)) : N.ES}
      %Equal.sym((Array<U32> & U32) & Array<U32> & N.Em, N.win.out(A.A.from(to), olen, A.A.from(tt), w0, w1, SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio), EM_.EM.em(EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)}))))))), ((A.A.from(WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), SG_.SG.cC(True{}, slen, nio, tio)), WS.pz(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), SG_.SG.cO(True{}, slen, nio, tio)), WS.pe(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), w0, w1, tt, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))))), WS.wol(olen, tt, w0, U32.sub(w1, w0), WS.pz(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), SG_.SG.cC(True{}, slen, nio, tio)), WS.pz(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), SG_.SG.cO(True{}, slen, nio, tio)), WS.pe(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), w0, w1, tt, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))))), (A.A.from(tt), EM_.EM.em(WS.ez(WS.pe(WS.big(w0, w1, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))), w0, w1, tt, EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)})))))))))), WS.out_code(to, olen, tt, w0, w1, SG_.SG.cC(True{}, slen, nio, tio), SG_.SG.cO(True{}, slen, nio, tio), EM_.EM.fl(EM_.EM.gap(tt, w1, SE_.SE.fe(SE_.SE.loop(V.U.N(U32.add(nio, 1)), nio, SG_.SG.cC(True{}, slen, nio, tio), w0, SG_.SG.cT(True{}, slen, nio, tio), tt, (U32.is_ne(nio, 0), SE_.FT{EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), WS.g0(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}), SE_.SE.ent(SG_.SG.cT(True{}, slen, nio, tio), 0), 1, U32.is_ne(nio, 0)}))))), Eo, Ea, he3, WS.w01(w0, w1, Et, BIGe, hwok), ha, hb)) :
        {N.win.fin.k3(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.cT(True{}, slen, nio, tio)), lidx, cont, _) == WS.es(ts, tt, WS.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, w1, tt, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, to, olen, lidx)) : N.ES}
      {==}

def WS.enc_code(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Eo, Ea, he, hk, hI, hp, hS, hW, hwok, hH, hEs, ha, he3, hb):
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(N.ES, N.win.start(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), WS.es(ts, tt, s)), N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), A.A.from(WS.to(s)), WS.olen(s), WS.lid0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), SC_.SC.sc(ts, tt, EM_.EM.reset(w0, WS.ee(s)), WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s))), WS.start_code(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s, Eb, WS.eok_tc(WS.ee(s), he), WS.w01(w0, U32.min(tlen, U32.add(w0, wsz)), Et, BIGe, hwok), hS, hW)) :
        {_ == WS.es(ts, tt, WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)) : N.ES}
      %Equal.sym(N.ES, N.win.scan(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), A.A.from(WS.to(s)), WS.olen(s), WS.lid0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), SC_.SC.sc(ts, tt, EM_.EM.reset(w0, WS.ee(s)), WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s))), N.win.fin(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), A.A.from(WS.to(s)), WS.olen(s), WS.lid0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), SC_.SC.sc(ts, tt, EM_.EM.reset(w0, WS.ee(s)), SC_.SC.loop(U32.to_nat(U32.add(U32.sub(U32.min(tlen, U32.add(w0, wsz)), w0), 2)), N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, ts, tt, EM_.EM.reset(w0, WS.ee(s)), SC_.SC.restart(N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, tt, WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s))))), WS.scan_code(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), WS.to(s), WS.olen(s), WS.lid0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), ts, tt, EM_.EM.reset(w0, WS.ee(s)), WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), Eb, BIGs, hk, hI, hp)) :
        {_ == WS.es(ts, tt, WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)) : N.ES}
      WS.fin_code(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, WS.ee(s), WS.stF(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), WS.to(s), WS.olen(s), WS.lid0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), Et, Es, BIGe, HB, Eo, Ea, he,
        SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(U32.min(tlen, U32.add(w0, wsz)), w0), 2)), ts, tt, EM_.EM.reset(w0, WS.ee(s)), N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, Eb, BIGs, SC_.SC.restart(N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, tt, WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s)), hk, SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS.ee(s)), N.SK{slen, w0, U32.min(tlen, U32.add(w0, wsz)), slen, lsh, lmask, ssh, smask, cap}, Eb, BIGs, WS.st0(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, U32.min(tlen, U32.add(w0, wsz)), ts, tt, s), hk, hI, hp)),
        hwok, hH, hEs, ha, he3, hb)
