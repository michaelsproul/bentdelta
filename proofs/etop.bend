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
import ./wpar.bend as WR_
import ./dtop.bend as DT_



# The encoder
# ===========
#
# encode: the header, the index the first window needs, the windows in
# tasks, and the delta they make; the delta decodes to the target.
#
# Source: proofs/etop.bp (tools/bpp.py writes proofs/etop.bend from it).

# Where the windows end
# ---------------------
#
# Positions are U32 sums, so moving where the windows start moves where
# they end by as much.

law TP.pick_add:
  for +c: Bool
  for +a: U32
  for +x: U32
  for +y: U32
  {U32.add(a, B.u32.pick(c, x, y)) == B.u32.pick(c, U32.add(a, x), U32.add(a, y)) : U32}

def TP.pick_add(c, a, x, y):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law TP.wnd_shift:
  for +a: U32
  for +b: U32
  for +w: Q.AW
  {Q.SP.wnd(U32.add(a, b), w) == U32.add(a, Q.SP.wnd(b, w)) : U32}

def TP.wnd_shift(a, b, w):
  match w:
    case Q.AW{cpl, off, tlen, dl, il, al, ops, sum}:
      %Equal.sym(U32, U32.add(a, B.u32.pick(U32.is_lt(0, cpl), U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))), B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))), TP.pick_add(U32.is_lt(0, cpl), a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(a, b), 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(U32.add(a, b), 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == _ : U32}
      %Equal.sym(U32, U32.add(U32.add(a, b), 1), U32.add(a, U32.add(b, 1)), V.U.add_assoc(a, b, 1)) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(U32.add(U32.add(U32.add(_, B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(_, B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(cpl)), U32.add(a, U32.add(U32.add(b, 1), B.B.var.len(cpl))), V.U.add_assoc(a, U32.add(b, 1), B.B.var.len(cpl))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(U32.add(U32.add(_, B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(U32.add(b, 1), B.B.var.len(cpl))), B.B.var.len(off)), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off))), V.U.add_assoc(a, U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(U32.add(_, B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off))), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))), V.U.add_assoc(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(_, Q.SP.enc(tlen, dl, il, al)), U32.add(U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))), Q.SP.enc(tlen, dl, il, al)), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), V.U.add_assoc(a, U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) :
        {B.u32.pick(U32.is_lt(0, cpl), _, U32.add(U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(b, 1)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))), V.U.add_assoc(a, U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(_, Q.SP.enc(tlen, dl, il, al))) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      %Equal.sym(U32, U32.add(U32.add(a, U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al)))), Q.SP.enc(tlen, dl, il, al)), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), V.U.add_assoc(a, U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))) :
        {B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), _) == B.u32.pick(U32.is_lt(0, cpl), U32.add(a, U32.add(U32.add(U32.add(U32.add(U32.add(b, 1), B.B.var.len(cpl)), B.B.var.len(off)), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al))), U32.add(a, U32.add(U32.add(U32.add(b, 1), B.B.var.len(Q.SP.enc(tlen, dl, il, al))), Q.SP.enc(tlen, dl, il, al)))) : U32}
      {==}

law TP.wend_shift:
  for +ws: List<&2, Q.AW>
  for +a: U32
  for +b: U32
  {Q.SP.wend(ws, U32.add(a, b)) == U32.add(a, Q.SP.wend(ws, b)) : U32}

def TP.wend_shift(ws, a, b):
  match ws:
    case []:
      {==}
    case w <> r:
      %Equal.sym(U32, Q.SP.wnd(U32.add(a, b), w), U32.add(a, Q.SP.wnd(b, w)), TP.wnd_shift(a, b, w)) :
        {Q.SP.wend(r, _) == U32.add(a, Q.SP.wend(r, Q.SP.wnd(b, w))) : U32}
      TP.wend_shift(r, a, Q.SP.wnd(b, w))

law TP.wend_app:
  for +xs: List<&2, Q.AW>
  for +ys: List<&2, Q.AW>
  for +p: U32
  {Q.SP.wend(WR_.WR.wapp(xs, ys), p) == Q.SP.wend(ys, Q.SP.wend(xs, p)) : U32}

def TP.wend_app(xs, ys, p):
  match xs:
    case []:
      {==}
    case w <> r:
      TP.wend_app(r, ys, Q.SP.wnd(p, w))

# The tasks' output ends where their windows do.
law TP.par_pos:
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
  for +hG: {WR_.WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), w0, cend, tlen, wsz) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(k), V.U.N(nw))) == True{} : Bool}
  for +hesl: {WP_.WP.esok(sl) == True{} : Bool}
  for +hesr: {WP_.WP.esok(sr) == True{} : Bool}
  for +hr0: {WS_.WS.olen(sr) == 0 : U32}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(sl), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(sl)) : Nat}
  {WS_.WS.olen(WR_.WR.par(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr)) == Q.SP.wend(WR_.WR.pws(k, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, nw, ts, tt, sl, sr), WS_.WS.olen(sl)) : U32}

def TP.par_pos(k, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, ts, tt, sl, sr, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hesl, hesr, hr0, hbud, hO, hOl):
  match k:
    case 0n:
      WL_.WL.loop_pos(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, sl, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR_.WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hesl, hbud, hO, hOl)
    case 1n+q:
      %Equal.sym(U32, Q.SP.wend(WR_.WR.wapp(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl)), WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr))), WS_.WS.olen(sl)), Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl)), WS_.WS.olen(sl))), TP.wend_app(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl)), WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), WS_.WS.olen(sl))) : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == _ : U32}
      %TP.par_pos(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WR_.WR.nl(nw), WR_.WR.wm(nw, w0, wsz), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, P.Bool.and_l(WL_.WL.tile(V.U.N(WR_.WR.nl(nw)), w0, N.adv(V.U.N(WR_.WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR_.WR.nr(nw)), N.adv(V.U.N(WR_.WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR_.WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR_.WR.halfL(nw, P.Nat.pow2(q), hk), hesl, WR_.WR.esok_fresh(WR_.WR.tl(sl), WR_.WR.ocap(WR_.WR.nl(nw), wsz), WR_.WR.lidx(sl), WR_.WR.wm(WR_.WR.nl(nw), w0, wsz)), {==}, WL_.WL.bud1(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR_.WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR_.WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz)), V.U.N(Eo), (%WR_.WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud)), hO, hOl) : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), _) : U32}
      %V.U.add_zero_r(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl)))) : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), _) : U32}
      %Equal.sym(U32, Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), 0)), U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), 0)), TP.wend_shift(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), 0)) : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == _ : U32}
      %hr0 : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), Q.SP.wend(WR_.WR.pws(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)), _)) : U32}
      %TP.par_pos(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), cend, ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr), Eb, BIGs, BIGe, HB, Es, S, Eo, [], hG, P.Bool.and_r(WL_.WL.tile(V.U.N(WR_.WR.nl(nw)), w0, N.adv(V.U.N(WR_.WR.nl(nw)), w0, wsz), tlen, wsz), WL_.WL.tile(V.U.N(WR_.WR.nr(nw)), N.adv(V.U.N(WR_.WR.nl(nw)), w0, wsz), cend, tlen, wsz), WR_.WR.tile2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw, cend, q, hk, ht)), WR_.WR.halfR(nw, P.Nat.pow2(q), hk), hesr, WR_.WR.esok_fresh(WR_.WR.tl(sr), WR_.WR.ocap(WR_.WR.nr(nw), wsz), WR_.WR.lidx(sr), WR_.WR.wm(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz)), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(WR_.WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz))), V.U.N(Eo))) == True{} : Bool}; P.Nat.le_trans(WL_.WL.rb(V.U.N(WR_.WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz)), Nat.add(V.U.N(WS_.WS.olen(sl)), Nat.add(WL_.WL.rb(V.U.N(WR_.WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR_.WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz)))), V.U.N(Eo), WR_.WR.le_r3(V.U.N(WS_.WS.olen(sl)), WL_.WL.rb(V.U.N(WR_.WR.nl(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(V.U.N(WR_.WR.nr(nw)), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz))), (%WR_.WR.rb2(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, nw) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(sl)), _), V.U.N(Eo))) == True{} : Bool}; hbud))), {==}, (%Equal.sym(U32, WS_.WS.olen(sr), 0, hr0) : {0n == V.U.N(_) : Nat}; {==})) : {U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, WR_.WR.wm(nw, w0, wsz), WR_.WR.nr(nw), ts, tt, sr, WR_.WR.sp(WR_.WR.nr(nw), WR_.WR.wm(nw, w0, wsz), wsz, sr)))) == U32.add(WS_.WS.olen(WR_.WR.par(q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WR_.WR.nl(nw), ts, tt, sl, WR_.WR.sp(WR_.WR.nl(nw), w0, wsz, sl))), _) : U32}
      {==}

# Small facts
# -----------

law TP.nantisym:
  for +a: Nat
  for +b: Nat
  for +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(b, a)) == True{} : Bool}
  {a == b : Nat}

def TP.nantisym(a, b, h1, h2):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      P.Bool.false_true({0n == 1n+q : Nat}, h2)
    case 1n+p 0n:
      P.Bool.false_true({1n+p == 0n : Nat}, h1)
    case 1n+p 1n+q:
      %TP.nantisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

law TP.antisym:
  for +x: U32
  for +y: U32
  for +h1: {U32.is_le(x, y) == True{} : Bool}
  for +h2: {U32.is_le(y, x) == True{} : Bool}
  {x == y : U32}

def TP.antisym(x, y, h1, h2):
  V.U.eq_N(x, y, TP.nantisym(V.U.N(x), V.U.N(y), V.U.le_N(x, y, h1), V.U.le_N(y, x, h2)))

law TP.min_T.c:
  for +T: U32
  for +w: U32
  for +h: {U32.is_le(T, w) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_lt(T, w) == c : Bool}
  {U32.is_eq(Bool.pick(U32, c, T, w), T) == True{} : Bool}

def TP.min_T.c(T, w, h, c, ec):
  match c:
    case True{}:
      V.U.is_eq_refl(T)
    case False{}:
      %TP.antisym(T, w, h, V.U.not_lt(T, w, ec)) : {U32.is_eq(_, T) == True{} : Bool}
      V.U.is_eq_refl(T)

# A window that reaches past the target ends at it.
law TP.min_T:
  for +T: U32
  for +w: U32
  for +h: {U32.is_le(T, w) == True{} : Bool}
  {U32.is_eq(U32.min(T, w), T) == True{} : Bool}

def TP.min_T(T, w, h):
  %Equal.sym(U32, U32.min(T, w), Bool.pick(U32, U32.is_lt(T, w), T, w), K.WD.min(T, w)) : {U32.is_eq(_, T) == True{} : Bool}
  TP.min_T.c(T, w, h, U32.is_lt(T, w), {==})

# w + d does not wrap if c + d does not, for w <= c.
law TP.nowrap:
  for +w: U32
  for +c: U32
  for +d: U32
  for +h1: {U32.is_le(w, c) == True{} : Bool}
  for +h2: {U32.is_le(c, U32.add(c, d)) == True{} : Bool}
  {U32.is_le(w, U32.add(w, d)) == True{} : Bool}

def TP.nowrap(w, c, d, h1, h2):
  V.U.N_le(w, U32.add(w, d), (%Equal.sym(Nat, V.U.N(U32.add(w, d)), Nat.add(V.U.N(w), V.U.N(d)), V.U.add_N(w, d, U32.add(c, d), (%Equal.sym(Nat, V.U.N(U32.add(c, d)), Nat.add(V.U.N(c), V.U.N(d)), V.U.add_nowrap(c, d, h2)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w), V.U.N(d)), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(w), V.U.N(c), V.U.N(d), V.U.N(d), V.U.le_N(w, c, h1), C.CP.le_refl(V.U.N(d)))))) : {Cmp.is_le(Nat.cmp(V.U.N(w), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(w), V.U.N(d))))

# The windows of the target
# -------------------------
#
# wn counts the windows: one, and one more for each window end short of
# the target. TP.wnr counts the more.

def TP.wnr(k: Nat, +w: U32, +T: U32, +wsz: U32) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+q:
      Bool.pick(Nat, U32.is_lt(w, T), 1n+TP.wnr(q, U32.add(w, wsz), T, wsz), 0n)

# Fuel past where the count stops changes nothing.
law TP.wn_fuel:
  for +j: Nat
  for +m: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  for +h: {U32.is_le(T, N.adv(j, w, wsz)) == True{} : Bool}
  {N.wn.go(Nat.add(j, m), w, T, wsz) == N.wn.go(j, w, T, wsz) : U32}

def TP.wn_fuel(j, m, w, T, wsz, h):
  match j:
    case 0n:
      match m:
        case 0n:
          {==}
        case 1n+q:
          %Equal.sym(Bool, U32.is_lt(w, T), False{}, SC_.SC.nlt(T, w, h)) :
            {N.u32.pick(_, U32.add(N.wn.go(q, U32.add(w, wsz), T, wsz), 1), 1) == 1 : U32}
          {==}
    case 1n+i:
      %Equal.sym(U32, N.wn.go(Nat.add(i, m), U32.add(w, wsz), T, wsz), N.wn.go(i, U32.add(w, wsz), T, wsz), TP.wn_fuel(i, m, U32.add(w, wsz), T, wsz, h)) :
        {N.u32.pick(U32.is_lt(w, T), U32.add(_, 1), 1) == N.u32.pick(U32.is_lt(w, T), U32.add(N.wn.go(i, U32.add(w, wsz), T, wsz), 1), 1) : U32}
      {==}

law TP.wnr_le.z:
  for +p: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  for +z: Bool
  for +ih: {Cmp.is_le(Nat.cmp(TP.wnr(p, U32.add(w, wsz), T, wsz), p)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Bool.pick(Nat, z, 1n+TP.wnr(p, U32.add(w, wsz), T, wsz), 0n), 1n+p)) == True{} : Bool}

def TP.wnr_le.z(p, w, T, wsz, z, ih):
  match z:
    case True{}:
      ih
    case False{}:
      {==}

law TP.wnr_le:
  for +q: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  {Cmp.is_le(Nat.cmp(TP.wnr(q, w, T, wsz), q)) == True{} : Bool}

def TP.wnr_le(q, w, T, wsz):
  match q:
    case 0n:
      {==}
    case 1n+p:
      +ih = TP.wnr_le(p, U32.add(w, wsz), T, wsz)
      TP.wnr_le.z(p, w, T, wsz, U32.is_lt(w, T), ih)

law TP.wn_N.z:
  for +q: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  for +e: U32
  for +z: Bool
  for +he: {Cmp.is_le(Nat.cmp(1n+1n+q, V.U.N(e))) == True{} : Bool}
  for +ih: {V.U.N(N.wn.go(q, U32.add(w, wsz), T, wsz)) == 1n+TP.wnr(q, U32.add(w, wsz), T, wsz) : Nat}
  for +hle: {Cmp.is_le(Nat.cmp(TP.wnr(q, U32.add(w, wsz), T, wsz), q)) == True{} : Bool}
  {V.U.N(N.u32.pick(z, U32.add(N.wn.go(q, U32.add(w, wsz), T, wsz), 1), 1)) == 1n+Bool.pick(Nat, z, 1n+TP.wnr(q, U32.add(w, wsz), T, wsz), 0n) : Nat}

def TP.wn_N.z(q, w, T, wsz, e, z, he, ih, hle):
  match z:
    case True{}:
      %Equal.sym(Nat, V.U.N(U32.add(N.wn.go(q, U32.add(w, wsz), T, wsz), 1)), 1n+V.U.N(N.wn.go(q, U32.add(w, wsz), T, wsz)), V.U.succ_N(N.wn.go(q, U32.add(w, wsz), T, wsz), e, K.WD.lt_of_succ_le(V.U.N(N.wn.go(q, U32.add(w, wsz), T, wsz)), V.U.N(e), (%Equal.sym(Nat, V.U.N(N.wn.go(q, U32.add(w, wsz), T, wsz)), 1n+TP.wnr(q, U32.add(w, wsz), T, wsz), ih) : {Cmp.is_le(Nat.cmp(1n+_, V.U.N(e))) == True{} : Bool}; P.Nat.le_trans(1n+1n+TP.wnr(q, U32.add(w, wsz), T, wsz), 1n+1n+q, V.U.N(e), hle, he))))) : {_ == 1n+1n+TP.wnr(q, U32.add(w, wsz), T, wsz) : Nat}
      %Equal.sym(Nat, V.U.N(N.wn.go(q, U32.add(w, wsz), T, wsz)), 1n+TP.wnr(q, U32.add(w, wsz), T, wsz), ih) : {1n+_ == 1n+1n+TP.wnr(q, U32.add(w, wsz), T, wsz) : Nat}
      {==}
    case False{}:
      {==}

# The count, as a value.
law TP.wn_N:
  for +k: Nat
  for +w: U32
  for +T: U32
  for +wsz: U32
  for +e: U32
  for +he: {Cmp.is_le(Nat.cmp(1n+k, V.U.N(e))) == True{} : Bool}
  {V.U.N(N.wn.go(k, w, T, wsz)) == 1n+TP.wnr(k, w, T, wsz) : Nat}

def TP.wn_N(k, w, T, wsz, e, he):
  match k:
    case 0n:
      {==}
    case 1n+q:
      +ih = TP.wn_N(q, U32.add(w, wsz), T, wsz, e, P.Nat.le_succ_l(1n+q, V.U.N(e), he))
      TP.wn_N.z(q, w, T, wsz, e, U32.is_lt(w, T), he, ih, TP.wnr_le(q, U32.add(w, wsz), T, wsz))

# The windows from w0 tile the target, if w0 is in it.
law TP.wn_tile0:
  for +w0: U32
  for +T: U32
  for +wsz: U32
  for +hT: {U32.is_le(T, U32.add(T, wsz)) == True{} : Bool}
  for +hf: {U32.is_le(T, U32.add(w0, wsz)) == True{} : Bool}
  for +c0: Bool
  for +ec0: {U32.is_le(w0, T) == c0 : Bool}
  {Bool.or(Bool.not(c0), WL_.WL.tile(1n, w0, T, T, wsz)) == True{} : Bool}

def TP.wn_tile0(w0, T, wsz, hT, hf, c0, ec0):
  match c0:
    case False{}:
      {==}
    case True{}:
      +h1 = ec0
      SC_.SC.and_tt(U32.is_le(w0, T), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, T, T, wsz), True{})), h1, SC_.SC.and_tt(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, T, T, wsz), True{}), TP.nowrap(w0, T, wsz, h1, hT), SC_.SC.and_tt(WL_.WL.last(0n, w0, T, T, wsz), True{}, TP.min_T(T, U32.add(w0, wsz), hf), {==})))

law TP.wn_tile1.z:
  for +q: Nat
  for +w0: U32
  for +T: U32
  for +wsz: U32
  for +hT: {U32.is_le(T, U32.add(T, wsz)) == True{} : Bool}
  for +h1: {U32.is_le(w0, T) == True{} : Bool}
  for +ih: {Bool.or(Bool.not(U32.is_le(U32.add(w0, wsz), T)), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz)) == True{} : Bool}
  for +z: Bool
  for +ez: {U32.is_lt(U32.add(w0, wsz), T) == z : Bool}
  {WL_.WL.tile(1n+Bool.pick(Nat, z, 1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), 0n), w0, T, T, wsz) == True{} : Bool}

def TP.wn_tile1.z(q, w0, T, wsz, hT, h1, ih, z, ez):
  match z:
    case True{}:
      SC_.SC.and_tt(U32.is_le(w0, T), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), w0, T, T, wsz), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz))), h1, SC_.SC.and_tt(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), w0, T, T, wsz), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz)), TP.nowrap(w0, T, wsz, h1, hT), SC_.SC.and_tt(WL_.WL.last(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), w0, T, T, wsz), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz), V.U.lt_to_le(U32.add(w0, wsz), T, ez), (%V.U.lt_to_le(U32.add(w0, wsz), T, ez) : {Bool.or(Bool.not(_), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz)) == True{} : Bool}; ih))))
    case False{}:
      SC_.SC.and_tt(U32.is_le(w0, T), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, T, T, wsz), True{})), h1, SC_.SC.and_tt(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, T, T, wsz), True{}), TP.nowrap(w0, T, wsz, h1, hT), SC_.SC.and_tt(WL_.WL.last(0n, w0, T, T, wsz), True{}, TP.min_T(T, U32.add(w0, wsz), V.U.not_lt(U32.add(w0, wsz), T, ez)), {==})))

law TP.wn_tile1:
  for +q: Nat
  for +w0: U32
  for +T: U32
  for +wsz: U32
  for +hT: {U32.is_le(T, U32.add(T, wsz)) == True{} : Bool}
  for +ih: {Bool.or(Bool.not(U32.is_le(U32.add(w0, wsz), T)), WL_.WL.tile(1n+TP.wnr(q, U32.add(U32.add(w0, wsz), wsz), T, wsz), U32.add(w0, wsz), T, T, wsz)) == True{} : Bool}
  for +c0: Bool
  for +ec0: {U32.is_le(w0, T) == c0 : Bool}
  {Bool.or(Bool.not(c0), WL_.WL.tile(1n+TP.wnr(1n+q, U32.add(w0, wsz), T, wsz), w0, T, T, wsz)) == True{} : Bool}

def TP.wn_tile1(q, w0, T, wsz, hT, ih, c0, ec0):
  match c0:
    case False{}:
      {==}
    case True{}:
      TP.wn_tile1.z(q, w0, T, wsz, hT, ec0, ih, U32.is_lt(U32.add(w0, wsz), T), {==})

law TP.wn_tile:
  for +k: Nat
  for +w0: U32
  for +T: U32
  for +wsz: U32
  for +hT: {U32.is_le(T, U32.add(T, wsz)) == True{} : Bool}
  for +hf: {U32.is_le(T, N.adv(k, U32.add(w0, wsz), wsz)) == True{} : Bool}
  {Bool.or(Bool.not(U32.is_le(w0, T)), WL_.WL.tile(1n+TP.wnr(k, U32.add(w0, wsz), T, wsz), w0, T, T, wsz)) == True{} : Bool}

def TP.wn_tile(k, w0, T, wsz, hT, hf):
  match k:
    case 0n:
      TP.wn_tile0(w0, T, wsz, hT, hf, U32.is_le(w0, T), {==})
    case 1n+q:
      +ih = TP.wn_tile(q, U32.add(w0, wsz), T, wsz, hT, hf)
      TP.wn_tile1(q, w0, T, wsz, hT, ih, U32.is_le(w0, T), {==})

# Bounds
# ------
#
# The run's bounds, as U32 sums and shifts of the lengths: their values
# follow from bounds on the lengths and checks on the bounds' own values,
# which the checker computes (it never builds a large Nat).

law TP.le_refl_u:
  for +x: U32
  {U32.is_le(x, x) == True{} : Bool}

def TP.le_refl_u(x):
  V.U.N_le(x, x, C.CP.le_refl(V.U.N(x)))

law TP.shl_N:
  for +x: U32
  for +c: U32
  for +hx: {U32.is_le(x, c) == True{} : Bool}
  for +hc: {U32.is_lt(c, 2147483648) == True{} : Bool}
  {V.U.N(U32.shl(x)) == Nat.double(V.U.N(x)) : Nat}

def TP.shl_N(x, c, hx, hc):
  V.U.N_shl(x, V.U.bit_lt_pow(x, 31n, 31n, V.U.le_lt_trans(x, c, 2147483648, hx, hc), {==}, {==}))

law TP.shl_le:
  for +x: U32
  for +c: U32
  for +hx: {U32.is_le(x, c) == True{} : Bool}
  for +hc: {U32.is_lt(c, 2147483648) == True{} : Bool}
  {U32.is_le(U32.shl(x), U32.shl(c)) == True{} : Bool}

def TP.shl_le(x, c, hx, hc):
  V.U.N_le(U32.shl(x), U32.shl(c), (%Equal.sym(Nat, V.U.N(U32.shl(x)), Nat.double(V.U.N(x)), TP.shl_N(x, c, hx, hc)) : {Cmp.is_le(Nat.cmp(_, V.U.N(U32.shl(c)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.shl(c)), Nat.double(V.U.N(c)), TP.shl_N(c, c, TP.le_refl_u(c), hc)) : {Cmp.is_le(Nat.cmp(Nat.double(V.U.N(x)), _)) == True{} : Bool}; P.Nat.double_mono(V.U.N(x), V.U.N(c), V.U.le_N(x, c, hx)))))

law TP.add_N2:
  for +x: U32
  for +y: U32
  for +c: U32
  for +e: U32
  for +hx: {U32.is_le(x, c) == True{} : Bool}
  for +hy: {U32.is_le(y, e) == True{} : Bool}
  for +hce: {U32.is_le(c, U32.add(c, e)) == True{} : Bool}
  {V.U.N(U32.add(x, y)) == Nat.add(V.U.N(x), V.U.N(y)) : Nat}

def TP.add_N2(x, y, c, e, hx, hy, hce):
  V.U.add_N(x, y, U32.add(c, e), (%Equal.sym(Nat, V.U.N(U32.add(c, e)), Nat.add(V.U.N(c), V.U.N(e)), V.U.add_nowrap(c, e, hce)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(x), V.U.N(y)), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(x), V.U.N(c), V.U.N(y), V.U.N(e), V.U.le_N(x, c, hx), V.U.le_N(y, e, hy))))

law TP.add_le2:
  for +x: U32
  for +y: U32
  for +c: U32
  for +e: U32
  for +hx: {U32.is_le(x, c) == True{} : Bool}
  for +hy: {U32.is_le(y, e) == True{} : Bool}
  for +hce: {U32.is_le(c, U32.add(c, e)) == True{} : Bool}
  {U32.is_le(U32.add(x, y), U32.add(c, e)) == True{} : Bool}

def TP.add_le2(x, y, c, e, hx, hy, hce):
  V.U.N_le(U32.add(x, y), U32.add(c, e), (%Equal.sym(Nat, V.U.N(U32.add(x, y)), Nat.add(V.U.N(x), V.U.N(y)), TP.add_N2(x, y, c, e, hx, hy, hce)) : {Cmp.is_le(Nat.cmp(_, V.U.N(U32.add(c, e)))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(c, e)), Nat.add(V.U.N(c), V.U.N(e)), V.U.add_nowrap(c, e, hce)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(x), V.U.N(y)), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(x), V.U.N(c), V.U.N(y), V.U.N(e), V.U.le_N(x, c, hx), V.U.le_N(y, e, hy)))))

law TP.max_ge_l.c:
  for +a: U32
  for +b: U32
  for +z: Bool
  for +ez: {U32.is_lt(a, b) == z : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(a), V.U.N(Bool.pick(U32, z, b, a)))) == True{} : Bool}

def TP.max_ge_l.c(a, b, z, ez):
  match z:
    case True{}:
      V.U.le_N(a, b, V.U.lt_to_le(a, b, ez))
    case False{}:
      C.CP.le_refl(V.U.N(a))

law TP.max_ge_r.c:
  for +a: U32
  for +b: U32
  for +z: Bool
  for +ez: {U32.is_lt(a, b) == z : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(b), V.U.N(Bool.pick(U32, z, b, a)))) == True{} : Bool}

def TP.max_ge_r.c(a, b, z, ez):
  match z:
    case True{}:
      C.CP.le_refl(V.U.N(b))
    case False{}:
      V.U.le_N(b, a, V.U.not_lt(a, b, ez))

law TP.max_ge_l:
  for +a: U32
  for +b: U32
  {Cmp.is_le(Nat.cmp(V.U.N(a), V.U.N(N.u32.max(a, b)))) == True{} : Bool}

def TP.max_ge_l(a, b):
  TP.max_ge_l.c(a, b, U32.is_lt(a, b), {==})

law TP.max_ge_r:
  for +a: U32
  for +b: U32
  {Cmp.is_le(Nat.cmp(V.U.N(b), V.U.N(N.u32.max(a, b)))) == True{} : Bool}

def TP.max_ge_r(a, b):
  TP.max_ge_r.c(a, b, U32.is_lt(a, b), {==})

law TP.min_le_u.c:
  for +a: U32
  for +b: U32
  for +z: Bool
  for +ez: {U32.is_lt(a, b) == z : Bool}
  {U32.is_le(Bool.pick(U32, z, a, b), b) == True{} : Bool}

def TP.min_le_u.c(a, b, z, ez):
  match z:
    case True{}:
      V.U.lt_to_le(a, b, ez)
    case False{}:
      TP.le_refl_u(b)

law TP.min_le_u:
  for +a: U32
  for +b: U32
  {U32.is_le(U32.min(a, b), b) == True{} : Bool}

def TP.min_le_u(a, b):
  %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) : {U32.is_le(_, b) == True{} : Bool}
  TP.min_le_u.c(a, b, U32.is_lt(a, b), {==})

law TP.sh2_N:
  for +t: U32
  for +c: U32
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +k0: {U32.is_lt(c, 2147483648) == True{} : Bool}
  for +k1: {U32.is_lt(U32.shl(c), 2147483648) == True{} : Bool}
  {V.U.N(U32.shln(t, 2n)) == Nat.double(Nat.double(V.U.N(t))) : Nat}

def TP.sh2_N(t, c, ht, k0, k1):
  (%TP.shl_N(t, c, ht, k0) : {V.U.N(U32.shln(t, 2n)) == Nat.double(_) : Nat}; TP.shl_N(U32.shl(t), U32.shl(c), TP.shl_le(t, c, ht, k0), k1))

law TP.sh2_le:
  for +t: U32
  for +c: U32
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +k0: {U32.is_lt(c, 2147483648) == True{} : Bool}
  for +k1: {U32.is_lt(U32.shl(c), 2147483648) == True{} : Bool}
  {U32.is_le(U32.shln(t, 2n), U32.shln(c, 2n)) == True{} : Bool}

def TP.sh2_le(t, c, ht, k0, k1):
  TP.shl_le(U32.shl(t), U32.shl(c), TP.shl_le(t, c, ht, k0), k1)

law TP.sh3_N:
  for +t: U32
  for +c: U32
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +k0: {U32.is_lt(c, 2147483648) == True{} : Bool}
  for +k1: {U32.is_lt(U32.shl(c), 2147483648) == True{} : Bool}
  for +k2: {U32.is_lt(U32.shln(c, 2n), 2147483648) == True{} : Bool}
  {V.U.N(U32.shln(t, 3n)) == Nat.double(Nat.double(Nat.double(V.U.N(t)))) : Nat}

def TP.sh3_N(t, c, ht, k0, k1, k2):
  (%TP.sh2_N(t, c, ht, k0, k1) : {V.U.N(U32.shln(t, 3n)) == Nat.double(_) : Nat}; TP.shl_N(U32.shln(t, 2n), U32.shln(c, 2n), TP.sh2_le(t, c, ht, k0, k1), k2))

law TP.sh3_le:
  for +t: U32
  for +c: U32
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +k0: {U32.is_lt(c, 2147483648) == True{} : Bool}
  for +k1: {U32.is_lt(U32.shl(c), 2147483648) == True{} : Bool}
  for +k2: {U32.is_lt(U32.shln(c, 2n), 2147483648) == True{} : Bool}
  {U32.is_le(U32.shln(t, 3n), U32.shln(c, 3n)) == True{} : Bool}

def TP.sh3_le(t, c, ht, k0, k1, k2):
  TP.shl_le(U32.shln(t, 2n), U32.shln(c, 2n), TP.sh2_le(t, c, ht, k0, k1), k2)

# The output's bound: the target's bytes, and 16 KiB for the header and
# 47 bytes a window.
def TP.Eo(+t: U32) -> U32:
  U32.add(t, 16384)

def TP.BIGs(+t: U32) -> U32:
  U32.add(U32.add(U32.shln(t, 3n), U32.shln(t, 2n)), 12)

def TP.BIGe(+t: U32) -> U32:
  U32.add(U32.shln(t, 3n), 16)

def TP.Eb(+s: U32, +t: U32, +wsz: U32) -> U32:
  N.u32.max(U32.add(s, wsz), U32.add(t, 9))

# The checks on the bounds of the match buffer and the sections, at the
# window size c.
def TP.kc(+c: U32) -> Bool:
  Bool.and(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))))

law TP.kc.k0:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_lt(c, 2147483648) == True{} : Bool}

def TP.kc.k0(c, h):
  P.Bool.and_l(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h)

law TP.kc.k1:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_lt(U32.shl(c), 2147483648) == True{} : Bool}

def TP.kc.k1(c, h):
  P.Bool.and_l(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h))

law TP.kc.k2:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_lt(U32.shln(c, 2n), 2147483648) == True{} : Bool}

def TP.kc.k2(c, h):
  P.Bool.and_l(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h)))

law TP.kc.b1:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))) == True{} : Bool}

def TP.kc.b1(c, h):
  P.Bool.and_l(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))), P.Bool.and_r(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h))))

law TP.kc.b2:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)) == True{} : Bool}

def TP.kc.b2(c, h):
  P.Bool.and_l(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))), P.Bool.and_r(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))), P.Bool.and_r(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h)))))

law TP.kc.b3:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648) == True{} : Bool}

def TP.kc.b3(c, h):
  P.Bool.and_l(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)), P.Bool.and_r(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))), P.Bool.and_r(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))), P.Bool.and_r(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h))))))

law TP.kc.e1:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)) == True{} : Bool}

def TP.kc.e1(c, h):
  P.Bool.and_l(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648), P.Bool.and_r(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)), P.Bool.and_r(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))), P.Bool.and_r(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))), P.Bool.and_r(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h)))))))

law TP.kc.e2:
  for +c: U32
  for +h: {TP.kc(c) == True{} : Bool}
  {U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648) == True{} : Bool}

def TP.kc.e2(c, h):
  P.Bool.and_r(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648), P.Bool.and_r(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)), P.Bool.and_r(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))), P.Bool.and_r(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))), P.Bool.and_r(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))), P.Bool.and_r(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648)))))), P.Bool.and_r(U32.is_lt(c, 2147483648), Bool.and(U32.is_lt(U32.shl(c), 2147483648), Bool.and(U32.is_lt(U32.shln(c, 2n), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), U32.shln(c, 2n))), Bool.and(U32.is_le(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12)), Bool.and(U32.is_lt(U32.add(U32.add(U32.shln(c, 3n), U32.shln(c, 2n)), 12), 2147483648), Bool.and(U32.is_le(U32.shln(c, 3n), U32.add(U32.shln(c, 3n), 16)), U32.is_lt(U32.add(U32.shln(c, 3n), 16), 2147483648))))))), h)))))))

# The checks on the bounds at the largest target, c.
def TP.kt(+c: U32) -> Bool:
  Bool.and(U32.is_le(c, U32.add(c, 9)), Bool.and(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648))))

law TP.kt.n9:
  for +c: U32
  for +h: {TP.kt(c) == True{} : Bool}
  {U32.is_le(c, U32.add(c, 9)) == True{} : Bool}

def TP.kt.n9(c, h):
  P.Bool.and_l(U32.is_le(c, U32.add(c, 9)), Bool.and(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648))), h)

law TP.kt.c11:
  for +c: U32
  for +h: {TP.kt(c) == True{} : Bool}
  {U32.is_le(c, 2147483648) == True{} : Bool}

def TP.kt.c11(c, h):
  P.Bool.and_l(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648)), P.Bool.and_r(U32.is_le(c, U32.add(c, 9)), Bool.and(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648))), h))

law TP.kt.o1:
  for +c: U32
  for +h: {TP.kt(c) == True{} : Bool}
  {U32.is_le(c, U32.add(c, 16384)) == True{} : Bool}

def TP.kt.o1(c, h):
  P.Bool.and_l(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648), P.Bool.and_r(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648)), P.Bool.and_r(U32.is_le(c, U32.add(c, 9)), Bool.and(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648))), h)))

law TP.kt.o2:
  for +c: U32
  for +h: {TP.kt(c) == True{} : Bool}
  {U32.is_lt(U32.add(c, 16384), 2147483648) == True{} : Bool}

def TP.kt.o2(c, h):
  P.Bool.and_r(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648), P.Bool.and_r(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648)), P.Bool.and_r(U32.is_le(c, U32.add(c, 9)), Bool.and(U32.is_le(c, 2147483648), Bool.and(U32.is_le(c, U32.add(c, 16384)), U32.is_lt(U32.add(c, 16384), 2147483648))), h)))

law TP.Eo_lt:
  for +t: U32
  for +c: U32
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +hc: {TP.kt(c) == True{} : Bool}
  {U32.is_lt(TP.Eo(t), 2147483648) == True{} : Bool}

def TP.Eo_lt(t, c, ht, hc):
  V.U.le_lt_trans(TP.Eo(t), TP.Eo(c), 2147483648, TP.add_le2(t, 16384, c, 16384, ht, TP.le_refl_u(16384), TP.kt.o1(c, hc)), TP.kt.o2(c, hc))

# 4 * tri(1 + n) = 12 + 8n + 4n.
law TP.r4_eq:
  for +n: Nat
  {Nat.double(Nat.double(SG_.SG.tri(1n+n))) == Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n) : Nat}

def TP.r4_eq(n):
  %SG_.SG.tri_eq(n) : {Nat.double(Nat.double(Nat.add(3n, _))) == Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.double(n), n)), Nat.add(Nat.double(Nat.double(n)), Nat.double(n)), P.Nat.double_distr(Nat.double(n), n)) : {Nat.double(Nat.add(6n, _)) == Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.double(Nat.double(n)), Nat.double(n))), Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), P.Nat.double_distr(Nat.double(Nat.double(n)), Nat.double(n))) : {Nat.add(12n, _) == Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n), Nat.add(12n, Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n)))), P.Nat.add_comm(Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n))), 12n)) : {Nat.add(12n, Nat.add(Nat.double(Nat.double(Nat.double(n))), Nat.double(Nat.double(n)))) == _ : Nat}
  {==}

# The bounds every window needs hold for targets up to c bytes and
# sources up to cs bytes.
law TP.G_of:
  for +slen: U32
  for +tlen: U32
  for +wsz: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +rslen: U32
  for +c: U32
  for +cs: U32
  for +hs: {U32.is_le(slen, cs) == True{} : Bool}
  for +hsr: {U32.is_le(slen, rslen) == True{} : Bool}
  for +ht: {U32.is_le(tlen, c) == True{} : Bool}
  for +hc: {TP.kt(c) == True{} : Bool}
  for +hkw: {TP.kc(wsz) == True{} : Bool}
  for +hs1: {U32.is_le(cs, U32.add(cs, wsz)) == True{} : Bool}
  for +hw4: {U32.is_le(4, wsz) == True{} : Bool}
  {WR_.WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, TP.Eb(slen, tlen, wsz), TP.BIGs(wsz), TP.BIGe(wsz), U32.add(slen, wsz), rslen, rslen, TP.Eo(tlen)) == True{} : Bool}

def TP.G_of(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, rslen, c, cs, hs, hsr, ht, hc, hkw, hs1, hw4):
  SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(TP.BIGs(wsz)))), Bool.and(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)))))))))))), P.Nat.le_trans(Nat.add(V.U.N(slen), 4n), V.U.N(U32.add(slen, wsz)), V.U.N(TP.Eb(slen, tlen, wsz)), (%Equal.sym(Nat, V.U.N(U32.add(slen, wsz)), Nat.add(V.U.N(slen), V.U.N(wsz)), V.U.add_nowrap(slen, wsz, TP.nowrap(slen, cs, wsz, hs, hs1))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(slen), V.U.N(slen), 4n, V.U.N(wsz), C.CP.le_refl(V.U.N(slen)), V.U.le_N(4, wsz, hw4))), TP.max_ge_l(U32.add(slen, wsz), U32.add(tlen, 9))), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(TP.BIGs(wsz)))), Bool.and(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648))))))))))), P.Nat.le_trans(Nat.add(V.U.N(tlen), 9n), V.U.N(U32.add(tlen, 9)), V.U.N(TP.Eb(slen, tlen, wsz)), (%Equal.sym(Nat, V.U.N(U32.add(tlen, 9)), Nat.add(V.U.N(tlen), V.U.N(9)), TP.add_N2(tlen, 9, c, 9, ht, TP.le_refl_u(9), TP.kt.n9(c, hc))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(tlen), 9n), _)) == True{} : Bool}; C.CP.le_refl(Nat.add(V.U.N(tlen), 9n))), TP.max_ge_r(U32.add(slen, wsz), U32.add(tlen, 9))), SC_.SC.and_tt(U32.is_le(slen, U32.add(slen, wsz)), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(TP.BIGs(wsz)))), Bool.and(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)))))))))), TP.nowrap(slen, cs, wsz, hs, hs1), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(TP.Eb(slen, tlen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(TP.BIGs(wsz)))), Bool.and(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648))))))))), TP.max_ge_l(U32.add(slen, wsz), U32.add(tlen, 9)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), V.U.N(TP.BIGs(wsz)))), Bool.and(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)))))))), (%Equal.sym(Nat, V.U.N(TP.BIGs(wsz)), Nat.add(V.U.N(U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n))), V.U.N(12)), TP.add_N2(U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n)), 12, U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n)), 12, TP.add_le2(U32.shln(wsz, 3n), U32.shln(wsz, 2n), U32.shln(wsz, 3n), U32.shln(wsz, 2n), TP.sh3_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw)), TP.sh2_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw)), TP.kc.b1(wsz, hkw)), TP.le_refl_u(12), TP.kc.b2(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), _)) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n))), Nat.add(V.U.N(U32.shln(wsz, 3n)), V.U.N(U32.shln(wsz, 2n))), TP.add_N2(U32.shln(wsz, 3n), U32.shln(wsz, 2n), U32.shln(wsz, 3n), U32.shln(wsz, 2n), TP.sh3_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw)), TP.sh2_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw)), TP.kc.b1(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), Nat.add(_, 12n))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.shln(wsz, 3n)), Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), TP.sh3_N(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), Nat.add(Nat.add(_, V.U.N(U32.shln(wsz, 2n))), 12n))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.shln(wsz, 2n)), Nat.double(Nat.double(V.U.N(wsz))), TP.sh2_N(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), _), 12n))) == True{} : Bool}; (%Equal.sym(Nat, Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(wsz)))), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), Nat.double(Nat.double(V.U.N(wsz)))), 12n), TP.r4_eq(V.U.N(wsz))) : {Cmp.is_le(Nat.cmp(_, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), Nat.double(Nat.double(V.U.N(wsz)))), 12n))) == True{} : Bool}; C.CP.le_refl(Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), Nat.double(Nat.double(V.U.N(wsz)))), 12n))))))), SC_.SC.and_tt(U32.is_lt(TP.BIGs(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648))))))), V.U.le_lt_trans(TP.BIGs(wsz), TP.BIGs(wsz), 2147483648, TP.add_le2(U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n)), 12, U32.add(U32.shln(wsz, 3n), U32.shln(wsz, 2n)), 12, TP.add_le2(U32.shln(wsz, 3n), U32.shln(wsz, 2n), U32.shln(wsz, 3n), U32.shln(wsz, 2n), TP.sh3_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw)), TP.sh2_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw)), TP.kc.b1(wsz, hkw)), TP.le_refl_u(12), TP.kc.b2(wsz, hkw)), TP.kc.b3(wsz, hkw)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), V.U.N(TP.BIGe(wsz)))), Bool.and(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)))))), (%Equal.sym(Nat, V.U.N(TP.BIGe(wsz)), Nat.add(V.U.N(U32.shln(wsz, 3n)), V.U.N(16)), TP.add_N2(U32.shln(wsz, 3n), 16, U32.shln(wsz, 3n), 16, TP.sh3_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw)), TP.le_refl_u(16), TP.kc.e1(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), _)) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(U32.shln(wsz, 3n)), Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), TP.sh3_N(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n), Nat.add(_, 16n))) == True{} : Bool}; C.CP.le_refl(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(wsz)))), 16n)))), SC_.SC.and_tt(U32.is_lt(TP.BIGe(wsz), 2147483648), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648))))), V.U.le_lt_trans(TP.BIGe(wsz), TP.BIGe(wsz), 2147483648, TP.add_le2(U32.shln(wsz, 3n), 16, U32.shln(wsz, 3n), 16, TP.sh3_le(wsz, wsz, TP.le_refl_u(wsz), TP.kc.k0(wsz, hkw), TP.kc.k1(wsz, hkw), TP.kc.k2(wsz, hkw)), TP.le_refl_u(16), TP.kc.e1(wsz, hkw)), TP.kc.e2(wsz, hkw)), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(V.U.N(U32.add(slen, wsz)), V.U.N(U32.add(slen, wsz)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)))), C.CP.le_refl(V.U.N(U32.add(slen, wsz))), SC_.SC.and_tt(Cmp.is_le(Nat.cmp(V.U.N(slen), V.U.N(rslen))), Bool.and(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648))), V.U.le_N(slen, rslen, hsr), SC_.SC.and_tt(U32.is_le(slen, rslen), Bool.and(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648)), hsr, SC_.SC.and_tt(U32.is_le(tlen, 2147483648), U32.is_lt(TP.Eo(tlen), 2147483648), WR_.WR.le_trans_u(tlen, c, 2147483648, ht, TP.kt.c11(c, hc)), TP.Eo_lt(tlen, c, ht, hc)))))))))))))

# The output's budget
# -------------------
#
# A window takes 47 bytes besides its own at most, so a run of windows
# over a target takes 47 a window and the target's bytes.

def TP.m47(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(47n, TP.m47(p))

law TP.add_swap_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def TP.add_swap_r(a, b, c):
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), P.Nat.add_assoc(a, b, c)) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %P.Nat.add_comm(c, b) : {Nat.add(a, _) == Nat.add(Nat.add(a, c), b) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), P.Nat.add_assoc(a, c, b))

# A window's cost moves the measure from its start to its end.
law TP.K1:
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
  for +hw: {U32.is_le(w0, WL_.WL.w1(tlen, w0, wsz)) == True{} : Bool}
  {Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), V.U.N(w0)) == Nat.add(47n, V.U.N(WL_.WL.w1(tlen, w0, wsz))) : Nat}

def TP.K1(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, hw):
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(WL_.WL.w1(tlen, w0, wsz), w0)), V.U.N(w0)), V.U.N(WL_.WL.w1(tlen, w0, wsz)), V.U.sub_nat(WL_.WL.w1(tlen, w0, wsz), w0, hw)) : {Nat.add(47n, _) == Nat.add(47n, V.U.N(WL_.WL.w1(tlen, w0, wsz))) : Nat}
  {==}

law TP.rb_le:
  for +q: Nat
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
  for +ht: {WL_.WL.tile(1n+q, w0, cend, tlen, wsz) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(WL_.WL.rb(1n+q, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), V.U.N(w0)), Nat.add(TP.m47(1n+q), V.U.N(cend)))) == True{} : Bool}

def TP.rb_le(q, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, cend, ht):
  match q:
    case 0n:
      %Equal.sym(Nat, Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), 0n), WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), P.Nat.add_zero_r(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0))) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(w0)), Nat.add(TP.m47(1n), V.U.N(cend)))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), V.U.N(w0)), Nat.add(47n, V.U.N(WL_.WL.w1(tlen, w0, wsz))), TP.K1(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WL_.WL.w01(tlen, w0, wsz, P.Bool.and_l(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz))), ht), P.Bool.and_l(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz))), ht))))) : {Cmp.is_le(Nat.cmp(_, Nat.add(TP.m47(1n), V.U.N(cend)))) == True{} : Bool}
      %Equal.sym(U32, WL_.WL.w1(tlen, w0, wsz), cend, V.U.is_eq(WL_.WL.w1(tlen, w0, wsz), cend, P.Bool.and_l(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(0n, w0, cend, tlen, wsz), WL_.WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz))), ht))))) : {Cmp.is_le(Nat.cmp(Nat.add(47n, V.U.N(_)), Nat.add(TP.m47(1n), V.U.N(cend)))) == True{} : Bool}
      C.CP.le_refl(Nat.add(47n, V.U.N(cend)))
    case 1n+p:
      +ih = TP.rb_le(p, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, U32.add(w0, wsz), cend, P.Bool.and_r(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz))), ht))))
      %Equal.sym(Nat, Nat.add(Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), V.U.N(w0)), Nat.add(Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), V.U.N(w0)), WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), TP.add_swap_r(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(w0))) : {Cmp.is_le(Nat.cmp(_, Nat.add(TP.m47(1n+1n+p), V.U.N(cend)))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(WL_.WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), V.U.N(w0)), Nat.add(47n, V.U.N(WL_.WL.w1(tlen, w0, wsz))), TP.K1(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, WL_.WL.w01(tlen, w0, wsz, P.Bool.and_l(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz))), ht), P.Bool.and_l(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz))), ht))))) : {Cmp.is_le(Nat.cmp(Nat.add(_, WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(TP.m47(1n+1n+p), V.U.N(cend)))) == True{} : Bool}
      %Equal.sym(U32, WL_.WL.w1(tlen, w0, wsz), U32.add(w0, wsz), WL_.WL.wnext(tlen, w0, wsz, P.Bool.and_l(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL_.WL.last(1n+p, w0, cend, tlen, wsz), WL_.WL.tile(1n+p, U32.add(w0, wsz), cend, tlen, wsz))), ht))))) : {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(47n, V.U.N(_)), WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz))), Nat.add(TP.m47(1n+1n+p), V.U.N(cend)))) == True{} : Bool}
      %P.Nat.add_comm(WL_.WL.rb(1n+p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(U32.add(w0, wsz))) : {Cmp.is_le(Nat.cmp(Nat.add(47n, _), Nat.add(TP.m47(1n+1n+p), V.U.N(cend)))) == True{} : Bool}
      ih

law TP.m47_mono:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(TP.m47(a), TP.m47(b))) == True{} : Bool}

def TP.m47_mono(a, b, h):
  match a b:
    case 0n b:
      SE_.SE.le0(TP.m47(b))
    case 1n+p 0n:
      P.Bool.false_true({Cmp.is_le(Nat.cmp(TP.m47(1n+p), TP.m47(0n))) == True{} : Bool}, h)
    case 1n+p 1n+r:
      TP.m47_mono(p, r, h)

# The index before the tasks
# --------------------------

# The state with the source indexed as far as the first window needs.
def TP.idx(+E: N.EK, +w1: U32, +ts: A.Tr, +s: WS_.EST) -> WS_.EST:
  WS_.EST{WS_.WS.uptot(E, w1, WR_.WR.lidx(s), WR_.WR.tl(s), ts), WR_.WR.tb(s), WR_.WR.tv(s), WS_.WS.tio(s), WS_.WS.ee(s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.uptol(E, w1, WR_.WR.lidx(s)), WR_.WR.cont(s)}

law TP.idx_code:
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {N.win.index(E, w1, WS_.WS.es(ts, tt, s)) == WS_.WS.es(ts, tt, TP.idx(E, w1, ts, s)) : N.ES}

def TP.idx_code(E, w1, ts, tt, s):
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      %Equal.sym(Array<U32>, N.tab.need(U32.to_nat(U32.sub(32, lsh)), A.A.from(tl)), A.A.from(WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl)), WS_.WS.need_code(U32.to_nat(U32.sub(32, lsh)), tl)) :
        {N.win.index.fin(A.A.from(tt), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), cont, N.ix.blocks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, (A.A.from(ts), _))) == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(WS_.WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), cont} : N.ES}
      %Equal.sym(Array<U32> & Array<U32>, N.ix.blocks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, (A.A.from(ts), A.A.from(WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl)))), (A.A.from(ts), A.A.from(WS_.WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts))), WS_.WS.ixblks_code(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)) :
        {N.win.index.fin(A.A.from(tt), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), cont, _) == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(WS_.WS.ixblks(U32.to_nat(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0)), lidx, slen, blk, U32.to_nat(lsh), lmask, WS_.WS.need(U32.to_nat(U32.sub(32, lsh)), tl), ts)), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), A.A.from(to), olen, U32.add(lidx, U32.mul(N.u32.pick(U32.is_lt(lidx, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.div(U32.sub(U32.add(U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), lidx), blk), 1), blk), 0), blk)), cont} : N.ES}
      {==}

law TP.idx_esok:
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +s: WS_.EST
  for +h: {WP_.WP.esok(s) == True{} : Bool}
  {WP_.WP.esok(TP.idx(E, w1, ts, s)) == True{} : Bool}

def TP.idx_esok(E, w1, ts, s, h):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      h

def TP.pre(k: Nat, +E: N.EK, +w1: U32, +ts: A.Tr, +s: WS_.EST) -> WS_.EST:
  match k:
    case 0n:
      s
    case 1n+q:
      TP.idx(E, w1, ts, s)

law TP.pre_code:
  for +k: Nat
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {N.enc.pre(k, E, w1, WS_.WS.es(ts, tt, s)) == WS_.WS.es(ts, tt, TP.pre(k, E, w1, ts, s)) : N.ES}

def TP.pre_code(k, E, w1, ts, tt, s):
  match k:
    case 0n:
      {==}
    case 1n+q:
      TP.idx_code(E, w1, ts, tt, s)

law TP.pre_esok:
  for +k: Nat
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +s: WS_.EST
  for +h: {WP_.WP.esok(s) == True{} : Bool}
  {WP_.WP.esok(TP.pre(k, E, w1, ts, s)) == True{} : Bool}

def TP.pre_esok(k, E, w1, ts, s, h):
  match k:
    case 0n:
      h
    case 1n+q:
      TP.idx_esok(E, w1, ts, s, h)

law TP.pre_olen:
  for +k: Nat
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +s: WS_.EST
  {WS_.WS.olen(TP.pre(k, E, w1, ts, s)) == WS_.WS.olen(s) : U32}

def TP.pre_olen(k, E, w1, ts, s):
  match k:
    case 0n:
      {==}
    case 1n+q:
      {==}

law TP.pre_to:
  for +k: Nat
  for +E: N.EK
  for +w1: U32
  for +ts: A.Tr
  for +s: WS_.EST
  {WS_.WS.to(TP.pre(k, E, w1, ts, s)) == WS_.WS.to(s) : A.Tr}

def TP.pre_to(k, E, w1, ts, s):
  match k:
    case 0n:
      {==}
    case 1n+q:
      {==}

# The tasks of the run
# --------------------

# 2^depth windows at least: depth is 3 from 8 windows, else 0.
law TP.hk_top.c:
  for +nw: U32
  for +h1: {Cmp.is_le(Nat.cmp(1n, V.U.N(nw))) == True{} : Bool}
  for +c: Bool
  for +ec: {U32.is_le(8, nw) == c : Bool}
  {Cmp.is_le(Nat.cmp(P.Nat.pow2(Bool.pick(Nat, c, 3n, 0n)), V.U.N(nw))) == True{} : Bool}

def TP.hk_top.c(nw, h1, c, ec):
  match c:
    case True{}:
      V.U.le_N(8, nw, ec)
    case False{}:
      h1

law TP.hk_top:
  for +nw: U32
  for +h1: {Cmp.is_le(Nat.cmp(1n, V.U.N(nw))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(P.Nat.pow2(N.enc.depth(nw)), V.U.N(nw))) == True{} : Bool}

def TP.hk_top(nw, h1):
  TP.hk_top.c(nw, h1, U32.is_le(8, nw), {==})

# The tasks the run starts with.
def TP.top(+E: N.EK, +nw: U32, +ts: A.Tr, +tt: A.Tr, +s: WS_.EST) -> WS_.EST:
  WR_.WR.par(N.enc.depth(nw), E, 0, nw, ts, tt, s, WR_.WR.sp(nw, 0, WL_.WL.wz(E), s))

def TP.tws(+E: N.EK, +nw: U32, +ts: A.Tr, +tt: A.Tr, +s: WS_.EST) -> List<&2, Q.AW>:
  WR_.WR.pws(N.enc.depth(nw), E, 0, nw, ts, tt, s, WR_.WR.sp(nw, 0, WL_.WL.wz(E), s))

law TP.top_code.c:
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
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR_.WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), 0, cend, tlen, wsz) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, 0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  for +c: Bool
  for +hk: {Cmp.is_le(Nat.cmp(P.Nat.pow2(Bool.pick(Nat, c, 3n, 0n)), V.U.N(nw))) == True{} : Bool}
  {N.enc.par(Bool.pick(Nat, c, 3n, 0n), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, 0, nw, N.enc.top.sp(Bool.pick(Nat, c, 3n, 0n), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, nw, WS_.WS.es(ts, tt, s))) == WS_.WS.es(ts, tt, WR_.WR.par(Bool.pick(Nat, c, 3n, 0n), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, 0, nw, ts, tt, s, WR_.WR.sp(nw, 0, wsz, s))) : N.ES}

def TP.top_code.c(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, nw, cend, ts, tt, s, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hes, hbud, hO, hOl, c, hk):
  match c:
    case True{}:
      %Equal.sym(N.ES & N.ES, N.es.split(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, 0, nw, WS_.WS.es(ts, tt, s)), (WS_.WS.es(ts, tt, s), WS_.WS.es(ts, tt, WR_.WR.sp(nw, 0, wsz, s))), WR_.WR.split_code(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, 0, nw, ts, tt, s)) : {N.enc.par(3n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, 0, nw, _) == WS_.WS.es(ts, tt, WR_.WR.par(3n, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, 0, nw, ts, tt, s, WR_.WR.sp(nw, 0, wsz, s))) : N.ES}
      WR_.WR.par_code(3n, sbits, wb, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, 0, nw, cend, ts, tt, s, WR_.WR.sp(nw, 0, wsz, s), Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hk, hes, WR_.WR.esok_fresh(WR_.WR.tl(s), WR_.WR.ocap(nw, wsz), WR_.WR.lidx(s), WR_.WR.wm(nw, 0, wsz)), {==}, hbud, hO, hOl)
    case False{}:
      WL_.WL.loop_code(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, 0, ts, tt, s, Eb, BIGs, tlen, Es, BIGe, HB, tlen, S, Eo, OUT, WR_.WR.whs_of(V.U.N(nw), slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, 0, cend, Eb, BIGs, BIGe, HB, Es, S, Eo, hG, ht), hes, hbud, hO, hOl)

law TP.top_code:
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
  for +nw: U32
  for +cend: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +Eb: U32
  for +BIGs: U32
  for +BIGe: U32
  for +HB: U32
  for +Es: U32
  for +S: U32
  for +Eo: U32
  for +OUT: List<&2, U32>
  for +hG: {WR_.WR.G(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, Eb, BIGs, BIGe, HB, Es, S, Eo) == True{} : Bool}
  for +ht: {WL_.WL.tile(V.U.N(nw), 0, cend, tlen, wsz) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL_.WL.rb(V.U.N(nw), N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, 0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  for +hk1: {Cmp.is_le(Nat.cmp(1n, V.U.N(nw))) == True{} : Bool}
  {N.enc.par.top(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, sbits, wb, nw, WS_.WS.es(ts, tt, s)) == WS_.WS.es(ts, tt, TP.top(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, nw, ts, tt, s)) : N.ES}

def TP.top_code(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, nw, cend, ts, tt, s, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hes, hbud, hO, hOl, hk1):
  TP.top_code.c(slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, sbits, wb, nw, cend, ts, tt, s, Eb, BIGs, BIGe, HB, Es, S, Eo, OUT, hG, ht, hes, hbud, hO, hOl, U32.is_le(8, nw), TP.hk_top(nw, hk1))

# The header and the first state
# -------------------------------

def TP.to0(+tlen: U32) -> A.Tr:
  S.S.puts(214 <> 195 <> 196 <> 0 <> 0 <> [], A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0)

law TP.wrb:
  for +v: U32
  for +t: A.Tr
  for +p: U32
  {N.wr.byte(v, (A.A.from(t), p)) == (A.A.from(Y.BP.put(t, p, v)), U32.add(p, 1)) : Array<U32> & U32}

def TP.wrb(v, t, p):
  %Equal.sym(Array<U32>, B.B.put(A.A.from(t), p, v), A.A.from(Y.BP.put(t, p, v)), Y.BP.put_from(t, p, v)) : {(_, U32.add(p, 1)) == (A.A.from(Y.BP.put(t, p, v)), U32.add(p, 1)) : Array<U32> & U32}
  {==}

# The header's five bytes.
law TP.hdr_code:
  for +tlen: U32
  {N.wr.byte(0, N.wr.byte(0, N.wr.byte(196, N.wr.byte(195, N.wr.byte(214, (B.B.zeros(N.u32.max(U32.shrn(tlen, 3n), 4096)), 0)))))) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}

def TP.hdr_code(tlen):
  %Equal.sym(Array<U32>, Array.new(U32, B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), A.A.from(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0)), A.A.new_from(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0)) : {N.wr.byte(0, N.wr.byte(0, N.wr.byte(196, N.wr.byte(195, N.wr.byte(214, (_, 0)))))) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, N.wr.byte(214, (A.A.from(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0)), 0)), (A.A.from(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214)), U32.add(0, 1)), TP.wrb(214, A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0)) : {N.wr.byte(0, N.wr.byte(0, N.wr.byte(196, N.wr.byte(195, _)))) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, N.wr.byte(195, (A.A.from(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214)), 1)), (A.A.from(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195)), U32.add(1, 1)), TP.wrb(195, Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1)) : {N.wr.byte(0, N.wr.byte(0, N.wr.byte(196, _))) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, N.wr.byte(196, (A.A.from(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195)), 2)), (A.A.from(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196)), U32.add(2, 1)), TP.wrb(196, Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2)) : {N.wr.byte(0, N.wr.byte(0, _)) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, N.wr.byte(0, (A.A.from(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196)), 3)), (A.A.from(Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196), 3, 0)), U32.add(3, 1)), TP.wrb(0, Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196), 3)) : {N.wr.byte(0, _) == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  %Equal.sym(Array<U32> & U32, N.wr.byte(0, (A.A.from(Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196), 3, 0)), 4)), (A.A.from(Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196), 3, 0), 4, 0)), U32.add(4, 1)), TP.wrb(0, Y.BP.put(Y.BP.put(Y.BP.put(Y.BP.put(A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, 214), 1, 195), 2, 196), 3, 0), 4)) : {_ == (A.A.from(TP.to0(tlen)), 5) : Array<U32> & U32}
  {==}

# The first state.
def TP.s0(+to: A.Tr) -> WS_.EST:
  WS_.EST{A.TL{0}, A.TL{0}, A.TL{0}, A.T.new(17n, 0), EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, to, 5, 0, 0}

law TP.s0_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +to: A.Tr
  {N.ES{A.A.from(ts), A.A.from(tt), [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], Array.new(U32, 17n, 0), N.Em{B.B.zeros(65536), B.B.zeros(65536), B.B.zeros(65536), Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} == WS_.WS.es(ts, tt, TP.s0(to)) : N.ES}

def TP.s0_code(ts, tt, to):
  %Equal.sym(Array<U32>, Array.new(U32, 17n, 0), A.A.from(A.T.new(17n, 0)), A.A.new_from(17n, 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], _, N.Em{Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, B.B.depth(B.B.words(65536)), 0), Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} : N.ES}
  %Equal.sym(Array<U32>, Array.new(U32, B.B.depth(B.B.words(65536)), 0), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.new_from(B.B.depth(B.B.words(65536)), 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], A.A.from(A.T.new(17n, 0)), N.Em{_, _, _, Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} : N.ES}
  %Equal.sym(Array<U32>, Array.new(U32, 10n, 0), A.A.from(A.T.new(10n, 0)), A.A.new_from(10n, 0)) :
    {N.ES{A.A.from(ts), A.A.from(tt), [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), _, 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} == N.ES{A.A.from(ts), A.A.from(tt), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.TL{0}), A.A.from(A.T.new(17n, 0)), N.Em{A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(B.B.depth(B.B.words(65536)), 0)), A.A.from(A.T.new(10n, 0)), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(to), 5, 0, 0} : N.ES}
  {==}

law TP.esok_s0:
  for +to: A.Tr
  for +h: {WP_.WP.ook(to) == True{} : Bool}
  {WP_.WP.esok(TP.s0(to)) == True{} : Bool}

def TP.esok_s0(to, h):
  %Equal.sym(Bool, WP_.WP.ook(to), True{}, h) :
    {Bool.and(WS_.WS.eok(EM_.ET{A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(B.B.depth(B.B.words(65536)), 0), A.T.new(10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}), Bool.and(WP_.WP.bok(A.T.new(17n, 0)), _)) == True{} : Bool}
  {==}

law TP.ook_to0:
  for +tlen: U32
  {WP_.WP.ook(TP.to0(tlen)) == True{} : Bool}

def TP.ook_to0(tlen):
  %Equal.sym(Nat, SC_.SC.dep(TP.to0(tlen)), B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), SC_.SC.dep_pf(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), TP.to0(tlen), S.S.pf_puts(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 214 <> 195 <> 196 <> 0 <> 0 <> [], A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, A.T.pf_new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0)))) : {Bool.and(A.T.pf(_, TP.to0(tlen)), Cmp.is_lt(Nat.cmp(_, 32n))) == True{} : Bool}
  SC_.SC.and_tt(A.T.pf(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), TP.to0(tlen)), Cmp.is_lt(Nat.cmp(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 32n)), S.S.pf_puts(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 214 <> 195 <> 196 <> 0 <> 0 <> [], A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, A.T.pf_new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0)), (%Equal.sym(Cmp, Nat.cmp(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 32n), LT{}, Y.BD.lt(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096)))) : {Cmp.is_lt(_) == True{} : Bool}; {==}))

law TP.shr_le:
  for +x: U32
  {U32.is_le(U32.shr(x), x) == True{} : Bool}

def TP.shr_le(x):
  V.U.N_le(U32.shr(x), x, (%Equal.sym(Nat, V.U.N(U32.shr(x)), P.Nat.half(V.U.N(x)), V.U.N_shr(x)) : {Cmp.is_le(Nat.cmp(_, V.U.N(x))) == True{} : Bool}; P.Nat.le_trans(P.Nat.half(V.U.N(x)), Nat.double(P.Nat.half(V.U.N(x))), V.U.N(x), EM_.GR.le_dbl(P.Nat.half(V.U.N(x))), WR_.WR.hh(V.U.N(x)))))

law TP.shrn3_le:
  for +x: U32
  {U32.is_le(U32.shrn(x, 3n), x) == True{} : Bool}

def TP.shrn3_le(x):
  WR_.WR.le_trans_u(U32.shr(U32.shr(U32.shr(x))), U32.shr(U32.shr(x)), x, TP.shr_le(U32.shr(U32.shr(x))), WR_.WR.le_trans_u(U32.shr(U32.shr(x)), U32.shr(x), x, TP.shr_le(U32.shr(x)), TP.shr_le(x)))

law TP.max_lt.c:
  for +a: U32
  for +b: U32
  for +c: U32
  for +ha: {U32.is_lt(a, c) == True{} : Bool}
  for +hb: {U32.is_lt(b, c) == True{} : Bool}
  for +z: Bool
  {U32.is_lt(Bool.pick(U32, z, b, a), c) == True{} : Bool}

def TP.max_lt.c(a, b, c, ha, hb, z):
  match z:
    case True{}:
      hb
    case False{}:
      ha

# A tree of depth(words(n)) holds n bytes.
law TP.room:
  for +n: U32
  for +hn: {U32.is_lt(n, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(n), Nat.double(Nat.double(P.Nat.pow2(B.B.depth(B.B.words(n))))))) == True{} : Bool}

def TP.room(n, hn):
  P.Nat.le_trans(V.U.N(n), Nat.double(Nat.double(V.U.N(B.B.words(n)))), Nat.double(Nat.double(P.Nat.pow2(B.B.depth(B.B.words(n))))), EM_.GR.lw(n, hn), EM_.GR.dd2(V.U.N(B.B.words(n)), P.Nat.pow2(B.B.depth(B.B.words(n))), (%V.U.N_pow(B.B.depth(B.B.words(n)), Y.BD.lt(B.B.words(n))) : {Cmp.is_le(Nat.cmp(V.U.N(B.B.words(n)), _)) == True{} : Bool}; V.U.le_N(B.B.words(n), U32.shln(1, B.B.depth(B.B.words(n))), Y.BD.le(B.B.words(n), EM_.GR.wb(n))))))

# The first state's output holds the header.
law TP.has_hdr:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {S.S.has(214 <> 195 <> 196 <> 0 <> 0 <> [], TP.to0(tlen), 0) == True{} : Bool}

def TP.has_hdr(tlen, h):
  S.S.has_puts(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 214 <> 195 <> 196 <> 0 <> 0 <> [], A.T.new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), 0, N.u32.max(U32.shrn(tlen, 3n), 4096), A.T.pf_new(B.B.depth(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), 0), Y.BD.lt(B.B.words(N.u32.max(U32.shrn(tlen, 3n), 4096))), TP.room(N.u32.max(U32.shrn(tlen, 3n), 4096), TP.max_lt.c(U32.shrn(tlen, 3n), 4096, 2147483648, V.U.le_lt_trans(U32.shrn(tlen, 3n), tlen, 2147483648, TP.shrn3_le(tlen), V.U.lt_trans(tlen, 2146435072, 2147483648, h, {==})), {==}, U32.is_lt(U32.shrn(tlen, 3n), 4096))), P.Nat.le_trans(5n, V.U.N(4096), V.U.N(N.u32.max(U32.shrn(tlen, 3n), 4096)), {==}, TP.max_ge_r(U32.shrn(tlen, 3n), 4096)))

# The windows at the encoder's size
# ---------------------------------
#
# Windows of 8 MiB over a target of 2^31 bytes at most: at most 255 more
# than the first.

law TP.nw_N512:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)) == 1n+TP.wnr(255n, 8388608, tlen, 8388608) : Nat}

def TP.nw_N512(tlen, h):
  %Equal.sym(U32, N.wn.go(Nat.add(255n, 257n), 8388608, tlen, 8388608), N.wn.go(255n, 8388608, tlen, 8388608), TP.wn_fuel(255n, 257n, 8388608, tlen, 8388608, WR_.WR.le_trans_u(tlen, 2146435072, N.adv(255n, 8388608, 8388608), V.U.lt_to_le(tlen, 2146435072, h), {==}))) : {V.U.N(_) == 1n+TP.wnr(255n, 8388608, tlen, 8388608) : Nat}
  TP.wn_N(255n, 8388608, tlen, 8388608, 256, {==})

law TP.nw_N:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {V.U.N(N.wn(tlen, 8388608)) == 1n+TP.wnr(255n, 8388608, tlen, 8388608) : Nat}

def TP.nw_N(tlen, h):
  TP.nw_N512(tlen, h)

law TP.nw_tile512:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {WL_.WL.tile(V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)), 0, tlen, tlen, 8388608) == True{} : Bool}

def TP.nw_tile512(tlen, h):
  %Equal.sym(Nat, V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)), 1n+TP.wnr(255n, 8388608, tlen, 8388608), TP.nw_N512(tlen, h)) : {WL_.WL.tile(_, 0, tlen, tlen, 8388608) == True{} : Bool}
  (%V.U.N_le(0, tlen, SE_.SE.le0(V.U.N(tlen))) : {Bool.or(Bool.not(_), WL_.WL.tile(1n+TP.wnr(255n, 8388608, tlen, 8388608), 0, tlen, tlen, 8388608)) == True{} : Bool}; TP.wn_tile(255n, 0, tlen, 8388608, TP.nowrap(tlen, 2146435072, 8388608, V.U.lt_to_le(tlen, 2146435072, h), {==}), WR_.WR.le_trans_u(tlen, 2146435072, N.adv(255n, 8388608, 8388608), V.U.lt_to_le(tlen, 2146435072, h), {==})))

law TP.nw_tile:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {WL_.WL.tile(V.U.N(N.wn(tlen, 8388608)), 0, tlen, tlen, 8388608) == True{} : Bool}

def TP.nw_tile(tlen, h):
  TP.nw_tile512(tlen, h)

law TP.nw_pos512:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(1n, V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)))) == True{} : Bool}

def TP.nw_pos512(tlen, h):
  %Equal.sym(Nat, V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)), 1n+TP.wnr(255n, 8388608, tlen, 8388608), TP.nw_N512(tlen, h)) : {Cmp.is_le(Nat.cmp(1n, _)) == True{} : Bool}
  SE_.SE.le0(TP.wnr(255n, 8388608, tlen, 8388608))

# The run's output fits Eo.
law TP.nw_pos:
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(1n, V.U.N(N.wn(tlen, 8388608)))) == True{} : Bool}

def TP.nw_pos(tlen, h):
  TP.nw_pos512(tlen, h)

# The header and the windows fit Eo: 5 bytes, 47 a window and the target's,
# for n windows of B at most, with 5 + 47 B at most K (a check on values:
# K and B stay variables here, so no large number is built).
law TP.bud_gen:
  for +t: U32
  for +c: U32
  for +K: U32
  for +r: Nat
  for +n: Nat
  for +B: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, Nat.add(TP.m47(n), V.U.N(t)))) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(n, B)) == True{} : Bool}
  for +hK: {Cmp.is_le(Nat.cmp(Nat.add(5n, TP.m47(B)), V.U.N(K))) == True{} : Bool}
  for +ht: {U32.is_le(t, c) == True{} : Bool}
  for +hc: {U32.is_le(c, U32.add(c, K)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(5n, r), V.U.N(U32.add(t, K)))) == True{} : Bool}

def TP.bud_gen(t, c, K, r, n, B, hr, hn, hK, ht, hc):
  %Equal.sym(Nat, V.U.N(U32.add(t, K)), Nat.add(V.U.N(t), V.U.N(K)), TP.add_N2(t, K, c, K, ht, TP.le_refl_u(K), hc)) :
    {Cmp.is_le(Nat.cmp(Nat.add(5n, r), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(t), V.U.N(K)), Nat.add(V.U.N(K), V.U.N(t)), P.Nat.add_comm(V.U.N(t), V.U.N(K))) :
    {Cmp.is_le(Nat.cmp(Nat.add(5n, r), _)) == True{} : Bool}
  P.Nat.le_trans(Nat.add(5n, r), Nat.add(Nat.add(5n, TP.m47(B)), V.U.N(t)), Nat.add(V.U.N(K), V.U.N(t)), MT_.MT.add_le(5n, 5n, r, Nat.add(TP.m47(B), V.U.N(t)), C.CP.le_refl(5n), P.Nat.le_trans(r, Nat.add(TP.m47(n), V.U.N(t)), Nat.add(TP.m47(B), V.U.N(t)), hr, MT_.MT.add_le(TP.m47(n), TP.m47(B), V.U.N(t), V.U.N(t), TP.m47_mono(n, B, hn), C.CP.le_refl(V.U.N(t))))), MT_.MT.add_le(Nat.add(5n, TP.m47(B)), V.U.N(K), V.U.N(t), V.U.N(t), hK, C.CP.le_refl(V.U.N(t))))

law TP.bud_top512:
  for +slen: U32
  for +tlen: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  for +ht: {U32.is_le(tlen, 2146435072) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(5n, WL_.WL.rb(V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0)), V.U.N(TP.Eo(tlen)))) == True{} : Bool}

def TP.bud_top512(slen, tlen, blk, lsh, lmask, ssh, smask, cap, h, ht):
  %Equal.sym(Nat, V.U.N(N.wn.go(512n, 8388608, tlen, 8388608)), 1n+TP.wnr(255n, 8388608, tlen, 8388608), TP.nw_N512(tlen, h)) : {Cmp.is_le(Nat.cmp(Nat.add(5n, WL_.WL.rb(_, N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0)), V.U.N(TP.Eo(tlen)))) == True{} : Bool}
  TP.bud_gen(tlen, 2146435072, 16384, WL_.WL.rb(1n+TP.wnr(255n, 8388608, tlen, 8388608), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0), 1n+TP.wnr(255n, 8388608, tlen, 8388608), 256n, P.Nat.le_trans(WL_.WL.rb(1n+TP.wnr(255n, 8388608, tlen, 8388608), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0), Nat.add(WL_.WL.rb(1n+TP.wnr(255n, 8388608, tlen, 8388608), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0), V.U.N(0)), Nat.add(TP.m47(1n+TP.wnr(255n, 8388608, tlen, 8388608)), V.U.N(tlen)), P.Nat.cmp_add_r(WL_.WL.rb(1n+TP.wnr(255n, 8388608, tlen, 8388608), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0), V.U.N(0)), TP.rb_le(TP.wnr(255n, 8388608, tlen, 8388608), slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap, 0, tlen, (%V.U.N_le(0, tlen, SE_.SE.le0(V.U.N(tlen))) : {Bool.or(Bool.not(_), WL_.WL.tile(1n+TP.wnr(255n, 8388608, tlen, 8388608), 0, tlen, tlen, 8388608)) == True{} : Bool}; TP.wn_tile(255n, 0, tlen, 8388608, TP.nowrap(tlen, 2146435072, 8388608, V.U.lt_to_le(tlen, 2146435072, h), {==}), WR_.WR.le_trans_u(tlen, 2146435072, N.adv(255n, 8388608, 8388608), V.U.lt_to_le(tlen, 2146435072, h), {==}))))), TP.wnr_le(255n, 8388608, tlen, 8388608), {==}, ht, {==})

# x < c + 1 is x <= c.
law TP.bud_top:
  for +slen: U32
  for +tlen: U32
  for +blk: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  for +ht: {U32.is_le(tlen, 2146435072) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(5n, WL_.WL.rb(V.U.N(N.wn(tlen, 8388608)), N.EK{slen, tlen, 8388608, blk, lsh, lmask, ssh, smask, cap}, 0)), V.U.N(TP.Eo(tlen)))) == True{} : Bool}

def TP.bud_top(slen, tlen, blk, lsh, lmask, ssh, smask, cap, h, ht):
  TP.bud_top512(slen, tlen, blk, lsh, lmask, ssh, smask, cap, h, ht)

# The encoder's parameters
# ------------------------

def TP.SL(+rslen: U32) -> U32:
  U32.min(rslen, 4278190080)

def TP.mk.lb(+slen: U32) -> U32:
  U32.from_nat(B.B.depth(N.u32.max(slen, 16384)))

def TP.mk.lbits(+slen: U32) -> U32:
  N.u32.pick(U32.is_le(slen, 67108864), N.u32.max(3, U32.sub(TP.mk.lb(slen), 3)), 23)

def TP.mk.sbits(+tlen: U32) -> U32:
  U32.min(23, U32.from_nat(B.B.depth(N.u32.max(tlen, 16384))))

def TP.mk.blk(+slen: U32) -> U32:
  N.u32.pick(U32.is_le(slen, 67108864), U32.shln(1, U32.to_nat(TP.mk.lb(slen))), 2097152)

def TP.mk.lsh(+slen: U32) -> U32:
  U32.sub(32, TP.mk.lbits(slen))

def TP.mk.lmask(+slen: U32) -> U32:
  U32.sub(U32.shln(1, U32.to_nat(TP.mk.lbits(slen))), 1)

def TP.mk.ssh(+tlen: U32) -> U32:
  U32.sub(32, TP.mk.sbits(tlen))

def TP.mk.smask(+tlen: U32) -> U32:
  U32.sub(U32.shln(1, U32.to_nat(TP.mk.sbits(tlen))), 1)

law TP.mk_eq:
  for +slen: U32
  for +tlen: U32
  {N.EK.mk(slen, tlen) == N.EK{slen, tlen, 8388608, TP.mk.blk(slen), TP.mk.lsh(slen), TP.mk.lmask(slen), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576} : N.EK}

def TP.mk_eq(slen, tlen):
  {==}

# The state the tasks start from.
def TP.S1(+rslen: U32, +tlen: U32, +ts: A.Tr) -> WS_.EST:
  TP.pre(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), ts, TP.s0(TP.to0(tlen)))

law TP.top_hG:
  for +rslen: U32
  for +tlen: U32
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {WR_.WR.G(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen)) == True{} : Bool}

def TP.top_hG(rslen, tlen, h):
  TP.G_of(TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, rslen, 2146435072, 4278190080, TP.min_le_u(rslen, 4278190080), SE_.SE.min_le(rslen, 4278190080), V.U.lt_to_le(tlen, 2146435072, h), {==}, {==}, {==}, {==})

law TP.top_hes:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {WP_.WP.esok(TP.S1(rslen, tlen, ts)) == True{} : Bool}

def TP.top_hes(rslen, tlen, ts, h):
  TP.pre_esok(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), ts, TP.s0(TP.to0(tlen)), TP.esok_s0(TP.to0(tlen), TP.ook_to0(tlen)))

law TP.top_olen:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {WS_.WS.olen(TP.S1(rslen, tlen, ts)) == 5 : U32}

def TP.top_olen(rslen, tlen, ts, h):
  TP.pre_olen(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), ts, TP.s0(TP.to0(tlen)))

law TP.top_hbud:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(TP.S1(rslen, tlen, ts))), WL_.WL.rb(V.U.N(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, 0)), V.U.N(TP.Eo(tlen)))) == True{} : Bool}

def TP.top_hbud(rslen, tlen, ts, h):
  %Equal.sym(U32, WS_.WS.olen(TP.S1(rslen, tlen, ts)), 5, TP.top_olen(rslen, tlen, ts, h)) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), WL_.WL.rb(V.U.N(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, 0)), V.U.N(TP.Eo(tlen)))) == True{} : Bool}
  TP.bud_top(TP.SL(rslen), tlen, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, h, V.U.lt_to_le(tlen, 2146435072, h))

law TP.top_hO:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {S.S.has(214 <> 195 <> 196 <> 0 <> 0 <> [], WS_.WS.to(TP.S1(rslen, tlen, ts)), 0) == True{} : Bool}

def TP.top_hO(rslen, tlen, ts, h):
  %Equal.sym(A.Tr, WS_.WS.to(TP.S1(rslen, tlen, ts)), TP.to0(tlen), TP.pre_to(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), ts, TP.s0(TP.to0(tlen)))) : {S.S.has(214 <> 195 <> 196 <> 0 <> 0 <> [], _, 0) == True{} : Bool}
  TP.has_hdr(tlen, h)

law TP.top_hOl:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {S.S.len(214 <> 195 <> 196 <> 0 <> 0 <> []) == V.U.N(WS_.WS.olen(TP.S1(rslen, tlen, ts))) : Nat}

def TP.top_hOl(rslen, tlen, ts, h):
  %Equal.sym(U32, WS_.WS.olen(TP.S1(rslen, tlen, ts)), 5, TP.top_olen(rslen, tlen, ts, h)) : {S.S.len(214 <> 195 <> 196 <> 0 <> 0 <> []) == V.U.N(_) : Nat}
  {==}

# The whole run
# -------------

def TP.FF(+rslen: U32, +tlen: U32, +ts: A.Tr, +tt: A.Tr) -> WS_.EST:
  TP.top(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, N.wn(tlen, 8388608), ts, tt, TP.S1(rslen, tlen, ts))

def TP.WW(+rslen: U32, +tlen: U32, +ts: A.Tr, +tt: A.Tr) -> List<&2, Q.AW>:
  TP.tws(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, N.wn(tlen, 8388608), ts, tt, TP.S1(rslen, tlen, ts))

law TP.f_out:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {S.S.has(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt))), WS_.WS.to(TP.FF(rslen, tlen, ts, tt)), 0) == True{} : Bool}

def TP.f_out(rslen, tlen, ts, tt, h):
  WR_.WR.par_out(N.enc.depth(N.wn(tlen, 8388608)), TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, 0, N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), WR_.WR.sp(N.wn(tlen, 8388608), 0, 8388608, TP.S1(rslen, tlen, ts)), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.hk_top(N.wn(tlen, 8388608), TP.nw_pos(tlen, h)), TP.top_hes(rslen, tlen, ts, h), WR_.WR.esok_fresh(WR_.WR.tl(TP.S1(rslen, tlen, ts)), WR_.WR.ocap(N.wn(tlen, 8388608), 8388608), WR_.WR.lidx(TP.S1(rslen, tlen, ts)), WR_.WR.wm(N.wn(tlen, 8388608), 0, 8388608)), {==}, TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h))

law TP.f_len:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))) == V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))) : Nat}

def TP.f_len(rslen, tlen, ts, tt, h):
  WR_.WR.par_len(N.enc.depth(N.wn(tlen, 8388608)), TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, 0, N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), WR_.WR.sp(N.wn(tlen, 8388608), 0, 8388608, TP.S1(rslen, tlen, ts)), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.hk_top(N.wn(tlen, 8388608), TP.nw_pos(tlen, h)), TP.top_hes(rslen, tlen, ts, h), WR_.WR.esok_fresh(WR_.WR.tl(TP.S1(rslen, tlen, ts)), WR_.WR.ocap(N.wn(tlen, 8388608), 8388608), WR_.WR.lidx(TP.S1(rslen, tlen, ts)), WR_.WR.wm(N.wn(tlen, 8388608), 0, 8388608)), {==}, TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h))

law TP.f_wsok:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Q.SP.wsok(TP.WW(rslen, tlen, ts, tt), ts, tt, rslen, 0, A.A.to(D.ct.table()), tlen, rslen) == True{} : Bool}

def TP.f_wsok(rslen, tlen, ts, tt, h):
  WR_.WR.par_wsok(N.enc.depth(N.wn(tlen, 8388608)), TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, 0, N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), WR_.WR.sp(N.wn(tlen, 8388608), 0, 8388608, TP.S1(rslen, tlen, ts)), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.hk_top(N.wn(tlen, 8388608), TP.nw_pos(tlen, h)), TP.top_hes(rslen, tlen, ts, h), WR_.WR.esok_fresh(WR_.WR.tl(TP.S1(rslen, tlen, ts)), WR_.WR.ocap(N.wn(tlen, 8388608), 8388608), WR_.WR.lidx(TP.S1(rslen, tlen, ts)), WR_.WR.wm(N.wn(tlen, 8388608), 0, 8388608)), {==}, TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h))

law TP.f_wop:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Q.SP.wop(TP.WW(rslen, tlen, ts, tt), 0) == tlen : U32}

def TP.f_wop(rslen, tlen, ts, tt, h):
  WR_.WR.par_wop(N.enc.depth(N.wn(tlen, 8388608)), TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, 0, N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), WR_.WR.sp(N.wn(tlen, 8388608), 0, 8388608, TP.S1(rslen, tlen, ts)), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.hk_top(N.wn(tlen, 8388608), TP.nw_pos(tlen, h)), TP.top_hes(rslen, tlen, ts, h), WR_.WR.esok_fresh(WR_.WR.tl(TP.S1(rslen, tlen, ts)), WR_.WR.ocap(N.wn(tlen, 8388608), 8388608), WR_.WR.lidx(TP.S1(rslen, tlen, ts)), WR_.WR.wm(N.wn(tlen, 8388608), 0, 8388608)), {==}, TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h))

law TP.f_pos:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {Q.SP.wend(TP.WW(rslen, tlen, ts, tt), 5) == WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)) : U32}

def TP.f_pos(rslen, tlen, ts, tt, h):
  %TP.top_olen(rslen, tlen, ts, h) : {Q.SP.wend(TP.WW(rslen, tlen, ts, tt), _) == WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)) : U32}
  Equal.sym(U32, WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), Q.SP.wend(TP.WW(rslen, tlen, ts, tt), WS_.WS.olen(TP.S1(rslen, tlen, ts))), TP.par_pos(N.enc.depth(N.wn(tlen, 8388608)), TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, 0, N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), WR_.WR.sp(N.wn(tlen, 8388608), 0, 8388608, TP.S1(rslen, tlen, ts)), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.hk_top(N.wn(tlen, 8388608), TP.nw_pos(tlen, h)), TP.top_hes(rslen, tlen, ts, h), WR_.WR.esok_fresh(WR_.WR.tl(TP.S1(rslen, tlen, ts)), WR_.WR.ocap(N.wn(tlen, 8388608), 8388608), WR_.WR.lidx(TP.S1(rslen, tlen, ts)), WR_.WR.wm(N.wn(tlen, 8388608), 0, 8388608)), {==}, TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h)))

law TP.done_es:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {N.enc.done(rslen, tlen, WS_.WS.es(ts, tt, s)) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(s), A.A.from(WS_.WS.to(s))}) : (B.Bytes & B.Bytes) & B.Bytes}

def TP.done_es(rslen, tlen, ts, tt, s):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      {==}

# The encoder's code: the delta is the run's output.
law TP.enc_code:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {N.encode(B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) : (B.Bytes & B.Bytes) & B.Bytes}

def TP.enc_code(rslen, tlen, ts, tt, h):
  %Equal.sym(Array<U32> & U32, N.wr.byte(0, N.wr.byte(0, N.wr.byte(196, N.wr.byte(195, N.wr.byte(214, (B.B.zeros(N.u32.max(U32.shrn(tlen, 3n), 4096)), 0)))))), (A.A.from(TP.to0(tlen)), 5), TP.hdr_code(tlen)) : {N.enc.go(N.EK.mk(TP.SL(rslen), tlen), rslen, A.A.from(ts), A.A.from(tt), U32.to_nat(TP.mk.lbits(TP.SL(rslen))), U32.to_nat(TP.mk.sbits(tlen)), U32.min(8388608, N.u32.max(tlen, 64)), _) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) : (B.Bytes & B.Bytes) & B.Bytes}
  %Equal.sym(N.ES, N.ES{A.A.from(ts), A.A.from(tt), [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], Array.new(U32, 17n, 0), N.Em{B.B.zeros(65536), B.B.zeros(65536), B.B.zeros(65536), Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0}, A.A.from(TP.to0(tlen)), 5, 0, 0}, WS_.WS.es(ts, tt, TP.s0(TP.to0(tlen))), TP.s0_code(ts, tt, TP.to0(tlen))) : {N.enc.done(rslen, tlen, N.enc.par.top(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.to_nat(TP.mk.sbits(tlen)), U32.min(8388608, N.u32.max(tlen, 64)), N.wn(tlen, 8388608), N.enc.pre(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), _))) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) : (B.Bytes & B.Bytes) & B.Bytes}
  %Equal.sym(N.ES, N.enc.pre(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), WS_.WS.es(ts, tt, TP.s0(TP.to0(tlen)))), WS_.WS.es(ts, tt, TP.S1(rslen, tlen, ts)), TP.pre_code(N.enc.depth(N.wn(tlen, 8388608)), N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.min(tlen, 8388608), ts, tt, TP.s0(TP.to0(tlen)))) : {N.enc.done(rslen, tlen, N.enc.par.top(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.to_nat(TP.mk.sbits(tlen)), U32.min(8388608, N.u32.max(tlen, 64)), N.wn(tlen, 8388608), _)) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) : (B.Bytes & B.Bytes) & B.Bytes}
  %Equal.sym(N.ES, N.enc.par.top(N.EK{TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576}, U32.to_nat(TP.mk.sbits(tlen)), U32.min(8388608, N.u32.max(tlen, 64)), N.wn(tlen, 8388608), WS_.WS.es(ts, tt, TP.S1(rslen, tlen, ts))), WS_.WS.es(ts, tt, TP.FF(rslen, tlen, ts, tt)), TP.top_code(TP.SL(rslen), tlen, 8388608, TP.mk.blk(TP.SL(rslen)), TP.mk.lsh(TP.SL(rslen)), TP.mk.lmask(TP.SL(rslen)), TP.mk.ssh(tlen), TP.mk.smask(tlen), 1048576, U32.to_nat(TP.mk.sbits(tlen)), U32.min(8388608, N.u32.max(tlen, 64)), N.wn(tlen, 8388608), tlen, ts, tt, TP.S1(rslen, tlen, ts), TP.Eb(TP.SL(rslen), tlen, 8388608), TP.BIGs(8388608), TP.BIGe(8388608), U32.add(TP.SL(rslen), 8388608), rslen, rslen, TP.Eo(tlen), 214 <> 195 <> 196 <> 0 <> 0 <> [], TP.top_hG(rslen, tlen, h), TP.nw_tile(tlen, h), TP.top_hes(rslen, tlen, ts, h), TP.top_hbud(rslen, tlen, ts, h), TP.top_hO(rslen, tlen, ts, h), TP.top_hOl(rslen, tlen, ts, h), TP.nw_pos(tlen, h))) : {N.enc.done(rslen, tlen, _) == ((B.Bytes{rslen, A.A.from(ts)}, B.Bytes{tlen, A.A.from(tt)}), B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) : (B.Bytes & B.Bytes) & B.Bytes}
  TP.done_es(rslen, tlen, ts, tt, TP.FF(rslen, tlen, ts, tt))

# The delta decodes, against the source, to the target.
law TP.dec:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {D.decode(B.Bytes{rslen, A.A.from(ts)}, B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}) == (B.Bytes{rslen, A.A.from(ts)}, (B.Bytes{WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), A.A.from(WS_.WS.to(TP.FF(rslen, tlen, ts, tt)))}, Done{B.Bytes{tlen, A.A.from(Q.SP.wto(TP.WW(rslen, tlen, ts, tt), ts, tt, A.T.new(DT_.O.dep(tlen), 0), 0))}})) : B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)}

def TP.dec(rslen, tlen, ts, tt, h):
  DT_.DT.dec(TP.WW(rslen, tlen, ts, tt), ts, WS_.WS.to(TP.FF(rslen, tlen, ts, tt)), tt, rslen, WS_.WS.olen(TP.FF(rslen, tlen, ts, tt)), tlen, SC_.SC.and_tt(S.S.has(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt))), WS_.WS.to(TP.FF(rslen, tlen, ts, tt)), 0), Cmp.is_le(Nat.cmp(Nat.add(S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))), V.U.N(0)), V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))))), TP.f_out(rslen, tlen, ts, tt, h), (%Equal.sym(Nat, Nat.add(S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))), 0n), S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))), P.Nat.add_zero_r(S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))))) : {Cmp.is_le(Nat.cmp(_, V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))))) == True{} : Bool}; (%Equal.sym(Nat, S.S.len(K.WD.app(214 <> 195 <> 196 <> 0 <> 0 <> [], Q.SP.wbs(TP.WW(rslen, tlen, ts, tt)))), V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))), TP.f_len(rslen, tlen, ts, tt, h)) : {Cmp.is_le(Nat.cmp(_, V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))))) == True{} : Bool}; C.CP.le_refl(V.U.N(WS_.WS.olen(TP.FF(rslen, tlen, ts, tt))))))), TP.f_pos(rslen, tlen, ts, tt, h), TP.f_wsok(rslen, tlen, ts, tt, h), TP.f_wop(rslen, tlen, ts, tt, h), V.U.lt_trans(tlen, 2146435072, 2147483648, h, {==}))

law TP.list:
  for +rslen: U32
  for +tlen: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +h: {U32.is_lt(tlen, 2146435072) == True{} : Bool}
  {B.B.list(B.Bytes{tlen, A.A.from(Q.SP.wto(TP.WW(rslen, tlen, ts, tt), ts, tt, A.T.new(DT_.O.dep(tlen), 0), 0))}) == B.B.list(B.Bytes{tlen, A.A.from(tt)}) : List<&2, U32>}

def TP.list(rslen, tlen, ts, tt, h):
  %Equal.sym(List<&2, U32>, B.B.list(B.Bytes{tlen, A.A.from(tt)}), S.S.sl(U32.to_nat(tlen), tt, 0), S.S.list(tlen, tt)) : {B.B.list(B.Bytes{tlen, A.A.from(Q.SP.wto(TP.WW(rslen, tlen, ts, tt), ts, tt, A.T.new(DT_.O.dep(tlen), 0), 0))}) == _ : List<&2, U32>}
  DT_.DT.list(TP.WW(rslen, tlen, ts, tt), ts, tt, rslen, tlen, TP.f_wsok(rslen, tlen, ts, tt, h), TP.f_wop(rslen, tlen, ts, tt, h), V.U.lt_trans(tlen, 2146435072, 2147483648, h, {==}))
