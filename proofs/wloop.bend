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
import ./wwrite.bend as WW_
import ./wfin.bend as WF_
import ./einst.bend as EI_
import ./adler.bend as H
import ./varint.bend as R
import ./dwin.bend as J


# The windows
# ===========
#
# win.loop: a run of windows, each appended to the output, together
# rebuilding the target from their first position to their last.
#
# Source: proofs/wloop.bp (tools/bpp.py writes proofs/wloop.bend from it).

# A window's size
# ---------------

law WL.lv5:
  for +v: U32
  {Cmp.is_le(Nat.cmp(S.S.len(R.VI.var(v)), 5n)) == True{} : Bool}

def WL.lv5(v):
  %Equal.sym(Nat, S.S.len(R.VI.var(v)), V.U.N(B.B.var.len(v)), R.VI.len_var(v)) :
    {Cmp.is_le(Nat.cmp(_, 5n)) == True{} : Bool}
  EM_.EM.vl5(v)

law WL.segb.go:
  for +cpl: U32
  for +off: U32
  for +z: Bool
  {Cmp.is_le(Nat.cmp(S.S.len(WW_.WW.sb(z, cpl, off)), 10n)) == True{} : Bool}

def WL.segb.go(cpl, off, z):
  match z:
    case True{}:
      %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(cpl), R.VI.var(off))), Nat.add(S.S.len(R.VI.var(cpl)), S.S.len(R.VI.var(off))), K.WD.len_app(R.VI.var(cpl), R.VI.var(off))) :
        {Cmp.is_le(Nat.cmp(_, 10n)) == True{} : Bool}
      MT_.MT.add_le(S.S.len(R.VI.var(cpl)), 5n, S.S.len(R.VI.var(off)), 5n, WL.lv5(cpl), WL.lv5(off))
    case False{}:
      {==}

law WL.segb:
  for +cpl: U32
  for +off: U32
  {Cmp.is_le(Nat.cmp(S.S.len(Q.SP.segb(cpl, off)), 10n)) == True{} : Bool}

def WL.segb(cpl, off):
  %Equal.sym(List<&2, U32>, Q.SP.segb(cpl, off), WW_.WW.sb(U32.is_lt(0, cpl), cpl, off), WP_.WP.segb(cpl, off)) :
    {Cmp.is_le(Nat.cmp(S.S.len(_), 10n)) == True{} : Bool}
  WL.segb.go(cpl, off, U32.is_lt(0, cpl))

# A window is at most 41 bytes of header and its sections, which are at
# most k, 8k + 6 and 5k bytes for a window of k bytes.
law WL.wbb:
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +dl: U32
  for +il: U32
  for +al: U32
  for +ops: List<&2, Q.OP>
  for +sum: U32
  for +k: Nat
  for +l1: {Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl) == True{} : Bool}
  for +l2: {Q.SP.lenis(Q.SP.insl(ops), il) == True{} : Bool}
  for +l3: {Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al) == True{} : Bool}
  for +hd: {Cmp.is_le(Nat.cmp(V.U.N(dl), k)) == True{} : Bool}
  for +hi: {Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n))) == True{} : Bool}
  for +ha: {Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(k))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(S.S.len(Q.SP.wb(Q.AW{cpl, off, tlen, dl, il, al, ops, sum})), Nat.add(41n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}

def WL.wbb(cpl, off, tlen, dl, il, al, ops, sum, k, l1, l2, l3, hd, hi, ha):
  %Equal.sym(Nat, S.S.len(K.WD.app(Q.SP.segb(cpl, off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(S.S.len(Q.SP.segb(cpl, off)), S.S.len(K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), K.WD.len_app(Q.SP.segb(cpl, off), K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))))), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), S.S.len(K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))))), K.WD.len_app(R.VI.var(Q.SP.enc(tlen, dl, il, al)), K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), _), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))), Nat.add(S.S.len(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))), K.WD.len_app(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), _)), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), Nat.add(S.S.len(R.VI.var(tlen)), S.S.len(0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), K.WD.len_app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(_, S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), Nat.add(S.S.len(R.VI.var(dl)), S.S.len(K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))), K.WD.len_app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+_), S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))), Nat.add(S.S.len(R.VI.var(il)), S.S.len(K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))), K.WD.len_app(R.VI.var(il), K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), _)), S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])), K.WD.len_app(R.VI.var(al), U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> [])) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), _))), S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))), Nat.add(S.S.len(Q.SP.datl(Q.SP.halves(ops))), S.S.len(K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))), K.WD.len_app(Q.SP.datl(Q.SP.halves(ops)), K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops))))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), _))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(K.WD.app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))), Nat.add(S.S.len(Q.SP.insl(ops)), S.S.len(Q.SP.adrl(Q.SP.halves(ops)))), K.WD.len_app(Q.SP.insl(ops), Q.SP.adrl(Q.SP.halves(ops)))) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), Nat.add(S.S.len(Q.SP.datl(Q.SP.halves(ops))), _)))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(Q.SP.datl(Q.SP.halves(ops))), V.U.N(dl), WP_.WP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl, l1)) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), Nat.add(_, Nat.add(S.S.len(Q.SP.insl(ops)), S.S.len(Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(Q.SP.insl(ops)), V.U.N(il), WP_.WP.lenis(Q.SP.insl(ops), il, l2)) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), Nat.add(V.U.N(dl), Nat.add(_, S.S.len(Q.SP.adrl(Q.SP.halves(ops)))))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  %Equal.sym(Nat, S.S.len(Q.SP.adrl(Q.SP.halves(ops))), V.U.N(al), WP_.WP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al, l3)) :
    {Cmp.is_le(Nat.cmp(Nat.add(S.S.len(Q.SP.segb(cpl, off)), Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), S.S.len(U32.shrn(sum, 24n) <> U32.and(U32.shrn(sum, 16n), 255) <> U32.and(U32.shrn(sum, 8n), 255) <> U32.and(sum, 255) <> []))))), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), _))))), Nat.add(40n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))))) == True{} : Bool}
  MT_.MT.add_le(S.S.len(Q.SP.segb(cpl, off)), 10n, Nat.add(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), 4n)))), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))))), Nat.add(5n, Nat.add(25n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k))))), WL.segb(cpl, off), MT_.MT.add_le(S.S.len(R.VI.var(Q.SP.enc(tlen, dl, il, al))), 5n, Nat.add(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), 4n)))), Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al)))), Nat.add(25n, Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)))), WL.lv5(Q.SP.enc(tlen, dl, il, al)), MT_.MT.add_le(Nat.add(S.S.len(R.VI.var(tlen)), 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), 4n)))), 25n, Nat.add(V.U.N(dl), Nat.add(V.U.N(il), V.U.N(al))), Nat.add(k, Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k))), MT_.MT.add_le(S.S.len(R.VI.var(tlen)), 5n, 1n+Nat.add(S.S.len(R.VI.var(dl)), Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), 4n))), 20n, WL.lv5(tlen), MT_.MT.add_le(S.S.len(R.VI.var(dl)), 5n, Nat.add(S.S.len(R.VI.var(il)), Nat.add(S.S.len(R.VI.var(al)), 4n)), 14n, WL.lv5(dl), MT_.MT.add_le(S.S.len(R.VI.var(il)), 5n, Nat.add(S.S.len(R.VI.var(al)), 4n), 9n, WL.lv5(il), MT_.MT.add_le(S.S.len(R.VI.var(al)), 5n, 4n, 4n, WL.lv5(al), {==})))), MT_.MT.add_le(V.U.N(dl), k, Nat.add(V.U.N(il), V.U.N(al)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), EM_.EM.k5(k)), hd, MT_.MT.add_le(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(k))), 6n), V.U.N(al), EM_.EM.k5(k), hi, ha)))))

# Tiling
# ------
#
# k windows of wsz bytes from w0, in a target of T bytes, end at cend: each
# is within the target, all but the last are whole, and the last ends at
# cend.

def WL.last(q: Nat, +w: U32, +cend: U32, +T: U32, +wsz: U32) -> Bool:
  match q:
    case 0n:
      U32.is_eq(U32.min(T, U32.add(w, wsz)), cend)
    case 1n+r:
      U32.is_le(U32.add(w, wsz), T)

def WL.tile(k: Nat, +w: U32, +cend: U32, +T: U32, +wsz: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+q0:
      +q = {q0 : Nat}
      Bool.and(U32.is_le(w, T), Bool.and(U32.is_le(w, U32.add(w, wsz)), Bool.and(WL.last(q, w, cend, T, wsz), WL.tile(q, U32.add(w, wsz), cend, T, wsz))))

# A window's end.
def WL.w1(+T: U32, +w: U32, +wsz: U32) -> U32:
  U32.min(T, U32.add(w, wsz))

law WL.min_ge:
  for +a: U32
  for +b: U32
  for +c: U32
  for +ha: {U32.is_le(c, a) == True{} : Bool}
  for +hb: {U32.is_le(c, b) == True{} : Bool}
  {U32.is_le(c, U32.min(a, b)) == True{} : Bool}

law WL.min_ge.go:
  for +a: U32
  for +b: U32
  for +c: U32
  for +z: Bool
  for +ez: {U32.is_lt(a, b) == z : Bool}
  for +ha: {U32.is_le(c, a) == True{} : Bool}
  for +hb: {U32.is_le(c, b) == True{} : Bool}
  {U32.is_le(c, U32.min(a, b)) == True{} : Bool}

def WL.min_ge.go(a, b, c, z, ez, ha, hb):
  match z:
    case True{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {U32.is_le(c, _) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), True{}, ez) :
        {U32.is_le(c, Bool.pick(U32, _, a, b)) == True{} : Bool}
      ha
    case False{}:
      %Equal.sym(U32, U32.min(a, b), Bool.pick(U32, U32.is_lt(a, b), a, b), K.WD.min(a, b)) :
        {U32.is_le(c, _) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(a, b), False{}, ez) :
        {U32.is_le(c, Bool.pick(U32, _, a, b)) == True{} : Bool}
      hb

def WL.min_ge(a, b, c, ha, hb):
  WL.min_ge.go(a, b, c, U32.is_lt(a, b), {==}, ha, hb)

law WL.w01:
  for +T: U32
  for +w: U32
  for +wsz: U32
  for +h1: {U32.is_le(w, T) == True{} : Bool}
  for +h2: {U32.is_le(w, U32.add(w, wsz)) == True{} : Bool}
  {U32.is_le(w, WL.w1(T, w, wsz)) == True{} : Bool}

def WL.w01(T, w, wsz, h1, h2):
  WL.min_ge(T, U32.add(w, wsz), w, h1, h2)

law WL.w1T:
  for +T: U32
  for +w: U32
  for +wsz: U32
  {Cmp.is_le(Nat.cmp(V.U.N(WL.w1(T, w, wsz)), V.U.N(T))) == True{} : Bool}

def WL.w1T(T, w, wsz):
  MT_.MT.min_le(T, U32.add(w, wsz))

# A window is wsz bytes at most.
law WL.wk:
  for +T: U32
  for +w: U32
  for +wsz: U32
  for +h1: {U32.is_le(w, T) == True{} : Bool}
  for +h2: {U32.is_le(w, U32.add(w, wsz)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(WL.w1(T, w, wsz), w)), V.U.N(wsz))) == True{} : Bool}

def WL.wk(T, w, wsz, h1, h2):
  %P.Nat.cmp_add_rr(V.U.N(U32.sub(WL.w1(T, w, wsz), w)), V.U.N(wsz), V.U.N(w)) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(WL.w1(T, w, wsz), w)), V.U.N(w)), V.U.N(WL.w1(T, w, wsz)), V.U.sub_nat(WL.w1(T, w, wsz), w, WL.w01(T, w, wsz, h1, h2))) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(wsz), V.U.N(w)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(wsz), V.U.N(w)), Nat.add(V.U.N(w), V.U.N(wsz)), P.Nat.add_comm(V.U.N(wsz), V.U.N(w))) :
    {Cmp.is_le(Nat.cmp(V.U.N(WL.w1(T, w, wsz)), _)) == True{} : Bool}
  %V.U.add_nowrap(w, wsz, h2) :
    {Cmp.is_le(Nat.cmp(V.U.N(WL.w1(T, w, wsz)), _)) == True{} : Bool}
  MT_.MT.min_le_r(T, U32.add(w, wsz))

# A whole window ends where the next one starts.
law WL.wnext:
  for +T: U32
  for +w: U32
  for +wsz: U32
  for +h: {U32.is_le(U32.add(w, wsz), T) == True{} : Bool}
  {WL.w1(T, w, wsz) == U32.add(w, wsz) : U32}

def WL.wnext(T, w, wsz, h):
  %Equal.sym(U32, U32.min(T, U32.add(w, wsz)), Bool.pick(U32, U32.is_lt(T, U32.add(w, wsz)), T, U32.add(w, wsz)), K.WD.min(T, U32.add(w, wsz))) :
    {_ == U32.add(w, wsz) : U32}
  %Equal.sym(Bool, U32.is_lt(T, U32.add(w, wsz)), False{}, SC_.SC.nlt(U32.add(w, wsz), T, h)) :
    {Bool.pick(U32, _, T, U32.add(w, wsz)) == U32.add(w, wsz) : U32}
  {==}

# A window's facts, from the run's
# --------------------------------

# The scan's fixed facts, for the reset emitter.
law WL.kf:
  for +E: N.EK
  for +e: EM_.ET
  for +w0: U32
  for +w1: U32
  for +Eb: U32
  for +BIGs: U32
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  for +h1: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))) == True{} : Bool}
  for +h2: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))) == True{} : Bool}
  for +h3: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))) == True{} : Bool}
  for +hB: {U32.is_lt(BIGs, 2147483648) == True{} : Bool}
  {SC_.SC.kf(WS_.WS.sk(E, w0, w1), EM_.EM.reset(w0, e), Eb, BIGs) == True{} : Bool}

def WL.kf(E, e, w0, w1, Eb, BIGs, hw, h1, h2, h3, hk, hB):
  match E e:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      SC_.SC.and_tt(U32.is_eq(EM_.EM.uo(EM_.EM.reset(w0, EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc})), w0), Bool.and(U32.is_eq(slen, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648))))))), V.U.is_eq_refl(w0), SC_.SC.and_tt(U32.is_eq(slen, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648)))))), V.U.is_eq_refl(slen), SC_.SC.and_tt(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648))))), hw, SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648)))), h1, SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648))), h2, SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648)), h3, SC_.SC.and_tt(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(w1, w0))))), V.U.N(BIGs))), U32.is_lt(BIGs, 2147483648), hk, hB)))))))

# The scan starts within the window.
law WL.pp0.go:
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +cont: U32
  for +c: Bool
  for +ec: {U32.is_le(4, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))) == c : Bool}
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  {U32.is_le(N.u32.pick(c, U32.add(w0, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), w0), w1) == True{} : Bool}

def WL.pp0.go(slen, w0, w1, ts, tt, cont, c, ec, hw):
  match c:
    case True{}:
      V.U.N_le(U32.add(w0, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), w1, (%Equal.sym(Nat, V.U.N(U32.add(w0, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))))), V.U.add_N(w0, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))), w1, P.Nat.le_trans(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(U32.sub(w1, w0))), V.U.N(w1), MT_.MT.add_le(V.U.N(w0), V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(w0)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), 2n), 1)), ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), MT_.MT.cf(ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), 0), MT_.MT.cn(ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), SC_.SC.fb1(w0, w1, hw)))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; P.Nat.le_trans(Nat.add(V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))))), Nat.add(V.U.N(w0), V.U.N(U32.sub(w1, w0))), V.U.N(w1), MT_.MT.add_le(V.U.N(w0), V.U.N(w0), V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(w0)), P.Nat.le_trans(V.U.N(SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), V.U.N(U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont)))), V.U.N(U32.sub(w1, w0)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), 2n), 1)), ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), MT_.MT.cf(ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))), 0), MT_.MT.cn(ts, WS_.WS.at(slen, cont), MT_.MW{tt, w0}, 0)), MT_.MT.min_le(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), SC_.SC.fb1(w0, w1, hw))))
    case False{}:
      hw

law WL.pp0:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +hw: {U32.is_le(w0, w1) == True{} : Bool}
  {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, w1, ts, tt, s)), w1) == True{} : Bool}

def WL.pp0(E, w0, w1, ts, tt, s, hw):
  match E s:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      WL.pp0.go(slen, w0, w1, ts, tt, cont, U32.is_le(4, SC_.SC.flen(ts, WS_.WS.at(slen, cont), tt, w0, U32.min(U32.sub(w1, w0), U32.sub(slen, WS_.WS.at(slen, cont))))), {==}, hw)

# The write's bound, from a bound on the window's bytes.
law WL.hbv_of:
  for +olen: U32
  for +tt: A.Tr
  for +w0: U32
  for +tlen: U32
  for +cpl: U32
  for +off: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +Eo: U32
  for +hs: {WP_.WP.secs(e, g) == True{} : Bool}
  for +hle: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(olen), S.S.len(Q.SP.wb(WP_.WP.aw(cpl, off, tlen, tt, w0, e, g)))), V.U.N(Eo))) == True{} : Bool}
  {WS_.WS.hbv(olen, tt, w0, tlen, cpl, off, e, Eo) == True{} : Bool}

def WL.hbv_of(olen, tt, w0, tlen, cpl, off, e, g, Eo, hs, hle):
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      %Equal.sym(List<&2, U32>, K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(K.WD.app(N.u32.pick(U32.is_lt(0, cpl), 5, 4) <> [], WW_.WW.sb(U32.is_lt(0, cpl), cpl, off)), R.VI.var(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al))), R.VI.var(tlen)), 0 <> []), R.VI.var(dl)), R.VI.var(il)), R.VI.var(al)), U32.shrn(H.AD.T(tt, w0, tlen), 24n) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 16n), 255) <> []), U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 8n), 255) <> []), U32.and(H.AD.T(tt, w0, tlen), 255) <> []), S.S.sl(V.U.N(dl), td, 0)), S.S.sl(V.U.N(il), ti, 0)), S.S.sl(V.U.N(al), ta, 0)), K.WD.app(K.WD.app(N.u32.pick(U32.is_lt(0, cpl), 5, 4) <> [], K.WD.app(WW_.WW.sb(U32.is_lt(0, cpl), cpl, off), K.WD.app(R.VI.var(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(1, B.B.var.len(tlen)), B.B.var.len(dl)), B.B.var.len(il)), B.B.var.len(al)), 4), dl), il), al)), K.WD.app(R.VI.var(tlen), K.WD.app(0 <> [], K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), K.WD.app(U32.shrn(H.AD.T(tt, w0, tlen), 24n) <> [], K.WD.app(U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 16n), 255) <> [], K.WD.app(U32.and(U32.shrn(H.AD.T(tt, w0, tlen), 8n), 255) <> [], U32.and(H.AD.T(tt, w0, tlen), 255) <> []))))))))))), K.WD.app(S.S.sl(V.U.N(dl), td, 0), K.WD.app(S.S.sl(V.U.N(il), ti, 0), S.S.sl(V.U.N(al), ta, 0)))), WW_.WW.p15_eq(tlen, cpl, off, td, ti, ta, dl, il, al, H.AD.T(tt, w0, tlen))) :
        {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(olen), S.S.len(_)), V.U.N(Eo))) == True{} : Bool}
      %WP_.WP.wblen(tlen, cpl, off, td, ti, ta, dl, il, al, ops, H.AD.T(tt, w0, tlen), P.Bool.and_r(S.S.has(Q.SP.datl(Q.SP.halves(ops)), td, 0), Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl), P.Bool.and_l(Bool.and(S.S.has(Q.SP.datl(Q.SP.halves(ops)), td, 0), Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl)), Bool.and(Bool.and(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il)), Bool.and(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al))), hs)), P.Bool.and_r(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il), P.Bool.and_l(Bool.and(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il)), Bool.and(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al)), P.Bool.and_r(Bool.and(S.S.has(Q.SP.datl(Q.SP.halves(ops)), td, 0), Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl)), Bool.and(Bool.and(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il)), Bool.and(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al))), hs))), P.Bool.and_r(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al), P.Bool.and_r(Bool.and(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il)), Bool.and(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al)), P.Bool.and_r(Bool.and(S.S.has(Q.SP.datl(Q.SP.halves(ops)), td, 0), Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl)), Bool.and(Bool.and(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il)), Bool.and(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al))), hs)))) :
        {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(olen), _), V.U.N(Eo))) == True{} : Bool}
      hle

# A window's bytes: at most 41 + 14 k + 6, for a window of k bytes.
law WL.wbb_of:
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +tt: A.Tr
  for +ts: A.Tr
  for +w0: U32
  for +w1: U32
  for +e: EM_.ET
  for +g: EM_.EG
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +hF: {EI_.EI.F(e, g, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}) == True{} : Bool}
  for +huo: {EM_.EM.uo(e) == w1 : U32}
  {Cmp.is_le(Nat.cmp(S.S.len(Q.SP.wb(WP_.WP.aw(cpl, off, tlen, tt, w0, e, g))), Nat.add(41n, Nat.add(V.U.N(U32.sub(w1, w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(w1, w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(w1, w0)))))))) == True{} : Bool}

def WL.wbb_of(cpl, off, tlen, tt, ts, w0, w1, e, g, Et, Es, BIGe, hF, huo):
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      WL.wbb(cpl, off, tlen, dl, il, al, ops, H.AD.T(tt, w0, tlen), V.U.N(U32.sub(w1, w0)), P.Bool.and_r(S.S.has(Q.SP.datl(Q.SP.halves(ops)), td, 0), Q.SP.lenis(Q.SP.datl(Q.SP.halves(ops)), dl), WP_.WP.F0_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)), P.Bool.and_r(S.S.has(Q.SP.insl(ops), ti, 0), Q.SP.lenis(Q.SP.insl(ops), il), WP_.WP.F1_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)), P.Bool.and_r(S.S.has(Q.SP.adrl(Q.SP.halves(ops)), ta, 0), Q.SP.lenis(Q.SP.adrl(Q.SP.halves(ops)), al), WP_.WP.F2_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)), (%huo : {Cmp.is_le(Nat.cmp(V.U.N(dl), V.U.N(U32.sub(_, w0)))) == True{} : Bool}; WP_.WP.F11_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)), (%huo : {Cmp.is_le(Nat.cmp(V.U.N(il), Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(_, w0))))), 6n))) == True{} : Bool}; WP_.WP.F12_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)), (%huo : {Cmp.is_le(Nat.cmp(V.U.N(al), EM_.EM.k5(V.U.N(U32.sub(_, w0))))) == True{} : Bool}; WP_.WP.F13_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, EM_.EW{Q.XC{ts, tt, Q.SP.wseg(cpl, off), cpl, w0, w1}, Et, Es, A.A.to(D.ct.table()), BIGe}, hF)))

# A window's bounds
# -----------------

# The facts a window needs of its place and of the bounds.
def WL.wh(+E: N.EK, +w0: U32, +Eb: U32, +BIGs: U32, +Et: U32, +Es: U32, +BIGe: U32, +HB: U32, +Ea: U32, +S: U32, +Eo: U32) -> Bool:
  Bool.and(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))))

law WL.wh.hw:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_le(w0, WS_.WS.w1(E, w0)) == True{} : Bool}

def WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)

law WL.wh.hE1:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))) == True{} : Bool}

def WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))

law WL.wh.hE2:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))) == True{} : Bool}

def WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))

law WL.wh.hE3:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))) == True{} : Bool}

def WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))))

law WL.wh.hk:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))) == True{} : Bool}

def WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))

law WL.wh.hB:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_lt(BIGs, 2147483648) == True{} : Bool}

def WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))))))

law WL.wh.hwok:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe) == True{} : Bool}

def WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))))

law WL.wh.hH:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))) == True{} : Bool}

def WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))))))))

law WL.wh.hEs:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))) == True{} : Bool}

def WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))))))

law WL.wh.ha:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))) == True{} : Bool}

def WL.wh.ha(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))))))))))

law WL.wh.hS:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_le(WS_.WS.slen(E), S) == True{} : Bool}

def WL.wh.hS(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))))))))

law WL.wh.h5:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_le(w0, 2147483648) == True{} : Bool}

def WL.wh.h5(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h))))))))))))

law WL.wh.h6:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)) == True{} : Bool}

def WL.wh.h6(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_l(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648), P.Bool.and_r(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))))))))))

law WL.wh.hEo:
  for +E: N.EK
  for +w0: U32
  for +Eb: U32
  for +BIGs: U32
  for +Et: U32
  for +Es: U32
  for +BIGe: U32
  for +HB: U32
  for +Ea: U32
  for +S: U32
  for +Eo: U32
  for +h: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  {U32.is_lt(Eo, 2147483648) == True{} : Bool}

def WL.wh.hEo(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, h):
  P.Bool.and_r(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648), P.Bool.and_r(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)), P.Bool.and_r(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))), P.Bool.and_r(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))), P.Bool.and_r(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648)))))))))))), P.Bool.and_r(U32.is_le(w0, WS_.WS.w1(E, w0)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), 4n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(Eb))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), V.U.N(BIGs))), Bool.and(U32.is_lt(BIGs, 2147483648), Bool.and(WS_.WS.wokv(w0, WS_.WS.w1(E, w0), Et, BIGe), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.slen(E)), V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))), V.U.N(HB))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(WS_.WS.slen(E)), V.U.N(Es))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), V.U.N(w0)), V.U.N(Ea))), Bool.and(U32.is_le(WS_.WS.slen(E), S), Bool.and(U32.is_le(w0, 2147483648), Bool.and(U32.is_le(U32.sub(WS_.WS.w1(E, w0), w0), U32.sub(2147483648, w0)), U32.is_lt(Eo, 2147483648))))))))))))), h)))))))))))))

law WL.es_e:
  for +s: WS_.EST
  for +h: {WP_.WP.esok(s) == True{} : Bool}
  {WS_.WS.eok(WS_.WS.ee(s)) == True{} : Bool}

def WL.es_e(s, h):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      P.Bool.and_l(WS_.WS.eok(e), Bool.and(WP_.WP.bok(tio), WP_.WP.ook(to)), h)

law WL.es_b:
  for +s: WS_.EST
  for +h: {WP_.WP.esok(s) == True{} : Bool}
  {WP_.WP.bok(WS_.WS.tio(s)) == True{} : Bool}

def WL.es_b(s, h):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      P.Bool.and_l(WP_.WP.bok(tio), WP_.WP.ook(to), P.Bool.and_r(WS_.WS.eok(e), Bool.and(WP_.WP.bok(tio), WP_.WP.ook(to)), h))

law WL.es_o:
  for +s: WS_.EST
  for +h: {WP_.WP.esok(s) == True{} : Bool}
  {WP_.WP.ook(WS_.WS.to(s)) == True{} : Bool}

def WL.es_o(s, h):
  match s:
    case WS_.EST{tl, tb, tv, tio, e, to, olen, lidx, cont}:
      P.Bool.and_r(WP_.WP.bok(tio), WP_.WP.ook(to), P.Bool.and_r(WS_.WS.eok(e), Bool.and(WP_.WP.bok(tio), WP_.WP.ook(to)), h))

# The buffer's three facts.
law WL.bok_pf:
  for +t: A.Tr
  for +h: {WP_.WP.bok(t) == True{} : Bool}
  {A.T.pf(SC_.SC.dep(t), t) == True{} : Bool}

def WL.bok_pf(t, h):
  P.Bool.and_l(A.T.pf(SC_.SC.dep(t), t), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t))))), h)

law WL.bok_lt:
  for +t: A.Tr
  for +h: {WP_.WP.bok(t) == True{} : Bool}
  {Nat.cmp(SC_.SC.dep(t), 32n) == LT{} : Cmp}

def WL.bok_lt(t, h):
  SC_.SC.ltc(Nat.cmp(SC_.SC.dep(t), 32n), P.Bool.and_l(Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t)))), P.Bool.and_r(A.T.pf(SC_.SC.dep(t), t), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t))))), h)))

law WL.bok_3:
  for +t: A.Tr
  for +h: {WP_.WP.bok(t) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t)))) == True{} : Bool}

def WL.bok_3(t, h):
  P.Bool.and_r(Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t)))), P.Bool.and_r(A.T.pf(SC_.SC.dep(t), t), Bool.and(Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), Cmp.is_le(Nat.cmp(3n, P.Nat.pow2(SC_.SC.dep(t))))), h))

law WL.ook_pf:
  for +t: A.Tr
  for +h: {WP_.WP.ook(t) == True{} : Bool}
  {A.T.pf(SC_.SC.dep(t), t) == True{} : Bool}

def WL.ook_pf(t, h):
  P.Bool.and_l(A.T.pf(SC_.SC.dep(t), t), Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), h)

law WL.ook_lt:
  for +t: A.Tr
  for +h: {WP_.WP.ook(t) == True{} : Bool}
  {Nat.cmp(SC_.SC.dep(t), 32n) == LT{} : Cmp}

def WL.ook_lt(t, h):
  SC_.SC.ltc(Nat.cmp(SC_.SC.dep(t), 32n), P.Bool.and_r(A.T.pf(SC_.SC.dep(t), t), Cmp.is_lt(Nat.cmp(SC_.SC.dep(t), 32n)), h))

# The sections, from the end-of-window facts.
law WL.secs_F:
  for +e: EM_.ET
  for +g: EM_.EG
  for +w: EM_.EW
  for +hF: {EI_.EI.F(e, g, w) == True{} : Bool}
  {WP_.WP.secs(e, g) == True{} : Bool}

def WL.secs_F(e, g, w, hF):
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      SC_.SC.and_tt(EM_.EM.S1(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, Q.SP.halves(ops)), Bool.and(EM_.EM.S2(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, ops), EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, Q.SP.halves(ops))), WP_.WP.F0_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, w, hF), SC_.SC.and_tt(EM_.EM.S2(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, ops), EM_.EM.S3(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, Q.SP.halves(ops)), WP_.WP.F1_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, w, hF), WP_.WP.F2_ok(EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc}, EM_.EG{ops, ph, dd, di, da}, w, hF)))

# A window's length in the target.
law WL.wtl:
  for +cpl: U32
  for +off: U32
  for +tlen: U32
  for +tt: A.Tr
  for +w0: U32
  for +e: EM_.ET
  for +g: EM_.EG
  {Q.SP.wtl(WP_.WP.aw(cpl, off, tlen, tt, w0, e, g)) == tlen : U32}

def WL.wtl(cpl, off, tlen, tt, w0, e, g):
  match e g:
    case EM_.ET{td, ti, ta, tc, dl, il, al, slot, uoff, pt, ps, pm, pc} EM_.EG{ops, ph, dd, di, da}:
      {==}

# A window, in the run

law WL.skw1:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  {SC_.SC.w1(WS_.WS.sk(E, w0, w1)) == w1 : U32}

def WL.skw1(E, w0, w1):
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      {==}

# --------------------

# The window win.enc writes at w0.
def WL.aw(+E: N.EK, +w0: U32, +ts: A.Tr, +tt: A.Tr, +s: WS_.EST) -> Q.AW:
  WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)))

law WL.fin_to:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: SC_.ST
  for +to: A.Tr
  for +olen: U32
  for +lidx: U32
  {WS_.WS.to(WS_.WS.fin(E, w0, w1, tt, e, st, to, olen, lidx)) == WS_.WS.wto(to, olen, tt, w0, U32.sub(w1, w0), WS_.WS.c4(E, w0, w1, tt, e, st), WS_.WS.o4(E, w0, w1, tt, e, st), WS_.WS.e4(E, w0, w1, tt, e, st)) : A.Tr}

def WL.fin_to(E, w0, w1, tt, e, st, to, olen, lidx):
  match E st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law WL.fin_ol:
  for +E: N.EK
  for +w0: U32
  for +w1: U32
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: SC_.ST
  for +to: A.Tr
  for +olen: U32
  for +lidx: U32
  {WS_.WS.olen(WS_.WS.fin(E, w0, w1, tt, e, st, to, olen, lidx)) == WS_.WS.wol(olen, tt, w0, U32.sub(w1, w0), WS_.WS.c4(E, w0, w1, tt, e, st), WS_.WS.o4(E, w0, w1, tt, e, st), WS_.WS.e4(E, w0, w1, tt, e, st)) : U32}

def WL.fin_ol(E, w0, w1, tt, e, st, to, olen, lidx):
  match E st:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} SC_.ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law WL.code:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  {N.win.enc(E, w0, WS_.WS.es(ts, tt, s)) == WS_.WS.es(ts, tt, WS_.WS.enc(E, w0, ts, tt, s)) : N.ES}

def WL.code(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud):
  WS_.WS.enc_code(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Eo, Ea, WL.es_e(s, hes), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.ha(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WP_.WP.eok3(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.hbv_of(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Eo, WL.secs_F(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), EM_.EW{Q.XC{ts, tt, Q.SP.wseg(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0)}, Et, Es, A.A.to(D.ct.table()), BIGe}, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)))))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo), MT_.MT.add_le(V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))))), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)))))), C.CP.le_refl(V.U.N(WS_.WS.olen(s))), WL.wbb_of(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, ts, w0, WS_.WS.w1(E, w0), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Et, Es, BIGe, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.uowin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))), hbud)))

law WL.esok:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  {WP_.WP.esok(WS_.WS.enc(E, w0, ts, tt, s)) == True{} : Bool}

def WL.esok(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud):
  WP_.WP.esok_fin(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.es_o(s, hes))

law WL.out:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  for +OUT: List<&2, U32>
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {S.S.has(K.WD.app(OUT, Q.SP.wb(WL.aw(E, w0, ts, tt, s))), WS_.WS.to(WS_.WS.enc(E, w0, ts, tt, s)), 0) == True{} : Bool}

def WL.out(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud, OUT, hO, hOl):
  (%Equal.sym(A.Tr, WS_.WS.to(WS_.WS.fin(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))), WS_.WS.wto(WS_.WS.to(s), WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WL.fin_to(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))) : {S.S.has(K.WD.app(OUT, Q.SP.wb(WL.aw(E, w0, ts, tt, s))), _, 0) == True{} : Bool};
    WP_.WP.wout(WS_.WS.to(s), SC_.SC.dep(WS_.WS.to(s)), OUT, WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Eo, WL.ook_pf(WS_.WS.to(s), WL.es_o(s, hes)), WL.ook_lt(WS_.WS.to(s), WL.es_o(s, hes)), hO, hOl, WL.secs_F(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), EM_.EW{Q.XC{ts, tt, Q.SP.wseg(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0)}, Et, Es, A.A.to(D.ct.table()), BIGe}, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))), WL.hbv_of(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Eo, WL.secs_F(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), EM_.EW{Q.XC{ts, tt, Q.SP.wseg(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0)}, Et, Es, A.A.to(D.ct.table()), BIGe}, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)))))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo), MT_.MT.add_le(V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))))), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)))))), C.CP.le_refl(V.U.N(WS_.WS.olen(s))), WL.wbb_of(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, ts, w0, WS_.WS.w1(E, w0), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Et, Es, BIGe, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.uowin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))), hbud)), WL.wh.hEo(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))

law WL.len:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  for +OUT: List<&2, U32>
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {S.S.len(K.WD.app(OUT, Q.SP.wb(WL.aw(E, w0, ts, tt, s)))) == V.U.N(WS_.WS.olen(WS_.WS.enc(E, w0, ts, tt, s))) : Nat}

def WL.len(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud, OUT, hO, hOl):
  (%Equal.sym(U32, WS_.WS.olen(WS_.WS.fin(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))), WS_.WS.wol(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WL.fin_ol(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))) : {S.S.len(K.WD.app(OUT, Q.SP.wb(WL.aw(E, w0, ts, tt, s)))) == V.U.N(_) : Nat};
    WP_.WP.wlen(WS_.WS.to(s), SC_.SC.dep(WS_.WS.to(s)), OUT, WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Eo, WL.ook_pf(WS_.WS.to(s), WL.es_o(s, hes)), WL.ook_lt(WS_.WS.to(s), WL.es_o(s, hes)), hO, hOl, WL.secs_F(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), EM_.EW{Q.XC{ts, tt, Q.SP.wseg(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0)}, Et, Es, A.A.to(D.ct.table()), BIGe}, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))), WL.hbv_of(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Eo, WL.secs_F(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), EM_.EW{Q.XC{ts, tt, Q.SP.wseg(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0)}, Et, Es, A.A.to(D.ct.table()), BIGe}, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)))))), Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo), MT_.MT.add_le(V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WP_.WP.aw(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))))), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)))))), C.CP.le_refl(V.U.N(WS_.WS.olen(s))), WL.wbb_of(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, ts, w0, WS_.WS.w1(E, w0), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Et, Es, BIGe, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.uowin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))), hbud)), WL.wh.hEo(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))

law WL.pos:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  {WS_.WS.olen(WS_.WS.enc(E, w0, ts, tt, s)) == Q.SP.wnd(WS_.WS.olen(s), WL.aw(E, w0, ts, tt, s)) : U32}

def WL.pos(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud):
  (%Equal.sym(U32, WS_.WS.olen(WS_.WS.fin(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))), WS_.WS.wol(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))), WL.fin_ol(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), WS_.WS.to(s), WS_.WS.olen(s), WS_.WS.lid0(E, w0, WS_.WS.w1(E, w0), ts, tt, s))) : {_ == Q.SP.wnd(WS_.WS.olen(s), WL.aw(E, w0, ts, tt, s)) : U32};
    WP_.WP.wnd(WS_.WS.olen(s), tt, w0, U32.sub(WS_.WS.w1(E, w0), w0), WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s))))

law WL.wok:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))), V.U.N(Eo))) == True{} : Bool}
  {Q.SP.wok(WL.aw(E, w0, ts, tt, s), ts, tt, S, w0, A.A.to(D.ct.table()), Et, Es) == True{} : Bool}

def WL.wok(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes, hbud):
  WP_.WP.wokd(WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), ts, tt, WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), w0, WS_.WS.w1(E, w0), Et, Es, BIGe, S, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.uowin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.awwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), S, SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hS(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.h5(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.h6(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))

law WL.wtlw:
  for +E: N.EK
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {Q.SP.wtl(WL.aw(E, w0, ts, tt, s)) == U32.sub(WS_.WS.w1(E, w0), w0) : U32}

def WL.wtlw(E, w0, ts, tt, s):
  WL.wtl(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, w0, WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)))

# The run of windows
# ------------------

def WL.loop(k: Nat, +E: N.EK, +w0: U32, +ts: A.Tr, +tt: A.Tr, +s: WS_.EST) -> WS_.EST:
  match k E:
    case 0n e:
      s
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))

# The windows it writes.
def WL.ws(k: Nat, +E: N.EK, +w0: U32, +ts: A.Tr, +tt: A.Tr, +s: WS_.EST) -> List<&2, Q.AW>:
  match k E:
    case 0n e:
      []
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s) <> WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))

# A bound on the bytes they take.
def WL.wB(+E: N.EK, +w0: U32) -> Nat:
  Nat.add(41n, Nat.add(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0)), Nat.add(Nat.add(Nat.double(Nat.double(Nat.double(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))), 6n), EM_.EM.k5(V.U.N(U32.sub(WS_.WS.w1(E, w0), w0))))))

def WL.rb(k: Nat, +E: N.EK, +w0: U32) -> Nat:
  match k E:
    case 0n e:
      0n
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      Nat.add(WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)))

# Each window's facts.
def WL.whs(k: Nat, +E: N.EK, +w0: U32, +Eb: U32, +BIGs: U32, +Et: U32, +Es: U32, +BIGe: U32, +HB: U32, +Ea: U32, +S: U32, +Eo: U32) -> Bool:
  match k E:
    case 0n e:
      True{}
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      Bool.and(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo))

law WL.size:
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
  for +hw: {WL.wh(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(S.S.len(Q.SP.wb(WL.aw(E, w0, ts, tt, s))), WL.wB(E, w0))) == True{} : Bool}

def WL.size(E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw, hes):
  WL.wbb_of(WS_.WS.c4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WS_.WS.o4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), tt, ts, w0, WS_.WS.w1(E, w0), WS_.WS.e4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), WP_.WP.g4(E, w0, WS_.WS.w1(E, w0), tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s)), Et, Es, BIGe, WP_.WP.Fwin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WP_.WP.uowin4(E, w0, WS_.WS.w1(E, w0), ts, tt, WS_.WS.ee(s), WS_.WS.stF(E, w0, ts, tt, s), Et, Es, BIGe, HB, WL.es_e(s, hes), SC_.SC.loop_inv(U32.to_nat(U32.add(U32.sub(WS_.WS.w1(E, w0), w0), 2)), ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, SC_.SC.restart(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), tt, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), SC_.SC.restart_inv(ts, tt, EM_.EM.reset(w0, WS_.WS.ee(s)), WS_.WS.sk(E, w0, WS_.WS.w1(E, w0)), Eb, BIGs, WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s), WL.kf(E, WS_.WS.ee(s), w0, WS_.WS.w1(E, w0), Eb, BIGs, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hE3(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WS_.WS.inv0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, Eb, BIGs, WL.bok_pf(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_lt(WS_.WS.tio(s), WL.es_b(s, hes)), WL.bok_3(WS_.WS.tio(s), WL.es_b(s, hes)), WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), P.Nat.le_trans(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n), V.U.N(Eb), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(WS_.WS.w1(E, w0)), 4n), Nat.add(V.U.N(WS_.WS.w1(E, w0)), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(WS_.WS.w1(E, w0)), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), WL.wh.hE2(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), WL.wh.hE1(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hk(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hB(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)), (%Equal.sym(U32, SC_.SC.w1(WS_.WS.sk(E, w0, WS_.WS.w1(E, w0))), WS_.WS.w1(E, w0), WL.skw1(E, w0, WS_.WS.w1(E, w0))) : {U32.is_le(SC_.SC.pp(WS_.WS.st0(E, w0, WS_.WS.w1(E, w0), ts, tt, s)), _) == True{} : Bool}; WL.pp0(E, w0, WS_.WS.w1(E, w0), ts, tt, s, WL.wh.hw(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw))))), WL.wh.hwok(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hH(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw), WL.wh.hEs(E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, hw)))

# The budget after a window.
law WL.nbud:
  for +ol: Nat
  for +l: Nat
  for +b: Nat
  for +r: Nat
  for +ol2: Nat
  for +eo: Nat
  for +he: {ol2 == Nat.add(ol, l) : Nat}
  for +hl: {Cmp.is_le(Nat.cmp(l, b)) == True{} : Bool}
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(ol, Nat.add(b, r)), eo)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(ol2, r), eo)) == True{} : Bool}

def WL.nbud(ol, l, b, r, ol2, eo, he, hl, h):
  %Equal.sym(Nat, ol2, Nat.add(ol, l), he) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, r), eo)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(ol, l), r), Nat.add(ol, Nat.add(l, r)), P.Nat.add_assoc(ol, l, r)) :
    {Cmp.is_le(Nat.cmp(_, eo)) == True{} : Bool}
  P.Nat.le_trans(Nat.add(ol, Nat.add(l, r)), Nat.add(ol, Nat.add(b, r)), eo, MT_.MT.add_le(ol, ol, Nat.add(l, r), Nat.add(b, r), C.CP.le_refl(ol), MT_.MT.add_le(l, b, r, r, hl, C.CP.le_refl(r))), h)

# A window's own budget, from the run's.
law WL.bud1:
  for +ol: Nat
  for +b: Nat
  for +r: Nat
  for +eo: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.add(ol, Nat.add(b, r)), eo)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(ol, b), eo)) == True{} : Bool}

def WL.bud1(ol, b, r, eo, h):
  P.Nat.le_trans(Nat.add(ol, b), Nat.add(ol, Nat.add(b, r)), eo, MT_.MT.add_le(ol, ol, b, Nat.add(b, r), C.CP.le_refl(ol), P.Nat.cmp_add_r(b, r)), h)

law WL.olen_next:
  for +OUT: List<&2, U32>
  for +wb: List<&2, U32>
  for +ol: Nat
  for +ol2: Nat
  for +hOl: {S.S.len(OUT) == ol : Nat}
  for +h: {S.S.len(K.WD.app(OUT, wb)) == ol2 : Nat}
  {ol2 == Nat.add(ol, S.S.len(wb)) : Nat}

def WL.olen_next(OUT, wb, ol, ol2, hOl, h):
  %h :
    {_ == Nat.add(ol, S.S.len(wb)) : Nat}
  %Equal.sym(Nat, S.S.len(K.WD.app(OUT, wb)), Nat.add(S.S.len(OUT), S.S.len(wb)), K.WD.len_app(OUT, wb)) :
    {_ == Nat.add(ol, S.S.len(wb)) : Nat}
  %Equal.sym(Nat, S.S.len(OUT), ol, hOl) :
    {Nat.add(_, S.S.len(wb)) == Nat.add(ol, S.S.len(wb)) : Nat}
  {==}

# The run, as code.
law WL.loop_code:
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
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {N.win.loop(k, E, w0, WS_.WS.es(ts, tt, s)) == WS_.WS.es(ts, tt, WL.loop(k, E, w0, ts, tt, s)) : N.ES}

def WL.loop_code(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      {==}
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(N.ES, N.win.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, WS_.WS.es(ts, tt, s)), WS_.WS.es(ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), WL.code(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud))) :
        {N.win.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), _) == WS_.WS.es(ts, tt, WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))) : N.ES}
      WL.loop_code(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))

law WL.loop_es:
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
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {WP_.WP.esok(WL.loop(k, E, w0, ts, tt, s)) == True{} : Bool}

def WL.loop_es(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      hes
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      WL.loop_es(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))

law WL.loop_out:
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
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {S.S.has(K.WD.app(OUT, Q.SP.wbs(WL.ws(k, E, w0, ts, tt, s))), WS_.WS.to(WL.loop(k, E, w0, ts, tt, s)), 0) == True{} : Bool}

def WL.loop_out(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      %Equal.sym(List<&2, U32>, K.WD.app(OUT, []), OUT, K.WD.app_nil(OUT)) :
        {S.S.has(_, WS_.WS.to(s), 0) == True{} : Bool}
      hO
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %K.WD.app_assoc(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), Q.SP.wbs(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))) :
        {S.S.has(_, WS_.WS.to(WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), 0) == True{} : Bool}
      WL.loop_out(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))

law WL.loop_len:
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
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {S.S.len(K.WD.app(OUT, Q.SP.wbs(WL.ws(k, E, w0, ts, tt, s)))) == V.U.N(WS_.WS.olen(WL.loop(k, E, w0, ts, tt, s))) : Nat}

def WL.loop_len(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      %Equal.sym(List<&2, U32>, K.WD.app(OUT, []), OUT, K.WD.app_nil(OUT)) :
        {S.S.len(_) == V.U.N(WS_.WS.olen(s)) : Nat}
      hOl
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %K.WD.app_assoc(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), Q.SP.wbs(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))) :
        {S.S.len(_) == V.U.N(WS_.WS.olen(WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)))) : Nat}
      WL.loop_len(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))

law WL.loop_pos:
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
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  {WS_.WS.olen(WL.loop(k, E, w0, ts, tt, s)) == Q.SP.wend(WL.ws(k, E, w0, ts, tt, s), WS_.WS.olen(s)) : U32}

def WL.loop_pos(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, hws, hes, hbud, hO, hOl):
  match k E:
    case 0n e:
      {==}
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %WL.pos(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)) :
        {WS_.WS.olen(WL.loop(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))) == Q.SP.wend(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), _) : U32}
      WL.loop_pos(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl))

def WL.tl(+E: N.EK) -> U32:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      tlen

def WL.wz(+E: N.EK) -> U32:
  match E:
    case N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      wsz

# The next window starts where this one ends.
law WL.onext:
  for +E: N.EK
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  {U32.add(w0, Q.SP.wtl(WL.aw(E, w0, ts, tt, s))) == WS_.WS.w1(E, w0) : U32}

def WL.onext(E, w0, ts, tt, s):
  %Equal.sym(U32, Q.SP.wtl(WL.aw(E, w0, ts, tt, s)), U32.sub(WS_.WS.w1(E, w0), w0), WL.wtlw(E, w0, ts, tt, s)) :
    {U32.add(w0, _) == WS_.WS.w1(E, w0) : U32}
  SC_.SC.addsub(w0, WS_.WS.w1(E, w0))

# Where the run's windows end in the target.
law WL.loop_wop:
  for +q: Nat
  for +E: N.EK
  for +w0: U32
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: WS_.EST
  for +cend: U32
  for +ht: {WL.tile(1n+q, w0, cend, WL.tl(E), WL.wz(E)) == True{} : Bool}
  {Q.SP.wop(WL.ws(1n+q, E, w0, ts, tt, s), w0) == cend : U32}

def WL.loop_wop(q, E, w0, ts, tt, s, cend, ht):
  match q E:
    case 0n N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(U32, U32.add(w0, Q.SP.wtl(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.onext(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)) :
        {_ == cend : U32}
      V.U.is_eq(WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), cend, P.Bool.and_l(WL.last(0n, w0, cend, tlen, wsz), WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(0n, w0, cend, tlen, wsz), WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(0n, w0, cend, tlen, wsz), WL.tile(0n, U32.add(w0, wsz), cend, tlen, wsz))), ht))))
    case 1n+r N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(U32, U32.add(w0, Q.SP.wtl(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.onext(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)) :
        {Q.SP.wop(WL.ws(1n+r, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), _) == cend : U32}
      %Equal.sym(U32, WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), U32.add(w0, wsz), WL.wnext(tlen, w0, wsz, P.Bool.and_l(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz))), ht))))) :
        {Q.SP.wop(WL.ws(1n+r, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), _) == cend : U32}
      WL.loop_wop(r, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), cend, P.Bool.and_r(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(1n+r, w0, cend, tlen, wsz), WL.tile(1n+r, U32.add(w0, wsz), cend, tlen, wsz))), ht))))

# The rest of the run starts where the window ends: the window is whole,
# or there is no rest.
law WL.wsok_rest:
  for +p: Nat
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
  for +S: U32
  for +Et: U32
  for +Es: U32
  for +cend: U32
  for +hl: {WL.last(p, w0, cend, tlen, wsz) == True{} : Bool}
  for +ih: {Q.SP.wsok(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), ts, tt, S, U32.add(w0, wsz), A.A.to(D.ct.table()), Et, Es) == True{} : Bool}
  {Q.SP.wsok(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), ts, tt, S, U32.add(w0, Q.SP.wtl(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), A.A.to(D.ct.table()), Et, Es) == True{} : Bool}

def WL.wsok_rest(p, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, ts, tt, s, S, Et, Es, cend, hl, ih):
  match p:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(U32, U32.add(w0, Q.SP.wtl(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.onext(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)) :
        {Q.SP.wsok(WL.ws(1n+r, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), ts, tt, S, _, A.A.to(D.ct.table()), Et, Es) == True{} : Bool}
      %Equal.sym(U32, WS_.WS.w1(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), U32.add(w0, wsz), WL.wnext(tlen, w0, wsz, hl)) :
        {Q.SP.wsok(WL.ws(1n+r, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), ts, tt, S, _, A.A.to(D.ct.table()), Et, Es) == True{} : Bool}
      ih

# Every window of the run is a window the decoder rebuilds the target with.
law WL.loop_wsok:
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
  for +cend: U32
  for +hws: {WL.whs(k, E, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo) == True{} : Bool}
  for +hes: {WP_.WP.esok(s) == True{} : Bool}
  for +hbud: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(WS_.WS.olen(s)), WL.rb(k, E, w0)), V.U.N(Eo))) == True{} : Bool}
  for +hO: {S.S.has(OUT, WS_.WS.to(s), 0) == True{} : Bool}
  for +hOl: {S.S.len(OUT) == V.U.N(WS_.WS.olen(s)) : Nat}
  for +ht: {WL.tile(k, w0, cend, WL.tl(E), WL.wz(E)) == True{} : Bool}
  {Q.SP.wsok(WL.ws(k, E, w0, ts, tt, s), ts, tt, S, w0, A.A.to(D.ct.table()), Et, Es) == True{} : Bool}

def WL.loop_wsok(k, E, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, OUT, cend, hws, hes, hbud, hO, hOl, ht):
  match k E:
    case 0n e:
      {==}
    case 1n+p N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      SC_.SC.and_tt(Q.SP.wok(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), ts, tt, S, w0, A.A.to(D.ct.table()), Et, Es), Q.SP.wsok(WL.ws(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), ts, tt, S, U32.add(w0, Q.SP.wtl(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), A.A.to(D.ct.table()), Et, Es), WL.wok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.wsok_rest(p, slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap, w0, ts, tt, s, S, Et, Es, cend, P.Bool.and_l(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz))), ht))), WL.loop_wsok(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), ts, tt, WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, K.WD.app(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), cend, P.Bool.and_r(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), WL.esok(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud)), WL.nbud(V.U.N(WS_.WS.olen(s)), S.S.len(Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), V.U.N(Eo), WL.olen_next(OUT, Q.SP.wb(WL.aw(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s)), V.U.N(WS_.WS.olen(s)), V.U.N(WS_.WS.olen(WS_.WS.enc(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s))), hOl, WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl)), WL.size(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes), hbud), WL.out(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), WL.len(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, ts, tt, s, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo, P.Bool.and_l(WL.wh(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0, Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), WL.whs(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz), Eb, BIGs, Et, Es, BIGe, HB, Ea, S, Eo), hws), hes, WL.bud1(V.U.N(WS_.WS.olen(s)), WL.wB(N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, w0), WL.rb(p, N.EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}, U32.add(w0, wsz)), V.U.N(Eo), hbud), OUT, hO, hOl), P.Bool.and_r(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz), P.Bool.and_r(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz)), P.Bool.and_r(U32.is_le(w0, tlen), Bool.and(U32.is_le(w0, U32.add(w0, wsz)), Bool.and(WL.last(p, w0, cend, tlen, wsz), WL.tile(p, U32.add(w0, wsz), cend, tlen, wsz))), ht))))))
