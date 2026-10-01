import Base
import ../bytes.bend as B
import ../vcdiff.bend as D
import ./nat.bend as P
import ./u32.bend as V
import ./array.bend as A
import ./bytes.bend as Y
import ./seq.bend as S
import ./words.bend as K
import ./copy.bend as C
import ./varint.bend as R
import ./adler.bend as H

# What a window of a delta says: its instructions (each half of an opcode
# of the code table), the bytes they put in the window's three sections,
# and when they rebuild a target's bytes. The decoder's proof reads a
# window through these, and the encoder's proof writes them.
#
# Source: proofs/spec.bp (tools/bpp.py writes proofs/spec.bend from it).

# Instructions
# ============

# One half of an opcode: no instruction, an ADD of the bytes xs, a RUN of
# n copies of b, or a COPY of n bytes whose address is v in mode m.
type HF is Data:
  HN{}
  HA{n: U32, xs: List<&2, U32>}
  HR{n: U32, b: U32}
  HC{n: U32, m: U32, v: U32}

# An opcode and its two halves.
type OP is Data:
  OP{c: U32, h1: HF, h2: HF}

def SP.kind(+h: HF) -> U32:
  match h:
    case HN{}:
      0
    case HA{n, xs}:
      1
    case HR{n, b}:
      2
    case HC{n, m, v}:
      3

def SP.size(+h: HF) -> U32:
  match h:
    case HN{}:
      0
    case HA{n, xs}:
      n
    case HR{n, b}:
      n
    case HC{n, m, v}:
      n

def SP.mode(+h: HF) -> U32:
  match h:
    case HN{}:
      0
    case HA{n, xs}:
      0
    case HR{n, b}:
      0
    case HC{n, m, v}:
      m

# The code table's halves: type, size (0: in the instruction section) and
# address mode, as the decoder unpacks them.
def SP.ht(+h: U32) -> U32:
  (h .&. 3 : U32)

def SP.hs(+h: U32) -> U32:
  ((h >> 2n : U32) .&. 255 : U32)

def SP.hm(+h: U32) -> U32:
  ((h >> 10n : U32) .&. 15 : U32)

def SP.e1(+c: U32) -> U32:
  (D.ct.entry(c) .&. 65535 : U32)

def SP.e2(+c: U32) -> U32:
  (D.ct.entry(c) >> 16n : U32)

# A table half fits an instruction: the same type, its size (or 0) and
# its mode.
def SP.hok(+h: U32, +f: HF) -> Bool:
  U32.is_eq(SP.ht(h), SP.kind(f))
    && (U32.is_eq(SP.hs(h), 0) || U32.is_eq(SP.hs(h), SP.size(f)))
    && (U32.is_ne(SP.kind(f), 3) || U32.is_eq(SP.hm(h), SP.mode(f)))

# An opcode fits its halves, and the table tb holds the code table's entry
# for it (the decoder's table, as a tree).
def SP.cok(+tb: A.Tr, +o: OP) -> Bool:
  match o:
    case OP{c, h1, h2}:
      (c < 256 : U32) && U32.is_eq(A.T.word(tb, c), D.ct.entry(c))
        && SP.hok(SP.e1(c), h1) && SP.hok(SP.e2(c), h2)

# Sections
# ========

# The size of a half, in the instruction section when its table half has
# size 0.
# Whether a table half takes its size from the instruction section.
def SP.z(+h: U32) -> Bool:
  U32.is_eq(SP.hs(h), 0) && U32.is_ne(SP.ht(h), 0)

def SP.sz(+h: U32, +f: HF) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, SP.z(h), R.VI.var(SP.size(f)), [])

# The instruction section position after the size of a half.
def SP.ipos(+h: U32, +f: HF, +ipos: U32) -> U32:
  Bool.pick(U32, SP.z(h), (ipos + B.B.var.len(SP.size(f)) : U32), ipos)

def SP.ins(+o: OP) -> List<&2, U32>:
  match o:
    case OP{c, h1, h2}:
      c <> K.WD.app(SP.sz(SP.e1(c), h1), SP.sz(SP.e2(c), h2))

def SP.insl(+os: List<&2, OP>) -> List<&2, U32>:
  match os:
    case []:
      []
    case o <> r:
      K.WD.app(SP.ins(o), SP.insl(r))

def SP.halves(+os: List<&2, OP>) -> List<&2, HF>:
  match os:
    case []:
      []
    case o <> r:
      match o:
        case OP{c, h1, h2}:
          h1 <> h2 <> SP.halves(r)

# The data a half takes from the data section.
def SP.dat(+h: HF) -> List<&2, U32>:
  match h:
    case HN{}:
      []
    case HA{n, xs}:
      xs
    case HR{n, b}:
      b <> []
    case HC{n, m, v}:
      []

def SP.datl(+hs: List<&2, HF>) -> List<&2, U32>:
  match hs:
    case []:
      []
    case h <> r:
      K.WD.app(SP.dat(h), SP.datl(r))

# The address a half takes from the address section: a varint, or a byte
# for the SAME modes.
def SP.adr.m(z: Bool, +v: U32) -> List<&2, U32>:
  match z:
    case True{}:
      R.VI.var(v)
    case False{}:
      v <> []

def SP.adr(+h: HF) -> List<&2, U32>:
  match h:
    case HN{}:
      []
    case HA{n, xs}:
      []
    case HR{n, b}:
      []
    case HC{n, m, v}:
      SP.adr.m((m < 6 : U32), v)

def SP.adrl(+hs: List<&2, HF>) -> List<&2, U32>:
  match hs:
    case []:
      []
    case h <> r:
      K.WD.app(SP.adr(h), SP.adrl(r))

# What a window's instructions do
# ===============================

# The address cache as a tree: cache.put writes the NEAR slot, then the
# SAME slot.
def SP.cput(+c: A.Tr, +slot: U32, +addr: U32) -> A.Tr:
  A.T.set(A.T.set(c, (768 + slot : U32), addr), (addr % 768 : U32), addr)

# The address a COPY's value v names in mode m, here being the address of
# the bytes it writes (dec.copy.v and dec.addr.c).
def SP.daddr(+m: U32, +v: U32, +here: U32, +c: A.Tr) -> U32:
  +idx = B.u32.pick((m < 6 : U32), (766 + m : U32), (((m - 6 : U32) * 256 : U32) + (v .&. 255 : U32) : U32))
  +w = A.T.word(c, idx)
  B.u32.pick(U32.is_eq(m, 0), v, B.u32.pick(U32.is_eq(m, 1), (here - v : U32), B.u32.pick((m < 6 : U32), (w + v : U32), w)))

def SP.aok(+m: U32, +v: U32, +here: U32) -> Bool:
  (m < 9 : U32) && Bool.or(U32.is_ne(m, 1), (v <= here : U32))

# A window: the source and target (as trees), its copy segment in the
# source (start, length), and where it starts and ends in the target.
type XC is Data:
  XC{ts: A.Tr, tt: A.Tr, seg: U32, cpl: U32, wst: U32, oend: U32}

def SP.lenis(+xs: List<&2, U32>, +n: U32) -> Bool:
  Cmp.is_eq(Nat.cmp(S.S.len(xs), U32.to_nat(n)))

# A copy of n bytes from the window address addr rebuilds the target at
# opos: from the segment, or from earlier in the target window.
def SP.cpok(+x: XC, +opos: U32, +n: U32, +addr: U32) -> Bool:
  match x:
    case XC{ts, tt, seg, +cpl, wst, oend}:
      Bool.pick(Bool, (addr < cpl : U32),
        (n <= (cpl - addr : U32) : U32) && S.S.has(S.S.sl(U32.to_nat(n), ts, (seg + addr : U32)), tt, opos),
        S.S.has(S.S.sl(U32.to_nat(n), tt, (wst + (addr - cpl : U32) : U32)), tt, opos))

def SP.here(+x: XC, +opos: U32) -> U32:
  match x:
    case XC{ts, tt, seg, cpl, wst, oend}:
      (cpl + (opos - wst : U32) : U32)

def SP.room(+x: XC, +opos: U32, +n: U32) -> Bool:
  match x:
    case XC{ts, tt, seg, cpl, wst, oend}:
      (n <= (oend - opos : U32) : U32)

def SP.tt(+x: XC) -> A.Tr:
  match x:
    case XC{ts, tt, seg, cpl, wst, oend}:
      tt

# A half rebuilds the target's bytes at opos, with the cache c.
def SP.vh(+x: XC, +opos: U32, +c: A.Tr, +h: HF) -> Bool:
  match h:
    case HN{}:
      True{}
    case HA{n, xs}:
      SP.lenis(xs, n) && SP.room(x, opos, n) && S.S.has(xs, SP.tt(x), opos)
    case HR{n, b}:
      SP.room(x, opos, n) && S.S.has(C.CP.rep(U32.to_nat(n), b), SP.tt(x), opos)
    case HC{n, m, v}:
      SP.aok(m, v, SP.here(x, opos))
        && (SP.daddr(m, v, SP.here(x, opos), c) < SP.here(x, opos) : U32)
        && SP.room(x, opos, n)
        && SP.cpok(x, opos, n, SP.daddr(m, v, SP.here(x, opos), c))

# The decoder's state after a half: the target position, cache and slot.
type ST is Data:
  ST{opos: U32, c: A.Tr, slot: U32}

def SP.next(+x: XC, +s: ST, +h: HF) -> ST:
  match s h:
    case ST{opos, c, slot} HN{}:
      ST{opos, c, slot}
    case ST{opos, c, slot} HA{n, xs}:
      ST{(opos + n : U32), c, slot}
    case ST{opos, c, slot} HR{n, b}:
      ST{(opos + n : U32), c, slot}
    case ST{opos, c, slot} HC{n, m, v}:
      ST{(opos + n : U32), SP.cput(c, slot, SP.daddr(m, v, SP.here(x, opos), c)),
        ((slot + 1 : U32) .&. 3 : U32)}

def SP.vst(+x: XC, +s: ST, +h: HF) -> Bool:
  match s:
    case ST{opos, c, slot}:
      SP.vh(x, opos, c, h)

# Every half in turn rebuilds the target, and the state after them.
def SP.vhs(+hs: List<&2, HF>, +x: XC, +s: ST) -> Bool:
  match hs:
    case []:
      True{}
    case h <> r:
      SP.vst(x, s, h) && SP.vhs(r, x, SP.next(x, s, h))

def SP.run(+hs: List<&2, HF>, +x: XC, +s: ST) -> ST:
  match hs:
    case []:
      s
    case h <> r:
      SP.run(r, x, SP.next(x, s, h))

# The address section position after a half.
def SP.anext(+f: HF, +apos: U32) -> U32:
  match f:
    case HN{}:
      apos
    case HA{n, xs}:
      apos
    case HR{n, b}:
      apos
    case HC{n, m, v}:
      Bool.pick(U32, (m < 6 : U32), (apos + B.B.var.len(v) : U32), (apos + 1 : U32))

# The data section position after a half.
def SP.dnext(+f: HF, +dpos: U32) -> U32:
  match f:
    case HN{}:
      dpos
    case HA{n, xs}:
      (dpos + n : U32)
    case HR{n, b}:
      (dpos + 1 : U32)
    case HC{n, m, v}:
      dpos

# The target after a half's copy from window address addr.
def SP.cout(+x: XC, +to: A.Tr, +opos: U32, +n: U32, +addr: U32) -> A.Tr:
  match x:
    case XC{ts, tt, +seg, +cpl, +wst, oend}:
      Bool.pick(A.Tr, (addr < cpl : U32), S.S.puts(S.S.sl(U32.to_nat(n), ts, (seg + addr : U32)), to, opos),
        C.CP.mv(U32.to_nat(n), to, opos, (wst + (addr - cpl : U32) : U32)))

# The target after a half.
def SP.out(+x: XC, +to: A.Tr, +s: ST, +f: HF) -> A.Tr:
  match s f:
    case ST{opos, c, slot} HN{}:
      to
    case ST{opos, c, slot} HA{n, xs}:
      S.S.puts(xs, to, opos)
    case ST{opos, c, slot} HR{n, b}:
      S.S.puts(C.CP.rep(U32.to_nat(n), b), to, opos)
    case ST{opos, c, slot} HC{n, m, v}:
      SP.cout(x, to, opos, n, SP.daddr(m, v, SP.here(x, opos), c))

def SP.so(+s: ST) -> U32:
  match s:
    case ST{opos, c, slot}:
      opos

def SP.sc(+s: ST) -> A.Tr:
  match s:
    case ST{opos, c, slot}:
      c

def SP.ss(+s: ST) -> U32:
  match s:
    case ST{opos, c, slot}:
      slot

# The bound a COPY's copy needs: its source bytes below E, or its target
# bytes before its destination.
def SP.cbnd(+x: XC, +opos: U32, +n: U32, +addr: U32, +E: U32) -> Bool:
  match x:
    case XC{ts, tt, +seg, +cpl, +wst, oend}:
      Bool.pick(Bool, (addr < cpl : U32),
        Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(n), U32.to_nat((seg + addr : U32))), U32.to_nat(E))),
        Cmp.is_lt(Nat.cmp(U32.to_nat((wst + (addr - cpl : U32) : U32)), U32.to_nat(opos))))

def SP.hbnd(+x: XC, +s: ST, +f: HF, +E: U32) -> Bool:
  match s f:
    case ST{opos, c, slot} HN{}:
      True{}
    case ST{opos, c, slot} HA{n, xs}:
      True{}
    case ST{opos, c, slot} HR{n, b}:
      True{}
    case ST{opos, c, slot} HC{n, m, v}:
      SP.cbnd(x, opos, n, SP.daddr(m, v, SP.here(x, opos), c), E)

# The tree t holds xs at q, ending by e.
def SP.at(+xs: List<&2, U32>, +t: A.Tr, +q: U32, +e: U32) -> Bool:
  S.S.has(xs, t, q) && Cmp.is_le(Nat.cmp(Nat.add(S.S.len(xs), U32.to_nat(q)), U32.to_nat(e)))

# What a half of an ADD needs of its data: as many bytes as its size.
def SP.dok(+f: HF) -> Bool:
  match f:
    case HN{}:
      True{}
    case HA{n, xs}:
      SP.lenis(xs, n)
    case HR{n, b}:
      True{}
    case HC{n, m, v}:
      True{}

# A window's halves in turn
# =========================

def SP.outs(+hs: List<&2, HF>, +x: XC, +to: A.Tr, +s: ST) -> A.Tr:
  match hs:
    case []:
      to
    case h <> r:
      SP.outs(r, x, SP.out(x, to, s, h), SP.next(x, s, h))

def SP.dnexts(+hs: List<&2, HF>, +dpos: U32) -> U32:
  match hs:
    case []:
      dpos
    case h <> r:
      SP.dnexts(r, SP.dnext(h, dpos))

def SP.anexts(+hs: List<&2, HF>, +apos: U32) -> U32:
  match hs:
    case []:
      apos
    case h <> r:
      SP.anexts(r, SP.anext(h, apos))

def SP.doks(+hs: List<&2, HF>) -> Bool:
  match hs:
    case []:
      True{}
    case h <> r:
      SP.dok(h) && SP.doks(r)

def SP.coks(+os: List<&2, OP>, +tb: A.Tr) -> Bool:
  match os:
    case []:
      True{}
    case o <> r:
      SP.cok(tb, o) && SP.coks(r, tb)

# The bounds each half's copy needs, below E.
# (E bounds the target, Es the source.)
def SP.bnd(+x: XC, +s: ST, +f: HF, +E: U32, +Es: U32) -> Bool:
  Cmp.is_le(Nat.cmp(Nat.add(U32.to_nat(SP.size(f)), U32.to_nat(SP.so(s))), U32.to_nat(E)))
    && SP.hbnd(x, s, f, Es)

def SP.bnds(+hs: List<&2, HF>, +x: XC, +s: ST, +E: U32, +Es: U32) -> Bool:
  match hs:
    case []:
      True{}
    case h <> r:
      SP.bnd(x, s, h, E, Es) && SP.bnds(r, x, SP.next(x, s, h), E, Es)

# Windows
# =======

# A window as the encoder writes it: the copy segment (length, offset), the
# target length, the section lengths, the opcodes and the checksum.
type AW is Data:
  AW{cpl: U32, off: U32, tlen: U32, dl: U32, il: U32, al: U32, ops: List<&2, OP>, sum: U32}

def SP.ind(+cpl: U32) -> U32:
  B.u32.pick((0 < cpl : U32), 5, 4)

def SP.segb(+cpl: U32, +off: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, (0 < cpl : U32), K.WD.app(R.VI.var(cpl), R.VI.var(off)), [])

# The length of what follows the delta encoding length.
def SP.enc(+tlen: U32, +dl: U32, +il: U32, +al: U32) -> U32:
  ((((((((1 + B.B.var.len(tlen) : U32) + B.B.var.len(dl) : U32)
    + B.B.var.len(il) : U32) + B.B.var.len(al) : U32) + 4 : U32) + dl : U32)
    + il : U32) + al : U32)

# A big-endian word, as wr.be32 writes it.
def SP.be(+v: U32) -> List<&2, U32>:
  (v >> 24n : U32) <> ((v >> 16n : U32) .&. 255 : U32) <> ((v >> 8n : U32) .&. 255 : U32) <> (v .&. 255 : U32) <> []

# The sections after the header.
def SP.secs(+w: AW) -> List<&2, U32>:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      K.WD.app(SP.datl(SP.halves(ops)), K.WD.app(SP.insl(ops), SP.adrl(SP.halves(ops))))

# The header fields after the delta encoding length.
def SP.hdr2(+w: AW) -> List<&2, U32>:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      K.WD.app(R.VI.var(tlen), 0 <> K.WD.app(R.VI.var(dl), K.WD.app(R.VI.var(il), K.WD.app(R.VI.var(al), SP.be(sum)))))

# A window's bytes.
def SP.wb(+w: AW) -> List<&2, U32>:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      SP.ind(cpl) <> K.WD.app(SP.segb(cpl, off), K.WD.app(R.VI.var(SP.enc(tlen, dl, il, al)),
        K.WD.app(SP.hdr2(AW{cpl, off, tlen, dl, il, al, ops, sum}), SP.secs(AW{cpl, off, tlen, dl, il, al, ops, sum}))))

# Where a window's copy segment starts (0 when it has none).
def SP.wseg(+cpl: U32, +off: U32) -> U32:
  B.u32.pick((0 < cpl : U32), off, 0)

# A window's facts as the decoder sees them: from the target position opos.
def SP.wx(+ts: A.Tr, +tt: A.Tr, +w: AW, +opos: U32) -> XC:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      XC{ts, tt, SP.wseg(cpl, off), cpl, opos, (opos + tlen : U32)}

# The cache at the start of a window: every slot 0.
def SP.c0() -> A.Tr:
  A.T.new(10n, 0)

# A window's state at its start: at opos, with the cache cleared.
def SP.s0(+opos: U32) -> ST:
  ST{opos, A.T.new(10n, 0), 0}

# Where a window starting at pos ends.
def SP.wnd(+pos: U32, +w: AW) -> U32:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      B.u32.pick((0 < cpl : U32),
        (((((pos + 1 : U32) + B.B.var.len(cpl) : U32) + B.B.var.len(off) : U32) + B.B.var.len(SP.enc(tlen, dl, il, al)) : U32) + SP.enc(tlen, dl, il, al) : U32),
        (((pos + 1 : U32) + B.B.var.len(SP.enc(tlen, dl, il, al)) : U32) + SP.enc(tlen, dl, il, al) : U32))

# What makes a window at opos rebuild tt's bytes [opos, opos + tlen): its
# section lengths, its copy segment inside the source (of slen bytes), its
# target inside 2^31 bytes, its opcodes in the code table tb, its halves
# rebuilding the target (inside the bounds E of the target and Es of the
# source), and its checksum.
def SP.wok(+w: AW, +ts: A.Tr, +tt: A.Tr, +slen: U32, +opos: U32, +tb: A.Tr, +E: U32, +Es: U32) -> Bool:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      Bool.and(SP.lenis(SP.datl(SP.halves(ops)), dl),
      Bool.and(SP.lenis(SP.insl(ops), il),
      Bool.and(SP.lenis(SP.adrl(SP.halves(ops)), al),
      Bool.and(Bool.or(Bool.not((0 < cpl : U32)), Bool.and((cpl <= slen : U32), (off <= (slen - cpl : U32) : U32))),
      Bool.and((opos <= 2147483648 : U32),
      Bool.and((tlen <= (2147483648 - opos : U32) : U32),
      Bool.and(SP.coks(ops, tb),
      Bool.and(SP.vhs(SP.halves(ops), SP.wx(ts, tt, AW{cpl, off, tlen, dl, il, al, ops, sum}, opos), SP.s0(opos)),
      Bool.and(SP.doks(SP.halves(ops)),
      Bool.and(SP.bnds(SP.halves(ops), SP.wx(ts, tt, AW{cpl, off, tlen, dl, il, al, ops, sum}, opos), SP.s0(opos), E, Es),
      Bool.and(U32.is_eq(SP.so(SP.run(SP.halves(ops), SP.wx(ts, tt, AW{cpl, off, tlen, dl, il, al, ops, sum}, opos), SP.s0(opos))), (opos + tlen : U32)),
        U32.is_eq(sum, H.AD.T(tt, opos, tlen)))))))))))))

def SP.wtl(+w: AW) -> U32:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      tlen

def SP.wops(+w: AW) -> List<&2, OP>:
  match w:
    case AW{cpl, off, tlen, dl, il, al, ops, sum}:
      ops

# A delta's windows
# =================

def SP.wbs(+ws: List<&2, AW>) -> List<&2, U32>:
  match ws:
    case []:
      []
    case w <> r:
      K.WD.app(SP.wb(w), SP.wbs(r))

def SP.wsok(+ws: List<&2, AW>, +ts: A.Tr, +tt: A.Tr, +slen: U32, +opos: U32, +tb: A.Tr, +E: U32, +Es: U32) -> Bool:
  match ws:
    case []:
      True{}
    case w <> r:
      Bool.and(SP.wok(w, ts, tt, slen, opos, tb, E, Es), SP.wsok(r, ts, tt, slen, (opos + SP.wtl(w) : U32), tb, E, Es))

# Where the windows end in the target.
def SP.wop(+ws: List<&2, AW>, +opos: U32) -> U32:
  match ws:
    case []:
      opos
    case w <> r:
      SP.wop(r, (opos + SP.wtl(w) : U32))

# The target after the windows.
def SP.wto(+ws: List<&2, AW>, +ts: A.Tr, +tt: A.Tr, +to: A.Tr, +opos: U32) -> A.Tr:
  match ws:
    case []:
      to
    case w <> r:
      SP.wto(r, ts, tt, SP.outs(SP.halves(SP.wops(w)), SP.wx(ts, tt, w, opos), to, SP.s0(opos)), (opos + SP.wtl(w) : U32))

# The cache after the windows.
def SP.wca(+ws: List<&2, AW>, +ts: A.Tr, +tt: A.Tr, +ca: A.Tr, +opos: U32) -> A.Tr:
  match ws:
    case []:
      ca
    case w <> r:
      SP.wca(r, ts, tt, SP.sc(SP.run(SP.halves(SP.wops(w)), SP.wx(ts, tt, w, opos), SP.s0(opos))), (opos + SP.wtl(w) : U32))

# Where the windows end in the delta, from pos.
def SP.wend(+ws: List<&2, AW>, +pos: U32) -> U32:
  match ws:
    case []:
      pos
    case w <> r:
      SP.wend(r, SP.wnd(pos, w))

# How many windows.
def SP.nw(+ws: List<&2, AW>) -> Nat:
  match ws:
    case []:
      0n
    case w <> r:
      1n+SP.nw(r)

# A delta: its header (no secondary compression, no code table, no
# application data), then its windows.
def SP.delta(+ws: List<&2, AW>) -> List<&2, U32>:
  214 <> 195 <> 196 <> 0 <> 0 <> SP.wbs(ws)
