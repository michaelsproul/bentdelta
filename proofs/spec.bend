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

def SP.cok(+o: OP) -> Bool:
  match o:
    case OP{c, h1, h2}:
      (c < 256 : U32) && SP.hok(SP.e1(c), h1) && SP.hok(SP.e2(c), h2)

# Sections
# ========

# The size of a half, in the instruction section when its table half has
# size 0.
def SP.sz(+h: U32, +f: HF) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(SP.hs(h), 0) && U32.is_ne(SP.ht(h), 0),
    R.VI.var(SP.size(f)), [])

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
