import Base
import ./bytes.bend as B

# VCDIFF (RFC 3284) delta decoding, compatible with xdelta3.
#
# Byte strings are packed four to a word (see bytes.bend). Every read of an
# array hands the array back beside the value, and Bend matches only
# parameters, so a read is followed by a def that receives the pair: most
# helpers below are the second half of a read.

# Helpers
# =======

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

# The first error wins: `err` unless it is 0 and `bad` holds.
def err.set(+err: U32, bad: Bool, code: U32) -> U32:
  u32.pick(U32.is_eq(err, 0) && bad, code, err)

# Error codes
# ===========

def E.MAGIC() -> U32:
  1

def E.VERSION() -> U32:
  2

def E.SECONDARY() -> U32:
  3

def E.CODETABLE() -> U32:
  4

def E.HDRIND() -> U32:
  5

def E.TRUNCATED() -> U32:
  6

def E.WININD() -> U32:
  7

def E.DELIND() -> U32:
  8

def E.INST() -> U32:
  9

def E.ADDR() -> U32:
  10

def E.LENGTH() -> U32:
  11

def E.CHECKSUM() -> U32:
  12

def E.SOURCE() -> U32:
  13

def E.TOOBIG() -> U32:
  14

def E.show(+e: U32) -> String:
  Bool.pick(String, U32.is_eq(e, 1), "not a VCDIFF file (bad magic)",
  Bool.pick(String, U32.is_eq(e, 2), "unsupported VCDIFF version",
  Bool.pick(String, U32.is_eq(e, 3), "secondary compression is not supported",
  Bool.pick(String, U32.is_eq(e, 4), "application-defined code tables are not supported",
  Bool.pick(String, U32.is_eq(e, 5), "invalid header indicator",
  Bool.pick(String, U32.is_eq(e, 6), "truncated delta",
  Bool.pick(String, U32.is_eq(e, 7), "invalid window indicator",
  Bool.pick(String, U32.is_eq(e, 8), "invalid delta indicator",
  Bool.pick(String, U32.is_eq(e, 9), "invalid instruction",
  Bool.pick(String, U32.is_eq(e, 10), "invalid copy address",
  Bool.pick(String, U32.is_eq(e, 11), "target window length mismatch",
  Bool.pick(String, U32.is_eq(e, 12), "checksum mismatch",
  Bool.pick(String, U32.is_eq(e, 13), "source segment out of bounds",
  Bool.pick(String, U32.is_eq(e, 14), "delta too large", "unknown error"))))))))))))))

# Code table
# ==========

# The default code table of RFC 3284 section 5.6. A half instruction packs
# its type (0 NOOP, 1 ADD, 2 RUN, 3 COPY) in bits 0-1, its size (0: the size
# follows in the instruction section) in bits 2-9 and its address mode in
# bits 10-13; an entry packs two halves, the first in the low 16 bits.

def ct.half(+t: U32, +s: U32, +m: U32) -> U32:
  ((t .|. (s << 2n : U32) : U32) .|. (m << 10n : U32) : U32)

def ct.pair(+h1: U32, +h2: U32) -> U32:
  (h1 .|. (h2 << 16n : U32) : U32)

# op = 19 + 16 * mode + k: COPY of size 0 (k = 0) or k + 3, alone.
def ct.copy1(+k: U32) -> U32:
  +s = (k % 16 : U32)
  ct.pair(ct.half(3, u32.pick(U32.is_eq(s, 0), 0, (s + 3 : U32)), (k / 16 : U32)), 0)

# op = 163 + 12 * mode + 3 * (add - 1) + (copy - 4), mode < 6.
def ct.addcopy(+k: U32) -> U32:
  +r = (k % 12 : U32)
  ct.pair(ct.half(1, ((r / 3 : U32) + 1 : U32), 0),
    ct.half(3, ((r % 3 : U32) + 4 : U32), (k / 12 : U32)))

# op = 235 + 4 * (mode - 6) + (add - 1): ADD then COPY of size 4.
def ct.addcopy4(+k: U32) -> U32:
  ct.pair(ct.half(1, ((k % 4 : U32) + 1 : U32), 0),
    ct.half(3, 4, ((k / 4 : U32) + 6 : U32)))

# op = 247 + mode: COPY of size 4 then ADD of size 1.
def ct.copyadd(+k: U32) -> U32:
  ct.pair(ct.half(3, 4, k), ct.half(1, 1, 0))

def ct.entry(+op: U32) -> U32:
  u32.pick(U32.is_eq(op, 0), ct.pair(ct.half(2, 0, 0), 0),
  u32.pick((op < 19 : U32), ct.pair(ct.half(1, (op - 1 : U32), 0), 0),
  u32.pick((op < 163 : U32), ct.copy1((op - 19 : U32)),
  u32.pick((op < 235 : U32), ct.addcopy((op - 163 : U32)),
  u32.pick((op < 247 : U32), ct.addcopy4((op - 235 : U32)),
    ct.copyadd((op - 247 : U32)))))))

def ct.fill(n: Nat, a: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      a2 = a[i] <- ct.entry(i)
      ct.fill(p, a2, (i + 1 : U32))

def ct.table() -> Array<U32>:
  ct.fill(256n, [0 : U32^8n], 0)

# Address cache
# =============

# RFC 3284 section 5.1 with s_near = 4 and s_same = 3: slots [0, 768) are
# the SAME cache and [768, 772) the NEAR cache.

def cache.new() -> Array<U32>:
  [0 : U32^10n]

def cache.put(ca: Array<U32>, +slot: U32, +addr: U32) -> Array<U32>:
  c2 = ca[(768 + slot : U32)] <- addr
  c2[(addr % 768 : U32)] <- addr

def cache.clear.go(n: Nat, a: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      a2 = a[i] <- 0
      cache.clear.go(p, a2, (i + 1 : U32))

def cache.clear(ca: Array<U32>) -> Array<U32>:
  cache.clear.go(772n, ca, 0)

def cache.next(+slot: U32) -> U32:
  ((slot + 1 : U32) .&. 3 : U32)

# Decoder
# =======

# The fixed facts of a window: where its copy segment starts (in the source,
# or in the target with VCD_TARGET) and how long it is, where the window
# starts and ends in the target, and where its sections end in the delta.
type WinC is Data:
  WinC{seg: U32, cpl: U32, tseg: Bool, wst: U32, oend: U32, dend: U32,
    iend: U32, aend: U32}

# A window being decoded: the arrays, the section cursors, the next NEAR
# slot and the first error (0 for none).
type Dec is Type:
  Dec{src: Array<U32>, del: Array<U32>, out: Array<U32>, tab: Array<U32>,
    ca: Array<U32>, opos: U32, dpos: U32, ipos: U32, apos: U32, slot: U32,
    err: U32}

# The size of a half instruction: its table size, or a varint from the
# instruction section when the table says 0.
def dec.size.k(src: Array<U32>, out: Array<U32>, tab: Array<U32>,
  ca: Array<U32>, +opos: U32, +dpos: U32, +apos: U32, +slot: U32, +err: U32,
  v: B.VR) -> U32 & Dec:
  match v:
    case B.VR{del, +val, +ipos, ok}:
      (val, Dec{src, del, out, tab, ca, opos, dpos, ipos, apos, slot,
        err.set(err, Bool.not(ok), E.INST())})

def dec.size.go(+wc: WinC, st: Dec) -> U32 & Dec:
  match wc st:
    case WinC{seg, cpl, tseg, wst, oend, dend, iend, aend}
      Dec{src, del, out, tab, ca, opos, dpos, ipos, apos, slot, err}:
      dec.size.k(src, out, tab, ca, opos, dpos, apos, slot, err,
        B.B.var.get(del, ipos, iend))

def dec.size(+wc: WinC, z: Bool, +s: U32, st: Dec) -> U32 & Dec:
  match z:
    case False{}:
      (s, st)
    case True{}:
      dec.size.go(wc, st)

# ADD: n bytes from the data section.
def dec.add.k(src: Array<U32>, tab: Array<U32>, ca: Array<U32>, +opos: U32,
  +dpos: U32, +ipos: U32, +apos: U32, +slot: U32, +err: U32, +n: U32,
  ok: Bool, r: Array<U32> & Array<U32>) -> Dec:
  (del, out) = r
  Dec{src, del, out, tab, ca, (opos + n : U32), (dpos + n : U32), ipos, apos,
    slot, err.set(err, Bool.not(ok), E.INST())}

def dec.add(+wc: WinC, sd: U32 & Dec) -> Dec:
  match wc sd:
    case WinC{seg, cpl, tseg, wst, +oend, +dend, iend, aend}
      Tuple{+n, Dec{src, del, out, tab, ca, +opos, +dpos, ipos, apos, slot, err}}:
      +ok = (n <= (dend - dpos : U32) : U32) && (n <= (oend - opos : U32) : U32)
      +m = u32.pick(ok, n, 0)
      dec.add.k(src, tab, ca, opos, dpos, ipos, apos, slot, err, m, ok,
        B.B.copy(out, opos, del, dpos, m))

# RUN: n copies of one byte from the data section.
def dec.run.k(src: Array<U32>, out: Array<U32>, tab: Array<U32>,
  ca: Array<U32>, +opos: U32, +dpos: U32, +ipos: U32, +apos: U32, +slot: U32,
  +err: U32, +n: U32, ok: Bool, r: Array<U32> & U32) -> Dec:
  (del, +b) = r
  Dec{src, del, B.B.fill(out, opos, b, n), tab, ca, (opos + n : U32),
    (dpos + 1 : U32), ipos, apos, slot, err.set(err, Bool.not(ok), E.INST())}

def dec.run(+wc: WinC, sd: U32 & Dec) -> Dec:
  match wc sd:
    case WinC{seg, cpl, tseg, wst, +oend, +dend, iend, aend}
      Tuple{+n, Dec{src, del, out, tab, ca, +opos, +dpos, ipos, apos, slot, err}}:
      +ok = (dpos < dend : U32) && (n <= (oend - opos : U32) : U32)
      dec.run.k(src, out, tab, ca, opos, dpos, ipos, apos, slot, err,
        u32.pick(ok, n, 0), ok, B.B.get(del, dpos))

# COPY, once its address is known: from the copy segment (in the source, or
# in the target for VCD_TARGET) or from earlier in this target window.
def dec.copy.go(seg_in_out: Bool, +n: U32, +from: U32, +opos: U32,
  src: Array<U32>, out: Array<U32>) -> Array<U32> & Array<U32>:
  match seg_in_out:
    case False{}:
      B.B.copy(out, opos, src, from, n)
    case True{}:
      (src, B.B.move(out, opos, from, n))

def dec.copy.k(del: Array<U32>, tab: Array<U32>, ca: Array<U32>, +opos: U32,
  +dpos: U32, +ipos: U32, +apos: U32, +slot: U32, +err: U32, +n: U32,
  ok: Bool, r: Array<U32> & Array<U32>) -> Dec:
  (src, out) = r
  Dec{src, del, out, tab, ca, (opos + n : U32), dpos, ipos, apos, slot,
    err.set(err, Bool.not(ok), E.ADDR())}

def dec.copy.at(+wc: WinC, +n: U32, +addr: U32, aok: Bool, st: Dec) -> Dec:
  match wc st:
    case WinC{+seg, +cpl, +tseg, +wst, +oend, dend, iend, aend}
      Dec{src, del, out, tab, ca, +opos, dpos, ipos, apos, +slot, err}:
      +here = (cpl + (opos - wst : U32) : U32)
      +in_seg = (addr < cpl : U32)
      +ok = aok && (addr < here : U32) && (n <= (oend - opos : U32) : U32)
        && Bool.or(Bool.not(in_seg), (n <= (cpl - addr : U32) : U32))
      +m = u32.pick(ok, n, 0)
      +from = u32.pick(in_seg, (seg + addr : U32), (wst + (addr - cpl : U32) : U32))
      dec.copy.k(del, tab, cache.put(ca, slot, addr), opos, dpos, ipos, apos,
        cache.next(slot), err, m, ok,
        dec.copy.go(Bool.or(Bool.not(in_seg), tseg), m, from, opos, src, out))

# The address of a COPY in mode `mode` (RFC 3284 section 5.3): the value is
# a varint for SELF, HERE and NEAR, and a byte for SAME.
def dec.addr.c(+mode: U32, +here: U32, +v: U32, vok: Bool,
  r: Array<U32> & U32) -> Array<U32> & (U32 & Bool):
  (ca, +c) = r
  +addr = u32.pick(U32.is_eq(mode, 0), v,
    u32.pick(U32.is_eq(mode, 1), (here - v : U32),
    u32.pick((mode < 6 : U32), (c + v : U32), c)))
  +ok = vok && (mode < 9 : U32) && Bool.or(U32.is_ne(mode, 1), (v <= here : U32))
  (ca, (addr, ok))

def dec.addr.v(z: Bool, del: Array<U32>, +apos: U32, +aend: U32) -> B.VR:
  match z:
    case True{}:
      B.B.var.get(del, apos, aend)
    case False{}:
      B.B.byte.get(del, apos, aend)

def dec.copy.c(+wc: WinC, +n: U32, src: Array<U32>, del: Array<U32>,
  out: Array<U32>, tab: Array<U32>, +opos: U32, +dpos: U32, +ipos: U32,
  +apos: U32, +slot: U32, +err: U32, r: Array<U32> & (U32 & Bool)) -> Dec:
  (ca, ak) = r
  (+addr, aok) = ak
  dec.copy.at(wc, n, addr, aok,
    Dec{src, del, out, tab, ca, opos, dpos, ipos, apos, slot, err})

def dec.copy.v(+wc: WinC, +n: U32, +mode: U32, +here: U32, src: Array<U32>,
  out: Array<U32>, tab: Array<U32>, ca: Array<U32>, +opos: U32, +dpos: U32,
  +ipos: U32, +slot: U32, +err: U32, v: B.VR) -> Dec:
  match v:
    case B.VR{del, +val, +apos, vok}:
      +idx = u32.pick((mode < 6 : U32), (766 + mode : U32),
        (((mode - 6 : U32) * 256 : U32) + (val .&. 255 : U32) : U32))
      dec.copy.c(wc, n, src, del, out, tab, opos, dpos, ipos, apos, slot, err,
        dec.addr.c(mode, here, val, vok, ca[idx]))

def dec.copy(+wc: WinC, +mode: U32, sd: U32 & Dec) -> Dec:
  match wc sd:
    case WinC{seg, +cpl, tseg, +wst, oend, dend, iend, +aend}
      Tuple{+n, Dec{src, del, out, tab, ca, +opos, dpos, ipos, +apos, slot, err}}:
      dec.copy.v(wc, n, mode, (cpl + (opos - wst : U32) : U32), src, out, tab,
        ca, opos, dpos, ipos, slot, err,
        dec.addr.v((mode < 6 : U32), del, apos, aend))

def dec.half.go(+wc: WinC, b1: Bool, b0: Bool, +mode: U32, sd: U32 & Dec) ->
  Dec:
  match b1 b0:
    case False{} False{}:
      (n, st) = sd
      st
    case False{} True{}:
      dec.add(wc, sd)
    case True{} False{}:
      dec.run(wc, sd)
    case True{} True{}:
      dec.copy(wc, mode, sd)

# One half of an instruction, as packed by ct.half.
def dec.half(+wc: WinC, +h: U32, st: Dec) -> Dec:
  +t = (h .&. 3 : U32)
  +s = ((h >> 2n : U32) .&. 255 : U32)
  dec.half.go(wc, U32.is_ne((t .&. 2 : U32), 0), U32.is_ne((t .&. 1 : U32), 0),
    ((h >> 10n : U32) .&. 15 : U32),
    dec.size(wc, U32.is_eq(s, 0) && U32.is_ne(t, 0), s, st))

# Whether to decode another instruction.
def dec.more(+wc: WinC, st: Dec) -> Bool & Dec:
  match wc st:
    case WinC{seg, cpl, tseg, wst, oend, dend, +iend, aend}
      Dec{src, del, out, tab, ca, opos, dpos, +ipos, apos, slot, +err}:
      ((ipos < iend : U32) && U32.is_eq(err, 0),
        Dec{src, del, out, tab, ca, opos, dpos, ipos, apos, slot, err})

def dec.op(+wc: WinC, src: Array<U32>, del: Array<U32>, out: Array<U32>,
  ca: Array<U32>, +opos: U32, +dpos: U32, +ipos: U32, +apos: U32, +slot: U32,
  +err: U32, r: Array<U32> & U32) -> Bool & Dec:
  (tab, +e) = r
  dec.more(wc, dec.half(wc, (e >> 16n : U32), dec.half(wc, (e .&. 65535 : U32),
    Dec{src, del, out, tab, ca, opos, dpos, ipos, apos, slot, err})))

def dec.opcode(+wc: WinC, src: Array<U32>, out: Array<U32>, tab: Array<U32>,
  ca: Array<U32>, +opos: U32, +dpos: U32, +ipos: U32, +apos: U32, +slot: U32,
  +err: U32, r: Array<U32> & U32) -> Bool & Dec:
  (del, +op) = r
  dec.op(wc, src, del, out, ca, opos, dpos, (ipos + 1 : U32), apos, slot, err,
    tab[op])

def dec.step(+wc: WinC, st: Dec) -> Bool & Dec:
  match st:
    case Dec{src, del, out, tab, ca, opos, dpos, +ipos, apos, slot, err}:
      dec.opcode(wc, src, out, tab, ca, opos, dpos, ipos, apos, slot, err,
        B.B.get(del, ipos))

# Decodes instructions while any remain and no error is seen; n bounds the
# count, as each takes at least one byte of the instruction section.
def dec.loop(n: Nat, +wc: WinC, s: Bool & Dec) -> Dec:
  match n s:
    case 0n Tuple{g, st}:
      st
    case 1n+p Tuple{False{}, st}:
      st
    case 1n+p Tuple{True{}, st}:
      dec.loop(p, wc, dec.step(wc, st))

# Window headers
# ==============

# A parsed window header (RFC 3284 section 4.2): the indicator, the copy
# segment, the target length, the section lengths, the checksum, where the
# sections start and where the window ends, and the first error (0: none).
type WH is Data:
  WH{ind: U32, cpl: U32, cpo: U32, tlen: U32, dlen: U32, ilen: U32,
    alen: U32, sum: U32, body: U32, end: U32, err: U32}

# A big-endian U32: four bytes.
def be32.k3(+acc: U32, +pos: U32, +end: U32, r: Array<U32> & U32) -> B.VR:
  (a, +b) = r
  B.VR{a, ((acc << 8n : U32) .|. b : U32), (pos + 1 : U32), (pos < end : U32)}

def be32.k2(+acc: U32, +pos: U32, +end: U32, r: Array<U32> & U32) -> B.VR:
  (a, +b) = r
  +p2 = (pos + 1 : U32)
  be32.k3(((acc << 8n : U32) .|. b : U32), p2, end, B.B.get(a, p2))

def be32.k1(+acc: U32, +pos: U32, +end: U32, r: Array<U32> & U32) -> B.VR:
  (a, +b) = r
  +p2 = (pos + 1 : U32)
  be32.k2(((acc << 8n : U32) .|. b : U32), p2, end, B.B.get(a, p2))

def be32.k0(+pos: U32, +end: U32, r: Array<U32> & U32) -> B.VR:
  (a, +b) = r
  +p2 = (pos + 1 : U32)
  be32.k1(b, p2, end, B.B.get(a, p2))

def be32.get(a: Array<U32>, +pos: U32, +end: U32) -> B.VR:
  be32.k0(pos, end, B.B.get(a, pos))

def wp.sum(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +tlen: U32, +dli: U32,
  +dl: U32, +il: U32, +al: U32, +err: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +sum, +body, ok}:
      +e1 = err.set(err, Bool.not(ok), E.TRUNCATED())
      +e2 = err.set(e1, U32.is_ne(dli, 0), E.SECONDARY())
      +secs_ok = (dl <= (wend - body : U32) : U32)
        && (il <= ((wend - body : U32) - dl : U32) : U32)
        && U32.is_eq(al, (((wend - body : U32) - dl : U32) - il : U32))
      +e3 = err.set(e2, Bool.not((body <= wend : U32) && secs_ok), E.TRUNCATED())
      (a, WH{ind, cpl, cpo, tlen, dl, il, al, sum, body, wend, e3})

def wp.sum.if(z: Bool, a: Array<U32>, +pos: U32, +end: U32) -> B.VR:
  match z:
    case True{}:
      be32.get(a, pos, end)
    case False{}:
      B.VR{a, 0, pos, True{}}

def wp.al(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +tlen: U32, +dli: U32,
  +dl: U32, +il: U32, +err: U32, +end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +al, +pos, ok}:
      wp.sum(ind, cpl, cpo, wend, tlen, dli, dl, il, al,
        err.set(err, Bool.not(ok), E.TRUNCATED()),
        wp.sum.if(U32.is_ne((ind .&. 4 : U32), 0), a, pos, end))

def wp.il(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +tlen: U32, +dli: U32,
  +dl: U32, +err: U32, +end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +il, +pos, ok}:
      wp.al(ind, cpl, cpo, wend, tlen, dli, dl, il,
        err.set(err, Bool.not(ok), E.TRUNCATED()), end, B.B.var.get(a, pos, end))

def wp.dl(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +tlen: U32, +dli: U32,
  +err: U32, +end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +dl, +pos, ok}:
      wp.il(ind, cpl, cpo, wend, tlen, dli, dl,
        err.set(err, Bool.not(ok), E.TRUNCATED()), end, B.B.var.get(a, pos, end))

def wp.dli(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +tlen: U32, +err: U32,
  +end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +dli, +pos, ok}:
      wp.dl(ind, cpl, cpo, wend, tlen, dli,
        err.set(err, Bool.not(ok), E.TRUNCATED()), end, B.B.var.get(a, pos, end))

def wp.tlen(+ind: U32, +cpl: U32, +cpo: U32, +wend: U32, +err: U32, +end: U32,
  v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +tlen, +pos, ok}:
      wp.dli(ind, cpl, cpo, wend, tlen,
        err.set(err, Bool.not(ok), E.TRUNCATED()), end, B.B.byte.get(a, pos, end))

def wp.enc(+ind: U32, +cpl: U32, +cpo: U32, +err: U32, +end: U32, v: B.VR) ->
  Array<U32> & WH:
  match v:
    case B.VR{a, +elen, +pos, ok}:
      +fits = ok && (elen <= (end - pos : U32) : U32)
      wp.tlen(ind, cpl, cpo, (pos + elen : U32),
        err.set(err, Bool.not(fits), E.TRUNCATED()), end, B.B.var.get(a, pos, end))

def wp.cpo(+ind: U32, +cpl: U32, +err: U32, +end: U32, v: B.VR) ->
  Array<U32> & WH:
  match v:
    case B.VR{a, +cpo, +pos, ok}:
      wp.enc(ind, cpl, cpo, err.set(err, Bool.not(ok), E.TRUNCATED()), end,
        B.B.var.get(a, pos, end))

def wp.cpl(+ind: U32, +err: U32, +end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +cpl, +pos, ok}:
      wp.cpo(ind, cpl, err.set(err, Bool.not(ok), E.TRUNCATED()), end,
        B.B.var.get(a, pos, end))

def wp.seg(z: Bool, +ind: U32, +err: U32, +end: U32, a: Array<U32>,
  +pos: U32) -> Array<U32> & WH:
  match z:
    case True{}:
      wp.cpl(ind, err, end, B.B.var.get(a, pos, end))
    case False{}:
      wp.enc(ind, 0, 0, err, end, B.B.var.get(a, pos, end))

def wp.ind(+end: U32, v: B.VR) -> Array<U32> & WH:
  match v:
    case B.VR{a, +ind, +pos, ok}:
      +e1 = err.set(0, Bool.not(ok), E.TRUNCATED())
      +e2 = err.set(e1, U32.is_ne((ind .&. 248 : U32), 0)
        || U32.is_eq((ind .&. 3 : U32), 3), E.WININD())
      wp.seg(U32.is_ne((ind .&. 3 : U32), 0), ind, e2, end, a, pos)

# Parses the window header at pos of a delta of length end.
def win.parse(a: Array<U32>, +pos: U32, +end: U32) -> Array<U32> & WH:
  wp.ind(end, B.B.byte.get(a, pos, end))

# Decoding
# ========

# The state between windows: the arrays, the lengths of the source and of
# the delta, where the next window starts in the delta and in the target,
# and the first error.
type DS is Type:
  DS{src: Array<U32>, del: Array<U32>, out: Array<U32>, tab: Array<U32>,
    ca: Array<U32>, slen: U32, dlen: U32, pos: U32, opos: U32, err: U32}

def win.sum.k(src: Array<U32>, del: Array<U32>, tab: Array<U32>,
  ca: Array<U32>, +slen: U32, +dlen: U32, +pos: U32, +opos: U32, +sum: U32,
  +err: U32, r: Array<U32> & U32) -> DS:
  (out, +c) = r
  DS{src, del, out, tab, ca, slen, dlen, pos, opos,
    err.set(err, U32.is_ne(c, sum), E.CHECKSUM())}

def win.sum(z: Bool, src: Array<U32>, del: Array<U32>, out: Array<U32>,
  tab: Array<U32>, ca: Array<U32>, +slen: U32, +dlen: U32, +pos: U32,
  +opos: U32, +sum: U32, +err: U32, +wst: U32) -> DS:
  match z:
    case False{}:
      DS{src, del, out, tab, ca, slen, dlen, pos, opos, err}
    case True{}:
      win.sum.k(src, del, tab, ca, slen, dlen, pos, opos, sum, err,
        B.B.adler32(out, wst, (opos - wst : U32)))

def win.fin(+slen: U32, +dlen: U32, +ind: U32, +sum: U32, +wc: WinC,
  st: Dec) -> DS:
  match wc st:
    case WinC{seg, cpl, tseg, +wst, +oend, dend, iend, +wend}
      Dec{src, del, out, tab, ca, +opos, dpos, ipos, apos, slot, +err}:
      +e1 = err.set(err, U32.is_ne(opos, oend), E.LENGTH())
      win.sum(U32.is_ne((ind .&. 4 : U32), 0) && U32.is_eq(e1, 0), src, del,
        out, tab, ca, slen, dlen, wend, oend, sum, e1, wst)

def win.go(src: Array<U32>, out: Array<U32>, tab: Array<U32>, ca: Array<U32>,
  +slen: U32, +dlen: U32, +opos: U32, +err: U32, r: Array<U32> & WH) -> DS:
  match r:
    case Tuple{del, WH{+ind, +cpl, +cpo, +tlen, +dl, +il, +al, +sum, +body,
      +wend, +werr}}:
      +tseg = U32.is_ne((ind .&. 2 : U32), 0)
      +hasseg = U32.is_ne((ind .&. 3 : U32), 0)
      +lim = u32.pick(tseg, opos, slen)
      +seg_ok = Bool.not(hasseg)
        || ((cpl <= lim : U32) && (cpo <= (lim - cpl : U32) : U32))
      +e1 = err.set(err, U32.is_ne(werr, 0), werr)
      +e2 = err.set(e1, Bool.not(seg_ok), E.SOURCE())
      +e3 = err.set(e2, (tlen > (2147483648 - opos : U32) : U32), E.TOOBIG())
      +dend = (body + dl : U32)
      +iend = (dend + il : U32)
      +wc = {WinC{cpo, u32.pick(hasseg, cpl, 0), tseg, opos, (opos + tlen : U32),
        dend, iend, wend} : WinC}
      win.fin(slen, dlen, ind, sum, wc, dec.loop(U32.to_nat(il), wc,
        ((0 < il : U32) && U32.is_eq(e3, 0),
          Dec{src, del, out, tab, cache.clear(ca), opos, body, dend,
            iend, 0, e3})))

def win.dec(st: DS) -> DS:
  match st:
    case DS{src, del, out, tab, ca, slen, +dlen, pos, opos, err}:
      win.go(src, out, tab, ca, slen, dlen, opos, err, win.parse(del, pos, dlen))

def win.more(st: DS) -> Bool & DS:
  match st:
    case DS{src, del, out, tab, ca, slen, +dlen, +pos, opos, +err}:
      ((pos < dlen : U32) && U32.is_eq(err, 0),
        DS{src, del, out, tab, ca, slen, dlen, pos, opos, err})

# Decodes windows until the delta ends or an error is seen; n bounds the
# count, as each window takes at least one byte.
def win.loop(n: Nat, s: Bool & DS) -> DS:
  match n s:
    case 0n Tuple{g, st}:
      st
    case 1n+p Tuple{False{}, st}:
      st
    case 1n+p Tuple{True{}, st}:
      win.loop(p, win.more(win.dec(st)))

# Prescan: the total target length, so the target is allocated once.
type PS is Type:
  PS{del: Array<U32>, dlen: U32, pos: U32, total: U32, err: U32}

def pre.k(+dlen: U32, +total: U32, +err: U32, r: Array<U32> & WH) ->
  Bool & PS:
  match r:
    case Tuple{del, WH{ind, cpl, cpo, +tlen, dl, il, al, sum, body, +wend,
      +werr}}:
      +e1 = err.set(err, U32.is_ne(werr, 0), werr)
      +e2 = err.set(e1, (tlen > (2147483648 - total : U32) : U32), E.TOOBIG())
      ((wend < dlen : U32) && U32.is_eq(e2, 0),
        PS{del, dlen, wend, (total + tlen : U32), e2})

def pre.step(st: PS) -> Bool & PS:
  match st:
    case PS{del, +dlen, pos, total, err}:
      pre.k(dlen, total, err, win.parse(del, pos, dlen))

def pre.loop(n: Nat, s: Bool & PS) -> PS:
  match n s:
    case 0n Tuple{g, st}:
      st
    case 1n+p Tuple{False{}, st}:
      st
    case 1n+p Tuple{True{}, st}:
      pre.loop(p, pre.step(st))

# File header (RFC 3284 section 4.1): the magic and version, then the
# indicator, then (with VCD_APPHEADER) application data, which is skipped.
def hdr.app(+err: U32, +dlen: U32, v: B.VR) -> Array<U32> & (U32 & U32):
  match v:
    case B.VR{a, +n, +pos, ok}:
      +fits = ok && (n <= (dlen - pos : U32) : U32)
      (a, ((pos + n : U32), err.set(err, Bool.not(fits), E.TRUNCATED())))

def hdr.app.if(z: Bool, +err: U32, +dlen: U32, a: Array<U32>) ->
  Array<U32> & (U32 & U32):
  match z:
    case False{}:
      (a, (5, err))
    case True{}:
      hdr.app(err, dlen, B.B.var.get(a, 5, dlen))

def hdr.ind(+merr: U32, +dlen: U32, v: B.VR) -> Array<U32> & (U32 & U32):
  match v:
    case B.VR{a, +ind, pos, ok}:
      +e1 = err.set(merr, Bool.not(ok), E.TRUNCATED())
      +e2 = err.set(e1, U32.is_ne((ind .&. 248 : U32), 0), E.HDRIND())
      +e3 = err.set(e2, U32.is_ne((ind .&. 1 : U32), 0), E.SECONDARY())
      +e4 = err.set(e3, U32.is_ne((ind .&. 2 : U32), 0), E.CODETABLE())
      hdr.app.if(U32.is_ne((ind .&. 4 : U32), 0), e4, dlen, a)

def hdr.magic(+dlen: U32, v: B.VR) -> Array<U32> & (U32 & U32):
  match v:
    case B.VR{a, +m, pos, ok}:
      +e1 = err.set(0, Bool.not(ok), E.TRUNCATED())
      +e2 = err.set(e1, U32.is_ne((m >> 8n : U32), 14074820), E.MAGIC())
      +e3 = err.set(e2, U32.is_ne((m .&. 255 : U32), 0), E.VERSION())
      hdr.ind(e3, dlen, B.B.byte.get(a, 4, dlen))

# Parses the file header; answers where the first window starts.
def hdr.parse(a: Array<U32>, +dlen: U32) -> Array<U32> & (U32 & U32):
  hdr.magic(dlen, be32.get(a, 0, dlen))

def dec.res(z: Bool, +err: U32, +total: U32, out: Array<U32>) ->
  Result<&1, &1, U32, B.Bytes>:
  match z:
    case True{}:
      Done{B.Bytes{total, out}}
    case False{}:
      Fail{err}

def dec.done(+total: U32, st: DS) -> B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>):
  match st:
    case DS{src, del, out, tab, ca, slen, dlen, pos, opos, +err}:
      (B.Bytes{slen, src}, (B.Bytes{dlen, del},
        dec.res(U32.is_eq(err, 0), err, total, out)))

# The target array: buf when it holds at least size slots, else a new one.
def dec.buf.if(z: Bool, +size: U32, buf: Array<U32>) -> Array<U32>:
  match z:
    case True{}:
      buf
    case False{}:
      B.B.zeros(size)

def dec.buf(+size: U32, r: Array<U32> & U32) -> Array<U32>:
  (buf, +cap) = r
  dec.buf.if((B.B.words(size) <= cap : U32) && (0 < cap : U32), size, buf)

def dec.pre(+slen: U32, src: Array<U32>, +dlen: U32, +pos: U32,
  buf: Array<U32>, ps: PS) -> B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>):
  match ps:
    case PS{del, d, p, +total, +err}:
      +size = u32.pick(U32.is_eq(err, 0), total, 0)
      dec.done(size, win.loop(U32.to_nat(dlen),
        ((pos < dlen : U32) && U32.is_eq(err, 0),
          DS{src, del, dec.buf(size, Array.size(U32, buf)), ct.table(),
            cache.new(), slen, dlen, pos, 0, err})))

def dec.hdr(+slen: U32, src: Array<U32>, +dlen: U32, buf: Array<U32>,
  r: Array<U32> & (U32 & U32)) -> B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>):
  match r:
    case Tuple{del, Tuple{pos0, err0}}:
      +pos = pos0
      +err = {err0 : U32}
      dec.pre(slen, src, dlen, pos, buf, pre.loop(U32.to_nat(dlen),
        ((pos < dlen : U32) && U32.is_eq(err, 0), PS{del, dlen, pos, 0, err})))

# Applies the delta `del` to the source `src`, writing the target into buf
# when it is large enough. Answers both inputs back, then the target or the
# code of the first error found.
def decode.into(src: B.Bytes, del: B.Bytes, buf: Array<U32>) ->
  B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>):
  match src del:
    case B.Bytes{+slen, sa} B.Bytes{+dlen, da}:
      dec.hdr(slen, sa, dlen, buf, hdr.parse(da, dlen))

def decode(src: B.Bytes, del: B.Bytes) ->
  B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>):
  decode.into(src, del, [0 : U32^0n])

# The length of the target a delta decodes to, or 0 if its windows do not
# parse.
def decode.size.fin(ps: PS) -> B.Bytes & U32:
  match ps:
    case PS{del, +dlen, p, +total, +err}:
      (B.Bytes{dlen, del}, u32.pick(U32.is_eq(err, 0), total, 0))

def decode.size.k(+dlen: U32, r: Array<U32> & (U32 & U32)) -> B.Bytes & U32:
  match r:
    case Tuple{del, Tuple{pos0, err0}}:
      +pos = pos0
      +err = {err0 : U32}
      decode.size.fin(pre.loop(U32.to_nat(dlen),
        ((pos < dlen : U32) && U32.is_eq(err, 0), PS{del, dlen, pos, 0, err})))

def decode.size(del: B.Bytes) -> B.Bytes & U32:
  match del:
    case B.Bytes{+dlen, da}:
      decode.size.k(dlen, hdr.parse(da, dlen))
