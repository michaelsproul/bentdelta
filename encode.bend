import Base
import ./bytes.bend as B

# VCDIFF (RFC 3284) delta encoding, after xdelta3's default ("fast",
# level 3) string matcher: a rolling hash over 9 bytes of the source every
# 8 bytes, a 4-byte hash over the target with short chains, runs, lazy
# matching, and xdelta3's instruction optimizer and code-table choices.
#
# The encoder is not trusted: check.bend decodes what it produces and falls
# back to a plain encoding if that does not give back the target.

# Helpers
# =======

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

def u32.max(+a: U32, +b: U32) -> U32:
  u32.pick((a < b : U32), b, a)

# Emitter
# =======

# Writes instructions into the three sections of a window, choosing opcodes
# and address modes as xdelta3 does. The last instruction is held back (as
# xdelta3's iout) to pair it with the next one in a double opcode: its type
# (0 none, 1 ADD, 2 RUN, 3 COPY), size, address mode and single opcode.
type Em is Type:
  Em{dat: Array<U32>, ins: Array<U32>, adr: Array<U32>, ca: Array<U32>,
    dl: U32, il: U32, al: U32, slot: U32, uoff: U32, pt: U32, ps: U32,
    pm: U32, pc: U32}

def T.ADD() -> U32:
  1

def T.RUN() -> U32:
  2

def T.CPY() -> U32:
  3

# The opcode of an instruction alone (xd3_choose_instruction's code1).
def op.single(+t: U32, +size: U32, +mode: U32) -> U32:
  u32.pick(U32.is_eq(t, 2), 0,
  u32.pick(U32.is_eq(t, 1), u32.pick((size <= 17 : U32), (1 + size : U32), 1),
    (((19 + (16 * mode : U32) : U32))
      + u32.pick((4 <= size : U32) && (size <= 18 : U32), (size - 3 : U32), 0) : U32)))

# The opcode of the pending instruction (pt, ps, pm) followed by (t, size,
# mode) as one double instruction, or 0 (xd3_choose_instruction's code2).
def op.double(+pt: U32, +ps: U32, +pm: U32, +t: U32, +size: U32, +mode: U32) ->
  U32:
  +copy_add = U32.is_eq(t, 1) && U32.is_eq(size, 1) && U32.is_eq(pt, 3)
    && U32.is_eq(ps, 4)
  +add_copy = U32.is_eq(t, 3) && (4 <= size : U32) && (size <= 18 : U32)
    && U32.is_eq(pt, 1) && (ps <= 4 : U32)
  +ac1 = add_copy && (size <= 6 : U32) && (mode <= 5 : U32)
  +ac2 = add_copy && U32.is_eq(size, 4) && (mode >= 6 : U32)
  u32.pick(copy_add, (247 + pm : U32),
  u32.pick(ac1, ((((163 + (mode * 12 : U32) : U32) + ((ps - 1 : U32) * 3 : U32)) : U32)
      + (size - 4 : U32) : U32),
  u32.pick(ac2, (((235 + ((mode - 6 : U32) * 4 : U32) : U32)) + (ps - 1 : U32) : U32),
    0)))

# Whether a single opcode takes its size from the instruction section.
def op.sized(+c: U32) -> Bool:
  (c < 2 : U32) || ((19 <= c : U32) && (c < 163 : U32)
    && U32.is_eq(((c - 19 : U32) .&. 15 : U32), 0))

def em.single.if(z: Bool, ins: Array<U32>, +il: U32, +size: U32) ->
  Array<U32> & U32:
  match z:
    case True{}:
      B.B.var.put(ins, il, size)
    case False{}:
      (ins, il)

def em.single.go(z: Bool, +ps: U32, +pc: U32, ins: Array<U32>, +il: U32) ->
  Array<U32> & U32:
  match z:
    case False{}:
      (ins, il)
    case True{}:
      em.single.if(op.sized(pc), B.B.put(ins, il, pc), (il + 1 : U32), ps)

# Writes the pending instruction as a single opcode (if there is one).
def em.single(+pt: U32, +ps: U32, +pc: U32, ins: Array<U32>, +il: U32) ->
  Array<U32> & U32:
  em.single.go(U32.is_ne(pt, 0), ps, pc, ins, il)

def em.queue.k(dat: Array<U32>, adr: Array<U32>, ca: Array<U32>, +dl: U32,
  +al: U32, +slot: U32, +uoff: U32, +t: U32, +size: U32, +mode: U32,
  r: Array<U32> & U32) -> Em:
  (ins, +il) = r
  Em{dat, ins, adr, ca, dl, il, al, slot, uoff, t, size, mode,
    op.single(t, size, mode)}

def em.queue.dbl(dat: Array<U32>, ins: Array<U32>, adr: Array<U32>,
  ca: Array<U32>, +dl: U32, +il: U32, +al: U32, +slot: U32, +uoff: U32,
  +code: U32) -> Em:
  Em{dat, B.B.put(ins, il, code), adr, ca, dl, (il + 1 : U32), al, slot, uoff,
    0, 0, 0, 0}

def em.queue.go(dbl: Bool, dat: Array<U32>, ins: Array<U32>, adr: Array<U32>,
  ca: Array<U32>, +dl: U32, +il: U32, +al: U32, +slot: U32, +uoff: U32,
  +pt: U32, +ps: U32, +pc: U32, +code: U32, +t: U32, +size: U32, +mode: U32) ->
  Em:
  match dbl:
    case True{}:
      em.queue.dbl(dat, ins, adr, ca, dl, il, al, slot, uoff, code)
    case False{}:
      em.queue.k(dat, adr, ca, dl, al, slot, uoff, t, size, mode,
        em.single(pt, ps, pc, ins, il))

# An instruction whose data and address are written: pair it with the
# pending one, or write the pending one and hold this one back.
def em.queue(+t: U32, +size: U32, +mode: U32, em: Em) -> Em:
  match em:
    case Em{dat, ins, adr, ca, dl, il, al, slot, uoff, +pt, +ps, +pm, pc}:
      +code = op.double(pt, ps, pm, t, size, mode)
      em.queue.go(U32.is_ne(code, 0), dat, ins, adr, ca, dl, il, al, slot,
        uoff, pt, ps, pc, code, t, size, mode)

def em.flush.k(dat: Array<U32>, adr: Array<U32>, ca: Array<U32>, +dl: U32,
  +al: U32, +slot: U32, +uoff: U32, r: Array<U32> & U32) -> Em:
  (ins, +il) = r
  Em{dat, ins, adr, ca, dl, il, al, slot, uoff, 0, 0, 0, 0}

# Writes the pending instruction, at the end of a window.
def em.flush(em: Em) -> Em:
  match em:
    case Em{dat, ins, adr, ca, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      em.flush.k(dat, adr, ca, dl, al, slot, uoff, em.single(pt, ps, pc, ins, il))

# Address encoding
# ================

# A written address: the cache, the address section, its length and the
# mode used.
type AE is Type:
  AE{ca: Array<U32>, adr: Array<U32>, al: U32, mode: U32}

def ea.var(ca: Array<U32>, +m: U32, r: Array<U32> & U32) -> AE:
  (adr, +al) = r
  AE{ca, adr, al, m}

def ea.put(same: Bool, +d: U32, +m: U32, +r768: U32, adr: Array<U32>,
  +al: U32, ca: Array<U32>) -> AE:
  match same:
    case True{}:
      AE{ca, B.B.put(adr, al, (r768 .&. 255 : U32)), (al + 1 : U32),
        (6 + (r768 >> 8n : U32) : U32)}
    case False{}:
      ea.var(ca, m, B.B.var.put(adr, al, d))

# xd3_encode_address: SELF, then HERE, then each NEAR slot, each taken when
# it gives a smaller value, stopping at the first value below 128; then
# SAME when its slot holds the address. The cache is then updated.
def ea.k(+addr: U32, +here: U32, adr: Array<U32>, +al: U32, +slot: U32,
  +n0: U32, +n1: U32, +n2: U32, +n3: U32, r: Array<U32> & U32) -> AE:
  (ca, +sm) = r
  +d1 = (here - addr : U32)
  +t1 = (addr >= 128 : U32) && (d1 < addr : U32)
  +b1 = u32.pick(t1, d1, addr)
  +m1 = u32.pick(t1, 1, 0)
  +t2 = (b1 >= 128 : U32) && (addr >= n0 : U32) && ((addr - n0 : U32) < b1 : U32)
  +b2 = u32.pick(t2, (addr - n0 : U32), b1)
  +m2 = u32.pick(t2, 2, m1)
  +t3 = (b2 >= 128 : U32) && (addr >= n1 : U32) && ((addr - n1 : U32) < b2 : U32)
  +b3 = u32.pick(t3, (addr - n1 : U32), b2)
  +m3 = u32.pick(t3, 3, m2)
  +t4 = (b3 >= 128 : U32) && (addr >= n2 : U32) && ((addr - n2 : U32) < b3 : U32)
  +b4 = u32.pick(t4, (addr - n2 : U32), b3)
  +m4 = u32.pick(t4, 4, m3)
  +t5 = (b4 >= 128 : U32) && (addr >= n3 : U32) && ((addr - n3 : U32) < b4 : U32)
  +b5 = u32.pick(t5, (addr - n3 : U32), b4)
  +m5 = u32.pick(t5, 5, m4)
  +same = (b5 >= 128 : U32) && U32.is_eq(sm, addr)
  +r768 = (addr % 768 : U32)
  ea.put(same, b5, m5, r768, adr, al,
    (ca[(768 + slot : U32)] <- addr)[r768] <- addr)

# Instructions
# ============

def em.add.k(ins: Array<U32>, adr: Array<U32>, ca: Array<U32>, +dl: U32,
  +il: U32, +al: U32, +slot: U32, +pos: U32, +size: U32, +pt: U32, +ps: U32,
  +pm: U32, +pc: U32, r: Array<U32> & Array<U32>) -> Array<U32> & Em:
  (tgt, dat) = r
  (tgt, em.queue(1, size, 0, Em{dat, ins, adr, ca, (dl + size : U32), il, al,
    slot, (pos + size : U32), pt, ps, pm, pc}))

# ADD: tgt[pos, pos + size) into the data section.
def em.add(tgt: Array<U32>, +pos: U32, +size: U32, em: Em) -> Array<U32> & Em:
  match em:
    case Em{dat, ins, adr, ca, +dl, il, al, slot, uoff, pt, ps, pm, pc}:
      em.add.k(ins, adr, ca, dl, il, al, slot, pos, size, pt, ps, pm, pc,
        B.B.copy(dat, dl, tgt, pos, size))

# RUN: size copies of byte b.
def em.run(+pos: U32, +size: U32, +b: U32, em: Em) -> Em:
  match em:
    case Em{dat, ins, adr, ca, +dl, il, al, slot, uoff, pt, ps, pm, pc}:
      em.queue(2, size, 0, Em{B.B.put(dat, dl, b), ins, adr, ca, (dl + 1 : U32),
        il, al, slot, (pos + size : U32), pt, ps, pm, pc})

def em.copy.k(dat: Array<U32>, ins: Array<U32>, +dl: U32, +il: U32, +slot: U32,
  +pos: U32, +size: U32, +pt: U32, +ps: U32, +pm: U32, +pc: U32, ae: AE) -> Em:
  match ae:
    case AE{ca, adr, +al, +mode}:
      em.queue(3, size, mode, Em{dat, ins, adr, ca, dl, il, al,
        ((slot + 1 : U32) .&. 3 : U32), (pos + size : U32), pt, ps, pm, pc})

def ea.r3(+addr: U32, +here: U32, adr: Array<U32>, +al: U32, +slot: U32,
  +n0: U32, +n1: U32, +n2: U32, r: Array<U32> & U32) -> AE:
  (ca, +n3) = r
  ea.k(addr, here, adr, al, slot, n0, n1, n2, n3, ca[(addr % 768 : U32)])

def ea.r2(+addr: U32, +here: U32, adr: Array<U32>, +al: U32, +slot: U32,
  +n0: U32, +n1: U32, r: Array<U32> & U32) -> AE:
  (ca, +n2) = r
  ea.r3(addr, here, adr, al, slot, n0, n1, n2, ca[771])

def ea.r1(+addr: U32, +here: U32, adr: Array<U32>, +al: U32, +slot: U32,
  +n0: U32, r: Array<U32> & U32) -> AE:
  (ca, +n1) = r
  ea.r2(addr, here, adr, al, slot, n0, n1, ca[770])

def ea.r0(+addr: U32, +here: U32, adr: Array<U32>, +al: U32, +slot: U32,
  r: Array<U32> & U32) -> AE:
  (ca, +n0) = r
  ea.r1(addr, here, adr, al, slot, n0, ca[769])

# COPY: size bytes from window address addr, here being the address of pos.
def em.copy(+pos: U32, +size: U32, +addr: U32, +here: U32, em: Em) -> Em:
  match em:
    case Em{dat, ins, adr, ca, dl, il, +al, +slot, uoff, pt, ps, pm, pc}:
      em.copy.k(dat, ins, dl, il, slot, pos, size, pt, ps, pm, pc,
        ea.r0(addr, here, adr, al, slot, ca[768]))

def em.uoff(em: Em) -> U32 & Em:
  match em:
    case Em{dat, ins, adr, ca, dl, il, al, slot, +uoff, pt, ps, pm, pc}:
      (uoff, Em{dat, ins, adr, ca, dl, il, al, slot, uoff, pt, ps, pm, pc})

def em.gap.if(z: Bool, tgt: Array<U32>, +uoff: U32, +pos: U32, em: Em) ->
  Array<U32> & Em:
  match z:
    case True{}:
      em.add(tgt, uoff, (pos - uoff : U32), em)
    case False{}:
      (tgt, em)

def em.gap.k(tgt: Array<U32>, +pos: U32, r: U32 & Em) -> Array<U32> & Em:
  (+uoff, em) = r
  em.gap.if((uoff < pos : U32), tgt, uoff, pos, em)

# An ADD for the bytes between the last instruction and pos, if any.
def em.gap(tgt: Array<U32>, +pos: U32, em: Em) -> Array<U32> & Em:
  em.gap.k(tgt, pos, em.uoff(em))

def em.inst.go(run: Bool, +pos: U32, +size: U32, +val: U32, +here: U32,
  em: Em) -> Em:
  match run:
    case True{}:
      em.run(pos, size, val, em)
    case False{}:
      em.copy(pos, size, val, here, em)

def em.inst.k(+run: Bool, +pos: U32, +size: U32, +val: U32, +here: U32,
  r: Array<U32> & Em) -> Array<U32> & Em:
  (tgt, em) = r
  (tgt, em.inst.go(run, pos, size, val, here, em))

# A matched instruction at pos: a RUN of byte val, or a COPY from window
# address val. cpl and w0 place pos in the window's address space.
def em.inst(tgt: Array<U32>, +run: Bool, +pos: U32, +size: U32, +val: U32,
  +cpl: U32, +w0: U32, em: Em) -> Array<U32> & Em:
  em.inst.k(run, pos, size, val, (cpl + (pos - w0 : U32) : U32),
    em.gap(tgt, pos, em))

# Instruction buffer
# ==================

# Matches found in a window wait in a buffer, three words each (position,
# length with bit 31 set for a RUN, and the byte or window address), so
# that overlapping ones can be settled before they are written, as in
# xdelta3's iopt buffer.

def io.put(io: Array<U32>, +n: U32, +pos: U32, +len: U32, +val: U32) ->
  Array<U32>:
  +at = (n * 3 : U32)
  ((io[at] <- pos)[(at + 1 : U32)] <- len)[(at + 2 : U32)] <- val

def ent.k2(+pos: U32, +len: U32, r: Array<U32> & U32) -> Array<U32> & Ent:
  (io, +val) = r
  (io, Ent{pos, (len .&. 2147483647 : U32), val, (len >= 2147483648 : U32)})

def ent.k1(+at: U32, +pos: U32, r: Array<U32> & U32) -> Array<U32> & Ent:
  (io, +len) = r
  ent.k2(pos, len, io[(at + 2 : U32)])

def ent.k0(+at: U32, r: Array<U32> & U32) -> Array<U32> & Ent:
  (io, +pos) = r
  ent.k1(at, pos, io[(at + 1 : U32)])

# A buffered match: position, length, byte or address, whether a RUN.
type Ent is Data:
  Ent{pos: U32, len: U32, val: U32, run: Bool}

def io.get(io: Array<U32>, +n: U32) -> Array<U32> & Ent:
  +at = (n * 3 : U32)
  ent.k0(at, io[at])

# Settling overlaps
# =================

# xd3_iopt_flush_instructions, forced: walks the buffered matches with r1
# the one in hand, writing each once no later match can change it.
type FS is Type:
  FS{io: Array<U32>, tgt: Array<U32>, em: Em, r1: Ent, i: U32, has: Bool}

def ent.end(+e: Ent) -> U32:
  match e:
    case Ent{+pos, +len, val, run}:
      (pos + len : U32)

def ent.pos(+e: Ent) -> U32:
  match e:
    case Ent{+pos, len, val, run}:
      pos

def ent.len(+e: Ent) -> U32:
  match e:
    case Ent{pos, +len, val, run}:
      len

# r1 and r2 trimmed so they no longer overlap (the "shorten one of the
# instructions" branch).
type EE is Data:
  EE{a: Ent, b: Ent}

def ee.a(+e: EE) -> Ent:
  match e:
    case EE{+a, b}:
      a

def ee.b(+e: EE) -> Ent:
  match e:
    case EE{a, +b}:
      b

def ent.trim(+r1: Ent, +r2: Ent) -> EE:
  match r1 r2:
    case Ent{+p1, +l1, +v1, +u1} Ent{+p2, +l2, +v2, +u2}:
      +e1 = (p1 + l1 : U32)
      +gap = ((p2 + l2 : U32) - p1 : U32)
      +ns = U32.min(18, (gap - (gap >> 1n : U32) : U32))
      +over = (e1 - p2 : U32)
      +a1 = (l1 - ns : U32)
      +lim = (e1 - a1 : U32)
      +a1b = u32.pick((p2 > lim : U32), (a1 - (p2 - lim : U32) : U32), a1)
      +c1 = (ns > l1 : U32)
      +c2 = (ns > l2 : U32)
      +l1n = u32.pick(c1, l1, u32.pick(c2, (l1 - over : U32), (l1 - a1b : U32)))
      +adj = u32.pick(c1, over, u32.pick(c2, 0, ((p1 + l1n : U32) - p2 : U32)))
      EE{Ent{p1, l1n, v1, u1}, Ent{(p2 + adj : U32), (l2 - adj : U32),
        u32.pick(u2, v2, (v2 + adj : U32)), u2}}

def fs.emit(tgt: Array<U32>, +e: Ent, +cpl: U32, +w0: U32, em: Em) ->
  Array<U32> & Em:
  match e:
    case Ent{+pos, +len, +val, +run}:
      em.inst(tgt, run, pos, len, val, cpl, w0, em)

def fs.emit.if(z: Bool, tgt: Array<U32>, +e: Ent, +cpl: U32, +w0: U32,
  em: Em) -> Array<U32> & Em:
  match z:
    case False{}:
      (tgt, em)
    case True{}:
      fs.emit(tgt, e, cpl, w0, em)

def fs.next(io: Array<U32>, +r1: Ent, +i: U32, +has: Bool, r: Array<U32> & Em) ->
  Bool & FS:
  (tgt, em) = r
  (has, FS{io, tgt, em, r1, i, has})

# One decision, with r2 and r3 the next two buffered matches (r3 only when
# i + 1 < n).
def fs.decide(+n: U32, +cpl: U32, +w0: U32, tgt: Array<U32>, em: Em, +r1: Ent,
  +i: U32, +r2: Ent, r: Array<U32> & Ent) -> Bool & FS:
  (io, +r3) = r
  +e1 = ent.end(r1)
  +p2 = ent.pos(r2)
  +e2 = ent.end(r2)
  +p1 = ent.pos(r1)
  +apart = (e1 <= p2 : U32)
  +has3 = ((i + 1 : U32) < n : U32)
  +drop2 = Bool.not(apart) && has3 && (ent.pos(r3) <= (e1 + 1 : U32) : U32)
  +near = (((e2 - p1 : U32) < 8 : U32) || ((e2 - e1 : U32) <= 2 : U32)
    || ((p2 - p1 : U32) <= 2 : U32))
  +one = Bool.not(apart) && Bool.not(drop2) && near
  +take2 = one && (ent.len(r1) < ent.len(r2) : U32)
  +keep1 = one && Bool.not(take2)
  +trim = Bool.not(apart) && Bool.not(drop2) && Bool.not(near)
  +tt = ent.trim(r1, r2)
  +out = Bool.pick(Ent, trim, ee.a(tt), r1)
  +emit = apart || keep1 || trim
  +nr1 = Bool.pick(Ent, apart || take2, r2,
    Bool.pick(Ent, keep1, r3, Bool.pick(Ent, trim, ee.b(tt), r1)))
  +ni = (i + u32.pick(keep1, 2, 1) : U32)
  +nhas = Bool.not(keep1) || has3
  fs.next(io, nr1, ni, nhas, fs.emit.if(emit, tgt, out, cpl, w0, em))

def fs.r2(+n: U32, +cpl: U32, +w0: U32, tgt: Array<U32>, em: Em, +r1: Ent,
  +i: U32, r: Array<U32> & Ent) -> Bool & FS:
  (io, +r2) = r
  fs.decide(n, cpl, w0, tgt, em, r1, i, r2, io.get(io, (i + 1 : U32)))

def fs.last(io: Array<U32>, +r1: Ent, +i: U32, +cpl: U32, +w0: U32,
  r: Array<U32> & Em) -> Bool & FS:
  (tgt, em) = r
  (False{}, FS{io, tgt, em, r1, i, False{}})

def fs.step.go(z: Bool, +n: U32, +cpl: U32, +w0: U32, io: Array<U32>,
  tgt: Array<U32>, em: Em, +r1: Ent, +i: U32) -> Bool & FS:
  match z:
    case True{}:
      fs.r2(n, cpl, w0, tgt, em, r1, i, io.get(io, i))
    case False{}:
      fs.last(io, r1, i, cpl, w0, fs.emit(tgt, r1, cpl, w0, em))

def fs.step(+n: U32, +cpl: U32, +w0: U32, st: FS) -> Bool & FS:
  match st:
    case FS{io, tgt, em, +r1, +i, has}:
      fs.step.go((i < n : U32), n, cpl, w0, io, tgt, em, r1, i)

def fs.loop(k: Nat, +n: U32, +cpl: U32, +w0: U32, s: Bool & FS) -> FS:
  match k s:
    case 0n Tuple{g, st}:
      st
    case 1n+p Tuple{False{}, st}:
      st
    case 1n+p Tuple{True{}, st}:
      fs.loop(p, n, cpl, w0, fs.step(n, cpl, w0, st))

def fs.done(st: FS) -> Array<U32> & (Array<U32> & Em):
  match st:
    case FS{io, tgt, em, r1, i, has}:
      (io, (tgt, em))

def fs.start(+n: U32, +cpl: U32, +w0: U32, tgt: Array<U32>, em: Em,
  r: Array<U32> & Ent) -> Array<U32> & (Array<U32> & Em):
  (io, +r1) = r
  fs.done(fs.loop(U32.to_nat((n + 1 : U32)), n, cpl, w0,
    (U32.is_ne(n, 0), FS{io, tgt, em, r1, 1, U32.is_ne(n, 0)})))

# Settles and writes the n buffered matches.
def io.flush(io: Array<U32>, +n: U32, +cpl: U32, +w0: U32, tgt: Array<U32>,
  em: Em) -> Array<U32> & (Array<U32> & Em):
  fs.start(n, cpl, w0, tgt, em, io.get(io, 0))

# Writing windows
# ===============

def wr.byte(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +p) = r
  (B.B.put(a, p, v), (p + 1 : U32))

def wr.var(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +p) = r
  B.B.var.put(a, p, v)

def wr.be32(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  wr.byte((v .&. 255 : U32), wr.byte(((v >> 8n : U32) .&. 255 : U32),
    wr.byte(((v >> 16n : U32) .&. 255 : U32), wr.byte((v >> 24n : U32), r))))

def wr.seg(z: Bool, +cpl: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match z:
    case True{}:
      wr.var(0, wr.var(cpl, r))
    case False{}:
      r

def win.secs.k3(+dl: U32, +il: U32, +al: U32, +slot: U32, dat: Array<U32>,
  ins: Array<U32>, ca: Array<U32>, +pos: U32, r: Array<U32> & Array<U32>) ->
  (Array<U32> & U32) & Em:
  (adr, out) = r
  ((out, (pos + al : U32)), Em{dat, ins, adr, ca, 0, 0, 0, 0, 0, 0, 0, 0, 0})

def win.secs.k2(+dl: U32, +il: U32, +al: U32, +slot: U32, dat: Array<U32>,
  adr: Array<U32>, ca: Array<U32>, +pos: U32, r: Array<U32> & Array<U32>) ->
  (Array<U32> & U32) & Em:
  (ins, out) = r
  win.secs.k3(dl, il, al, slot, dat, ins, ca, (pos + il : U32),
    B.B.copy(out, (pos + il : U32), adr, 0, al))

def win.secs.k1(+dl: U32, +il: U32, +al: U32, +slot: U32, ins: Array<U32>,
  adr: Array<U32>, ca: Array<U32>, +pos: U32, r: Array<U32> & Array<U32>) ->
  (Array<U32> & U32) & Em:
  (dat, out) = r
  win.secs.k2(dl, il, al, slot, dat, adr, ca, (pos + dl : U32),
    B.B.copy(out, (pos + dl : U32), ins, 0, il))

# Copies the three sections after the header and empties the emitter.
def win.secs(em: Em, r: Array<U32> & U32) -> (Array<U32> & U32) & Em:
  match em r:
    case Em{dat, ins, adr, ca, +dl, +il, +al, +slot, uoff, pt, ps, pm, pc}
      Tuple{out, pos0}:
      +pos = {pos0 : U32}
      win.secs.k1(dl, il, al, slot, ins, adr, ca, pos,
        B.B.copy(out, pos, dat, 0, dl))

def win.write.fin(tgt: Array<U32>, r: (Array<U32> & U32) & Em) ->
  (Array<U32> & U32) & (Array<U32> & Em):
  (o, em) = r
  (o, (tgt, em))

def win.write.k(out: Array<U32>, +olen: U32, +tlen: U32, +cpl: U32, +enc: U32,
  +need: U32, +dl: U32, +il: U32, +al: U32, em: Em, r: Array<U32> & U32) ->
  (Array<U32> & U32) & (Array<U32> & Em):
  (tgt, +sum) = r
  +ind = u32.pick((0 < cpl : U32), 5, 4)
  win.write.fin(tgt, win.secs(em,
    wr.be32(sum, wr.var(al, wr.var(il, wr.var(dl, wr.byte(0, wr.var(tlen,
      wr.var(enc, wr.seg((0 < cpl : U32), cpl,
        wr.byte(ind, (B.B.grow(out, olen, (olen + need : U32)), olen))))))))))))

# Appends the window for tgt[w0, w0 + tlen) to out (RFC 3284 section 4.2,
# with xdelta3's Adler-32 of the target window).
def win.write(out: Array<U32>, +olen: U32, tgt: Array<U32>, +w0: U32,
  +tlen: U32, +cpl: U32, em: Em) -> (Array<U32> & U32) & (Array<U32> & Em):
  match em:
    case Em{dat, ins, adr, ca, +dl, +il, +al, slot, uoff, pt, ps, pm, pc}:
      +enc = ((((((((1 + B.B.var.len(tlen) : U32) + B.B.var.len(dl) : U32)
        + B.B.var.len(il) : U32) + B.B.var.len(al) : U32) + 4 : U32) + dl : U32)
        + il : U32) + al : U32)
      +hlen = ((1 + u32.pick((0 < cpl : U32), (B.B.var.len(cpl) + 1 : U32), 0) : U32)
        + B.B.var.len(enc) : U32)
      win.write.k(out, olen, tlen, cpl, enc, (hlen + enc : U32), dl, il, al,
        Em{dat, ins, adr, ca, dl, il, al, slot, uoff, pt, ps, pm, pc},
        B.B.adler32(tgt, w0, tlen))

# Hashing
# =======

def H.M() -> U32:
  1597334677

# M^9: removes the byte leaving the large window.
def H.M9() -> U32:
  1614047349

# The large checksum of the 9 bytes from i (xd3_large32_cksum).
def H.large.go(n: Nat, +h: U32, +i: U32, r: Array<U32> & U32) ->
  Array<U32> & U32:
  match n:
    case 0n:
      (a, x) = r
      (a, h)
    case 1n+p:
      (a, +x) = r
      +i2 = (i + 1 : U32)
      H.large.go(p, ((h * H.M() : U32) + x : U32), i2, B.B.get(a, i2))

def H.large(a: Array<U32>, +i: U32) -> Array<U32> & U32:
  H.large.go(9n, 0, i, B.B.get(a, i))

# A table slot: the hash's top bits folded onto its low bits.
def H.slot(+h: U32, +sh: Nat, +mask: U32) -> U32:
  ((h >> sh : U32) .^. (h .&. mask : U32) : U32)

# Source index
# ============

# Indexes n positions q, q - 8, ..., r holding the checksum at q
# (xd3_srcwin_move_point within one block: in reverse, so the earliest
# position of a block wins its slot).
def ix.go(n: Nat, lt: Array<U32>, +q: U32, +sh: Nat, +mask: U32,
  r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (src, h) = r
      (src, lt)
    case 1n+p:
      (src, +h) = r
      lt2 = lt[H.slot(h, sh, mask)] <- (q + 1 : U32)
      +q2 = (q - 8 : U32)
      ix.go(p, lt2, q2, sh, mask, H.large(src, q2))

def ix.block.if(z: Bool, src: Array<U32>, lt: Array<U32>, +b0: U32,
  +len: U32, +sh: Nat, +mask: U32) -> Array<U32> & Array<U32>:
  match z:
    case False{}:
      (src, lt)
    case True{}:
      +top = (b0 + (len - 9 : U32) : U32)
      ix.go(U32.to_nat((((len - 9 : U32) >> 3n : U32) + 1 : U32)), lt, top, sh,
        mask, H.large(src, top))

# Indexes the block [b0, b0 + len) of the source.
def ix.block(src: Array<U32>, lt: Array<U32>, +b0: U32, +len: U32, +sh: Nat,
  +mask: U32) -> Array<U32> & Array<U32>:
  ix.block.if((9 <= len : U32), src, lt, b0, len, sh, mask)

# Indexes n blocks of size blk from b0.
def ix.blocks(n: Nat, +b0: U32, +slen: U32, +blk: U32, +sh: Nat, +mask: U32,
  r: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      r
    case 1n+p:
      (src, lt) = r
      ix.blocks(p, (b0 + blk : U32), slen, blk, sh, mask,
        ix.block(src, lt, b0, U32.min(blk, (slen - b0 : U32)), sh, mask))

# Scanning
# ========

# The fixed facts of a window: the source length, the window [w0, w1), the
# copy segment length, the hash table shapes and the buffer capacity.
type SK is Data:
  SK{slen: U32, w0: U32, w1: U32, cpl: U32, lsh: U32, lmask: U32, ssh: U32,
    smask: U32, cap: U32}

# The scan of a window: the arrays (source, target, large and small hash
# tables, the small table's chains, the match buffer, the emitter) and the
# position, the minimum match length, the run byte and length, the large
# checksum, the last source position tried, the buffered match count and
# the source position a match reaching the window's end continues at.
type Sc is Type:
  Sc{src: Array<U32>, tgt: Array<U32>, lt: Array<U32>, stb: Array<U32>,
    spv: Array<U32>, io: Array<U32>, em: Em, p: U32, mm: U32, rc: U32,
    rl: U32, lck: U32, last: U32, nio: U32, cont: U32}

def NONE() -> U32:
  4294967295

def PMASK() -> U32:
  262143

# Buffering a match
# -----------------

def sc.push.k(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32,
  +last: U32, +cont: U32, +pos: U32, +len: U32, +val: U32,
  r: Array<U32> & (Array<U32> & Em)) -> Sc:
  (io, te) = r
  (tgt, em) = te
  Sc{src, tgt, lt, stb, spv, io.put(io, 0, pos, len, val), em, p, mm, rc, rl,
    lck, last, 1, cont}

def sc.push.go(full: Bool, +K: SK, +pos: U32, +len: U32, +val: U32, st: Sc) ->
  Sc:
  match full K st:
    case False{} k Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last,
      +nio, cont}:
      Sc{src, tgt, lt, stb, spv, io.put(io, nio, pos, len, val), em, p, mm, rc,
        rl, lck, last, (nio + 1 : U32), cont}
    case True{} SK{slen, +w0, w1, +cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, +nio, cont}:
      sc.push.k(src, lt, stb, spv, p, mm, rc, rl, lck, last, cont, pos, len,
        val, io.flush(io, nio, cpl, w0, tgt, em))

def sc.nio(+K: SK, st: Sc) -> Bool & Sc:
  match K st:
    case SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, +cap}
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, +nio, cont}:
      (U32.is_eq(nio, cap), Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl,
        lck, last, nio, cont})

def sc.push.k0(+K: SK, +pos: U32, +len: U32, +val: U32, r: Bool & Sc) -> Sc:
  (full, st) = r
  sc.push.go(full, K, pos, len, val, st)

# Buffers a match (flushing the buffer first when it is full).
def sc.push(+K: SK, +pos: U32, +len: U32, +val: U32, st: Sc) -> Sc:
  sc.push.k0(K, pos, len, val, sc.nio(K, st))

# Drops the buffered matches that start at or after pos: a source match
# extended backwards covers them (xd3_iopt_erase).
def er.k(+pos: U32, +n: U32, r: Array<U32> & U32) -> Bool & (U32 & Array<U32>):
  (io, +q) = r
  +drop = (q >= pos : U32)
  (drop && (1 < n : U32), (u32.pick(drop, (n - 1 : U32), n), io))

def er.loop(k: Nat, +pos: U32, s: Bool & (U32 & Array<U32>)) ->
  U32 & Array<U32>:
  match k s:
    case 0n Tuple{g, r}:
      r
    case 1n+p Tuple{False{}, r}:
      r
    case 1n+p Tuple{True{}, Tuple{n0, io}}:
      +n = {n0 : U32}
      er.loop(p, pos, er.k(pos, n, io[((n - 1 : U32) * 3 : U32)]))

def sc.erase.k(src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +cont: U32, r: U32 & Array<U32>) -> Sc:
  (+nio, io) = r
  Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont}

def sc.erase(+pos: U32, st: Sc) -> Sc:
  match st:
    case Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, +nio,
      cont}:
      sc.erase.k(src, tgt, lt, stb, spv, em, p, mm, rc, rl, lck, last, cont,
        er.loop(U32.to_nat(nio), pos, ((0 < nio : U32), (nio, io))))

# Moving on
# ---------

def sc.upd.k3(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32, +bin: U32,
  +bout: U32, r: Array<U32> & U32) -> Sc:
  (tgt, +b9) = r
  +same = U32.is_eq(bin, rc)
  Sc{src, tgt, lt, stb, spv, io, em, (p + 1 : U32), mm, bin,
    u32.pick(same, (rl + 1 : U32), 1),
    (((lck * H.M() : U32) - (bout * H.M9() : U32) : U32) + b9 : U32),
    last, nio, cont}

def sc.upd.k2(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32, +bin: U32,
  r: Array<U32> & U32) -> Sc:
  (tgt, +bout) = r
  sc.upd.k3(src, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont,
    bin, bout, B.B.get(tgt, (p + 9 : U32)))

def sc.upd.k1(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32,
  r: Array<U32> & U32) -> Sc:
  (tgt, +bin) = r
  sc.upd.k2(src, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont,
    bin, B.B.get(tgt, p))

# Advances one byte, rolling the run and the large checksum.
def sc.update(+K: SK, st: Sc) -> Bool & Sc:
  match K st:
    case SK{slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last, nio, cont}:
      (((p + 5 : U32) <= w1 : U32),
        sc.upd.k1(src, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
          cont, B.B.get(tgt, (p + 4 : U32))))

def sc.rs.k4(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +w1: U32, +mm: U32,
  +rc: U32, +rl: U32, +last: U32, +nio: U32, +cont: U32,
  r: Array<U32> & U32) -> Bool & Sc:
  (tgt, +lck) = r
  (((p + 4 : U32) <= w1 : U32),
    Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont})

def sc.rs.k3(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +w1: U32, +mm: U32,
  +last: U32, +nio: U32, +cont: U32, r: Array<U32> & U32) -> Bool & Sc:
  (tgt, +w) = r
  +b0 = (w .&. 255 : U32)
  +b1 = ((w >> 8n : U32) .&. 255 : U32)
  +b2 = ((w >> 16n : U32) .&. 255 : U32)
  +b3 = (w >> 24n : U32)
  +l1 = u32.pick(U32.is_eq(b1, b0), 2, 1)
  +l2 = u32.pick(U32.is_eq(b2, b1), (l1 + 1 : U32), 1)
  +l3 = u32.pick(U32.is_eq(b3, b2), (l2 + 1 : U32), 1)
  sc.rs.k4(src, lt, stb, spv, io, em, p, w1, mm, b3, l3, last, nio, cont,
    H.large(tgt, p))

def sc.rs.k2(src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, em: Em, +p: U32, +w1: U32, +last: U32,
  +nio: U32, +cont: U32, +q: U32, r: Array<U32> & U32) -> Bool & Sc:
  (io, +len) = r
  +le = u32.pick((0 < nio : U32), (q + (len .&. 2147483647 : U32) : U32), 0)
  +mm = u32.pick((p < le : U32), u32.max(4, ((le + 1 : U32) - p : U32)), 4)
  sc.rs.k3(src, lt, stb, spv, io, em, p, w1, mm, last, nio, cont,
    B.B.word(tgt, p))

def sc.rs.k1(src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, em: Em, +p: U32, +w1: U32, +last: U32,
  +nio: U32, +cont: U32, r: Array<U32> & U32) -> Bool & Sc:
  (io, +q) = r
  sc.rs.k2(src, tgt, lt, stb, spv, em, p, w1, last, nio, cont, q,
    io[((((nio - 1 : U32) * 3 : U32)) + 1 : U32)])

# Starts afresh at p: recomputes the minimum match from the last buffered
# match, the run and the large checksum (xdelta3's restartloop).
def sc.restart(+K: SK, st: Sc) -> Bool & Sc:
  match K st:
    case SK{slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, +last, +nio, cont}:
      sc.rs.k1(src, tgt, lt, stb, spv, em, p, w1, last, nio, cont,
        io[((nio - 1 : U32) * 3 : U32)])

def sc.lazy.go(z: Bool, +K: SK, +L: U32, st: Sc) -> Bool & Sc:
  match z st:
    case True{} Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last,
      nio, cont}:
      sc.update(K, Sc{src, tgt, lt, stb, spv, io, em, p, L, rc, rl, lck, last,
        nio, cont})
    case False{} Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last,
      nio, cont}:
      sc.restart(K, Sc{src, tgt, lt, stb, spv, io, em, (p + L : U32), mm, rc,
        rl, lck, last, nio, cont})

# After a match of L bytes at p: a short one is followed by lazy matching
# from p + 1, demanding at least as long a match; a long one is taken and
# the scan restarts after it (xdelta3's HANDLELAZY).
def sc.lazy(+K: SK, +L: U32, st: Sc) -> Bool & Sc:
  match K st:
    case SK{slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last, nio, cont}:
      sc.lazy.go((L < 18 : U32) && (((p + L : U32) + 2 : U32) <= w1 : U32), K, L,
        Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont})

# Runs
# ----

def ph.run.if(z: Bool, +K: SK, +L: U32, st: Sc) -> Bool & (Bool & Sc):
  match z st:
    case False{} s:
      (False{}, (True{}, s))
    case True{} Sc{src, tgt, lt, stb, spv, io, em, +p, mm, +rc, rl, lck, last,
      nio, cont}:
      (True{}, sc.lazy(K, L, sc.push(K, p, (L .|. 2147483648 : U32), rc,
        Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
          cont})))

def ph.run.k(+K: SK, src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +lck: U32, +last: U32, +nio: U32, +cont: U32, r: Array<U32> & U32) ->
  Bool & (Bool & Sc):
  (tgt, +n) = r
  +L = (4 + n : U32)
  ph.run.if((mm <= L : U32) && (8 <= L : U32), K, L,
    Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, L, lck, last, nio, cont})

def ph.run.go(z: Bool, +K: SK, st: Sc) -> Bool & (Bool & Sc):
  match z K st:
    case False{} k s:
      (False{}, (True{}, s))
    case True{} SK{slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, +p, mm, +rc, rl, lck, last, nio, cont}:
      ph.run.k(K, src, lt, stb, spv, io, em, p, mm, rc, lck, last, nio, cont,
        B.B.same(tgt, (p + 4 : U32), rc, (w1 - (p + 4 : U32) : U32)))

def sc.rl(st: Sc) -> U32 & Sc:
  match st:
    case Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, +rl, lck, last, nio,
      cont}:
      (rl, Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
        cont})

def ph.run.k0(+K: SK, r: U32 & Sc) -> Bool & (Bool & Sc):
  (+rl, st) = r
  ph.run.go(U32.is_eq(rl, 4), K, st)

# A run starting at p (xdelta3 looks once four equal bytes begin one).
def ph.run(+K: SK, st: Sc) -> Bool & (Bool & Sc):
  ph.run.k0(K, sc.rl(st))

def sc.erase.if(z: Bool, +pos: U32, st: Sc) -> Sc:
  match z:
    case True{}:
      sc.erase(pos, st)
    case False{}:
      st

# Notes where a match reaching the window's end continues in the source.
def sc.cont(+K: SK, +end: U32, +at: U32, st: Sc) -> Sc:
  match K st:
    case SK{slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, +cont}:
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
        u32.pick(U32.is_eq(end, w1), at, cont)}

# Source matches
# --------------

def ph.large.k3(+K: SK, lt: Array<U32>, stb: Array<U32>, spv: Array<U32>,
  io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32,
  +last: U32, +nio: U32, +cont: U32, +srcpos: U32, +fwd: U32,
  r: (Array<U32> & Array<U32>) & U32) -> Bool & (Bool & Sc):
  (st2, +back) = r
  (src, tgt) = st2
  +pos = (p - back : U32)
  +len = (fwd + back : U32)
  (True{}, sc.lazy(K, fwd, sc.cont(K, (pos + len : U32), (srcpos + fwd : U32),
    sc.push(K, pos, len, (srcpos - back : U32), sc.erase.if((0 < back : U32), pos,
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
        cont})))))

def ph.large.if(z: Bool, +K: SK, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32, +srcpos: U32,
  +maxback: U32, +fwd: U32, src: Array<U32>, tgt: Array<U32>) ->
  Bool & (Bool & Sc):
  match z:
    case False{}:
      (False{}, (True{}, Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck,
        last, nio, cont}))
    case True{}:
      ph.large.k3(K, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont,
        srcpos, fwd, B.B.back(src, srcpos, tgt, p, maxback))

def ph.large.k2(+K: SK, lt: Array<U32>, stb: Array<U32>, spv: Array<U32>,
  io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32,
  +last: U32, +nio: U32, +cont: U32, +srcpos: U32, +maxback: U32,
  r: (Array<U32> & Array<U32>) & U32) -> Bool & (Bool & Sc):
  (st2, +fwd) = r
  (src, tgt) = st2
  ph.large.if((mm <= fwd : U32), K, lt, stb, spv, io, em, p, mm, rc, rl, lck,
    last, nio, cont, srcpos, maxback, fwd, src, tgt)

def ph.large.u(+K: SK, src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, io: Array<U32>, +p: U32, +mm: U32,
  +rc: U32, +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32,
  +srcpos: U32, r: U32 & Em) -> Bool & (Bool & Sc):
  match K r:
    case SK{+slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap} Tuple{u0, em}:
      +uoff = {u0 : U32}
      ph.large.k2(K, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont,
        srcpos, U32.min((p - uoff : U32), srcpos),
        B.B.fwd(src, srcpos, tgt, p, U32.min((w1 - p : U32), (slen - srcpos : U32))))

def ph.large.try(z: Bool, +K: SK, src: Array<U32>, tgt: Array<U32>,
  lt: Array<U32>, stb: Array<U32>, spv: Array<U32>, io: Array<U32>, em: Em,
  +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32, +last: U32, +nio: U32,
  +cont: U32, +srcpos: U32) -> Bool & (Bool & Sc):
  match z:
    case False{}:
      (False{}, (True{}, Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck,
        last, nio, cont}))
    case True{}:
      ph.large.u(K, src, tgt, lt, stb, spv, io, p, mm, rc, rl, lck, last, nio,
        cont, srcpos, em.uoff(em))

def ph.large.k1(+K: SK, src: Array<U32>, tgt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32,
  r: Array<U32> & U32) -> Bool & (Bool & Sc):
  (lt, +cand) = r
  +srcpos = (cand - 1 : U32)
  +hit = U32.is_ne(cand, 0)
  +again = U32.is_ne(srcpos, 0) && U32.is_eq(srcpos, last)
  ph.large.try(hit && Bool.not(again), K, src, tgt, lt, stb, spv, io, em, p, mm,
    rc, rl, lck, u32.pick(hit, srcpos, last), nio, cont, srcpos)

def ph.large.go(z: Bool, +K: SK, st: Sc) -> Bool & (Bool & Sc):
  match z K st:
    case False{} k s:
      (False{}, (True{}, s))
    case True{} SK{slen, w0, w1, cpl, +lsh, +lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, +lck, last, nio, cont}:
      ph.large.k1(K, src, tgt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
        cont, lt[H.slot(lck, U32.to_nat(lsh), lmask)])

def sc.pos(st: Sc) -> U32 & Sc:
  match st:
    case Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last, nio,
      cont}:
      (p, Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont})

def ph.large.k0(+K: SK, r: U32 & Sc) -> Bool & (Bool & Sc):
  match K r:
    case SK{+slen, w0, +w1, cpl, lsh, lmask, ssh, smask, cap} Tuple{p0, st}:
      +p = {p0 : U32}
      ph.large.go((0 < slen : U32) && ((p + 9 : U32) <= w1 : U32), K, st)

# A source match: the large checksum's slot names a source position; the
# match is extended forward and, over not yet written bytes, backward
# (xd3_source_match_setup and xd3_source_extend_match).
def ph.large(+K: SK, st: Sc) -> Bool & (Bool & Sc):
  ph.large.k0(K, sc.pos(st))

# Target matches
# --------------

# A chain search: the target and the chains, the best length and where it
# starts, the position to try and the tries left.
type CS is Type:
  CS{tgt: Array<U32>, spv: Array<U32>, best: U32, off: U32, base: U32,
    chain: U32}

def cs.k2(+p: U32, +w0: U32, tgt: Array<U32>, +best: U32, +off: U32,
  +base: U32, +chain: U32, stop: Bool, r: Array<U32> & U32) -> Bool & CS:
  (spv, +prev) = r
  +pb = (prev - 1 : U32)
  +go = Bool.not(stop) && (0 < chain : U32) && U32.is_ne(prev, 0)
    && (pb < base : U32) && (w0 <= pb : U32) && ((p - pb : U32) <= PMASK() : U32)
  (go, CS{tgt, spv, best, off, pb, chain})

def cs.k1(+p: U32, +w1: U32, +w0: U32, spv: Array<U32>, +best: U32,
  +off: U32, +base: U32, +chain: U32, r: Array<U32> & U32) -> Bool & CS:
  (tgt, +len) = r
  +better = (best < len : U32)
  +stop = better && (U32.is_eq((p + len : U32), w1) || (35 <= len : U32))
  cs.k2(p, w0, tgt, u32.pick(better, len, best), u32.pick(better, base, off),
    base, (chain - 1 : U32), stop, spv[(base .&. PMASK() : U32)])

def cs.step(+p: U32, +w1: U32, +w0: U32, st: CS) -> Bool & CS:
  match st:
    case CS{tgt, spv, best, off, +base, chain}:
      cs.k1(p, w1, w0, spv, best, off, base, chain,
        B.B.fwd1(tgt, base, p, (w1 - p : U32)))

def cs.loop(k: Nat, +p: U32, +w1: U32, +w0: U32, s: Bool & CS) -> CS:
  match k s:
    case 0n Tuple{g, st}:
      st
    case 1n+q Tuple{False{}, st}:
      st
    case 1n+q Tuple{True{}, st}:
      cs.loop(q, p, w1, w0, cs.step(p, w1, w0, st))

def ph.small.if(z: Bool, +K: SK, +len: U32, +addr: U32, st: Sc) ->
  Bool & (Bool & Sc):
  match z st:
    case False{} s:
      (False{}, (True{}, s))
    case True{} Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last,
      nio, cont}:
      (True{}, sc.lazy(K, len, sc.push(K, p, len, addr,
        Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
          cont})))

def ph.small.fin(+K: SK, src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32,
  +last: U32, +nio: U32, +cont: U32, cs: CS) -> Bool & (Bool & Sc):
  match K cs:
    case SK{slen, +w0, w1, +cpl, lsh, lmask, ssh, smask, cap}
      CS{tgt, spv, +best, +off, base, chain}:
      +dist = (p - off : U32)
      +poor = (U32.is_eq(best, 4) && (16384 <= dist : U32))
        || (U32.is_eq(best, 5) && (2097152 <= dist : U32))
      ph.small.if(Bool.not(poor) && (mm <= best : U32), K, best,
        (cpl + (off - w0 : U32) : U32),
        Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio, cont})

def ph.small.k2(+K: SK, src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32, +slot: U32,
  r: Array<U32> & U32) -> Bool & (Bool & Sc):
  match K r:
    case SK{slen, +w0, +w1, cpl, lsh, lmask, ssh, smask, cap} Tuple{stb, h0}:
      +head = {h0 : U32}
      +base = (head - 1 : U32)
      +ok = U32.is_ne(head, 0) && (w0 <= base : U32) && (base < p : U32)
      ph.small.fin(K, src, lt, stb[slot] <- (p + 1 : U32), io, em, p, mm, rc,
        rl, lck, last, nio, cont,
        cs.loop(5n, p, w1, w0, (ok, CS{tgt, spv[(p .&. PMASK() : U32)] <- head,
          0, 0, base, u32.pick(U32.is_eq(mm, 4), 4, 1)})))

def ph.small.k1(+K: SK, src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, em: Em, +p: U32, +mm: U32, +rc: U32,
  +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32,
  r: Array<U32> & U32) -> Bool & (Bool & Sc):
  match K r:
    case SK{slen, w0, w1, cpl, lsh, lmask, +ssh, +smask, cap} Tuple{tgt, w}:
      +slot = H.slot((w * H.M() : U32), U32.to_nat(ssh), smask)
      ph.small.k2(K, src, tgt, lt, spv, io, em, p, mm, rc, rl, lck, last, nio,
        cont, slot, stb[slot])

# A target match: the 4-byte checksum's chain names earlier positions of
# this window; the position is then entered at the chain's head (xd3_smatch
# and xd3_scksum_insert).
def ph.small(+K: SK, st: Sc) -> Bool & (Bool & Sc):
  match st:
    case Sc{src, tgt, lt, stb, spv, io, em, +p, mm, rc, rl, lck, last, nio,
      cont}:
      ph.small.k1(K, src, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, nio,
        cont, B.B.word(tgt, p))

# Stepping
# --------

def sc.next(+K: SK, st: Sc) -> Bool & Sc:
  match st:
    case Sc{src, tgt, lt, stb, spv, io, em, p, +mm, rc, rl, lck, last, nio,
      cont}:
      sc.update(K, Sc{src, tgt, lt, stb, spv, io, em, p,
        u32.pick((4 < mm : U32), (mm - 1 : U32), mm), rc, rl, lck, last, nio,
        cont})

def sc.s3(+K: SK, r: Bool & (Bool & Sc)) -> Bool & Sc:
  match r:
    case Tuple{True{}, res}:
      res
    case Tuple{False{}, Tuple{c, st}}:
      sc.next(K, st)

def sc.s2(+K: SK, r: Bool & (Bool & Sc)) -> Bool & Sc:
  match r:
    case Tuple{True{}, res}:
      res
    case Tuple{False{}, Tuple{c, st}}:
      sc.s3(K, ph.small(K, st))

def sc.s1(+K: SK, r: Bool & (Bool & Sc)) -> Bool & Sc:
  match r:
    case Tuple{True{}, res}:
      res
    case Tuple{False{}, Tuple{c, st}}:
      sc.s2(K, ph.large(K, st))

# One position of xdelta3's string-matching loop: a run, else a source
# match, else a target match, else on to the next byte.
def sc.step(+K: SK, st: Sc) -> Bool & Sc:
  sc.s1(K, ph.run(K, st))

def sc.loop(k: Nat, +K: SK, s: Bool & Sc) -> Sc:
  match k s:
    case 0n Tuple{g, st}:
      st
    case 1n+q Tuple{False{}, st}:
      st
    case 1n+q Tuple{True{}, st}:
      sc.loop(q, K, sc.step(K, st))

# Windows
# =======

# The fixed facts of an encoding: the lengths, the window size, the source
# block size and the table shapes.
type EK is Data:
  EK{slen: U32, tlen: U32, wsz: U32, blk: U32, lsh: U32, lmask: U32, ssh: U32,
    smask: U32, cap: U32}

# The state between windows.
type ES is Type:
  ES{src: Array<U32>, tgt: Array<U32>, lt: Array<U32>, stb: Array<U32>,
    spv: Array<U32>, io: Array<U32>, em: Em, out: Array<U32>, olen: U32,
    lidx: U32, cont: U32}

def cache.clear.go(n: Nat, a: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      a2 = a[i] <- 0
      cache.clear.go(p, a2, (i + 1 : U32))

# A fresh emitter for a window starting at w0 (xd3_init_cache).
def em.reset(+w0: U32, em: Em) -> Em:
  match em:
    case Em{dat, ins, adr, ca, dl, il, al, slot, uoff, pt, ps, pm, pc}:
      Em{dat, ins, adr, cache.clear.go(772n, ca, 0), 0, 0, 0, 0, w0, 0, 0, 0, 0}

def win.fin.k3(src: Array<U32>, lt: Array<U32>, stb: Array<U32>,
  spv: Array<U32>, io: Array<U32>, +lidx: U32, +cont: U32,
  r: (Array<U32> & U32) & (Array<U32> & Em)) -> ES:
  (o, te) = r
  (out, olen) = o
  (tgt, em) = te
  ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, cont}

def win.fin.k2(+E: EK, +w0: U32, +w1: U32, src: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, io: Array<U32>, out: Array<U32>,
  +olen: U32, +lidx: U32, +cont: U32, r: Array<U32> & Em) -> ES:
  match E r:
    case EK{+slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap} Tuple{tgt, em}:
      win.fin.k3(src, lt, stb, spv, io, lidx, cont,
        win.write(out, olen, tgt, w0, (w1 - w0 : U32), slen, em.flush(em)))

def win.fin.k1(+E: EK, +w0: U32, +w1: U32, src: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, out: Array<U32>, +olen: U32, +lidx: U32,
  +cont: U32, r: Array<U32> & (Array<U32> & Em)) -> ES:
  (io, te) = r
  (tgt, em) = te
  win.fin.k2(E, w0, w1, src, lt, stb, spv, io, out, olen, lidx, cont,
    em.gap(tgt, w1, em))

# Settles the window's matches, writes the rest of it as an ADD and appends
# the window to the output.
def win.fin(+E: EK, +w0: U32, +w1: U32, out: Array<U32>, +olen: U32,
  +lidx: U32, st: Sc) -> ES:
  match E st:
    case EK{+slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}
      Sc{src, tgt, lt, stb, spv, io, em, p, mm, rc, rl, lck, last, +nio, +cont}:
      win.fin.k1(E, w0, w1, src, lt, stb, spv, out, olen, lidx, cont,
        io.flush(io, nio, slen, w0, tgt, em))

def win.scan(+E: EK, +K: SK, +w0: U32, +w1: U32, out: Array<U32>, +olen: U32,
  +lidx: U32, st: Sc) -> ES:
  win.fin(E, w0, w1, out, olen, lidx,
    sc.loop(U32.to_nat(((w1 - w0 : U32) + 2 : U32)), K, sc.restart(K, st)))

def io.put.if(z: Bool, io: Array<U32>, +pos: U32, +len: U32, +val: U32) ->
  Array<U32>:
  match z:
    case True{}:
      io.put(io, 0, pos, len, val)
    case False{}:
      io

# xdelta3's MATCH_TARGET: at the start of a window, the source match that
# reached the end of the last one (or, at first, the source's start) is
# tried as it stands.
def win.start.k(+E: EK, +K: SK, +w0: U32, +w1: U32, +at: U32, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, io: Array<U32>, em: Em, out: Array<U32>,
  +olen: U32, +lidx: U32, r: (Array<U32> & Array<U32>) & U32) -> ES:
  (st2, +fwd) = r
  (src, tgt) = st2
  +ok = (4 <= fwd : U32)
  +p = u32.pick(ok, (w0 + fwd : U32), w0)
  win.scan(E, K, w0, w1, out, olen, lidx,
    Sc{src, tgt, lt, stb, spv, io.put.if(ok, io, w0, fwd, at), em, p, 4, 0, 0, 0,
      NONE(), u32.pick(ok, 1, 0),
      u32.pick(ok && U32.is_eq(p, w1), (at + fwd : U32), NONE())})

def win.start(+E: EK, +K: SK, +w0: U32, +w1: U32, st: ES) -> ES:
  match E st:
    case EK{+slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}
      ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, +cont}:
      +at = u32.pick((cont < slen : U32), cont, slen)
      win.start.k(E, K, w0, w1, at, lt, stb, spv, io, em.reset(w0, em), out,
        olen, lidx,
        B.B.fwd(src, at, tgt, w0, U32.min((w1 - w0 : U32), (slen - at : U32))))

def win.index.k(+lidx: U32, r: Array<U32> & Array<U32>) -> U32 & (Array<U32> & Array<U32>):
  (lidx, r)

def win.index.fin(tgt: Array<U32>, stb: Array<U32>, spv: Array<U32>,
  io: Array<U32>, em: Em, out: Array<U32>, +olen: U32, +lidx: U32, +cont: U32,
  r: Array<U32> & Array<U32>) -> ES:
  (src, lt) = r
  ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, cont}

# Indexes the source up to the furthest of 64 MiB and 32 MiB past the
# window (xd3_srcwin_move_point), a block at a time.
def win.index(+E: EK, +w1: U32, st: ES) -> ES:
  match E st:
    case EK{+slen, tlen, wsz, +blk, +lsh, +lmask, ssh, smask, cap}
      ES{src, tgt, lt, stb, spv, io, em, out, olen, +lidx, cont}:
      +want = U32.min(slen, u32.max(67108864, (w1 + 33554432 : U32)))
      +nb = u32.pick((lidx < want : U32),
        ((((want - lidx : U32) + blk : U32) - 1 : U32) / blk : U32), 0)
      win.index.fin(tgt, stb, spv, io, em, out, olen, (lidx + (nb * blk : U32) : U32),
        cont, ix.blocks(U32.to_nat(nb), lidx, slen, blk, U32.to_nat(lsh), lmask,
          (src, lt)))

# Encodes the window starting at w0.
def win.enc(+E: EK, +w0: U32, st: ES) -> ES:
  match E:
    case EK{+slen, +tlen, +wsz, blk, +lsh, +lmask, +ssh, +smask, +cap}:
      +w1 = U32.min(tlen, (w0 + wsz : U32))
      win.start(E, SK{slen, w0, w1, slen, lsh, lmask, ssh, smask, cap}, w0, w1,
        win.index(E, w1, st))

def win.loop(k: Nat, +E: EK, +w0: U32, st: ES) -> ES:
  match k E:
    case 0n e:
      st
    case 1n+p EK{slen, tlen, +wsz, blk, lsh, lmask, ssh, smask, cap}:
      win.loop(p, E, (w0 + wsz : U32), win.enc(E, w0, st))

# Encoding
# ========

# xdelta3's defaults: 8 MiB target windows; a large table of one slot per 8
# source bytes of the first 64 MiB (as rounded up), the source indexed in
# blocks of all of it (if under 64 MiB) or of 2 MiB; a small table of one
# slot per target byte of a window; a buffer of 2^20 matches.
def EK.mk(+slen: U32, +tlen: U32) -> EK:
  +lb = U32.from_nat(B.B.depth(u32.max(slen, 16384)))
  +small = (slen <= 67108864 : U32)
  +lbits = u32.pick(small, u32.max(3, (lb - 3 : U32)), 23)
  +sbits = U32.min(23, U32.from_nat(B.B.depth(u32.max(tlen, 16384))))
  EK{slen, tlen, 8388608, u32.pick(small, (1 << U32.to_nat(lb) : U32), 2097152),
    (32 - lbits : U32), ((1 << U32.to_nat(lbits) : U32) - 1 : U32),
    (32 - sbits : U32), ((1 << U32.to_nat(sbits) : U32) - 1 : U32), 1048576}

def enc.done(+slen: U32, +tlen: U32, st: ES) -> (B.Bytes & B.Bytes) & B.Bytes:
  match st:
    case ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, cont}:
      ((B.Bytes{slen, src}, B.Bytes{tlen, tgt}), B.Bytes{olen, out})

# Parallel windows
# ================

# Windows are encoded in parallel, each range of them in a task of its own
# with copies of the source, the target and the source index. A task's
# index is the sequential one at its first window (it indexes from where
# the index stood, in the same order), so only xdelta3's MATCH_TARGET guess
# differs at a task's first window: it tries the source at the window's own
# offset.

# A task's own tables, emitter and output.
def es.fresh(+sbits: Nat, +wb: U32, +ocap: U32, src: Array<U32>,
  tgt: Array<U32>, lt: Array<U32>, +lidx: U32, +cont: U32) -> ES:
  ES{src, tgt, lt, Array.new(U32, sbits, 0), Array.new(U32, 18n, 0),
    Array.new(U32, 22n, 0),
    Em{B.B.zeros(wb), B.B.zeros((wb * 4 : U32)), B.B.zeros((wb * 2 : U32)),
      Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0},
    B.B.zeros(ocap), 0, lidx, cont}

def es.join.k(src: Array<U32>, tgt: Array<U32>, lt: Array<U32>,
  stb: Array<U32>, spv: Array<U32>, io: Array<U32>, em: Em, +olen: U32,
  +lidx: U32, +cont: U32, r: Array<U32> & Array<U32>) -> ES:
  (rout, out) = r
  ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, cont}

# The windows of l, then those of r.
def es.join(l: ES, r: ES) -> ES:
  match l r:
    case ES{src, tgt, lt, stb, spv, io, em, out, +olen, lidx, cont}
      ES{rs, rt, rl, rstb, rspv, rio, rem, rout, +rolen, +rlidx, +rcont}:
      es.join.k(src, tgt, lt, stb, spv, io, em, (olen + rolen : U32), rlidx, rcont,
        B.B.copy(B.B.grow(out, olen, (olen + rolen : U32)), olen, rout, 0, rolen))

def es.split.k(+sbits: Nat, +wb: U32, +wm: U32, +ocap: U32,
  sc: Array<U32> & Array<U32>, tc: Array<U32> & Array<U32>,
  lc: Array<U32> & Array<U32>, stb: Array<U32>, spv: Array<U32>,
  io: Array<U32>, em: Em, out: Array<U32>, +olen: U32, +lidx: U32,
  +cont: U32) -> ES & ES:
  (s1, s2) = sc
  (t1, t2) = tc
  (l1, l2) = lc
  (ES{s1, t1, l1, stb, spv, io, em, out, olen, lidx, cont},
    es.fresh(sbits, wb, ocap, s2, t2, l2, lidx, wm))

# Two states for the halves of the nw windows from w0: this one, and a
# fresh one with copies of the source, the target and the index.
def es.split(+E: EK, +sbits: Nat, +wb: U32, +w0: U32, +nw: U32, st: ES) ->
  ES & ES:
  match E st:
    case EK{slen, tlen, +wsz, blk, lsh, lmask, ssh, smask, cap}
      ES{src, tgt, lt, stb, spv, io, em, out, olen, lidx, cont}:
      +nl = (nw >> 1n : U32)
      +nr = (nw - nl : U32)
      es.split.k(sbits, wb, (w0 + (nl * wsz : U32) : U32),
        u32.max(((nr * wsz : U32) >> 3n : U32), 4096), Array.clone(U32, src),
        Array.clone(U32, tgt), Array.clone(U32, lt), stb, spv, io, em, out, olen,
        lidx, cont)

def EK.wsz(+E: EK) -> U32:
  match E:
    case EK{slen, tlen, wsz, blk, lsh, lmask, ssh, smask, cap}:
      wsz

# The windows of a task, one after another. It never forks, so the
# scheduler hands it to a core of its own.
def enc.leaf(+E: EK, +w0: U32, +nw: U32, st: ES) -> ES:
  win.loop(U32.to_nat(nw), E, w0, st)

# The nw windows from w0 in a full binary tree of 2^k tasks, each with at
# least one window; for k > 0, sp holds the states of the two halves, else
# the state and an unused one.
def enc.par(+k: Nat, +E: EK, +sbits: Nat, +wb: U32, +w0: U32, +nw: U32,
  sp: ES & ES) -> ES:
  match k:
    case 0n:
      (st, none) = sp
      enc.leaf(E, w0, nw, st)
    case 1n:
      (sl, sr) = sp
      +nl = (nw >> 1n : U32)
      +nr = (nw - nl : U32)
      +wm = (w0 + (nl * EK.wsz(E) : U32) : U32)
      l r = enc.leaf(E, w0, nl, sl) enc.leaf(E, wm, nr, sr)
      es.join(l, r)
    case 2n+q:
      (sl, sr) = sp
      +nl = (nw >> 1n : U32)
      +nr = (nw - nl : U32)
      +wm = (w0 + (nl * EK.wsz(E) : U32) : U32)
      l r = enc.par(1n+q, E, sbits, wb, w0, nl, es.split(E, sbits, wb, w0, nl, sl)) enc.par(1n+q, E, sbits, wb, wm, nr, es.split(E, sbits, wb, wm, nr, sr))
      es.join(l, r)

# How many levels of tasks for nw windows: 8 tasks of a window or more for
# large targets; below 8 windows, copying the inputs for each task costs
# more than it saves.
def enc.depth(+nw: U32) -> Nat:
  Bool.pick(Nat, (8 <= nw : U32), 3n, 0n)

# A state with no room in it, for a task that does not split.
def es.none() -> ES:
  ES{[0 : U32^0n], [0 : U32^0n], [0 : U32^0n], [0 : U32^0n], [0 : U32^0n],
    [0 : U32^0n], Em{[0 : U32^0n], [0 : U32^0n], [0 : U32^0n], [0 : U32^0n],
      0, 0, 0, 0, 0, 0, 0, 0, 0}, [0 : U32^0n], 0, 0, 0}

def enc.top.sp(+k: Nat, +E: EK, +sbits: Nat, +wb: U32, +nw: U32, st: ES) -> ES & ES:
  match k:
    case 0n:
      (st, es.none())
    case 1n+q:
      es.split(E, sbits, wb, 0, nw, st)

def enc.par.top(+E: EK, +sbits: Nat, +wb: U32, +nw: U32, st: ES) -> ES:
  enc.par(enc.depth(nw), E, sbits, wb, 0, nw, enc.top.sp(enc.depth(nw), E, sbits, wb, nw, st))

def enc.go(+E: EK, src: Array<U32>, tgt: Array<U32>, +lbits: Nat,
  +sbits: Nat, +wb: U32, r: Array<U32> & U32) -> (B.Bytes & B.Bytes) & B.Bytes:
  match E r:
    case EK{+slen, +tlen, +wsz, blk, lsh, lmask, ssh, smask, cap} Tuple{out, ol}:
      +olen = {ol : U32}
      enc.done(slen, tlen,
        enc.par.top(E, sbits, wb, u32.max(1, (((tlen + wsz : U32) - 1 : U32) / wsz : U32)),
          win.index(E, U32.min(tlen, wsz), ES{src, tgt, Array.new(U32, lbits, 0), Array.new(U32, sbits, 0),
            Array.new(U32, 18n, 0), Array.new(U32, 22n, 0),
            Em{B.B.zeros(wb), B.B.zeros((wb * 4 : U32)), B.B.zeros((wb * 2 : U32)),
              Array.new(U32, 10n, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0},
            out, olen, 0, 0})))

# A delta that turns src into tgt. Answers both inputs back.
def encode(src: B.Bytes, tgt: B.Bytes) -> (B.Bytes & B.Bytes) & B.Bytes:
  match src tgt:
    case B.Bytes{+slen, sa} B.Bytes{+tlen, ta}:
      +E = EK.mk(slen, tlen)
      +lb = U32.from_nat(B.B.depth(u32.max(slen, 16384)))
      +lbits = u32.pick((slen <= 67108864 : U32), u32.max(3, (lb - 3 : U32)), 23)
      +sbits = U32.min(23, U32.from_nat(B.B.depth(u32.max(tlen, 16384))))
      enc.go(E, sa, ta, U32.to_nat(lbits), U32.to_nat(sbits),
        U32.min(8388608, u32.max(tlen, 64)),
        wr.byte(0, wr.byte(0, wr.byte(196, wr.byte(195, wr.byte(214,
          (B.B.zeros(u32.max((tlen >> 3n : U32), 4096)), 0)))))))
