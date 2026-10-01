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
# ========
#
# The string matcher, on trees: every match it buffers is one its byte
# comparisons found, so it holds.
#
# Source: proofs/scan.bp (tools/bpp.py writes proofs/scan.bend from it).

# sc's state, its arrays as trees. The source, the target and the emitter
# stay as they are through the scan: they are the mirror's parameters.
type ST is Data:
  ST{tl: A.Tr, tb: A.Tr, tv: A.Tr, tio: A.Tr, p: U32, mm: U32, rc: U32,
    rl: U32, lck: U32, last: U32, nio: U32, cont: U32}

def SC.sc(+ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +st: ST) -> N.Sc:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont}

# A step's result: whether to go on, and the state; a phase's: whether it
# took the position, then a step's result.
type R1 is Data:
  R1{b: Bool, st: ST}

type R2 is Data:
  R2{b: Bool, r: R1}

def SC.b(+ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +r: R1) -> Bool & N.Sc:
  match r:
    case R1{b, st}:
      (b, SC.sc(ts, tt, e, st))

def SC.bb(+ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +r: R2) -> Bool & (Bool & N.Sc):
  match r:
    case R2{b, q}:
      (b, SC.b(ts, tt, e, q))

# Buffering a match
# -----------------

def SC.push.go(+full: Bool, +pos: U32, +len: U32, +val: U32, +st: ST) -> ST:
  match full st:
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      ST{tl, tb, tv, SG_.SG.put(tio, nio, pos, len, val), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      ST{tl, tb, tv, SG_.SG.put(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), nio, pos, len, val), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont}

def SC.full(+st: ST) -> Bool:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      U32.is_gt(U32.add(N.io.at(nio), 3), A.T.size(tio))

def SC.push.if(+z: Bool, +pos: U32, +len: U32, +val: U32, +st: ST) -> ST:
  match z:
    case True{}:
      SC.push.go(SC.full(st), pos, len, val, st)
    case False{}:
      st

def SC.push(+e: EM_.ET, +pos: U32, +len: U32, +val: U32, +st: ST) -> ST:
  +u = EM_.EM.uo(e)
  +d = N.u32.pick(U32.is_lt(pos, u), U32.sub(u, pos), 0)
  SC.push.if(U32.is_le(U32.add(d, 4), U32.and(len, 2147483647)), U32.add(pos, d), U32.sub(len, d), N.u32.pick(N.ent.run(len), val, U32.add(val, d)), st)

law SC.push.go_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +full: Bool
  for +K: N.SK
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {N.sc.push.go(full, K, pos, len, val, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.push.go(full, pos, len, val, st)) : N.Sc}

def SC.push.go_code(ts, tt, e, full, K, pos, len, val, st):
  match full st:
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32>, N.io.put(A.A.from(tio), nio, pos, len, val), A.A.from(SG_.SG.put(tio, nio, pos, len, val)), SG_.SG.put_code(tio, nio, pos, len, val)) :
        {N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), _, EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} == N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.put(tio, nio, pos, len, val)), EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} : N.Sc}
      {==}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32>, B.B.grow(A.A.from(tio), N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), A.A.from(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)))), EM_.GR.code(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)))) :
        {N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), N.io.put(_, nio, pos, len, val), EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} == N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.put(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), nio, pos, len, val)), EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} : N.Sc}
      %Equal.sym(Array<U32>, N.io.put(A.A.from(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)))), nio, pos, len, val), A.A.from(SG_.SG.put(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), nio, pos, len, val)), SG_.SG.put_code(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), nio, pos, len, val)) :
        {N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), _, EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} == N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(SG_.SG.put(EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), nio, pos, len, val)), EM_.EM.em(e), p, mm, rc, rl, lck, last, U32.add(nio, 1), cont} : N.Sc}
      {==}

law SC.push.if_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {N.sc.push.if(z, K, pos, len, val, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.push.if(z, pos, len, val, st)) : N.Sc}

def SC.push.if_code(ts, tt, e, z, K, pos, len, val, st):
  match z st:
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, Array.size(U32, A.A.from(tio)), (A.A.from(tio), A.T.size(tio)), A.A.size_from(tio)) :
        {N.sc.push.k0(K, pos, len, val, N.sc.nio.k(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, _)) == SC.sc(ts, tt, e, SC.push.go(U32.is_gt(U32.add(N.io.at(nio), 3), A.T.size(tio)), pos, len, val, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : N.Sc}
      SC.push.go_code(ts, tt, e, U32.is_gt(U32.add(N.io.at(nio), 3), A.T.size(tio)), K, pos, len, val, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law SC.push_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {N.sc.push(K, pos, len, val, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.push(e, pos, len, val, st)) : N.Sc}

def SC.push_code(ts, tt, e, K, pos, len, val, st):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(U32 & N.Em, N.em.uoff(EM_.EM.em(e)), (EM_.EM.uo(e), EM_.EM.em(e)), EM_.EM.uo_code(e)) :
        {N.sc.push.t(K, pos, len, val, N.sc.uoff.k(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), p, mm, rc, rl, lck, last, nio, cont, _)) == SC.sc(ts, tt, e, SC.push.if(U32.is_le(U32.add(N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0), 4), U32.and(len, 2147483647)), U32.add(pos, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), U32.sub(len, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), N.u32.pick(N.ent.run(len), val, U32.add(val, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0))), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : N.Sc}
      SC.push.if_code(ts, tt, e, U32.is_le(U32.add(N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0), 4), U32.and(len, 2147483647)), K, U32.add(pos, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), U32.sub(len, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), N.u32.pick(N.ent.run(len), val, U32.add(val, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0))), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

# Dropping the matches that start at or after pos
# -----------------------------------------------

def SC.erl(k: Nat, +pos: U32, +h: Bool, +n: U32, +tio: A.Tr) -> U32:
  match k h:
    case 0n b:
      n
    case 1n+q False{}:
      n
    case 1n+q True{}:
      SC.erl(q, pos, Bool.and(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.is_lt(1, n)), N.u32.pick(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.sub(n, 1), n), tio)

def SC.erase(+pos: U32, +st: ST) -> ST:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, SC.erl(U32.to_nat(nio), pos, U32.is_lt(0, nio), nio, tio), cont}

law SC.erl_code:
  for +k: Nat
  for +pos: U32
  for +h: Bool
  for +n: U32
  for +tio: A.Tr
  {N.er.loop(k, pos, (h, (n, A.A.from(tio)))) == (SC.erl(k, pos, h, n, tio), A.A.from(tio)) : U32 & Array<U32>}

def SC.erl_code(k, pos, h, n, tio):
  match k h:
    case 0n b:
      {==}
    case 1n+q False{}:
      {==}
    case 1n+q True{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), N.io.at(U32.sub(n, 1))), (A.A.from(tio), A.T.word(tio, N.io.at(U32.sub(n, 1)))), A.A.get_from(tio, N.io.at(U32.sub(n, 1)))) :
        {N.er.loop(q, pos, N.er.k(pos, n, _)) == (SC.erl(q, pos, Bool.and(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.is_lt(1, n)), N.u32.pick(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.sub(n, 1), n), tio), A.A.from(tio)) : U32 & Array<U32>}
      SC.erl_code(q, pos, Bool.and(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.is_lt(1, n)), N.u32.pick(U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), U32.sub(n, 1), n), tio)

law SC.erase_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +pos: U32
  for +st: ST
  {N.sc.erase(pos, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.erase(pos, st)) : N.Sc}

def SC.erase_code(ts, tt, e, pos, st):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(U32 & Array<U32>, N.er.loop(U32.to_nat(nio), pos, (U32.is_lt(0, nio), (nio, A.A.from(tio)))), (SC.erl(U32.to_nat(nio), pos, U32.is_lt(0, nio), nio, tio), A.A.from(tio)), SC.erl_code(U32.to_nat(nio), pos, U32.is_lt(0, nio), nio, tio)) :
        {N.sc.erase.k(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), EM_.EM.em(e), p, mm, rc, rl, lck, last, cont, _) == N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, SC.erl(U32.to_nat(nio), pos, U32.is_lt(0, nio), nio, tio), cont} : N.Sc}
      {==}

# Moving on
# ---------

def SC.update(+K: N.SK, +tt: A.Tr, +st: ST) -> R1:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      R1{U32.is_le(U32.add(p, 5), w1), ST{tl, tb, tv, tio, U32.add(p, 1), mm, Y.BP.byt(tt, U32.add(p, 4)), N.u32.pick(U32.is_eq(Y.BP.byt(tt, U32.add(p, 4)), rc), U32.add(rl, 1), 1), U32.add(U32.sub(U32.mul(lck, N.H.M()), U32.mul(Y.BP.byt(tt, p), N.H.M9())), Y.BP.byt(tt, U32.add(p, 9))), last, nio, cont}}

law SC.update_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +st: ST
  {N.sc.update(K, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.update(K, tt, st)) : Bool & N.Sc}

def SC.update_code(ts, tt, e, K, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), U32.add(p, 4)), (A.A.from(tt), Y.BP.byt(tt, U32.add(p, 4))), Y.BP.get_from(tt, U32.add(p, 4))) :
        {(U32.is_le(U32.add(p, 5), w1), N.sc.upd.k1(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, _)) == (U32.is_le(U32.add(p, 5), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), U32.add(p, 1), mm, Y.BP.byt(tt, U32.add(p, 4)), N.u32.pick(U32.is_eq(Y.BP.byt(tt, U32.add(p, 4)), rc), U32.add(rl, 1), 1), U32.add(U32.sub(U32.mul(lck, N.H.M()), U32.mul(Y.BP.byt(tt, p), N.H.M9())), Y.BP.byt(tt, U32.add(p, 9))), last, nio, cont}) : Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), p), (A.A.from(tt), Y.BP.byt(tt, p)), Y.BP.get_from(tt, p)) :
        {(U32.is_le(U32.add(p, 5), w1), N.sc.upd.k2(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, Y.BP.byt(tt, U32.add(p, 4)), _)) == (U32.is_le(U32.add(p, 5), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), U32.add(p, 1), mm, Y.BP.byt(tt, U32.add(p, 4)), N.u32.pick(U32.is_eq(Y.BP.byt(tt, U32.add(p, 4)), rc), U32.add(rl, 1), 1), U32.add(U32.sub(U32.mul(lck, N.H.M()), U32.mul(Y.BP.byt(tt, p), N.H.M9())), Y.BP.byt(tt, U32.add(p, 9))), last, nio, cont}) : Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), U32.add(p, 9)), (A.A.from(tt), Y.BP.byt(tt, U32.add(p, 9))), Y.BP.get_from(tt, U32.add(p, 9))) :
        {(U32.is_le(U32.add(p, 5), w1), N.sc.upd.k3(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, Y.BP.byt(tt, U32.add(p, 4)), Y.BP.byt(tt, p), _)) == (U32.is_le(U32.add(p, 5), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), U32.add(p, 1), mm, Y.BP.byt(tt, U32.add(p, 4)), N.u32.pick(U32.is_eq(Y.BP.byt(tt, U32.add(p, 4)), rc), U32.add(rl, 1), 1), U32.add(U32.sub(U32.mul(lck, N.H.M()), U32.mul(Y.BP.byt(tt, p), N.H.M9())), Y.BP.byt(tt, U32.add(p, 9))), last, nio, cont}) : Bool & N.Sc}
      {==}

# The large checksum
def SC.hl.go(n: Nat, +h: U32, +i: U32, +x: U32, +tt: A.Tr) -> U32:
  match n:
    case 0n:
      h
    case 1n+q:
      SC.hl.go(q, U32.add(U32.mul(h, N.H.M()), x), U32.add(i, 1), Y.BP.byt(tt, U32.add(i, 1)), tt)

def SC.hl(+tt: A.Tr, +i: U32) -> U32:
  SC.hl.go(9n, 0, i, Y.BP.byt(tt, i), tt)

law SC.hl.go_code:
  for +n: Nat
  for +h: U32
  for +i: U32
  for +x: U32
  for +tt: A.Tr
  {N.H.large.go(n, h, i, (A.A.from(tt), x)) == (A.A.from(tt), SC.hl.go(n, h, i, x, tt)) : Array<U32> & U32}

def SC.hl.go_code(n, h, i, x, tt):
  match n:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), U32.add(i, 1)), (A.A.from(tt), Y.BP.byt(tt, U32.add(i, 1))), Y.BP.get_from(tt, U32.add(i, 1))) :
        {N.H.large.go(q, U32.add(U32.mul(h, N.H.M()), x), U32.add(i, 1), _) == (A.A.from(tt), SC.hl.go(q, U32.add(U32.mul(h, N.H.M()), x), U32.add(i, 1), Y.BP.byt(tt, U32.add(i, 1)), tt)) : Array<U32> & U32}
      SC.hl.go_code(q, U32.add(U32.mul(h, N.H.M()), x), U32.add(i, 1), Y.BP.byt(tt, U32.add(i, 1)), tt)

law SC.hl_code:
  for +tt: A.Tr
  for +i: U32
  {N.H.large(A.A.from(tt), i) == (A.A.from(tt), SC.hl(tt, i)) : Array<U32> & U32}

def SC.hl_code(tt, i):
  %Equal.sym(Array<U32> & U32, B.B.get(A.A.from(tt), i), (A.A.from(tt), Y.BP.byt(tt, i)), Y.BP.get_from(tt, i)) :
    {N.H.large.go(9n, 0, i, _) == (A.A.from(tt), SC.hl.go(9n, 0, i, Y.BP.byt(tt, i), tt)) : Array<U32> & U32}
  SC.hl.go_code(9n, 0, i, Y.BP.byt(tt, i), tt)

# Starting afresh
def SC.restart(+K: N.SK, +tt: A.Tr, +st: ST) -> R1:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm0, rc0, rl0, lck0, last, nio, cont}:
      +q = A.T.word(tio, N.io.at(U32.sub(nio, 1)))
      +len = A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1))
      +le = N.u32.pick(U32.is_lt(0, nio), U32.add(q, U32.and(len, 2147483647)), 0)
      +mm = N.u32.pick(U32.is_lt(p, le), N.u32.max(4, U32.sub(U32.add(le, 1), p)), 4)
      +w = MT_.MT.W(tt, p)
      +b0 = U32.and(w, 255)
      +b1 = U32.and(U32.shrn(w, 8n), 255)
      +b2 = U32.and(U32.shrn(w, 16n), 255)
      +b3 = U32.shrn(w, 24n)
      +l1 = N.u32.pick(U32.is_eq(b1, b0), 2, 1)
      +l2 = N.u32.pick(U32.is_eq(b2, b1), U32.add(l1, 1), 1)
      +l3 = N.u32.pick(U32.is_eq(b3, b2), U32.add(l2, 1), 1)
      R1{U32.is_le(U32.add(p, 4), w1), ST{tl, tb, tv, tio, p, mm, b3, l3, SC.hl(tt, p), last, nio, cont}}

law SC.restart_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +st: ST
  {N.sc.restart(K, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.restart(K, tt, st)) : Bool & N.Sc}

def SC.restart_code(ts, tt, e, K, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm0, rc0, rl0, lck0, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), N.io.at(U32.sub(nio, 1))), (A.A.from(tio), A.T.word(tio, N.io.at(U32.sub(nio, 1)))), A.A.get_from(tio, N.io.at(U32.sub(nio, 1)))) :
        {N.sc.rs.k1(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), EM_.EM.em(e), p, w1, last, nio, cont, _) == (U32.is_le(U32.add(p, 4), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), U32.shrn(MT_.MT.W(tt, p), 24n), N.u32.pick(U32.is_eq(U32.shrn(MT_.MT.W(tt, p), 24n), U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255), U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255), U32.and(MT_.MT.W(tt, p), 255)), 2, 1), 1), 1), 1), 1), SC.hl(tt, p), last, nio, cont}) : Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tio), U32.add(N.io.at(U32.sub(nio, 1)), 1)), (A.A.from(tio), A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1))), A.A.get_from(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1))) :
        {N.sc.rs.k2(A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), EM_.EM.em(e), p, w1, last, nio, cont, A.T.word(tio, N.io.at(U32.sub(nio, 1))), _) == (U32.is_le(U32.add(p, 4), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), U32.shrn(MT_.MT.W(tt, p), 24n), N.u32.pick(U32.is_eq(U32.shrn(MT_.MT.W(tt, p), 24n), U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255), U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255), U32.and(MT_.MT.W(tt, p), 255)), 2, 1), 1), 1), 1), 1), SC.hl(tt, p), last, nio, cont}) : Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(tt), p), (A.A.from(tt), MT_.MT.W(tt, p)), MT_.MT.word(tt, p)) :
        {N.sc.rs.k3(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, w1, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), last, nio, cont, _) == (U32.is_le(U32.add(p, 4), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), U32.shrn(MT_.MT.W(tt, p), 24n), N.u32.pick(U32.is_eq(U32.shrn(MT_.MT.W(tt, p), 24n), U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255), U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255), U32.and(MT_.MT.W(tt, p), 255)), 2, 1), 1), 1), 1), 1), SC.hl(tt, p), last, nio, cont}) : Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, N.H.large(A.A.from(tt), p), (A.A.from(tt), SC.hl(tt, p)), SC.hl_code(tt, p)) :
        {N.sc.rs.k4(A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, w1, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), U32.shrn(MT_.MT.W(tt, p), 24n), N.u32.pick(U32.is_eq(U32.shrn(MT_.MT.W(tt, p), 24n), U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255), U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255), U32.and(MT_.MT.W(tt, p), 255)), 2, 1), 1), 1), 1), 1), last, nio, cont, _) == (U32.is_le(U32.add(p, 4), w1), N.Sc{A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), U32.shrn(MT_.MT.W(tt, p), 24n), N.u32.pick(U32.is_eq(U32.shrn(MT_.MT.W(tt, p), 24n), U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 16n), 255), U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255)), U32.add(N.u32.pick(U32.is_eq(U32.and(U32.shrn(MT_.MT.W(tt, p), 8n), 255), U32.and(MT_.MT.W(tt, p), 255)), 2, 1), 1), 1), 1), 1), SC.hl(tt, p), last, nio, cont}) : Bool & N.Sc}
      {==}

# After a match of L bytes
def SC.lazy.go(+z: Bool, +K: N.SK, +tt: A.Tr, +L: U32, +st: ST) -> R1:
  match z st:
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update(K, tt, ST{tl, tb, tv, tio, p, L, rc, rl, lck, last, nio, cont})
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.restart(K, tt, ST{tl, tb, tv, tio, U32.add(p, L), mm, rc, rl, lck, last, nio, cont})

def SC.lazy(+K: N.SK, +tt: A.Tr, +L: U32, +st: ST) -> R1:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy.go(Bool.and(U32.is_lt(L, 18), U32.is_le(U32.add(U32.add(p, L), 2), w1)), K, tt, L, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

law SC.lazy.go_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +L: U32
  for +st: ST
  {N.sc.lazy.go(z, K, L, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.lazy.go(z, K, tt, L, st)) : Bool & N.Sc}

def SC.lazy.go_code(ts, tt, e, z, K, L, st):
  match z st:
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update_code(ts, tt, e, K, ST{tl, tb, tv, tio, p, L, rc, rl, lck, last, nio, cont})
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.restart_code(ts, tt, e, K, ST{tl, tb, tv, tio, U32.add(p, L), mm, rc, rl, lck, last, nio, cont})

law SC.lazy_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +L: U32
  for +st: ST
  {N.sc.lazy(K, L, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.lazy(K, tt, L, st)) : Bool & N.Sc}

def SC.lazy_code(ts, tt, e, K, L, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy.go_code(ts, tt, e, Bool.and(U32.is_lt(L, 18), U32.is_le(U32.add(U32.add(p, L), 2), w1)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, L, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

# Runs
# ----

def SC.run.if(+z: Bool, +K: N.SK, +tt: A.Tr, +e: EM_.ET, +L: U32, +st: ST) -> R2:
  match z st:
    case False{} s:
      R2{False{}, R1{True{}, s}}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      R2{True{}, SC.lazy(K, tt, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))}

# The run's length at p.
def SC.rlen(+tt: A.Tr, +p: U32, +b: U32, +max: U32) -> U32:
  MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), tt, p, MT_.MR{b}, max, MT_.MT.cf(tt, p, MT_.MR{b}, max, 0), MT_.MT.cn(tt, p, MT_.MR{b}, 0))

def SC.run.go(+z: Bool, +K: N.SK, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R2:
  match z K st:
    case False{} k s:
      R2{False{}, R1{True{}, s}}
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.if(Bool.and(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), U32.is_le(8, SC.rlen(tt, p, rc, U32.sub(w1, p)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, SC.rlen(tt, p, rc, U32.sub(w1, p)), ST{tl, tb, tv, tio, p, mm, rc, SC.rlen(tt, p, rc, U32.sub(w1, p)), lck, last, nio, cont})

def SC.run(+K: N.SK, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R2:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.go(U32.is_eq(rl, 4), K, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

law SC.run.if_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +L: U32
  for +st: ST
  {N.ph.run.if(z, K, L, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.run.if(z, K, tt, e, L, st)) : Bool & (Bool & N.Sc)}

def SC.run.if_code(ts, tt, e, z, K, L, st):
  match z st:
    case False{} s:
      {==}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(N.Sc, N.sc.push(K, p, U32.or(L, 2147483648), rc, SC.sc(ts, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.sc(ts, tt, e, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.push_code(ts, tt, e, K, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) :
        {(True{}, N.sc.lazy(K, L, _)) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) : Bool & Bool & N.Sc}
      %Equal.sym(Bool & N.Sc, N.sc.lazy(K, L, SC.sc(ts, tt, e, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.b(ts, tt, e, SC.lazy(K, tt, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.lazy_code(ts, tt, e, K, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))) :
        {(True{}, _) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) : Bool & Bool & N.Sc}
      {==}

law SC.run.go_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +st: ST
  {N.ph.run.go(z, K, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.run.go(z, K, tt, e, st)) : Bool & (Bool & N.Sc)}

def SC.run.go_code(ts, tt, e, z, K, st):
  match z K st:
    case False{} k s:
      {==}
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, B.B.same(A.A.from(tt), p, rc, U32.sub(w1, p)), (A.A.from(tt), MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, p, MT_.MR{rc}, U32.sub(w1, p), MT_.MT.cf(tt, p, MT_.MR{rc}, U32.sub(w1, p), 0), MT_.MT.cn(tt, p, MT_.MR{rc}, 0))), MT_.MT.same(tt, p, rc, U32.sub(w1, p))) :
        {N.ph.run.k(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, lck, last, nio, cont, _) == SC.bb(ts, tt, e, SC.run.if(Bool.and(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), U32.is_le(8, SC.rlen(tt, p, rc, U32.sub(w1, p)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, SC.rlen(tt, p, rc, U32.sub(w1, p)), ST{tl, tb, tv, tio, p, mm, rc, SC.rlen(tt, p, rc, U32.sub(w1, p)), lck, last, nio, cont})) : Bool & Bool & N.Sc}
      SC.run.if_code(ts, tt, e, Bool.and(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), U32.is_le(8, SC.rlen(tt, p, rc, U32.sub(w1, p)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, SC.rlen(tt, p, rc, U32.sub(w1, p)), ST{tl, tb, tv, tio, p, mm, rc, SC.rlen(tt, p, rc, U32.sub(w1, p)), lck, last, nio, cont})

law SC.run_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +st: ST
  {N.ph.run(K, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.run(K, tt, e, st)) : Bool & (Bool & N.Sc)}

def SC.run_code(ts, tt, e, K, st):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.go_code(ts, tt, e, U32.is_eq(rl, 4), K, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

# Source matches
# --------------

def SC.w1(+K: N.SK) -> U32:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      w1

def SC.pp(+st: ST) -> U32:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      p

# E bounds the source and the window's end, for MT.fwd.
def SC.okE(+K: N.SK, +E: U32) -> Bool:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))))

def SC.cont(+K: N.SK, +end: U32, +at: U32, +st: ST) -> ST:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, N.u32.pick(U32.is_eq(end, w1), at, cont)}

def SC.erase.if(+z: Bool, +pos: U32, +st: ST) -> ST:
  match z:
    case True{}:
      SC.erase(pos, st)
    case False{}:
      st

# MT.fwd's and MT.back's lengths.
def SC.flen(+ts: A.Tr, +i: U32, +tt: A.Tr, +j: U32, +max: U32) -> U32:
  MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), ts, i, MT_.MW{tt, j}, max, MT_.MT.cf(ts, i, MT_.MW{tt, j}, max, 0), MT_.MT.cn(ts, i, MT_.MW{tt, j}, 0))

def SC.blen(+ts: A.Tr, +i: U32, +tt: A.Tr, +j: U32, +max: U32) -> U32:
  MT_.MT.bs(U32.to_nat(max), ts, i, tt, j, max, MT_.MT.bf(ts, i, tt, j, max, 0), MT_.MT.bn(ts, i, tt, j, 0))

def SC.large.if(+z: Bool, +K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +srcpos: U32, +maxback: U32, +fwd: U32, +st: ST) -> R2:
  match z st:
    case False{} s:
      R2{False{}, R1{True{}, s}}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      +back = SC.blen(ts, srcpos, tt, p, maxback)
      +pos = U32.sub(p, back)
      +len = U32.add(fwd, back)
      R2{True{}, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(pos, len), U32.add(srcpos, fwd), SC.push(e, pos, len, U32.sub(srcpos, back), SC.erase.if(U32.is_lt(0, back), pos, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))))}

def SC.fmax(+K: N.SK, +p: U32, +srcpos: U32) -> U32:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))

def SC.large.try(+z: Bool, +K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +srcpos: U32, +st: ST) -> R2:
  match z st:
    case False{} s:
      R2{False{}, R1{True{}, s}}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      +fwd = SC.flen(ts, srcpos, tt, p, SC.fmax(K, p, srcpos))
      SC.large.if(U32.is_le(mm, fwd), K, ts, tt, e, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), fwd, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

def SC.large.go(+z: Bool, +K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R2:
  match z K st:
    case False{} k s:
      R2{False{}, R1{True{}, s}}
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      +cand = A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask))
      +srcpos = U32.sub(cand, 1)
      +hit = Bool.and(Bool.and(U32.is_ne(cand, 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), srcpos)), U32.is_lt(srcpos, slen))
      +again = Bool.and(U32.is_ne(srcpos, 0), U32.is_eq(srcpos, last))
      SC.large.try(Bool.and(hit, Bool.not(again)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, srcpos, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, N.u32.pick(hit, srcpos, last), nio, cont})

def SC.large(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R2:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.go(Bool.and(U32.is_lt(0, slen), U32.is_le(U32.add(p, 9), w1)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

law SC.cont_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +end: U32
  for +at: U32
  for +st: ST
  {N.sc.cont(K, end, at, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.cont(K, end, at, st)) : N.Sc}

def SC.cont_code(ts, tt, e, K, end, at, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law SC.erase.if_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +pos: U32
  for +st: ST
  {N.sc.erase.if(z, pos, SC.sc(ts, tt, e, st)) == SC.sc(ts, tt, e, SC.erase.if(z, pos, st)) : N.Sc}

def SC.erase.if_code(ts, tt, e, z, pos, st):
  match z:
    case True{}:
      SC.erase_code(ts, tt, e, pos, st)
    case False{}:
      {==}

# A bound for MT.fwd: i, then at most L - i bytes, then 4.
law SC.fb:
  for +i: U32
  for +L: U32
  for +m: U32
  for +E: U32
  for +h: {U32.is_le(i, L) == True{} : Bool}
  for +hm: {Cmp.is_le(Nat.cmp(V.U.N(m), V.U.N(U32.sub(L, i)))) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(L), 4n), V.U.N(E))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(i), V.U.N(m)), 4n), V.U.N(E))) == True{} : Bool}

law SC.fb1:
  for +i: U32
  for +L: U32
  for +h: {U32.is_le(i, L) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), V.U.N(U32.sub(L, i))), V.U.N(L))) == True{} : Bool}

def SC.fb1(i, L, h):
  %Equal.sym(Nat, Nat.add(V.U.N(i), V.U.N(U32.sub(L, i))), Nat.add(V.U.N(U32.sub(L, i)), V.U.N(i)), P.Nat.add_comm(V.U.N(i), V.U.N(U32.sub(L, i)))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(L))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(V.U.N(U32.sub(L, i)), V.U.N(i)), V.U.N(L), V.U.sub_nat(L, i, h)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(L))) == True{} : Bool}
  C.CP.le_refl(V.U.N(L))

def SC.fb(i, L, m, E, h, hm, hE):
  P.Nat.le_trans(Nat.add(Nat.add(V.U.N(i), V.U.N(m)), 4n), Nat.add(V.U.N(L), 4n), V.U.N(E),
    MT_.MT.add_le(Nat.add(V.U.N(i), V.U.N(m)), V.U.N(L), 4n, 4n,
      P.Nat.le_trans(Nat.add(V.U.N(i), V.U.N(m)), Nat.add(V.U.N(i), V.U.N(U32.sub(L, i))), V.U.N(L),
        MT_.MT.add_le(V.U.N(i), V.U.N(i), V.U.N(m), V.U.N(U32.sub(L, i)), C.CP.le_refl(V.U.N(i)), hm),
        SC.fb1(i, L, h)),
      C.CP.le_refl(4n)),
    hE)

law SC.hit:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  {Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(a, b), c), Bool.not(d))), c) == True{} : Bool}

def SC.hit(a, b, c, d):
  match c:
    case True{}:
      %Equal.sym(Bool, Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(a, b), True{}), Bool.not(d))), True{}), True{}, P.Bool.or_true(Bool.not(Bool.and(Bool.and(Bool.and(a, b), True{}), Bool.not(d))))) :
        {_ == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Bool.and(Bool.and(a, b), False{}), False{}, P.Bool.and_false(Bool.and(a, b))) :
        {Bool.or(Bool.not(Bool.and(_, Bool.not(d))), False{}) == True{} : Bool}
      {==}

law SC.large.if_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +srcpos: U32
  for +maxback: U32
  for +fwd: U32
  for +tl: A.Tr
  for +tb: A.Tr
  for +tv: A.Tr
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +rc: U32
  for +rl: U32
  for +lck: U32
  for +last: U32
  for +nio: U32
  for +cont: U32
  {N.ph.large.if(z, K, A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, srcpos, maxback, fwd, A.A.from(ts), A.A.from(tt)) == SC.bb(ts, tt, e, SC.large.if(z, K, ts, tt, e, srcpos, maxback, fwd, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : Bool & (Bool & N.Sc)}

def SC.large.if_code(ts, tt, e, z, K, srcpos, maxback, fwd, tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont):
  match z:
    case False{}:
      {==}
    case True{}:
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.back(A.A.from(ts), srcpos, A.A.from(tt), p, maxback), ((A.A.from(ts), A.A.from(tt)), MT_.MT.bs(U32.to_nat(maxback), ts, srcpos, tt, p, maxback, MT_.MT.bf(ts, srcpos, tt, p, maxback, 0), MT_.MT.bn(ts, srcpos, tt, p, 0))), MT_.MT.back(ts, srcpos, tt, p, maxback)) :
        {N.ph.large.k3(K, A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, srcpos, fwd, _) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))) : Bool & Bool & N.Sc}
      %Equal.sym(N.Sc, N.sc.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), SC.sc(ts, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.sc(ts, tt, e, SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.erase.if_code(ts, tt, e, U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) :
        {(True{}, N.sc.lazy(K, fwd, N.sc.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), N.sc.push(K, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), _)))) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))) : Bool & Bool & N.Sc}
      %Equal.sym(N.Sc, N.sc.push(K, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.sc(ts, tt, e, SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.sc(ts, tt, e, SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.push_code(ts, tt, e, K, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))) :
        {(True{}, N.sc.lazy(K, fwd, N.sc.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), _))) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))) : Bool & Bool & N.Sc}
      %Equal.sym(N.Sc, N.sc.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.sc(ts, tt, e, SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))), SC.sc(ts, tt, e, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))), SC.cont_code(ts, tt, e, K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) :
        {(True{}, N.sc.lazy(K, fwd, _)) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))) : Bool & Bool & N.Sc}
      %Equal.sym(Bool & N.Sc, N.sc.lazy(K, fwd, SC.sc(ts, tt, e, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))))), SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))))), SC.lazy_code(ts, tt, e, K, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))))) :
        {(True{}, _) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))) : Bool & Bool & N.Sc}
      {==}

law SC.large.try_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +srcpos: U32
  for +E: U32
  for +tl: A.Tr
  for +tb: A.Tr
  for +tv: A.Tr
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +rc: U32
  for +rl: U32
  for +lck: U32
  for +last: U32
  for +nio: U32
  for +cont: U32
  for +hz: {Bool.or(Bool.not(z), U32.is_lt(srcpos, N.SK.slen(K))) == True{} : Bool}
  for +hp: {U32.is_le(p, SC.w1(K)) == True{} : Bool}
  for +hE: {SC.okE(K, E) == True{} : Bool}
  {N.ph.large.try(z, K, A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, srcpos) == SC.bb(ts, tt, e, SC.large.try(z, K, ts, tt, e, srcpos, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : Bool & (Bool & N.Sc)}

def SC.large.try_code(ts, tt, e, z, K, srcpos, E, tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont, hz, hp, hE):
  match z K:
    case False{} k:
      {==}
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(U32 & N.Em, N.em.uoff(EM_.EM.em(e)), (EM_.EM.uo(e), EM_.EM.em(e)), EM_.EM.uo_code(e)) :
        {N.ph.large.u(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), p, mm, rc, rl, lck, last, nio, cont, srcpos, _) == SC.bb(ts, tt, e, SC.large.if(U32.is_le(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : Bool & Bool & N.Sc}
      %Equal.sym((Array<U32> & Array<U32>) & U32, B.B.fwd(A.A.from(ts), srcpos, A.A.from(tt), p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), ((A.A.from(ts), A.A.from(tt)), MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0))), MT_.MT.fwd(ts, tt, srcpos, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, SC.fb(srcpos, slen, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, V.U.lt_to_le(srcpos, slen, hz), MT_.MT.min_le_r(U32.sub(w1, p), U32.sub(slen, srcpos)), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))), hE)), SC.fb(p, w1, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, hp, MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos)), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))), hE)))) :
        {N.ph.large.k2(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), _) == SC.bb(ts, tt, e, SC.large.if(U32.is_le(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : Bool & Bool & N.Sc}
      SC.large.if_code(ts, tt, e, U32.is_le(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont)

law SC.large.go_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +E: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hE: {SC.okE(K, E) == True{} : Bool}
  {N.ph.large.go(z, K, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.large.go(z, K, ts, tt, e, st)) : Bool & (Bool & N.Sc)}

def SC.large.go_code(ts, tt, e, z, K, E, st, hp, hE):
  match z K st:
    case False{} k s:
      {==}
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tl), N.H.slot(lck, U32.to_nat(lsh), lmask)), (A.A.from(tl), A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask))), A.A.get_from(tl, N.H.slot(lck, U32.to_nat(lsh), lmask))) :
        {N.ph.large.k1(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tt), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, _) == SC.bb(ts, tt, e, SC.large.try(Bool.and(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.u32.pick(U32.is_lt(67108864, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), 67108864), 0), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), Bool.not(Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, N.u32.pick(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.u32.pick(U32.is_lt(67108864, U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432)))), U32.sub(U32.min(slen, N.u32.max(67108864, U32.add(w1, 33554432))), 67108864), 0), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last), nio, cont})) : Bool & Bool & N.Sc}
      SC.large.try_code(ts, tt, e, Bool.and(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), Bool.not(Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), E, tl, tb, tv, tio, p, mm, rc, rl, lck, N.u32.pick(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last), nio, cont, SC.hit(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1)), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen), Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last))), hp, hE)

law SC.large_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hE: {SC.okE(K, E) == True{} : Bool}
  {N.ph.large(K, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.large(K, ts, tt, e, st)) : Bool & (Bool & N.Sc)}

def SC.large_code(ts, tt, e, K, E, st, hp, hE):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.go_code(ts, tt, e, Bool.and(U32.is_lt(0, slen), U32.is_le(U32.add(p, 9), w1)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hp, hE)

# Target matches
# --------------

# A chain search: the chains as a tree, the best length and where it
# starts, the position to try and the tries left; the target is fixed.
type CT is Data:
  CT{tv: A.Tr, best: U32, off: U32, base: U32, chain: U32}

def SC.cs(+tt: A.Tr, +ct: CT) -> N.CS:
  match ct:
    case CT{tv, best, off, base, chain}:
      N.CS{A.A.from(tt), A.A.from(tv), best, off, base, chain}

# MT.fwd1's length: the target from i against the target from j.
def SC.tlen(+tt: A.Tr, +i: U32, +j: U32, +max: U32) -> U32:
  MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(max, 2n), 1)), tt, i, MT_.MW{tt, j}, max, MT_.MT.cf(tt, i, MT_.MW{tt, j}, max, 0), MT_.MT.cn(tt, i, MT_.MW{tt, j}, 0))

# A chain step's result: whether to go on, and the search.
type CR is Data:
  CR{g: Bool, ct: CT}

def SC.csb(+tt: A.Tr, +r: CR) -> Bool & N.CS:
  match r:
    case CR{g, ct}:
      (g, SC.cs(tt, ct))

def SC.cs.k(+p: U32, +w0: U32, +stop: Bool, +best: U32, +off: U32, +base: U32, +chain: U32, +prev: U32, +tv: A.Tr) -> CR:
  CR{Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.not(stop), U32.is_lt(0, chain)), U32.is_ne(prev, 0)), U32.is_lt(U32.sub(prev, 1), base)), U32.is_le(w0, U32.sub(prev, 1))), U32.is_le(U32.sub(p, U32.sub(prev, 1)), N.PMASK())), CT{tv, best, off, U32.sub(prev, 1), chain}}

def SC.cs.step(+p: U32, +w1: U32, +w0: U32, +tt: A.Tr, +ct: CT) -> CR:
  match ct:
    case CT{tv, best, off, base, chain}:
      +len = SC.tlen(tt, base, p, U32.sub(w1, p))
      +better = U32.is_lt(best, len)
      SC.cs.k(p, w0, Bool.and(better, Bool.or(U32.is_eq(U32.add(p, len), w1), U32.is_le(35, len))), N.u32.pick(better, len, best), N.u32.pick(better, base, off), base, U32.sub(chain, 1), A.T.word(tv, U32.and(base, N.PMASK())), tv)

def SC.cs.loop(k: Nat, +p: U32, +w1: U32, +w0: U32, +tt: A.Tr, +r: CR) -> CT:
  match k r:
    case 0n CR{g, ct}:
      ct
    case 1n+q CR{False{}, ct}:
      ct
    case 1n+q CR{True{}, ct}:
      SC.cs.loop(q, p, w1, w0, tt, SC.cs.step(p, w1, w0, tt, ct))

law SC.cs.step_code:
  for +p: U32
  for +w1: U32
  for +w0: U32
  for +tt: A.Tr
  for +ct: CT
  {N.cs.step(p, w1, w0, SC.cs(tt, ct)) == SC.csb(tt, SC.cs.step(p, w1, w0, tt, ct)) : Bool & N.CS}

def SC.cs.step_code(p, w1, w0, tt, ct):
  match ct:
    case CT{tv, best, off, base, chain}:
      %Equal.sym(Array<U32> & U32, B.B.fwd1(A.A.from(tt), base, p, U32.sub(w1, p)), (A.A.from(tt), MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), MT_.MT.fwd1(tt, base, p, U32.sub(w1, p))) :
        {N.cs.k1(p, w1, w0, A.A.from(tv), best, off, base, chain, _) == SC.csb(tt, SC.cs.k(p, w0, Bool.and(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), Bool.or(U32.is_eq(U32.add(p, SC.tlen(tt, base, p, U32.sub(w1, p))), w1), U32.is_le(35, SC.tlen(tt, base, p, U32.sub(w1, p))))), N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), SC.tlen(tt, base, p, U32.sub(w1, p)), best), N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), base, off), base, U32.sub(chain, 1), A.T.word(tv, U32.and(base, N.PMASK())), tv)) : Bool & N.CS}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tv), U32.and(base, N.PMASK())), (A.A.from(tv), A.T.word(tv, U32.and(base, N.PMASK()))), A.A.get_from(tv, U32.and(base, N.PMASK()))) :
        {N.cs.k2(p, w0, A.A.from(tt), N.u32.pick(U32.is_lt(best, MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0)), best), N.u32.pick(U32.is_lt(best, MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), base, off), base, U32.sub(chain, 1), Bool.and(U32.is_lt(best, MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), Bool.or(U32.is_eq(U32.add(p, MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), w1), U32.is_le(35, MT_.MT.cs(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))))), _) == SC.csb(tt, SC.cs.k(p, w0, Bool.and(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), Bool.or(U32.is_eq(U32.add(p, SC.tlen(tt, base, p, U32.sub(w1, p))), w1), U32.is_le(35, SC.tlen(tt, base, p, U32.sub(w1, p))))), N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), SC.tlen(tt, base, p, U32.sub(w1, p)), best), N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), base, off), base, U32.sub(chain, 1), A.T.word(tv, U32.and(base, N.PMASK())), tv)) : Bool & N.CS}
      {==}

law SC.cs.loop_code:
  for +k: Nat
  for +p: U32
  for +w1: U32
  for +w0: U32
  for +tt: A.Tr
  for +r: CR
  {N.cs.loop(k, p, w1, w0, SC.csb(tt, r)) == SC.cs(tt, SC.cs.loop(k, p, w1, w0, tt, r)) : N.CS}

def SC.cs.loop_code(k, p, w1, w0, tt, r):
  match k r:
    case 0n CR{g, ct}:
      {==}
    case 1n+q CR{False{}, ct}:
      {==}
    case 1n+q CR{True{}, ct}:
      %Equal.sym(Bool & N.CS, N.cs.step(p, w1, w0, SC.cs(tt, ct)), SC.csb(tt, SC.cs.step(p, w1, w0, tt, ct)), SC.cs.step_code(p, w1, w0, tt, ct)) :
        {N.cs.loop(q, p, w1, w0, _) == SC.cs(tt, SC.cs.loop(q, p, w1, w0, tt, SC.cs.step(p, w1, w0, tt, ct))) : N.CS}
      SC.cs.loop_code(q, p, w1, w0, tt, SC.cs.step(p, w1, w0, tt, ct))

def SC.small.if(+z: Bool, +K: N.SK, +tt: A.Tr, +e: EM_.ET, +len: U32, +addr: U32, +st: ST) -> R2:
  match z st:
    case False{} s:
      R2{False{}, R1{True{}, s}}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      R2{True{}, SC.lazy(K, tt, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))}

def SC.small.fin(+K: N.SK, +tt: A.Tr, +e: EM_.ET, +tl: A.Tr, +tb: A.Tr, +tio: A.Tr, +p: U32, +mm: U32, +rc: U32, +rl: U32, +lck: U32, +last: U32, +nio: U32, +cont: U32, +ct: CT) -> R2:
  match K ct:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} CT{tv, best, off, base, chain}:
      +dist = U32.sub(p, off)
      +poor = Bool.or(Bool.and(U32.is_eq(best, 4), U32.is_le(16384, dist)), Bool.and(U32.is_eq(best, 5), U32.is_le(2097152, dist)))
      SC.small.if(Bool.and(Bool.not(poor), U32.is_le(mm, best)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, best, U32.add(cpl, U32.sub(off, w0)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

# The small table's slot for the 4 bytes at p.
def SC.sslot(+K: N.SK, +tt: A.Tr, +p: U32) -> U32:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)

def SC.small(+K: N.SK, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R2:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      +slot = N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)
      +head = A.T.word(tb, slot)
      +base = U32.sub(head, 1)
      SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, slot, U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(head, 0), U32.is_le(w0, base)), U32.is_lt(base, p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), head), 0, 0, base, N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))

law SC.small.if_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +z: Bool
  for +K: N.SK
  for +len: U32
  for +addr: U32
  for +st: ST
  {N.ph.small.if(z, K, len, addr, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.small.if(z, K, tt, e, len, addr, st)) : Bool & (Bool & N.Sc)}

def SC.small.if_code(ts, tt, e, z, K, len, addr, st):
  match z st:
    case False{} s:
      {==}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(N.Sc, N.sc.push(K, p, len, addr, SC.sc(ts, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.sc(ts, tt, e, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.push_code(ts, tt, e, K, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) :
        {(True{}, N.sc.lazy(K, len, _)) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) : Bool & Bool & N.Sc}
      %Equal.sym(Bool & N.Sc, N.sc.lazy(K, len, SC.sc(ts, tt, e, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.b(ts, tt, e, SC.lazy(K, tt, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.lazy_code(ts, tt, e, K, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))) :
        {(True{}, _) == (True{}, SC.b(ts, tt, e, SC.lazy(K, tt, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) : Bool & Bool & N.Sc}
      {==}

law SC.small.fin_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +tl: A.Tr
  for +tb: A.Tr
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +rc: U32
  for +rl: U32
  for +lck: U32
  for +last: U32
  for +nio: U32
  for +cont: U32
  for +ct: CT
  {N.ph.small.fin(K, A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, SC.cs(tt, ct)) == SC.bb(ts, tt, e, SC.small.fin(K, tt, e, tl, tb, tio, p, mm, rc, rl, lck, last, nio, cont, ct)) : Bool & (Bool & N.Sc)}

def SC.small.fin_code(ts, tt, e, K, tl, tb, tio, p, mm, rc, rl, lck, last, nio, cont, ct):
  match K ct:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} CT{tv, best, off, base, chain}:
      SC.small.if_code(ts, tt, e, Bool.and(Bool.not(Bool.or(Bool.and(U32.is_eq(best, 4), U32.is_le(16384, U32.sub(p, off))), Bool.and(U32.is_eq(best, 5), U32.is_le(2097152, U32.sub(p, off))))), U32.is_le(mm, best)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, best, U32.add(cpl, U32.sub(off, w0)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})

law SC.small_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +st: ST
  {N.ph.small(K, SC.sc(ts, tt, e, st)) == SC.bb(ts, tt, e, SC.small(K, tt, e, st)) : Bool & (Bool & N.Sc)}

def SC.small_code(ts, tt, e, K, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      %Equal.sym(Array<U32> & U32, B.B.word(A.A.from(tt), p), (A.A.from(tt), MT_.MT.W(tt, p)), MT_.MT.word(tt, p)) :
        {N.ph.small.k1(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tl), A.A.from(tb), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, _) == SC.bb(ts, tt, e, SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))) : Bool & Bool & N.Sc}
      %Equal.sym(Array<U32> & U32, Array.get(U32, A.A.from(tb), N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), (A.A.from(tb), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), A.A.get_from(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))) :
        {N.ph.small.k2(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tt), A.A.from(tl), A.A.from(tv), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), _) == SC.bb(ts, tt, e, SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))) : Bool & Bool & N.Sc}
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(tb), N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), A.A.from(A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1))), A.A.set_from(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1))) :
        {N.ph.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tl), _, A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, N.cs.loop(5n, p, w1, w0, (Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), N.CS{A.A.from(tt), Array.set(U32, A.A.from(tv), U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}))) == SC.bb(ts, tt, e, SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))) : Bool & Bool & N.Sc}
      %Equal.sym(Array<U32>, Array.set(U32, A.A.from(tv), U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), A.A.from(A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)))), A.A.set_from(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)))) :
        {N.ph.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tl), A.A.from(A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1))), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, N.cs.loop(5n, p, w1, w0, (Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), N.CS{A.A.from(tt), _, 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}))) == SC.bb(ts, tt, e, SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))) : Bool & Bool & N.Sc}
      %Equal.sym(N.CS, N.cs.loop(5n, p, w1, w0, (Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), N.CS{A.A.from(tt), A.A.from(A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)})), SC.cs(tt, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}})), SC.cs.loop_code(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}})) :
        {N.ph.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, A.A.from(ts), A.A.from(tl), A.A.from(A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1))), A.A.from(tio), EM_.EM.em(e), p, mm, rc, rl, lck, last, nio, cont, _) == SC.bb(ts, tt, e, SC.small.fin(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))) : Bool & Bool & N.Sc}
      SC.small.fin_code(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}))

# Stepping
# --------

def SC.next(+K: N.SK, +tt: A.Tr, +st: ST) -> R1:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update(K, tt, ST{tl, tb, tv, tio, p, N.u32.pick(U32.is_lt(4, mm), U32.sub(mm, 1), mm), rc, rl, lck, last, nio, cont})

def SC.s3(+K: N.SK, +tt: A.Tr, +r: R2) -> R1:
  match r:
    case R2{True{}, q}:
      q
    case R2{False{}, R1{c, st}}:
      SC.next(K, tt, st)

def SC.s2(+K: N.SK, +tt: A.Tr, +e: EM_.ET, +r: R2) -> R1:
  match r:
    case R2{True{}, q}:
      q
    case R2{False{}, R1{c, st}}:
      SC.s3(K, tt, SC.small(K, tt, e, st))

def SC.s1(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +r: R2) -> R1:
  match r:
    case R2{True{}, q}:
      q
    case R2{False{}, R1{c, st}}:
      SC.s2(K, tt, e, SC.large(K, ts, tt, e, st))

def SC.step(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +st: ST) -> R1:
  SC.s1(K, ts, tt, e, SC.run(K, tt, e, st))

def SC.loop(k: Nat, +K: N.SK, +ts: A.Tr, +tt: A.Tr, +e: EM_.ET, +r: R1) -> ST:
  match k r:
    case 0n R1{g, st}:
      st
    case 1n+q R1{False{}, st}:
      st
    case 1n+q R1{True{}, st}:
      SC.loop(q, K, ts, tt, e, SC.step(K, ts, tt, e, st))

# A phase that does not take the position leaves p within the window.
def SC.r2ok(+K: N.SK, +r: R2) -> Bool:
  match r:
    case R2{b, R1{c, st}}:
      Bool.or(b, U32.is_le(SC.pp(st), SC.w1(K)))

law SC.next_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +st: ST
  {N.sc.next(K, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.next(K, tt, st)) : Bool & N.Sc}

def SC.next_code(ts, tt, e, K, st):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update_code(ts, tt, e, K, ST{tl, tb, tv, tio, p, N.u32.pick(U32.is_lt(4, mm), U32.sub(mm, 1), mm), rc, rl, lck, last, nio, cont})

law SC.s3_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +r: R2
  {N.sc.s3(K, SC.bb(ts, tt, e, r)) == SC.b(ts, tt, e, SC.s3(K, tt, r)) : Bool & N.Sc}

def SC.s3_code(ts, tt, e, K, r):
  match r:
    case R2{True{}, q}:
      {==}
    case R2{False{}, R1{c, st}}:
      SC.next_code(ts, tt, e, K, st)

law SC.s2_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +r: R2
  {N.sc.s2(K, SC.bb(ts, tt, e, r)) == SC.b(ts, tt, e, SC.s2(K, tt, e, r)) : Bool & N.Sc}

def SC.s2_code(ts, tt, e, K, r):
  match r:
    case R2{True{}, q}:
      {==}
    case R2{False{}, R1{c, st}}:
      %Equal.sym(Bool & Bool & N.Sc, N.ph.small(K, SC.sc(ts, tt, e, st)), SC.bb(ts, tt, e, SC.small(K, tt, e, st)), SC.small_code(ts, tt, e, K, st)) :
        {N.sc.s3(K, _) == SC.b(ts, tt, e, SC.s3(K, tt, SC.small(K, tt, e, st))) : Bool & N.Sc}
      SC.s3_code(ts, tt, e, K, SC.small(K, tt, e, st))

law SC.s1_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +r: R2
  for +hp: {SC.r2ok(K, r) == True{} : Bool}
  for +hE: {SC.okE(K, E) == True{} : Bool}
  {N.sc.s1(K, SC.bb(ts, tt, e, r)) == SC.b(ts, tt, e, SC.s1(K, ts, tt, e, r)) : Bool & N.Sc}

def SC.s1_code(ts, tt, e, K, E, r, hp, hE):
  match r:
    case R2{True{}, q}:
      {==}
    case R2{False{}, R1{c, st}}:
      %Equal.sym(Bool & Bool & N.Sc, N.ph.large(K, SC.sc(ts, tt, e, st)), SC.bb(ts, tt, e, SC.large(K, ts, tt, e, st)), SC.large_code(ts, tt, e, K, E, st, hp, hE)) :
        {N.sc.s2(K, _) == SC.b(ts, tt, e, SC.s2(K, tt, e, SC.large(K, ts, tt, e, st))) : Bool & N.Sc}
      SC.s2_code(ts, tt, e, K, SC.large(K, ts, tt, e, st))

# The phases keep p when they do not take the position.
law SC.run.if_ok:
  for +z: Bool
  for +K: N.SK
  for +tt: A.Tr
  for +e: EM_.ET
  for +L: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.run.if(z, K, tt, e, L, st)) == True{} : Bool}

law SC.r1ok:
  for +K: N.SK
  for +q: R1
  {SC.r2ok(K, R2{True{}, q}) == True{} : Bool}

def SC.r1ok(K, q):
  match q:
    case R1{c, st}:
      {==}

def SC.run.if_ok(z, K, tt, e, L, st, hp):
  match z st:
    case False{} s:
      hp
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.r1ok(K, SC.lazy(K, tt, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))

law SC.run_ok:
  for +K: N.SK
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.run(K, tt, e, st)) == True{} : Bool}

law SC.run.go_ok:
  for +z: Bool
  for +K: N.SK
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.run.go(z, K, tt, e, st)) == True{} : Bool}

def SC.run.go_ok(z, K, tt, e, st, hp):
  match z K st:
    case False{} k s:
      hp
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.if_ok(Bool.and(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), U32.is_le(8, SC.rlen(tt, p, rc, U32.sub(w1, p)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, tt, e, SC.rlen(tt, p, rc, U32.sub(w1, p)), ST{tl, tb, tv, tio, p, mm, rc, SC.rlen(tt, p, rc, U32.sub(w1, p)), lck, last, nio, cont}, hp)

def SC.run_ok(K, tt, e, st, hp):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.go_ok(U32.is_eq(rl, 4), K, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hp)

law SC.large.if_ok:
  for +z: Bool
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +srcpos: U32
  for +maxback: U32
  for +fwd: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.large.if(z, K, ts, tt, e, srcpos, maxback, fwd, st)) == True{} : Bool}

def SC.large.if_ok(z, K, ts, tt, e, srcpos, maxback, fwd, st, hp):
  match z st:
    case False{} s:
      hp
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.r1ok(K, SC.lazy(K, tt, fwd, SC.cont(K, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))))

law SC.large.try_ok:
  for +z: Bool
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +srcpos: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.large.try(z, K, ts, tt, e, srcpos, st)) == True{} : Bool}

def SC.large.try_ok(z, K, ts, tt, e, srcpos, st, hp):
  match z st:
    case False{} s:
      hp
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.if_ok(U32.is_le(mm, SC.flen(ts, srcpos, tt, p, SC.fmax(K, p, srcpos))), K, ts, tt, e, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.flen(ts, srcpos, tt, p, SC.fmax(K, p, srcpos)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hp)

law SC.large.go_ok:
  for +z: Bool
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.large.go(z, K, ts, tt, e, st)) == True{} : Bool}

def SC.large.go_ok(z, K, ts, tt, e, st, hp):
  match z K st:
    case False{} k s:
      hp
    case True{} N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.try_ok(Bool.and(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), Bool.not(Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last)))), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, N.u32.pick(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last), nio, cont}, hp)

law SC.large_ok:
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.r2ok(K, SC.large(K, ts, tt, e, st)) == True{} : Bool}

def SC.large_ok(K, ts, tt, e, st, hp):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.go_ok(Bool.and(U32.is_lt(0, slen), U32.is_le(U32.add(p, 9), w1)), N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, e, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hp)

law SC.step_code:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +st: ST
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hE: {SC.okE(K, E) == True{} : Bool}
  {N.sc.step(K, SC.sc(ts, tt, e, st)) == SC.b(ts, tt, e, SC.step(K, ts, tt, e, st)) : Bool & N.Sc}

def SC.step_code(ts, tt, e, K, E, st, hp, hE):
  %Equal.sym(Bool & Bool & N.Sc, N.ph.run(K, SC.sc(ts, tt, e, st)), SC.bb(ts, tt, e, SC.run(K, tt, e, st)), SC.run_code(ts, tt, e, K, st)) :
    {N.sc.s1(K, _) == SC.b(ts, tt, e, SC.s1(K, ts, tt, e, SC.run(K, tt, e, st))) : Bool & N.Sc}
  SC.s1_code(ts, tt, e, K, E, SC.run(K, tt, e, st), SC.run_ok(K, tt, e, st, hp), hE)

# The invariant
# =============
#
# Every buffered match holds (SG.oks0), the buffer is a perfect tree with
# room for them, there are no more of them than bytes scanned (s more, just
# after a push), the scan is past w0 and the minimum match is 4 at least.

# A tree's depth along its left edge.
def SC.dep(+t: A.Tr) -> Nat:
  match t:
    case A.TL{v}:
      0n
    case A.TN{l, r}:
      1n+SC.dep(l)

law SC.dep_pf:
  for +d: Nat
  for +t: A.Tr
  for +h: {A.T.pf(d, t) == True{} : Bool}
  {SC.dep(t) == d : Nat}

def SC.dep_pf(d, t, h):
  match d t:
    case 0n A.TL{v}:
      {==}
    case 0n A.TN{l, r}:
      P.Bool.false_true({SC.dep(A.TN{l, r}) == 0n : Nat}, h)
    case 1n+q A.TL{v}:
      P.Bool.false_true({SC.dep(A.TL{v}) == 1n+q : Nat}, h)
    case 1n+q A.TN{l, r}:
      %Equal.sym(Nat, SC.dep(l), q, SC.dep_pf(q, l, P.Bool.and_l(A.T.pf(q, l), A.T.pf(q, r), h))) :
        {1n+_ == 1n+q : Nat}
      {==}

def SC.Iv(+ts: A.Tr, +tt: A.Tr, +slen: U32, +w0: U32, +w1: U32, +s: Nat, +tio: A.Tr, +p: U32, +mm: U32, +nio: U32) -> Bool:
  Bool.and(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0),
  Bool.and(A.T.pf(SC.dep(tio), tio),
  Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)),
  Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))),
  Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))),
  Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))))

def SC.Is(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +s: Nat, +st: ST) -> Bool:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio)

law SC.Iv.mk:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h1: {SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0) == True{} : Bool}
  for +h2: {A.T.pf(SC.dep(tio), tio) == True{} : Bool}
  for +h3: {Nat.cmp(SC.dep(tio), 32n) == LT{} : Cmp}
  for +h4: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))) == True{} : Bool}
  for +h5: {Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))) == True{} : Bool}
  for +h6: {U32.is_le(w0, p) == True{} : Bool}
  for +h7: {U32.is_le(4, mm) == True{} : Bool}
  {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}

def SC.Iv.mk(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h1, h2, h3, h4, h5, h6, h7):
  %Equal.sym(Bool, SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), True{}, h1) :
    {Bool.and(_, Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Bool, A.T.pf(SC.dep(tio), tio), True{}, h2) :
    {Bool.and(True{}, Bool.and(_, Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(SC.dep(tio), 32n), LT{}, h3) :
    {Bool.and(True{}, Bool.and(True{}, Bool.and(Cmp.is_lt(_), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), True{}, h4) :
    {Bool.and(True{}, Bool.and(True{}, Bool.and(Cmp.is_lt(LT{}), Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), True{}, h5) :
    {Bool.and(True{}, Bool.and(True{}, Bool.and(Cmp.is_lt(LT{}), Bool.and(True{}, Bool.and(_, Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, p), True{}, h6) :
    {Bool.and(True{}, Bool.and(True{}, Bool.and(Cmp.is_lt(LT{}), Bool.and(True{}, Bool.and(True{}, Bool.and(_, U32.is_le(4, mm))))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(4, mm), True{}, h7) :
    {Bool.and(True{}, Bool.and(True{}, Bool.and(Cmp.is_lt(LT{}), Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, _)))))) == True{} : Bool}
  {==}

law SC.Iv.ok:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0) == True{} : Bool}

def SC.Iv.ok(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h)

law SC.Iv.pf:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {A.T.pf(SC.dep(tio), tio) == True{} : Bool}

def SC.Iv.pf(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h))

law SC.Iv.lt:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)) == True{} : Bool}

def SC.Iv.lt(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))), P.Bool.and_r(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h)))

law SC.Iv.cap:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))) == True{} : Bool}

def SC.Iv.cap(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))), P.Bool.and_r(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))), P.Bool.and_r(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h))))

law SC.Iv.n:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))) == True{} : Bool}

def SC.Iv.n(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)), P.Bool.and_r(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))), P.Bool.and_r(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))), P.Bool.and_r(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h)))))

law SC.Iv.w0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {U32.is_le(w0, p) == True{} : Bool}

def SC.Iv.w0(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_l(U32.is_le(w0, p), U32.is_le(4, mm), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)), P.Bool.and_r(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))), P.Bool.and_r(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))), P.Bool.and_r(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h))))))

law SC.Iv.mm:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +s: Nat
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +h: {SC.Iv(ts, tt, slen, w0, w1, s, tio, p, mm, nio) == True{} : Bool}
  {U32.is_le(4, mm) == True{} : Bool}

def SC.Iv.mm(ts, tt, slen, w0, w1, s, tio, p, mm, nio, h):
  P.Bool.and_r(U32.is_le(w0, p), U32.is_le(4, mm), P.Bool.and_r(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)), P.Bool.and_r(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))), P.Bool.and_r(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))), P.Bool.and_r(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm))))), P.Bool.and_r(SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), Bool.and(A.T.pf(SC.dep(tio), tio), Bool.and(Cmp.is_lt(Nat.cmp(SC.dep(tio), 32n)), Bool.and(Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)))), Bool.and(Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), s))), Bool.and(U32.is_le(w0, p), U32.is_le(4, mm)))))), h))))))

# The buffer
# ----------

# A write past the range leaves the range's matches as they were.
law SC.oks_put:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +n: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +t: A.Tr
  for +i: U32
  for +d: Nat
  for +hp: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(n)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(n))) == True{} : Bool}
  {SG_.SG.oks0(k, ts, tt, slen, w0, w1, SG_.SG.put(t, n, pos, len, val), i) == SG_.SG.oks0(k, ts, tt, slen, w0, w1, t, i) : Bool}

def SC.oks_put(k, ts, tt, slen, w0, w1, n, pos, len, val, t, i, d, hp, hd, hcn, hr):
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(N.Ent, SE_.SE.ent(SG_.SG.put(t, n, pos, len, val), i), SE_.SE.ent(t, i), SG_.SG.get_other(t, n, pos, len, val, i, d, hp, hd, hcn, SG_.SG.cap_of(i, n, d, SG_.SG.i_lt(i, n, q, hr), P.Nat.le_trans(SG_.SG.tri(V.U.N(n)), Nat.add(SG_.SG.tri(V.U.N(n)), 3n), P.Nat.pow2(d), P.Nat.cmp_add_r(SG_.SG.tri(V.U.N(n)), 3n), hcn)), SG_.SG.ne_gt(n, i, SG_.SG.i_lt(i, n, q, hr)))) :
        {Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, _), SG_.SG.oks0(q, ts, tt, slen, w0, w1, SG_.SG.put(t, n, pos, len, val), U32.add(i, 1))) == Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      %Equal.sym(Bool, SG_.SG.oks0(q, ts, tt, slen, w0, w1, SG_.SG.put(t, n, pos, len, val), U32.add(i, 1)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1)), SC.oks_put(q, ts, tt, slen, w0, w1, n, pos, len, val, t, U32.add(i, 1), d, hp, hd, hcn, SG_.SG.r_next(i, n, q, hr))) :
        {Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), _) == Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      {==}

# The range's matches and the one after it.
law SC.oks_snoc:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +i: U32
  for +j: U32
  for +hj: {V.U.N(j) == Nat.add(k, V.U.N(i)) : Nat}
  for +h1: {SG_.SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  for +h2: {SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, j)) == True{} : Bool}
  {SG_.SG.oks0(1n+k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}

law SC.oks_snoc.j:
  for +q: Nat
  for +i: U32
  for +j: U32
  for +hj: {V.U.N(j) == 1n+Nat.add(q, V.U.N(i)) : Nat}
  {V.U.N(j) == Nat.add(q, V.U.N(U32.add(i, 1))) : Nat}

# i is below 1 + q + i.
law SC.lt_add1:
  for +q: Nat
  for +i: Nat
  {Nat.cmp(i, 1n+Nat.add(q, i)) == LT{} : Cmp}

def SC.lt_add1(q, i):
  match i:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Nat, Nat.add(q, 1n+r), 1n+Nat.add(q, r), P.Nat.add_succ_r(q, r)) :
        {Nat.cmp(1n+r, 1n+_) == LT{} : Cmp}
      SC.lt_add1(q, r)

def SC.oks_snoc.j(q, i, j, hj):
  %Equal.sym(Nat, V.U.N(U32.add(i, 1)), 1n+V.U.N(i), V.U.succ_N(i, j, (%Equal.sym(Nat, V.U.N(j), 1n+Nat.add(q, V.U.N(i)), hj) : {Nat.cmp(V.U.N(i), _) == LT{} : Cmp}; SC.lt_add1(q, V.U.N(i))))) :
    {V.U.N(j) == Nat.add(q, _) : Nat}
  %Equal.sym(Nat, Nat.add(q, 1n+V.U.N(i)), 1n+Nat.add(q, V.U.N(i)), P.Nat.add_succ_r(q, V.U.N(i))) :
    {V.U.N(j) == _ : Nat}
  hj

def SC.oks_snoc(k, ts, tt, slen, w0, w1, t, i, j, hj, h1, h2):
  match k:
    case 0n:
      %Equal.sym(U32, i, j, V.U.eq_N(i, j, Equal.sym(Nat, V.U.N(j), V.U.N(i), hj))) :
        {Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, _)), True{}) == True{} : Bool}
      %Equal.sym(Bool, SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, j)), True{}, h2) :
        {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 1n+q:
      %Equal.sym(Bool, SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), True{}, P.Bool.and_l(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1)), h1)) :
        {Bool.and(_, SG_.SG.oks0(1n+q, ts, tt, slen, w0, w1, t, U32.add(i, 1))) == True{} : Bool}
      SC.oks_snoc(q, ts, tt, slen, w0, w1, t, U32.add(i, 1), j, SC.oks_snoc.j(q, i, j, hj), P.Bool.and_r(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1)), h1), h2)

# Fewer matches still hold.
law SC.oks_pre:
  for +m: Nat
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +i: U32
  for +hm: {Cmp.is_le(Nat.cmp(m, k)) == True{} : Bool}
  for +h: {SG_.SG.oks0(k, ts, tt, slen, w0, w1, t, i) == True{} : Bool}
  {SG_.SG.oks0(m, ts, tt, slen, w0, w1, t, i) == True{} : Bool}

def SC.oks_pre(m, k, ts, tt, slen, w0, w1, t, i, hm, h):
  match m k:
    case 0n k2:
      {==}
    case 1n+a 0n:
      P.Bool.false_true({SG_.SG.oks0(1n+a, ts, tt, slen, w0, w1, t, i) == True{} : Bool}, hm)
    case 1n+a 1n+b:
      %Equal.sym(Bool, SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), True{}, P.Bool.and_l(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(b, ts, tt, slen, w0, w1, t, U32.add(i, 1)), h)) :
        {Bool.and(_, SG_.SG.oks0(a, ts, tt, slen, w0, w1, t, U32.add(i, 1))) == True{} : Bool}
      SC.oks_pre(a, b, ts, tt, slen, w0, w1, t, U32.add(i, 1), hm, P.Bool.and_r(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(b, ts, tt, slen, w0, w1, t, U32.add(i, 1)), h))

# Buffer arithmetic
# -----------------
#
# The buffer's indices and sizes as numbers, under a bound BIG < 2^31.

law SC.cgt:
  for +c: Cmp
  for +h: {Cmp.is_gt(c) == False{} : Bool}
  {Cmp.is_le(c) == True{} : Bool}

def SC.cgt(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.true_false({Cmp.is_le(GT{}) == True{} : Bool}, h)

law SC.ngt:
  for +a: U32
  for +b: U32
  for +h: {U32.is_gt(a, b) == False{} : Bool}
  {U32.is_le(a, b) == True{} : Bool}

def SC.ngt(a, b, h):
  SC.cgt(U32.cmp(a, b), h)

law SC.le_tri:
  for +a: Nat
  {Cmp.is_le(Nat.cmp(a, SG_.SG.tri(a))) == True{} : Bool}

def SC.le_tri(a):
  %SG_.SG.tri_eq(a) :
    {Cmp.is_le(Nat.cmp(a, _)) == True{} : Bool}
  P.Nat.le_add_l(Nat.double(a), a)

# Below BIG, so its top bit is clear.
law SC.le_dd:
  for +a: Nat
  {Cmp.is_le(Nat.cmp(a, Nat.double(Nat.double(a)))) == True{} : Bool}

def SC.le_dd(a):
  P.Nat.le_trans(a, Nat.double(a), Nat.double(Nat.double(a)), EM_.GR.le_dbl(a), EM_.GR.le_dbl(Nat.double(a)))

law SC.top:
  for +n: U32
  for +BIG: U32
  for +h: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.bit(n, 31n) == False{} : Bool}

def SC.top(n, BIG, h, hB):
  V.U.bit_lt_pow(n, 31n, 31n, EM_.EM.lt31(n, BIG, h, hB), {==}, {==})

law SC.atB:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(n)), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.N(N.io.at(n)) == SG_.SG.tri(V.U.N(n)) : Nat}

law SC.atB.b:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(n)), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.shl(n)), V.U.N(n)), V.U.N(BIG))) == True{} : Bool}

def SC.atB.b(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shl(n)), Nat.double(V.U.N(n)), V.U.N_shl(n, SC.top(n, BIG, P.Nat.le_trans(V.U.N(n), SG_.SG.tri(V.U.N(n)), V.U.N(BIG), SC.le_tri(V.U.N(n)), hb), hB))) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(n)), V.U.N(BIG))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.double(V.U.N(n)), V.U.N(n)), SG_.SG.tri(V.U.N(n)), SG_.SG.tri_eq(V.U.N(n))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}
  hb

def SC.atB(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.add(U32.shl(n), n)), Nat.add(V.U.N(U32.shl(n)), V.U.N(n)), V.U.add_N(U32.shl(n), n, BIG, SC.atB.b(n, BIG, hb, hB))) :
    {_ == SG_.SG.tri(V.U.N(n)) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(n)), Nat.double(V.U.N(n)), V.U.N_shl(n, SC.top(n, BIG, P.Nat.le_trans(V.U.N(n), SG_.SG.tri(V.U.N(n)), V.U.N(BIG), SC.le_tri(V.U.N(n)), hb), hB))) :
    {Nat.add(_, V.U.N(n)) == SG_.SG.tri(V.U.N(n)) : Nat}
  SG_.SG.tri_eq(V.U.N(n))

law SC.at3B:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(n)), 3n), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.N(U32.add(N.io.at(n), 3)) == Nat.add(SG_.SG.tri(V.U.N(n)), 3n) : Nat}

def SC.at3B(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.add(N.io.at(n), 3)), Nat.add(V.U.N(N.io.at(n)), 3n), V.U.add_N(N.io.at(n), 3, BIG, (%Equal.sym(Nat, V.U.N(N.io.at(n)), SG_.SG.tri(V.U.N(n)), SC.atB(n, BIG, P.Nat.le_trans(SG_.SG.tri(V.U.N(n)), Nat.add(SG_.SG.tri(V.U.N(n)), 3n), V.U.N(BIG), P.Nat.cmp_add_r(SG_.SG.tri(V.U.N(n)), 3n), hb), hB)) : {Cmp.is_le(Nat.cmp(Nat.add(_, V.U.N(3)), V.U.N(BIG))) == True{} : Bool}; hb))) :
    {_ == Nat.add(SG_.SG.tri(V.U.N(n)), 3n) : Nat}
  %Equal.sym(Nat, V.U.N(N.io.at(n)), SG_.SG.tri(V.U.N(n)), SC.atB(n, BIG, P.Nat.le_trans(SG_.SG.tri(V.U.N(n)), Nat.add(SG_.SG.tri(V.U.N(n)), 3n), V.U.N(BIG), P.Nat.cmp_add_r(SG_.SG.tri(V.U.N(n)), 3n), hb), hB)) :
    {Nat.add(_, 3n) == Nat.add(SG_.SG.tri(V.U.N(n)), 3n) : Nat}
  {==}

law SC.bytesB:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.N(N.io.bytes(n)) == Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))) : Nat}

law SC.bytesB.t:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(n)), V.U.N(BIG))) == True{} : Bool}

def SC.bytesB.t(n, BIG, hb):
  P.Nat.le_trans(SG_.SG.tri(V.U.N(n)), Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG), SC.le_dd(SG_.SG.tri(V.U.N(n))), hb)

law SC.bytesB.b0:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(N.io.at(n)), V.U.N(BIG))) == True{} : Bool}

def SC.bytesB.b0(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(N.io.at(n)), SG_.SG.tri(V.U.N(n)), SC.atB(n, BIG, SC.bytesB.t(n, BIG, hb), hB)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}
  SC.bytesB.t(n, BIG, hb)

law SC.bytesB.b1:
  for +n: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.shl(N.io.at(n))), V.U.N(BIG))) == True{} : Bool}

def SC.bytesB.b1(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shl(N.io.at(n))), Nat.double(V.U.N(N.io.at(n))), V.U.N_shl(N.io.at(n), SC.top(N.io.at(n), BIG, SC.bytesB.b0(n, BIG, hb, hB), hB))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(N.io.at(n)), SG_.SG.tri(V.U.N(n)), SC.atB(n, BIG, SC.bytesB.t(n, BIG, hb), hB)) :
    {Cmp.is_le(Nat.cmp(Nat.double(_), V.U.N(BIG))) == True{} : Bool}
  P.Nat.le_trans(Nat.double(SG_.SG.tri(V.U.N(n))), Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))), V.U.N(BIG), EM_.GR.le_dbl(Nat.double(SG_.SG.tri(V.U.N(n)))), hb)

def SC.bytesB(n, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shl(N.io.at(n)))), Nat.double(V.U.N(U32.shl(N.io.at(n)))), V.U.N_shl(U32.shl(N.io.at(n)), SC.top(U32.shl(N.io.at(n)), BIG, SC.bytesB.b1(n, BIG, hb, hB), hB))) :
    {_ == Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(N.io.at(n))), Nat.double(V.U.N(N.io.at(n))), V.U.N_shl(N.io.at(n), SC.top(N.io.at(n), BIG, SC.bytesB.b0(n, BIG, hb, hB), hB))) :
    {Nat.double(_) == Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))) : Nat}
  %Equal.sym(Nat, V.U.N(N.io.at(n)), SG_.SG.tri(V.U.N(n)), SC.atB(n, BIG, SC.bytesB.t(n, BIG, hb), hB)) :
    {Nat.double(Nat.double(_)) == Nat.double(Nat.double(SG_.SG.tri(V.U.N(n)))) : Nat}
  {==}

# The scan's fixed facts
# ----------------------
#
# The emitter starts at w0, the copy segment is the whole source, E bounds
# the source and the window (so the comparisons and target addresses do not
# wrap), and BIG < 2^31 bounds the buffer's bytes for a match a byte.
def SC.kv(+e: EM_.ET, +slen: U32, +w0: U32, +w1: U32, +cpl: U32, +E: U32, +BIG: U32) -> Bool:
  Bool.and(U32.is_eq(EM_.EM.uo(e), w0),
  Bool.and(U32.is_eq(cpl, slen),
  Bool.and(U32.is_le(w0, w1),
  Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))),
  Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))),
  Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))),
  Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))),
    U32.is_lt(BIG, 2147483648))))))))

def SC.kf(+K: N.SK, +e: EM_.ET, +E: U32, +BIG: U32) -> Bool:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      SC.kv(e, slen, w0, w1, cpl, E, BIG)

law SC.lt_add3:
  for +a: Nat
  {Nat.cmp(a, Nat.add(a, 3n)) == LT{} : Cmp}

def SC.lt_add3(a):
  %Equal.sym(Nat, Nat.add(a, 3n), Nat.add(3n, a), P.Nat.add_comm(a, 3n)) :
    {Nat.cmp(a, _) == LT{} : Cmp}
  SC.lt_add1(2n, a)

# n's bounds, for n at most w1.
law SC.B1:
  for +n: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(SG_.SG.tri(1n+V.U.N(n)), V.U.N(BIG))) == True{} : Bool}

def SC.B1(n, w1, BIG, hn, hk):
  P.Nat.le_trans(SG_.SG.tri(1n+V.U.N(n)), SG_.SG.tri(1n+V.U.N(w1)), V.U.N(BIG), SG_.SG.tri_mono(1n+V.U.N(n), 1n+V.U.N(w1), hn),
    P.Nat.le_trans(SG_.SG.tri(1n+V.U.N(w1)), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG), SC.le_dd(SG_.SG.tri(1n+V.U.N(w1))), hk))

law SC.B3:
  for +n: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(n)), 3n), V.U.N(BIG))) == True{} : Bool}

def SC.B3(n, w1, BIG, hn, hk):
  %Equal.sym(Nat, Nat.add(SG_.SG.tri(V.U.N(n)), 3n), Nat.add(3n, SG_.SG.tri(V.U.N(n))), P.Nat.add_comm(SG_.SG.tri(V.U.N(n)), 3n)) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}
  SC.B1(n, w1, BIG, hn, hk)

law SC.B2:
  for +n: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(n)))), V.U.N(BIG))) == True{} : Bool}

def SC.B2(n, w1, BIG, hn, hk):
  P.Nat.le_trans(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(n)))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG),
    P.Nat.double_mono(Nat.double(SG_.SG.tri(1n+V.U.N(n))), Nat.double(SG_.SG.tri(1n+V.U.N(w1))), P.Nat.double_mono(SG_.SG.tri(1n+V.U.N(n)), SG_.SG.tri(1n+V.U.N(w1)), SG_.SG.tri_mono(1n+V.U.N(n), 1n+V.U.N(w1), hn))),
    hk)

law SC.Bs:
  for +n: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(n), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  {V.U.N(U32.add(n, 1)) == 1n+V.U.N(n) : Nat}

def SC.Bs(n, w1, BIG, hn, hk):
  V.U.succ_N(n, BIG, P.Nat.le_lt_trans(V.U.N(n), SG_.SG.tri(V.U.N(n)), V.U.N(BIG), SC.le_tri(V.U.N(n)), P.Nat.lt_le_trans(SG_.SG.tri(V.U.N(n)), Nat.add(SG_.SG.tri(V.U.N(n)), 3n), V.U.N(BIG), SC.lt_add3(SG_.SG.tri(V.U.N(n))), SC.B3(n, w1, BIG, hn, hk))))

# Room in the buffer: not full, so 3 more words fit.
law SC.room:
  for +nio: U32
  for +t: A.Tr
  for +d: Nat
  for +BIG: U32
  for +hpf: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hf: {U32.is_gt(U32.add(N.io.at(nio), 3), A.T.size(t)) == False{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(nio)), 3n), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(nio)), 3n), P.Nat.pow2(d))) == True{} : Bool}

def SC.room(nio, t, d, BIG, hpf, hd, hf, hb, hB):
  %SC.at3B(nio, BIG, hb, hB) :
    {Cmp.is_le(Nat.cmp(_, P.Nat.pow2(d))) == True{} : Bool}
  %V.U.N_pow(d, hd) :
    {Cmp.is_le(Nat.cmp(V.U.N(U32.add(N.io.at(nio), 3)), _)) == True{} : Bool}
  %A.T.size_pf(d, t, hpf) :
    {Cmp.is_le(Nat.cmp(V.U.N(U32.add(N.io.at(nio), 3)), V.U.N(_))) == True{} : Bool}
  V.U.le_N(U32.add(N.io.at(nio), 3), A.T.size(t), SC.ngt(U32.add(N.io.at(nio), 3), A.T.size(t), hf))

# Growing the buffer keeps its matches
# ------------------------------------
#
# B.grow copies the buffer's bytes; a word is its four bytes.

law SC.w4inj:
  for +a: U32
  for +b: U32
  for +h: {K.WD.w4(a) == K.WD.w4(b) : List<&2, U32>}
  {a == b : U32}

def SC.w4inj(a, b, h):
  %Z.BB.ins4(0, a) :
    {_ == b : U32}
  %Equal.sym(U32, Y.BP.ext(a, 0n), Y.BP.ext(b, 0n), K.WD.cons_inj_h(Y.BP.ext(a, 0n), Y.BP.ext(a, 8n) <> Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 0n), Y.BP.ext(b, 8n) <> Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], h)) :
    {Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(0, 0n, _), 8n, Y.BP.ext(a, 8n)), 16n, Y.BP.ext(a, 16n)), 24n, Y.BP.ext(a, 24n)) == b : U32}
  %Equal.sym(U32, Y.BP.ext(a, 8n), Y.BP.ext(b, 8n), K.WD.cons_inj_h(Y.BP.ext(a, 8n), Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 8n), Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], K.WD.cons_inj_t(Y.BP.ext(a, 0n), Y.BP.ext(a, 8n) <> Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 0n), Y.BP.ext(b, 8n) <> Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], h))) :
    {Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(0, 0n, Y.BP.ext(b, 0n)), 8n, _), 16n, Y.BP.ext(a, 16n)), 24n, Y.BP.ext(a, 24n)) == b : U32}
  %Equal.sym(U32, Y.BP.ext(a, 16n), Y.BP.ext(b, 16n), K.WD.cons_inj_h(Y.BP.ext(a, 16n), Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 16n), Y.BP.ext(b, 24n) <> [], K.WD.cons_inj_t(Y.BP.ext(a, 8n), Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 8n), Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], K.WD.cons_inj_t(Y.BP.ext(a, 0n), Y.BP.ext(a, 8n) <> Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 0n), Y.BP.ext(b, 8n) <> Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], h)))) :
    {Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(0, 0n, Y.BP.ext(b, 0n)), 8n, Y.BP.ext(b, 8n)), 16n, _), 24n, Y.BP.ext(a, 24n)) == b : U32}
  %Equal.sym(U32, Y.BP.ext(a, 24n), Y.BP.ext(b, 24n), K.WD.cons_inj_h(Y.BP.ext(a, 24n), [], Y.BP.ext(b, 24n), [], K.WD.cons_inj_t(Y.BP.ext(a, 16n), Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 16n), Y.BP.ext(b, 24n) <> [], K.WD.cons_inj_t(Y.BP.ext(a, 8n), Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 8n), Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], K.WD.cons_inj_t(Y.BP.ext(a, 0n), Y.BP.ext(a, 8n) <> Y.BP.ext(a, 16n) <> Y.BP.ext(a, 24n) <> [], Y.BP.ext(b, 0n), Y.BP.ext(b, 8n) <> Y.BP.ext(b, 16n) <> Y.BP.ext(b, 24n) <> [], h))))) :
    {Y.BP.ins(Y.BP.ins(Y.BP.ins(Y.BP.ins(0, 0n, Y.BP.ext(b, 0n)), 8n, Y.BP.ext(b, 8n)), 16n, Y.BP.ext(b, 16n)), 24n, _) == b : U32}
  Z.BB.ins4(0, b)

law SC.add0l:
  for +x: U32
  {U32.add(0, x) == x : U32}

def SC.add0l(x):
  %Equal.sym(U32, U32.add(0, x), U32.add(x, 0), V.U.add_comm(0, x)) :
    {_ == x : U32}
  V.U.add_zero_r(x)

# Word j's bytes: from 4j.
law SC.wX:
  for +j: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.N(U32.shln(j, 2n)) == Nat.double(Nat.double(V.U.N(j))) : Nat}

law SC.wX.b0:
  for +j: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(j), V.U.N(BIG))) == True{} : Bool}

def SC.wX.b0(j, BIG, hb):
  P.Nat.le_trans(V.U.N(j), Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG), P.Nat.le_trans(V.U.N(j), 1n+V.U.N(j), Nat.double(Nat.double(1n+V.U.N(j))), P.Nat.lt_to_le(V.U.N(j), 1n+V.U.N(j), SC.lt_add1(0n, V.U.N(j))), SC.le_dd(1n+V.U.N(j))), hb)

law SC.wX.b1:
  for +j: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.shl(j)), V.U.N(BIG))) == True{} : Bool}

def SC.wX.b1(j, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shl(j)), Nat.double(V.U.N(j)), V.U.N_shl(j, SC.top(j, BIG, SC.wX.b0(j, BIG, hb), hB))) :
    {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}
  P.Nat.le_trans(Nat.double(V.U.N(j)), Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG), P.Nat.le_trans(Nat.double(V.U.N(j)), Nat.double(1n+V.U.N(j)), Nat.double(Nat.double(1n+V.U.N(j))), P.Nat.double_mono(V.U.N(j), 1n+V.U.N(j), P.Nat.lt_to_le(V.U.N(j), 1n+V.U.N(j), SC.lt_add1(0n, V.U.N(j)))), EM_.GR.le_dbl(Nat.double(1n+V.U.N(j)))), hb)

def SC.wX(j, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shl(U32.shl(j))), Nat.double(V.U.N(U32.shl(j))), V.U.N_shl(U32.shl(j), SC.top(U32.shl(j), BIG, SC.wX.b1(j, BIG, hb, hB), hB))) :
    {_ == Nat.double(Nat.double(V.U.N(j))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.shl(j)), Nat.double(V.U.N(j)), V.U.N_shl(j, SC.top(j, BIG, SC.wX.b0(j, BIG, hb), hB))) :
    {Nat.double(_) == Nat.double(Nat.double(V.U.N(j))) : Nat}
  {==}

# A word's four bytes.
law SC.w4of:
  for +u: A.Tr
  for +j: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {K.WD.w4(A.T.word(u, j)) == S.S.sl(4n, u, U32.shln(j, 2n)) : List<&2, U32>}

law SC.w4of.b:
  for +j: U32
  for +BIG: U32
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(4n, V.U.N(U32.shln(j, 2n))), V.U.N(BIG))) == True{} : Bool}

def SC.w4of.b(j, BIG, hb, hB):
  %Equal.sym(Nat, V.U.N(U32.shln(j, 2n)), Nat.double(Nat.double(V.U.N(j))), SC.wX(j, BIG, hb, hB)) :
    {Cmp.is_le(Nat.cmp(Nat.add(4n, _), V.U.N(BIG))) == True{} : Bool}
  hb

def SC.w4of(u, j, BIG, hb, hB):
  %K.WD.join(u, U32.shln(j, 2n), BIG, SC.w4of.b(j, BIG, hb, hB)) :
    {K.WD.w4(A.T.word(u, j)) == _ : List<&2, U32>}
  %Equal.sym(U32, U32.shrn(U32.shln(j, 2n), 2n), j, K.WD.at(U32.shln(j, 2n), j, 0n, SC.wX(j, BIG, hb, hB), {==})) :
    {K.WD.w4(A.T.word(u, j)) == K.WD.w4(B.B.join(A.T.word(u, _), A.T.word(u, U32.add(_, 1)), B.B.sh(U32.shln(j, 2n)))) : List<&2, U32>}
  %Equal.sym(U32, U32.and(3, U32.shln(j, 2n)), 0, Z.BB.al4(j)) :
    {K.WD.w4(A.T.word(u, j)) == K.WD.w4(B.B.join(A.T.word(u, j), A.T.word(u, U32.add(j, 1)), U32.to_nat(U32.shln(_, 3n)))) : List<&2, U32>}
  %Equal.sym(U32, B.B.join(A.T.word(u, j), A.T.word(u, U32.add(j, 1)), 0n), A.T.word(u, j), Z.BB.join0(A.T.word(u, j), A.T.word(u, U32.add(j, 1)))) :
    {K.WD.w4(A.T.word(u, j)) == K.WD.w4(_) : List<&2, U32>}
  {==}

law SC.sl_take:
  for +k: Nat
  for +n: Nat
  for +u: A.Tr
  for +t: A.Tr
  for +hk: {Cmp.is_le(Nat.cmp(k, n)) == True{} : Bool}
  for +he: {S.S.sl(n, u, 0) == S.S.sl(n, t, 0) : List<&2, U32>}
  {S.S.sl(k, u, 0) == S.S.sl(k, t, 0) : List<&2, U32>}

def SC.sl_take(k, n, u, t, hk, he):
  %MT_.MT.take_sl(k, n, u, 0, hk) :
    {_ == S.S.sl(k, t, 0) : List<&2, U32>}
  %MT_.MT.take_sl(k, n, t, 0, hk) :
    {MT_.MT.take(k, S.S.sl(n, u, 0)) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(n, u, 0), S.S.sl(n, t, 0), he) :
    {MT_.MT.take(k, _) == MT_.MT.take(k, S.S.sl(n, t, 0)) : List<&2, U32>}
  {==}

# A word within the bytes two trees share.
law SC.wk:
  for +t: A.Tr
  for +u: A.Tr
  for +used: U32
  for +j: U32
  for +BIG: U32
  for +he: {S.S.sl(V.U.N(used), u, 0) == S.S.sl(V.U.N(used), t, 0) : List<&2, U32>}
  for +hj: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used))) == True{} : Bool}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {A.T.word(u, j) == A.T.word(t, j) : U32}

law SC.wk.w:
  for +t: A.Tr
  for +u: A.Tr
  for +used: U32
  for +j: U32
  for +BIG: U32
  for +he: {S.S.sl(V.U.N(used), u, 0) == S.S.sl(V.U.N(used), t, 0) : List<&2, U32>}
  for +hj: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used))) == True{} : Bool}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {K.WD.w4(A.T.word(u, j)) == K.WD.w4(A.T.word(t, j)) : List<&2, U32>}

def SC.wk.w(t, u, used, j, BIG, he, hj, hu, hB):
  %Equal.sym(List<&2, U32>, K.WD.w4(A.T.word(u, j)), S.S.sl(4n, u, U32.shln(j, 2n)), SC.w4of(u, j, BIG, P.Nat.le_trans(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used), V.U.N(BIG), hj, hu), hB)) :
    {_ == K.WD.w4(A.T.word(t, j)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, K.WD.w4(A.T.word(t, j)), S.S.sl(4n, t, U32.shln(j, 2n)), SC.w4of(t, j, BIG, P.Nat.le_trans(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used), V.U.N(BIG), hj, hu), hB)) :
    {S.S.sl(4n, u, U32.shln(j, 2n)) == _ : List<&2, U32>}
  %SC.add0l(U32.shln(j, 2n)) :
    {S.S.sl(4n, u, _) == S.S.sl(4n, t, _) : List<&2, U32>}
  K.WD.sl_suf(Nat.double(Nat.double(V.U.N(j))), 4n, u, t, 0, U32.shln(j, 2n), SC.wX(j, BIG, P.Nat.le_trans(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used), V.U.N(BIG), hj, hu), hB),
    SC.sl_take(Nat.add(Nat.double(Nat.double(V.U.N(j))), 4n), V.U.N(used), u, t, (%P.Nat.add_comm(4n, Nat.double(Nat.double(V.U.N(j)))) : {Cmp.is_le(Nat.cmp(_, V.U.N(used))) == True{} : Bool}; hj), he))

def SC.wk(t, u, used, j, BIG, he, hj, hu, hB):
  SC.w4inj(A.T.word(u, j), A.T.word(t, j), SC.wk.w(t, u, used, j, BIG, he, hj, hu, hB))

# The three words of an entry before n, within 12n bytes.
law SC.ekb:
  for +j: U32
  for +a: Nat
  for +r: Nat
  for +n: Nat
  for +used: U32
  for +hj: {V.U.N(j) == Nat.add(SG_.SG.tri(a), r) : Nat}
  for +hr: {Cmp.is_le(Nat.cmp(r, 2n)) == True{} : Bool}
  for +ha: {Nat.cmp(a, n) == LT{} : Cmp}
  for +hus: {V.U.N(used) == Nat.double(Nat.double(SG_.SG.tri(n))) : Nat}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+V.U.N(j))), V.U.N(used))) == True{} : Bool}

law SC.ekb.r:
  for +a: Nat
  for +r: Nat
  for +hr: {Cmp.is_le(Nat.cmp(r, 2n)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(1n+Nat.add(SG_.SG.tri(a), r), SG_.SG.tri(1n+a))) == True{} : Bool}

def SC.ekb.r(a, r, hr):
  %Equal.sym(Nat, Nat.add(SG_.SG.tri(a), r), Nat.add(r, SG_.SG.tri(a)), P.Nat.add_comm(SG_.SG.tri(a), r)) :
    {Cmp.is_le(Nat.cmp(_, 2n+SG_.SG.tri(a))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(r, SG_.SG.tri(a)), Nat.add(SG_.SG.tri(a), r), P.Nat.add_comm(r, SG_.SG.tri(a))) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(2n, SG_.SG.tri(a)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(2n, SG_.SG.tri(a)), Nat.add(SG_.SG.tri(a), 2n), P.Nat.add_comm(2n, SG_.SG.tri(a))) :
    {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(a), r), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(SG_.SG.tri(a), r), Nat.add(SG_.SG.tri(a), 2n)), Nat.cmp(r, 2n), P.Nat.cmp_add_l(SG_.SG.tri(a), r, 2n)) :
    {Cmp.is_le(_) == True{} : Bool}
  hr

def SC.ekb(j, a, r, n, used, hj, hr, ha, hus):
  %Equal.sym(Nat, V.U.N(j), Nat.add(SG_.SG.tri(a), r), hj) :
    {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+_)), V.U.N(used))) == True{} : Bool}
  %Equal.sym(Nat, V.U.N(used), Nat.double(Nat.double(SG_.SG.tri(n))), hus) :
    {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(1n+Nat.add(SG_.SG.tri(a), r))), _)) == True{} : Bool}
  P.Nat.double_mono(Nat.double(1n+Nat.add(SG_.SG.tri(a), r)), Nat.double(SG_.SG.tri(n)), P.Nat.double_mono(1n+Nat.add(SG_.SG.tri(a), r), SG_.SG.tri(n),
    P.Nat.le_trans(1n+Nat.add(SG_.SG.tri(a), r), SG_.SG.tri(1n+a), SG_.SG.tri(n), SC.ekb.r(a, r, hr), SG_.SG.tri_mono(1n+a, n, P.Nat.lt_le_succ(a, n, ha)))))

law SC.ek:
  for +t: A.Tr
  for +u: A.Tr
  for +used: U32
  for +i: U32
  for +nio: U32
  for +d: Nat
  for +BIG: U32
  for +he: {S.S.sl(V.U.N(used), u, 0) == S.S.sl(V.U.N(used), t, 0) : List<&2, U32>}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcap: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hi: {Nat.cmp(V.U.N(i), V.U.N(nio)) == LT{} : Cmp}
  for +hus: {V.U.N(used) == Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))) : Nat}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SE_.SE.ent(u, i) == SE_.SE.ent(t, i) : N.Ent}

def SC.ek(t, u, used, i, nio, d, BIG, he, hd, hcap, hi, hus, hu, hB):
  %Equal.sym(N.Ent, SE_.SE.ent(u, i), N.Ent{A.T.word(u, N.io.at(i)), U32.and(A.T.word(u, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(u, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(u, U32.add(N.io.at(i), 1)))}, SG_.SG.ent_def(u, i)) :
    {_ == SE_.SE.ent(t, i) : N.Ent}
  %Equal.sym(N.Ent, SE_.SE.ent(t, i), N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))}, SG_.SG.ent_def(t, i)) :
    {N.Ent{A.T.word(u, N.io.at(i)), U32.and(A.T.word(u, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(u, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(u, U32.add(N.io.at(i), 1)))} == _ : N.Ent}
  %Equal.sym(U32, A.T.word(u, N.io.at(i)), A.T.word(t, N.io.at(i)), SC.wk(t, u, used, N.io.at(i), BIG, he, SC.ekb(N.io.at(i), V.U.N(i), 0n, V.U.N(nio), used, (%Equal.sym(Nat, Nat.add(SG_.SG.tri(V.U.N(i)), 0n), SG_.SG.tri(V.U.N(i)), P.Nat.add_zero_r(SG_.SG.tri(V.U.N(i)))) : {V.U.N(N.io.at(i)) == _ : Nat}; SG_.SG.atN(i, d, hd, SG_.SG.cap_of(i, nio, d, hi, hcap))), {==}, hi, hus), hu, hB)) :
    {N.Ent{_, U32.and(A.T.word(u, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(u, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(u, U32.add(N.io.at(i), 1)))} == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(u, U32.add(N.io.at(i), 1)), A.T.word(t, U32.add(N.io.at(i), 1)), SC.wk(t, u, used, U32.add(N.io.at(i), 1), BIG, he, SC.ekb(U32.add(N.io.at(i), 1), V.U.N(i), 1n, V.U.N(nio), used, SG_.SG.ixN(i, 1, d, hd, {==}, SG_.SG.cap_of(i, nio, d, hi, hcap)), {==}, hi, hus), hu, hB)) :
    {N.Ent{A.T.word(t, N.io.at(i)), U32.and(_, 2147483647), A.T.word(u, U32.add(N.io.at(i), 2)), N.ent.run(_)} == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  %Equal.sym(U32, A.T.word(u, U32.add(N.io.at(i), 2)), A.T.word(t, U32.add(N.io.at(i), 2)), SC.wk(t, u, used, U32.add(N.io.at(i), 2), BIG, he, SC.ekb(U32.add(N.io.at(i), 2), V.U.N(i), 2n, V.U.N(nio), used, SG_.SG.ixN(i, 2, d, hd, {==}, SG_.SG.cap_of(i, nio, d, hi, hcap)), {==}, hi, hus), hu, hB)) :
    {N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), _, N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} == N.Ent{A.T.word(t, N.io.at(i)), U32.and(A.T.word(t, U32.add(N.io.at(i), 1)), 2147483647), A.T.word(t, U32.add(N.io.at(i), 2)), N.ent.run(A.T.word(t, U32.add(N.io.at(i), 1)))} : N.Ent}
  {==}

law SC.oks_keep:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +u: A.Tr
  for +used: U32
  for +i: U32
  for +nio: U32
  for +d: Nat
  for +BIG: U32
  for +he: {S.S.sl(V.U.N(used), u, 0) == S.S.sl(V.U.N(used), t, 0) : List<&2, U32>}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcap: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(i), k), V.U.N(nio))) == True{} : Bool}
  for +hus: {V.U.N(used) == Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))) : Nat}
  for +hu: {Cmp.is_le(Nat.cmp(V.U.N(used), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SG_.SG.oks0(k, ts, tt, slen, w0, w1, u, i) == SG_.SG.oks0(k, ts, tt, slen, w0, w1, t, i) : Bool}

def SC.oks_keep(k, ts, tt, slen, w0, w1, t, u, used, i, nio, d, BIG, he, hd, hcap, hr, hus, hu, hB):
  match k:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(N.Ent, SE_.SE.ent(u, i), SE_.SE.ent(t, i), SC.ek(t, u, used, i, nio, d, BIG, he, hd, hcap, SG_.SG.i_lt(i, nio, q, hr), hus, hu, hB)) :
        {Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, _), SG_.SG.oks0(q, ts, tt, slen, w0, w1, u, U32.add(i, 1))) == Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      %Equal.sym(Bool, SG_.SG.oks0(q, ts, tt, slen, w0, w1, u, U32.add(i, 1)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1)), SC.oks_keep(q, ts, tt, slen, w0, w1, t, u, used, U32.add(i, 1), nio, d, BIG, he, hd, hcap, SG_.SG.r_next(i, nio, q, hr), hus, hu, hB)) :
        {Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), _) == Bool.and(SG_.SG.ok0(ts, tt, slen, w0, w1, SE_.SE.ent(t, i)), SG_.SG.oks0(q, ts, tt, slen, w0, w1, t, U32.add(i, 1))) : Bool}
      {==}

# The buffer's matches after B.grow.
law SC.oks_grow:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +nio: U32
  for +need: U32
  for +d: Nat
  for +BIG: U32
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcap: {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(d))) == True{} : Bool}
  for +hn: {U32.is_lt(need, 2147483648) == True{} : Bool}
  for +hun: {Cmp.is_le(Nat.cmp(V.U.N(N.io.bytes(nio)), V.U.N(need))) == True{} : Bool}
  for +hb: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, EM_.GR.t(t, N.io.bytes(nio), need), 0) == SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0) : Bool}

def SC.oks_grow(ts, tt, slen, w0, w1, t, nio, need, d, BIG, hd, hcap, hn, hun, hb, hB):
  SC.oks_keep(V.U.N(nio), ts, tt, slen, w0, w1, t, EM_.GR.t(t, N.io.bytes(nio), need), N.io.bytes(nio), 0, nio, d, BIG,
    S.S.sl_has(V.U.N(N.io.bytes(nio)), EM_.GR.t(t, N.io.bytes(nio), need), 0, t, 0, EM_.GR.keep(t, N.io.bytes(nio), need, S.S.sl(V.U.N(N.io.bytes(nio)), t, 0), hn, S.S.len_sl(V.U.N(N.io.bytes(nio)), t, 0), hun, EM_.EM.has_sl(V.U.N(N.io.bytes(nio)), t, 0))),
    hd, hcap, C.CP.le_refl(V.U.N(nio)), SC.bytesB(nio, BIG, hb, hB),
    (%Equal.sym(Nat, V.U.N(N.io.bytes(nio)), Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), SC.bytesB(nio, BIG, hb, hB)) : {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}; hb), hB)

law SC.kv.uo:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {U32.is_eq(EM_.EM.uo(e), w0) == True{} : Bool}

def SC.kv.uo(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h)

law SC.kv.cpl:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {U32.is_eq(cpl, slen) == True{} : Bool}

def SC.kv.cpl(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h))

law SC.kv.w01:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {U32.is_le(w0, w1) == True{} : Bool}

def SC.kv.w01(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h)))

law SC.kv.sE:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))) == True{} : Bool}

def SC.kv.sE(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))), P.Bool.and_r(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h))))

law SC.kv.wE:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))) == True{} : Bool}

def SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))), P.Bool.and_r(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h)))))

law SC.kv.swE:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))) == True{} : Bool}

def SC.kv.swE(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))), P.Bool.and_r(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h))))))

law SC.kv.big:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}

def SC.kv.big(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))), P.Bool.and_r(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h)))))))

law SC.kv.B:
  for +e: EM_.ET
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +E: U32
  for +BIG: U32
  for +h: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  {U32.is_lt(BIG, 2147483648) == True{} : Bool}

def SC.kv.B(e, slen, w0, w1, cpl, E, BIG, h):
  P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))), P.Bool.and_r(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))), P.Bool.and_r(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648)))))), P.Bool.and_r(U32.is_eq(EM_.EM.uo(e), w0), Bool.and(U32.is_eq(cpl, slen), Bool.and(U32.is_le(w0, w1), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))), Bool.and(Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))), U32.is_lt(BIG, 2147483648))))))), h)))))))

law SC.ltc:
  for +c: Cmp
  for +h: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}

def SC.ltc(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      P.Bool.false_true({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      P.Bool.false_true({GT{} == LT{} : Cmp}, h)

law SC.undd:
  for +a: Nat
  for +b: Nat
  for +h: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(a)), Nat.double(Nat.double(b)))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}

def SC.undd(a, b, h):
  (%P.Nat.half_double(a) : {Cmp.is_le(Nat.cmp(_, b)) == True{} : Bool};
    (%P.Nat.half_double(b) : {Cmp.is_le(Nat.cmp(P.Nat.half(Nat.double(a)), _)) == True{} : Bool};
      P.Nat.half_mono(Nat.double(a), Nat.double(b),
        (%P.Nat.half_double(Nat.double(a)) : {Cmp.is_le(Nat.cmp(_, Nat.double(b))) == True{} : Bool};
          (%P.Nat.half_double(Nat.double(b)) : {Cmp.is_le(Nat.cmp(P.Nat.half(Nat.double(Nat.double(a))), _)) == True{} : Bool};
            P.Nat.half_mono(Nat.double(Nat.double(a)), Nat.double(Nat.double(b)), h))))))

# A match, against the window.
def SC.okK(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +en: N.Ent) -> Bool:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      SG_.SG.ok0(ts, tt, slen, w0, w1, en)

# Adding the match at nio.
law SC.put_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +t: A.Tr
  for +d: Nat
  for +p: U32
  for +mm: U32
  for +nio: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +hpf: {A.T.pf(d, t) == True{} : Bool}
  for +hd: {Nat.cmp(d, 32n) == LT{} : Cmp}
  for +hcn: {Cmp.is_le(Nat.cmp(Nat.add(SG_.SG.tri(V.U.N(nio)), 3n), P.Nat.pow2(d))) == True{} : Bool}
  for +hok0: {SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0) == True{} : Bool}
  for +hok: {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)}) == True{} : Bool}
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(V.U.N(p), 0n))) == True{} : Bool}
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  for +hm: {U32.is_le(4, mm) == True{} : Bool}
  for +hs: {V.U.N(U32.add(nio, 1)) == 1n+V.U.N(nio) : Nat}
  {SC.Iv(ts, tt, slen, w0, w1, 1n, SG_.SG.put(t, nio, pos, len, val), p, mm, U32.add(nio, 1)) == True{} : Bool}

def SC.put_inv(ts, tt, slen, w0, w1, t, d, p, mm, nio, pos, len, val, hpf, hd, hcn, hok0, hok, hn, hw, hm, hs):
  SC.Iv.mk(ts, tt, slen, w0, w1, 1n, SG_.SG.put(t, nio, pos, len, val), p, mm, U32.add(nio, 1),
    (%Equal.sym(Nat, V.U.N(U32.add(nio, 1)), 1n+V.U.N(nio), hs) : {SG_.SG.oks0(_, ts, tt, slen, w0, w1, SG_.SG.put(t, nio, pos, len, val), 0) == True{} : Bool};
      SC.oks_snoc(V.U.N(nio), ts, tt, slen, w0, w1, SG_.SG.put(t, nio, pos, len, val), 0, nio, Equal.sym(Nat, Nat.add(V.U.N(nio), 0n), V.U.N(nio), P.Nat.add_zero_r(V.U.N(nio))),
        (%Equal.sym(Bool, SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, SG_.SG.put(t, nio, pos, len, val), 0), SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, t, 0), SC.oks_put(V.U.N(nio), ts, tt, slen, w0, w1, nio, pos, len, val, t, 0, d, hpf, hd, hcn, C.CP.le_refl(V.U.N(nio)))) : {_ == True{} : Bool};
          hok0),
        (%Equal.sym(N.Ent, SE_.SE.ent(SG_.SG.put(t, nio, pos, len, val), nio), N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)}, SG_.SG.get_same(t, nio, pos, len, val, d, hpf, hd, hcn)) : {SG_.SG.ok0(ts, tt, slen, w0, w1, _) == True{} : Bool};
          hok))),
    (%Equal.sym(Nat, SC.dep(SG_.SG.put(t, nio, pos, len, val)), d, SC.dep_pf(d, SG_.SG.put(t, nio, pos, len, val), SG_.SG.pf_put(t, nio, pos, len, val, d, hpf))) : {A.T.pf(_, SG_.SG.put(t, nio, pos, len, val)) == True{} : Bool};
      SG_.SG.pf_put(t, nio, pos, len, val, d, hpf)),
    (%Equal.sym(Nat, SC.dep(SG_.SG.put(t, nio, pos, len, val)), d, SC.dep_pf(d, SG_.SG.put(t, nio, pos, len, val), SG_.SG.pf_put(t, nio, pos, len, val, d, hpf))) : {Nat.cmp(_, 32n) == LT{} : Cmp};
      hd),
    (%Equal.sym(Nat, SC.dep(SG_.SG.put(t, nio, pos, len, val)), d, SC.dep_pf(d, SG_.SG.put(t, nio, pos, len, val), SG_.SG.pf_put(t, nio, pos, len, val, d, hpf))) : {Cmp.is_le(Nat.cmp(SG_.SG.tri(V.U.N(U32.add(nio, 1))), P.Nat.pow2(_))) == True{} : Bool};
      (%Equal.sym(Nat, V.U.N(U32.add(nio, 1)), 1n+V.U.N(nio), hs) : {Cmp.is_le(Nat.cmp(SG_.SG.tri(_), P.Nat.pow2(d))) == True{} : Bool};
        (%P.Nat.add_comm(SG_.SG.tri(V.U.N(nio)), 3n) : {Cmp.is_le(Nat.cmp(_, P.Nat.pow2(d))) == True{} : Bool};
          hcn))),
    (%Equal.sym(Nat, V.U.N(U32.add(nio, 1)), 1n+V.U.N(nio), hs) : {Cmp.is_le(Nat.cmp(_, Nat.add(V.U.N(p), 1n))) == True{} : Bool};
      (%Equal.sym(Nat, Nat.add(V.U.N(p), 1n), 1n+Nat.add(V.U.N(p), 0n), P.Nat.add_succ_r(V.U.N(p), 0n)) : {Cmp.is_le(Nat.cmp(1n+V.U.N(nio), _)) == True{} : Bool};
        hn)),
    hw, hm)

law SC.nlt.c:
  for +c: Cmp
  for +h: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_lt(P.Cmp.flip(c)) == False{} : Bool}

def SC.nlt.c(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      P.Bool.false_true({Cmp.is_lt(P.Cmp.flip(GT{})) == False{} : Bool}, h)

law SC.nlt:
  for +a: U32
  for +b: U32
  for +h: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_lt(b, a) == False{} : Bool}

def SC.nlt(a, b, h):
  %Equal.sym(Cmp, U32.cmp(b, a), Nat.cmp(V.U.N(b), V.U.N(a)), V.U.cmp_nat(b, a)) :
    {Cmp.is_lt(_) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(V.U.N(b), V.U.N(a)), P.Cmp.flip(Nat.cmp(V.U.N(a), V.U.N(b))), P.Nat.cmp_swap(V.U.N(a), V.U.N(b))) :
    {Cmp.is_lt(_) == False{} : Bool}
  SC.nlt.c(Nat.cmp(V.U.N(a), V.U.N(b)), (%V.U.cmp_nat(a, b) : {Cmp.is_le(_) == True{} : Bool}; h))

law SC.sub0:
  for +x: U32
  {U32.sub(x, 0) == x : U32}

def SC.sub0(x):
  %V.U.add_zero_r(U32.sub(x, 0)) :
    {_ == x : U32}
  V.U.add_sub(x, 0)

law SC.pick_same:
  for +b: Bool
  for +v: U32
  {N.u32.pick(b, v, v) == v : U32}

def SC.pick_same(b, v):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def SC.w0(+K: N.SK) -> U32:
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      w0

# More room in the count: s = 1 after a push.
law SC.Is_up:
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +st: ST
  for +h: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  {SC.Is(K, ts, tt, 1n, st) == True{} : Bool}

def SC.Is_up(K, ts, tt, st, h):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.Iv.mk(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h), SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h)), SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h),
        P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), Nat.add(V.U.N(p), 1n), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(p), 0n), Nat.add(V.U.N(p), 1n)), Nat.cmp(0n, 1n), P.Nat.cmp_add_l(V.U.N(p), 0n, 1n)) : {Cmp.is_le(_) == True{} : Bool}; {==})),
        SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h), SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, h))

# The bytes of nio + 1 matches.
law SC.needN:
  for +nio: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(nio), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {V.U.N(N.io.bytes(U32.add(nio, 1))) == Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))) : Nat}

def SC.needN(nio, w1, BIG, hn, hk, hB):
  %Equal.sym(Nat, V.U.N(N.io.bytes(U32.add(nio, 1))), Nat.double(Nat.double(SG_.SG.tri(V.U.N(U32.add(nio, 1))))), SC.bytesB(U32.add(nio, 1), BIG, (%Equal.sym(Nat, V.U.N(U32.add(nio, 1)), 1n+V.U.N(nio), SC.Bs(nio, w1, BIG, hn, hk)) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(_))), V.U.N(BIG))) == True{} : Bool}; SC.B2(nio, w1, BIG, hn, hk)), hB)) :
    {_ == Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))) : Nat}
  %Equal.sym(Nat, V.U.N(U32.add(nio, 1)), 1n+V.U.N(nio), SC.Bs(nio, w1, BIG, hn, hk)) :
    {Nat.double(Nat.double(SG_.SG.tri(_))) == Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))) : Nat}
  {==}

law SC.usedN:
  for +nio: U32
  for +w1: U32
  for +BIG: U32
  for +hn: {Cmp.is_le(Nat.cmp(V.U.N(nio), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), V.U.N(BIG))) == True{} : Bool}

law SC.ddtri:
  for +n: Nat
  {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(n))), Nat.double(Nat.double(SG_.SG.tri(1n+n))))) == True{} : Bool}

def SC.ddtri(n):
  P.Nat.double_mono(Nat.double(SG_.SG.tri(n)), Nat.double(SG_.SG.tri(1n+n)), P.Nat.double_mono(SG_.SG.tri(n), SG_.SG.tri(1n+n), SG_.SG.tri_mono(n, 1n+n, P.Nat.lt_to_le(n, 1n+n, SC.lt_add1(0n, n)))))

def SC.usedN(nio, w1, BIG, hn, hk):
  P.Nat.le_trans(Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))), V.U.N(BIG), SC.ddtri(V.U.N(nio)), SC.B2(nio, w1, BIG, hn, hk))

law SC.push.go_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +full: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hok: {SC.okK(K, ts, tt, N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)}) == True{} : Bool}
  for +hfe: {SC.full(st) == full : Bool}
  {SC.Is(K, ts, tt, 1n, SC.push.go(full, pos, len, val, st)) == True{} : Bool}

def SC.push.go_inv(ts, tt, e, K, E, BIG, full, pos, len, val, st, hk, hI, hp, hok, hfe):
  match K full st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.put_inv(ts, tt, slen, w0, w1, tio, SC.dep(tio), p, mm, nio, pos, len, val, SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.room(nio, tio, SC.dep(tio), BIG, SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), hfe, SC.B3(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk)), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)), SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), hok, SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Bs(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk)))
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.put_inv(ts, tt, slen, w0, w1, EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), EM_.GR.d(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio)), p, mm, nio, pos, len, val, EM_.GR.pf(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio), SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), EM_.GR.lt(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI))), (%P.Nat.add_comm(3n, SG_.SG.tri(V.U.N(nio))) : {Cmp.is_le(Nat.cmp(_, P.Nat.pow2(EM_.GR.d(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio))))) == True{} : Bool}; SC.undd(SG_.SG.tri(1n+V.U.N(nio)), P.Nat.pow2(EM_.GR.d(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio))), (%SC.needN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)) : {Cmp.is_le(Nat.cmp(_, Nat.double(Nat.double(P.Nat.pow2(EM_.GR.d(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio))))))) == True{} : Bool}; EM_.GR.cap(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1)), SC.dep(tio), SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), EM_.EM.lt31(N.io.bytes(U32.add(nio, 1)), BIG, (%Equal.sym(Nat, V.U.N(N.io.bytes(U32.add(nio, 1))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))), SC.needN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}; SC.B2(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk))), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)))))), (%Equal.sym(Bool, SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, EM_.GR.t(tio, N.io.bytes(nio), N.io.bytes(U32.add(nio, 1))), 0), SG_.SG.oks0(V.U.N(nio), ts, tt, slen, w0, w1, tio, 0), SC.oks_grow(ts, tt, slen, w0, w1, tio, nio, N.io.bytes(U32.add(nio, 1)), SC.dep(tio), BIG, SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), EM_.EM.lt31(N.io.bytes(U32.add(nio, 1)), BIG, (%Equal.sym(Nat, V.U.N(N.io.bytes(U32.add(nio, 1))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))), SC.needN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(_, V.U.N(BIG))) == True{} : Bool}; SC.B2(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk))), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)), (%Equal.sym(Nat, V.U.N(N.io.bytes(nio)), Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), SC.bytesB(nio, BIG, SC.usedN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk)), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(_, V.U.N(N.io.bytes(U32.add(nio, 1))))) == True{} : Bool}; (%Equal.sym(Nat, V.U.N(N.io.bytes(U32.add(nio, 1))), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(nio)))), SC.needN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(V.U.N(nio)))), _)) == True{} : Bool}; SC.ddtri(V.U.N(nio)))), SC.usedN(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk)), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))) : {_ == True{} : Bool}; SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), hok, SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Bs(nio, w1, BIG, P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 0n), V.U.N(w1), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), (%Equal.sym(Nat, Nat.add(V.U.N(p), 0n), V.U.N(p), P.Nat.add_zero_r(V.U.N(p))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; V.U.le_N(p, w1, hp))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk)))

law SC.push.if_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hok: {SC.okK(K, ts, tt, N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)}) == True{} : Bool}
  {SC.Is(K, ts, tt, 1n, SC.push.if(z, pos, len, val, st)) == True{} : Bool}

def SC.push.if_inv(ts, tt, e, K, E, BIG, z, pos, len, val, st, hk, hI, hp, hok):
  match z:
    case True{}:
      SC.push.go_inv(ts, tt, e, K, E, BIG, SC.full(st), pos, len, val, st, hk, hI, hp, hok, {==})
    case False{}:
      SC.Is_up(K, ts, tt, st, hI)

# A push of a match that holds, at or after w0.
law SC.push_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  for +hw: {U32.is_le(SC.w0(K), pos) == True{} : Bool}
  for +hok: {SC.okK(K, ts, tt, N.Ent{pos, U32.and(len, 2147483647), val, N.ent.run(len)}) == True{} : Bool}
  {SC.Is(K, ts, tt, 1n, SC.push(e, pos, len, val, st)) == True{} : Bool}

def SC.push_inv(ts, tt, e, K, E, BIG, pos, len, val, st, hk, hI, hp, hw, hok):
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      %Equal.sym(U32, EM_.EM.uo(e), w0, V.U.is_eq(EM_.EM.uo(e), w0, SC.kv.uo(e, slen, w0, w1, cpl, E, BIG, hk))) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(N.u32.pick(U32.is_lt(pos, _), U32.sub(_, pos), 0), 4), U32.and(len, 2147483647)), U32.add(pos, N.u32.pick(U32.is_lt(pos, _), U32.sub(_, pos), 0)), U32.sub(len, N.u32.pick(U32.is_lt(pos, _), U32.sub(_, pos), 0)), N.u32.pick(N.ent.run(len), val, U32.add(val, N.u32.pick(U32.is_lt(pos, _), U32.sub(_, pos), 0))), st)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(pos, w0), False{}, SC.nlt(w0, pos, hw)) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(N.u32.pick(_, U32.sub(w0, pos), 0), 4), U32.and(len, 2147483647)), U32.add(pos, N.u32.pick(_, U32.sub(w0, pos), 0)), U32.sub(len, N.u32.pick(_, U32.sub(w0, pos), 0)), N.u32.pick(N.ent.run(len), val, U32.add(val, N.u32.pick(_, U32.sub(w0, pos), 0))), st)) == True{} : Bool}
      %Equal.sym(U32, U32.add(pos, 0), pos, V.U.add_zero_r(pos)) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(0, 4), U32.and(len, 2147483647)), _, U32.sub(len, 0), N.u32.pick(N.ent.run(len), val, U32.add(val, 0)), st)) == True{} : Bool}
      %Equal.sym(U32, U32.sub(len, 0), len, SC.sub0(len)) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(0, 4), U32.and(len, 2147483647)), pos, _, N.u32.pick(N.ent.run(len), val, U32.add(val, 0)), st)) == True{} : Bool}
      %Equal.sym(U32, U32.add(val, 0), val, V.U.add_zero_r(val)) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(0, 4), U32.and(len, 2147483647)), pos, len, N.u32.pick(N.ent.run(len), val, _), st)) == True{} : Bool}
      %Equal.sym(U32, N.u32.pick(N.ent.run(len), val, val), val, SC.pick_same(N.ent.run(len), val)) :
        {SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, SC.push.if(U32.is_le(U32.add(0, 4), U32.and(len, 2147483647)), pos, len, _, st)) == True{} : Bool}
      SC.push.if_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, U32.is_le(U32.add(0, 4), U32.and(len, 2147483647)), pos, len, val, st, hk, hI, hp, hok)

# Erasing
# -------

law SC.erl_f:
  for +k: Nat
  for +pos: U32
  for +n: U32
  for +tio: A.Tr
  {SC.erl(k, pos, False{}, n, tio) == n : U32}

def SC.erl_f(k, pos, n, tio):
  match k:
    case 0n:
      {==}
    case 1n+q:
      {==}

law SC.dec_le:
  for +n: U32
  for +hn: {U32.is_lt(0, n) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(n, 1)), V.U.N(n))) == True{} : Bool}

def SC.dec_le(n, hn):
  (%V.U.sub_nat(n, 1, V.U.lt_succ_le(0, n, hn)) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(n, 1)), _)) == True{} : Bool};
    P.Nat.cmp_add_r(V.U.N(U32.sub(n, 1)), 1n))

law SC.dec_lt.go:
  for +n: U32
  for +c: Bool
  for +ec: {U32.is_lt(1, n) == c : Bool}
  {Bool.or(Bool.not(c), U32.is_lt(0, U32.sub(n, 1))) == True{} : Bool}

def SC.dec_lt.go(n, c, ec):
  match c:
    case False{}:
      {==}
    case True{}:
      V.U.N_lt(0, U32.sub(n, 1),
        (%P.Nat.add_comm(V.U.N(U32.sub(n, 1)), 1n) : {Nat.cmp(1n, _) == LT{} : Cmp};
          (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(n, 1)), V.U.N(1)), V.U.N(n), V.U.sub_nat(n, 1, V.U.lt_to_le(1, n, ec))) : {Nat.cmp(1n, _) == LT{} : Cmp};
            V.U.lt_N(1, n, ec))))

law SC.dec_lt:
  for +n: U32
  {Bool.or(Bool.not(U32.is_lt(1, n)), U32.is_lt(0, U32.sub(n, 1))) == True{} : Bool}

def SC.dec_lt(n):
  SC.dec_lt.go(n, U32.is_lt(1, n), {==})

law SC.erl_le:
  for +k: Nat
  for +pos: U32
  for +h: Bool
  for +n: U32
  for +tio: A.Tr
  for +hn: {Bool.or(Bool.not(h), U32.is_lt(0, n)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(SC.erl(k, pos, h, n, tio)), V.U.N(n))) == True{} : Bool}

law SC.erl_le.k:
  for +q: Nat
  for +pos: U32
  for +d: Bool
  for +n: U32
  for +tio: A.Tr
  for +hn: {U32.is_lt(0, n) == True{} : Bool}
  for +ih: {Cmp.is_le(Nat.cmp(V.U.N(SC.erl(q, pos, U32.is_lt(1, n), U32.sub(n, 1), tio)), V.U.N(U32.sub(n, 1)))) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(SC.erl(q, pos, Bool.and(d, U32.is_lt(1, n)), N.u32.pick(d, U32.sub(n, 1), n), tio)), V.U.N(n))) == True{} : Bool}

def SC.erl_le.k(q, pos, d, n, tio, hn, ih):
  match d:
    case True{}:
      P.Nat.le_trans(V.U.N(SC.erl(q, pos, U32.is_lt(1, n), U32.sub(n, 1), tio)), V.U.N(U32.sub(n, 1)), V.U.N(n), ih, SC.dec_le(n, hn))
    case False{}:
      (%Equal.sym(U32, SC.erl(q, pos, False{}, n, tio), n, SC.erl_f(q, pos, n, tio)) : {Cmp.is_le(Nat.cmp(V.U.N(_), V.U.N(n))) == True{} : Bool};
        C.CP.le_refl(V.U.N(n)))

def SC.erl_le(k, pos, h, n, tio, hn):
  match k h:
    case 0n b:
      C.CP.le_refl(V.U.N(n))
    case 1n+q False{}:
      C.CP.le_refl(V.U.N(n))
    case 1n+q True{}:
      SC.erl_le.k(q, pos, U32.is_ge(A.T.word(tio, N.io.at(U32.sub(n, 1))), pos), n, tio, hn, SC.erl_le(q, pos, U32.is_lt(1, n), U32.sub(n, 1), tio, SC.dec_lt(n)))

law SC.orn:
  for +b: Bool
  {Bool.or(Bool.not(b), b) == True{} : Bool}

def SC.orn(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law SC.erase_inv:
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: Nat
  for +pos: U32
  for +st: ST
  for +hI: {SC.Is(K, ts, tt, s, st) == True{} : Bool}
  {SC.Is(K, ts, tt, s, SC.erase(pos, st)) == True{} : Bool}

def SC.erase_inv(K, ts, tt, s, pos, st, hI):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.Iv.mk(ts, tt, slen, w0, w1, s, tio, p, mm, SC.erl(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio),
        SC.oks_pre(V.U.N(SC.erl(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio)), V.U.N(nio), ts, tt, slen, w0, w1, tio, 0, SC.erl_le(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio, SC.orn(U32.is_lt(0, nio))), SC.Iv.ok(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI)),
        SC.Iv.pf(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI),
        SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI)),
        P.Nat.le_trans(SG_.SG.tri(V.U.N(SC.erl(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio))), SG_.SG.tri(V.U.N(nio)), P.Nat.pow2(SC.dep(tio)), SG_.SG.tri_mono(V.U.N(SC.erl(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio)), V.U.N(nio), SC.erl_le(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio, SC.orn(U32.is_lt(0, nio)))), SC.Iv.cap(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI)),
        P.Nat.le_trans(V.U.N(SC.erl(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio)), V.U.N(nio), Nat.add(V.U.N(p), s), SC.erl_le(V.U.N(nio), pos, U32.is_lt(0, nio), nio, tio, SC.orn(U32.is_lt(0, nio))), SC.Iv.n(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI)),
        SC.Iv.w0(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI), SC.Iv.mm(ts, tt, slen, w0, w1, s, tio, p, mm, nio, hI))

law SC.erase.if_inv:
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: Nat
  for +z: Bool
  for +pos: U32
  for +st: ST
  for +hI: {SC.Is(K, ts, tt, s, st) == True{} : Bool}
  {SC.Is(K, ts, tt, s, SC.erase.if(z, pos, st)) == True{} : Bool}

def SC.erase.if_inv(K, ts, tt, s, z, pos, st, hI):
  match z:
    case True{}:
      SC.erase_inv(K, ts, tt, s, pos, st, hI)
    case False{}:
      hI

law SC.cont_inv:
  for +K: N.SK
  for +ts: A.Tr
  for +tt: A.Tr
  for +s: Nat
  for +end: U32
  for +at: U32
  for +st: ST
  for +hI: {SC.Is(K, ts, tt, s, st) == True{} : Bool}
  {SC.Is(K, ts, tt, s, SC.cont(K, end, at, st)) == True{} : Bool}

def SC.cont_inv(K, ts, tt, s, end, at, st, hI):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      hI

# Buffering, erasing and noting the continuation leave p.
law SC.pp_go:
  for +full: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {SC.pp(SC.push.go(full, pos, len, val, st)) == SC.pp(st) : U32}

def SC.pp_go(full, pos, len, val, st):
  match full st:
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law SC.pp_if:
  for +z: Bool
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {SC.pp(SC.push.if(z, pos, len, val, st)) == SC.pp(st) : U32}

def SC.pp_if(z, pos, len, val, st):
  match z:
    case True{}:
      SC.pp_go(SC.full(st), pos, len, val, st)
    case False{}:
      {==}

law SC.pp_push:
  for +e: EM_.ET
  for +pos: U32
  for +len: U32
  for +val: U32
  for +st: ST
  {SC.pp(SC.push(e, pos, len, val, st)) == SC.pp(st) : U32}

def SC.pp_push(e, pos, len, val, st):
  SC.pp_if(U32.is_le(U32.add(N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0), 4), U32.and(len, 2147483647)), U32.add(pos, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), U32.sub(len, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0)), N.u32.pick(N.ent.run(len), val, U32.add(val, N.u32.pick(U32.is_lt(pos, EM_.EM.uo(e)), U32.sub(EM_.EM.uo(e), pos), 0))), st)

law SC.pp_erase:
  for +z: Bool
  for +pos: U32
  for +st: ST
  {SC.pp(SC.erase.if(z, pos, st)) == SC.pp(st) : U32}

def SC.pp_erase(z, pos, st):
  match z st:
    case True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}
    case False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

law SC.pp_cont:
  for +K: N.SK
  for +end: U32
  for +at: U32
  for +st: ST
  {SC.pp(SC.cont(K, end, at, st)) == SC.pp(st) : U32}

def SC.pp_cont(K, end, at, st):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      {==}

# The scan's loop invariant: the state holds, and the scan goes on only
# with 4 bytes to go at least.
def SC.room4(+K: N.SK, +st: ST) -> Bool:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), 4n), V.U.N(w1)))

def SC.LI(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +r: R1) -> Bool:
  match r:
    case R1{g, st}:
      Bool.and(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(g), SC.room4(K, st)))

# Moving on keeps the invariant
# -----------------------------

law SC.and_tt:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def SC.and_tt(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) :
    {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) :
    {Bool.and(True{}, _) == True{} : Bool}
  {==}

law SC.lt_addk:
  for +a: Nat
  for +k: Nat
  {Nat.cmp(a, Nat.add(a, 1n+k)) == LT{} : Cmp}

def SC.lt_addk(a, k):
  %Equal.sym(Nat, Nat.add(a, 1n+k), Nat.add(1n+k, a), P.Nat.add_comm(a, 1n+k)) :
    {Nat.cmp(a, _) == LT{} : Cmp}
  SC.lt_add1(k, a)

# p + 1 does not wrap, for p at most w1.
law SC.p1:
  for +p: U32
  for +w1: U32
  for +E: U32
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(p, 1)) == 1n+V.U.N(p) : Nat}

def SC.p1(p, w1, E, hp, hE):
  V.U.succ_N(p, E, P.Nat.le_lt_trans(V.U.N(p), V.U.N(w1), V.U.N(E), V.U.le_N(p, w1, hp), P.Nat.lt_le_trans(V.U.N(w1), Nat.add(V.U.N(w1), 9n), V.U.N(E), SC.lt_addk(V.U.N(w1), 8n), hE)))

# p + k does not wrap, for p at most w1 and k at most 9.
law SC.pk:
  for +p: U32
  for +w1: U32
  for +E: U32
  for +k: U32
  for +hk: {Cmp.is_le(Nat.cmp(V.U.N(k), 9n)) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))) == True{} : Bool}
  {V.U.N(U32.add(p, k)) == Nat.add(V.U.N(p), V.U.N(k)) : Nat}

def SC.pk(p, w1, E, k, hk, hp, hE):
  V.U.add_N(p, k, E, P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(k)), Nat.add(V.U.N(w1), 9n), V.U.N(E), MT_.MT.add_le(V.U.N(p), V.U.N(w1), V.U.N(k), 9n, V.U.le_N(p, w1, hp), hk), hE))

law SC.upd_room:
  for +p: U32
  for +w1: U32
  for +E: U32
  for +c: Bool
  for +ec: {U32.is_le(U32.add(p, 5), w1) == c : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))) == True{} : Bool}
  {Bool.or(Bool.not(c), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(p, 1)), 4n), V.U.N(w1)))) == True{} : Bool}

def SC.upd_room(p, w1, E, c, ec, hp, hE):
  match c:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Nat, V.U.N(U32.add(p, 1)), 1n+V.U.N(p), SC.p1(p, w1, E, hp, hE)) :
        {Bool.or(Bool.not(True{}), Cmp.is_le(Nat.cmp(Nat.add(_, 4n), V.U.N(w1)))) == True{} : Bool}
      %P.Nat.add_succ_r(V.U.N(p), 4n) :
        {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}
      (%SC.pk(p, w1, E, 5, {==}, hp, hE) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool};
        V.U.le_N(U32.add(p, 5), w1, ec))

law SC.rs_room:
  for +p: U32
  for +w1: U32
  for +E: U32
  for +c: Bool
  for +ec: {U32.is_le(U32.add(p, 4), w1) == c : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 9n), V.U.N(E))) == True{} : Bool}
  {Bool.or(Bool.not(c), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), 4n), V.U.N(w1)))) == True{} : Bool}

def SC.rs_room(p, w1, E, c, ec, hp, hE):
  match c:
    case False{}:
      {==}
    case True{}:
      (%SC.pk(p, w1, E, 4, {==}, hp, hE) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool};
        V.U.le_N(U32.add(p, 4), w1, ec))

law SC.max4.go:
  for +x: U32
  for +c: Bool
  for +ec: {U32.is_lt(4, x) == c : Bool}
  {U32.is_le(4, N.u32.pick(c, x, 4)) == True{} : Bool}

def SC.max4.go(x, c, ec):
  match c:
    case True{}:
      V.U.lt_to_le(4, x, ec)
    case False{}:
      {==}

law SC.mm4:
  for +c: Bool
  for +x: U32
  {U32.is_le(4, N.u32.pick(c, N.u32.max(4, x), 4)) == True{} : Bool}

def SC.mm4(c, x):
  match c:
    case True{}:
      SC.max4.go(x, U32.is_lt(4, x), {==})
    case False{}:
      {==}

law SC.mmdec.go:
  for +mm: U32
  for +c: Bool
  for +ec: {U32.is_lt(4, mm) == c : Bool}
  for +h: {U32.is_le(4, mm) == True{} : Bool}
  {U32.is_le(4, N.u32.pick(c, U32.sub(mm, 1), mm)) == True{} : Bool}

def SC.mmdec.go(mm, c, ec, h):
  match c:
    case True{}:
      V.U.N_le(4, U32.sub(mm, 1), P.Nat.lt_succ_le(4n, V.U.N(U32.sub(mm, 1)),
        (%P.Nat.add_comm(V.U.N(U32.sub(mm, 1)), 1n) : {Nat.cmp(4n, _) == LT{} : Cmp};
          (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(mm, 1)), V.U.N(1)), V.U.N(mm), V.U.sub_nat(mm, 1, V.U.lt_to_le(1, mm, V.U.le_lt_trans(1, 4, mm, {==}, ec)))) : {Nat.cmp(4n, _) == LT{} : Cmp};
            V.U.lt_N(4, mm, ec)))))
    case False{}:
      h

law SC.update_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 1n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.update(K, tt, st)) == True{} : Bool}

def SC.update_inv(ts, tt, e, K, E, BIG, st, hk, hI, hp):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Iv(ts, tt, slen, w0, w1, 0n, tio, U32.add(p, 1), mm, nio), Bool.or(Bool.not(U32.is_le(U32.add(p, 5), w1)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(p, 1)), 4n), V.U.N(w1)))),
        SC.Iv.mk(ts, tt, slen, w0, w1, 0n, tio, U32.add(p, 1), mm, nio, SC.Iv.ok(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.Iv.pf(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI),
        (%Equal.sym(Nat, V.U.N(U32.add(p, 1)), 1n+V.U.N(p), SC.p1(p, w1, E, hp, SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(_, 0n))) == True{} : Bool};
          (%P.Nat.add_succ_r(V.U.N(p), 0n) : {Cmp.is_le(Nat.cmp(V.U.N(nio), _)) == True{} : Bool};
            SC.Iv.n(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI))),
        V.U.N_le(w0, U32.add(p, 1), (%Equal.sym(Nat, V.U.N(U32.add(p, 1)), 1n+V.U.N(p), SC.p1(p, w1, E, hp, SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk))) : {Cmp.is_le(Nat.cmp(V.U.N(w0), _)) == True{} : Bool};
          P.Nat.le_trans(V.U.N(w0), V.U.N(p), 1n+V.U.N(p), V.U.le_N(w0, p, SC.Iv.w0(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)), P.Nat.lt_to_le(V.U.N(p), 1n+V.U.N(p), SC.lt_add1(0n, V.U.N(p)))))),
        SC.Iv.mm(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)),
        SC.upd_room(p, w1, E, U32.is_le(U32.add(p, 5), w1), {==}, hp, SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk)))

law SC.restart_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hp: {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.restart(K, tt, st)) == True{} : Bool}

law SC.lazy.go_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +L: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 1n, st) == True{} : Bool}
  for +hpL: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.pp(st)), V.U.N(L)), V.U.N(SC.w1(K)))) == True{} : Bool}
  for +hL: {U32.is_le(4, L) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.lazy.go(z, K, tt, L, st)) == True{} : Bool}

law SC.lazy_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +L: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 1n, st) == True{} : Bool}
  for +hpL: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.pp(st)), V.U.N(L)), V.U.N(SC.w1(K)))) == True{} : Bool}
  for +hL: {U32.is_le(4, L) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.lazy(K, tt, L, st)) == True{} : Bool}

law SC.next_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.next(K, tt, st)) == True{} : Bool}

# p is in the window when there are 4 bytes to go.
law SC.r4p:
  for +p: U32
  for +w1: U32
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), 4n), V.U.N(w1))) == True{} : Bool}
  {U32.is_le(p, w1) == True{} : Bool}

def SC.r4p(p, w1, hr):
  V.U.N_le(p, w1, P.Nat.le_trans(V.U.N(p), Nat.add(V.U.N(p), 4n), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(p), 4n), hr))

def SC.restart_inv(ts, tt, e, K, E, BIG, st, hk, hI, hp):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Iv(ts, tt, slen, w0, w1, 0n, tio, p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), nio), Bool.or(Bool.not(U32.is_le(U32.add(p, 4), w1)), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), 4n), V.U.N(w1)))),
        SC.Iv.mk(ts, tt, slen, w0, w1, 0n, tio, p, N.u32.pick(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), N.u32.max(4, U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p)), 4), nio, SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.mm4(U32.is_lt(p, N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0)), U32.sub(U32.add(N.u32.pick(U32.is_lt(0, nio), U32.add(A.T.word(tio, N.io.at(U32.sub(nio, 1))), U32.and(A.T.word(tio, U32.add(N.io.at(U32.sub(nio, 1)), 1)), 2147483647)), 0), 1), p))),
        SC.rs_room(p, w1, E, U32.is_le(U32.add(p, 4), w1), {==}, hp, SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk)))

def SC.lazy.go_inv(ts, tt, e, K, E, BIG, z, L, st, hk, hI, hpL, hL):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, ST{tl, tb, tv, tio, p, L, rc, rl, lck, last, nio, cont}, hk,
        SC.Iv.mk(ts, tt, slen, w0, w1, 1n, tio, p, L, nio, SC.Iv.ok(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.Iv.pf(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.Iv.n(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.Iv.w0(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), hL),
        V.U.N_le(p, w1, P.Nat.le_trans(V.U.N(p), Nat.add(V.U.N(p), V.U.N(L)), V.U.N(w1), P.Nat.cmp_add_r(V.U.N(p), V.U.N(L)), hpL)))
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.restart_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, ST{tl, tb, tv, tio, U32.add(p, L), mm, rc, rl, lck, last, nio, cont}, hk,
        SC.Iv.mk(ts, tt, slen, w0, w1, 0n, tio, U32.add(p, L), mm, nio, SC.Iv.ok(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.Iv.pf(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI),
          (%Equal.sym(Nat, V.U.N(U32.add(p, L)), Nat.add(V.U.N(p), V.U.N(L)), V.U.add_N(p, L, w1, hpL)) : {Cmp.is_le(Nat.cmp(V.U.N(nio), Nat.add(_, 0n))) == True{} : Bool};
            (%Equal.sym(Nat, Nat.add(Nat.add(V.U.N(p), V.U.N(L)), 0n), Nat.add(V.U.N(p), V.U.N(L)), P.Nat.add_zero_r(Nat.add(V.U.N(p), V.U.N(L)))) : {Cmp.is_le(Nat.cmp(V.U.N(nio), _)) == True{} : Bool};
              P.Nat.le_trans(V.U.N(nio), Nat.add(V.U.N(p), 1n), Nat.add(V.U.N(p), V.U.N(L)), SC.Iv.n(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI),
                (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(p), 1n), Nat.add(V.U.N(p), V.U.N(L))), Nat.cmp(1n, V.U.N(L)), P.Nat.cmp_add_l(V.U.N(p), 1n, V.U.N(L))) : {Cmp.is_le(_) == True{} : Bool};
                  P.Nat.le_trans(1n, 4n, V.U.N(L), {==}, V.U.le_N(4, L, hL)))))),
          V.U.N_le(w0, U32.add(p, L), (%Equal.sym(Nat, V.U.N(U32.add(p, L)), Nat.add(V.U.N(p), V.U.N(L)), V.U.add_N(p, L, w1, hpL)) : {Cmp.is_le(Nat.cmp(V.U.N(w0), _)) == True{} : Bool};
            P.Nat.le_trans(V.U.N(w0), V.U.N(p), Nat.add(V.U.N(p), V.U.N(L)), V.U.le_N(w0, p, SC.Iv.w0(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)), P.Nat.cmp_add_r(V.U.N(p), V.U.N(L))))),
          SC.Iv.mm(ts, tt, slen, w0, w1, 1n, tio, p, mm, nio, hI)),
        V.U.N_le(U32.add(p, L), w1, (%Equal.sym(Nat, V.U.N(U32.add(p, L)), Nat.add(V.U.N(p), V.U.N(L)), V.U.add_N(p, L, w1, hpL)) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; hpL)))

def SC.lazy_inv(ts, tt, e, K, E, BIG, L, st, hk, hI, hpL, hL):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy.go_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, Bool.and(U32.is_lt(L, 18), U32.is_le(U32.add(U32.add(p, L), 2), w1)), L, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, hpL, hL)

def SC.next_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.update_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, ST{tl, tb, tv, tio, p, N.u32.pick(U32.is_lt(4, mm), U32.sub(mm, 1), mm), rc, rl, lck, last, nio, cont}, hk,
        SC.Is_up(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, ST{tl, tb, tv, tio, p, N.u32.pick(U32.is_lt(4, mm), U32.sub(mm, 1), mm), rc, rl, lck, last, nio, cont},
          SC.Iv.mk(ts, tt, slen, w0, w1, 0n, tio, p, N.u32.pick(U32.is_lt(4, mm), U32.sub(mm, 1), mm), nio, SC.Iv.ok(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.pf(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.ltc(Nat.cmp(SC.dep(tio), 32n), SC.Iv.lt(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.Iv.cap(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.n(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.mmdec.go(mm, U32.is_lt(4, mm), {==}, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)))),
        SC.r4p(p, w1, hr))

# The phases keep the invariant
# -----------------------------

# A phase's result: taken, the step's invariant; else the state as it was.
def SC.LI2(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +r: R2) -> Bool:
  match r:
    case R2{True{}, q}:
      SC.LI(K, ts, tt, q)
    case R2{False{}, R1{c, st}}:
      Bool.and(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st))

def SC.rc(+st: ST) -> U32:
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      rc

law SC.or_r:
  for +a: Bool
  for +b: Bool
  for +hb: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def SC.or_r(a, b, hb):
  %Equal.sym(Bool, b, True{}, hb) :
    {Bool.or(a, _) == True{} : Bool}
  P.Bool.or_true(a)

law SC.hrm:
  for +n: Nat
  for +b: U32
  for +t: A.Tr
  for +i: U32
  {S.S.has(C.CP.rep(n, U32.and(b, 255)), t, i) == S.S.has(C.CP.rep(n, b), t, i) : Bool}

def SC.hrm(n, b, t, i):
  match n:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(U32, U32.and(U32.and(b, 255), 255), U32.and(b, 255), V.U.and_idem_r(b, 255)) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, i), _), S.S.has(C.CP.rep(q, U32.and(b, 255)), t, U32.add(i, 1))) == Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(b, 255)), S.S.has(C.CP.rep(q, b), t, U32.add(i, 1))) : Bool}
      %Equal.sym(Bool, S.S.has(C.CP.rep(q, U32.and(b, 255)), t, U32.add(i, 1)), S.S.has(C.CP.rep(q, b), t, U32.add(i, 1)), SC.hrm(q, b, t, U32.add(i, 1))) :
        {Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(b, 255)), _) == Bool.and(U32.is_eq(Y.BP.byt(t, i), U32.and(b, 255)), S.S.has(C.CP.rep(q, b), t, U32.add(i, 1))) : Bool}
      {==}

law SC.z48.go:
  for +a: Bool
  for +L: U32
  for +c: Bool
  for +ec: {U32.is_le(8, L) == c : Bool}
  {Bool.or(Bool.not(Bool.and(a, c)), U32.is_le(4, L)) == True{} : Bool}

def SC.z48.go(a, L, c, ec):
  match c:
    case True{}:
      SC.or_r(Bool.not(Bool.and(a, True{})), U32.is_le(4, L), V.U.N_le(4, L, P.Nat.le_trans(4n, 8n, V.U.N(L), {==}, V.U.le_N(8, L, ec))))
    case False{}:
      %Equal.sym(Bool, Bool.and(a, False{}), False{}, P.Bool.and_false(a)) :
        {Bool.or(Bool.not(_), U32.is_le(4, L)) == True{} : Bool}
      {==}

law SC.z48:
  for +a: Bool
  for +L: U32
  {Bool.or(Bool.not(Bool.and(a, U32.is_le(8, L))), U32.is_le(4, L)) == True{} : Bool}

def SC.z48(a, L):
  SC.z48.go(a, L, U32.is_le(8, L), {==})

law SC.or4:
  for +z: Bool
  for +L: U32
  for +hz: {Bool.or(Bool.not(z), U32.is_le(4, L)) == True{} : Bool}
  for +ez: {z == True{} : Bool}
  {U32.is_le(4, L) == True{} : Bool}

def SC.or4(z, L, hz, ez):
  (%ez : {Bool.or(Bool.not(_), U32.is_le(4, L)) == True{} : Bool}; hz)

# Below w1, so below 2^31.
law SC.w31:
  for +x: U32
  for +w1: U32
  for +BIG: U32
  for +hx: {Cmp.is_le(Nat.cmp(V.U.N(x), V.U.N(w1))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {U32.is_lt(x, 2147483648) == True{} : Bool}

def SC.w31(x, w1, BIG, hx, hk, hB):
  EM_.EM.lt31(x, BIG, P.Nat.le_trans(V.U.N(x), V.U.N(w1), V.U.N(BIG), hx,
    P.Nat.le_trans(V.U.N(w1), SG_.SG.tri(1n+V.U.N(w1)), V.U.N(BIG), P.Nat.le_trans(V.U.N(w1), 1n+V.U.N(w1), SG_.SG.tri(1n+V.U.N(w1)), P.Nat.lt_to_le(V.U.N(w1), 1n+V.U.N(w1), SC.lt_add1(0n, V.U.N(w1))), SC.le_tri(1n+V.U.N(w1))),
      P.Nat.le_trans(SG_.SG.tri(1n+V.U.N(w1)), Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG), SC.le_dd(SG_.SG.tri(1n+V.U.N(w1))), hk))), hB)

# A length below 2^31, masked, is itself.
law SC.m31:
  for +x: U32
  for +h: {U32.is_lt(x, 2147483648) == True{} : Bool}
  {U32.and(x, 2147483647) == x : U32}

def SC.m31(x, h):
  V.U.mask_id(x, 31n, {==}, h)

# A run of L bytes at p, from MT.same.
law SC.run_ok0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +p: U32
  for +rc: U32
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  for +h31: {U32.is_lt(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648) == True{} : Bool}
  {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648), 2147483647), rc, N.ent.run(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648))}) == True{} : Bool}

def SC.run_ok0(ts, tt, slen, w0, w1, E, p, rc, hw, hp, hE, h31):
  %Equal.sym(U32, U32.and(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648), 2147483647), U32.and(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483647), Z.BB.runl(SC.rlen(tt, p, rc, U32.sub(w1, p)))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, _, rc, N.ent.run(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648))}) == True{} : Bool}
  %Equal.sym(U32, U32.and(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483647), SC.rlen(tt, p, rc, U32.sub(w1, p)), SC.m31(SC.rlen(tt, p, rc, U32.sub(w1, p)), h31)) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, _, rc, N.ent.run(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648))}) == True{} : Bool}
  %Equal.sym(U32, U32.and(U32.or(SC.rlen(tt, p, rc, U32.sub(w1, p)), 2147483648), 2147483648), 2147483648, Z.BB.runf(SC.rlen(tt, p, rc, U32.sub(w1, p)))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, SC.rlen(tt, p, rc, U32.sub(w1, p)), rc, U32.is_ne(_, 0)}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, p), True{}, hw) :
    {Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), V.U.N(w1))), Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), S.S.has(C.CP.rep(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), rc), tt, p)))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), V.U.N(w1))), True{}, P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), V.U.N(w1), MT_.MT.add_le(V.U.N(p), V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), V.U.N(U32.sub(w1, p)), C.CP.le_refl(V.U.N(p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, p, MT_.MR{rc}, U32.sub(w1, p), MT_.MT.cf(tt, p, MT_.MR{rc}, U32.sub(w1, p), 0), MT_.MT.cn(tt, p, MT_.MR{rc}, 0))), SC.fb1(p, w1, hp))) :
    {Bool.and(True{}, Bool.and(_, Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), S.S.has(C.CP.rep(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), rc), tt, p)))) == True{} : Bool}
  %SC.hrm(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), rc, tt, p) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), _))) == True{} : Bool}
  %MT_.MT.cs0_ok(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, p, MT_.MR{rc}, U32.sub(w1, p), E, SC.fb(p, w1, U32.sub(w1, p), E, hp, C.CP.le_refl(V.U.N(U32.sub(w1, p))), hE), {==}) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), S.S.has(_, tt, p)))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), tt, p), tt, p), True{}, EM_.EM.has_sl(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), tt, p)) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), _))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0), True{}), True{}, P.Bool.or_true(U32.is_eq(SC.rlen(tt, p, rc, U32.sub(w1, p)), 0))) :
    {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

law SC.run.if_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +L: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  for +hz: {Bool.or(Bool.not(z), U32.is_le(4, L)) == True{} : Bool}
  for +hpL: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.pp(st)), V.U.N(L)), V.U.N(SC.w1(K)))) == True{} : Bool}
  for +hok: {SC.okK(K, ts, tt, N.Ent{SC.pp(st), U32.and(U32.or(L, 2147483648), 2147483647), SC.rc(st), N.ent.run(U32.or(L, 2147483648))}) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.run.if(z, K, tt, e, L, st)) == True{} : Bool}

def SC.run.if_inv(ts, tt, e, K, E, BIG, z, L, st, hk, hI, hr, hz, hpL, hok):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, L, SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hk,
        SC.push_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, SC.r4p(p, w1, hr), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), hok),
        (%Equal.sym(U32, SC.pp(SC.push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.pp(ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.pp_push(e, p, U32.or(L, 2147483648), rc, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), V.U.N(L)), V.U.N(w1))) == True{} : Bool};
          hpL),
        SC.or4(True{}, L, hz, {==}))

law SC.run.go_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.run.go(z, K, tt, e, st)) == True{} : Bool}

def SC.run.go_inv(ts, tt, e, K, E, BIG, z, st, hk, hI, hr):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.if_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, Bool.and(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), U32.is_le(8, SC.rlen(tt, p, rc, U32.sub(w1, p)))), SC.rlen(tt, p, rc, U32.sub(w1, p)), ST{tl, tb, tv, tio, p, mm, rc, SC.rlen(tt, p, rc, U32.sub(w1, p)), lck, last, nio, cont}, hk, hI, hr, SC.z48(U32.is_le(mm, SC.rlen(tt, p, rc, U32.sub(w1, p))), SC.rlen(tt, p, rc, U32.sub(w1, p))), P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), V.U.N(w1), MT_.MT.add_le(V.U.N(p), V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), V.U.N(U32.sub(w1, p)), C.CP.le_refl(V.U.N(p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, p, MT_.MR{rc}, U32.sub(w1, p), MT_.MT.cf(tt, p, MT_.MR{rc}, U32.sub(w1, p), 0), MT_.MT.cn(tt, p, MT_.MR{rc}, 0))), SC.fb1(p, w1, SC.r4p(p, w1, hr))),
        SC.run_ok0(ts, tt, slen, w0, w1, E, p, rc, SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.r4p(p, w1, hr), P.Nat.le_trans(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n), V.U.N(E), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(w1), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk)), SC.w31(SC.rlen(tt, p, rc, U32.sub(w1, p)), w1, BIG, P.Nat.le_trans(V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), V.U.N(w1), P.Nat.le_add_l(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p)))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), V.U.N(w1), MT_.MT.add_le(V.U.N(p), V.U.N(p), V.U.N(SC.rlen(tt, p, rc, U32.sub(w1, p))), V.U.N(U32.sub(w1, p)), C.CP.le_refl(V.U.N(p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, p, MT_.MR{rc}, U32.sub(w1, p), MT_.MT.cf(tt, p, MT_.MR{rc}, U32.sub(w1, p), 0), MT_.MT.cn(tt, p, MT_.MR{rc}, 0))), SC.fb1(p, w1, SC.r4p(p, w1, hr)))), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk))))

law SC.run_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.run(K, tt, e, st)) == True{} : Bool}

def SC.run_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr):
  match st:
    case ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.run.go_inv(ts, tt, e, K, E, BIG, U32.is_eq(rl, 4), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, hr)

# Source matches hold
# -------------------

law SC.run0:
  for +x: U32
  for +h: {U32.is_lt(x, 2147483648) == True{} : Bool}
  {N.ent.run(x) == False{} : Bool}

def SC.run0(x, h):
  %SC.m31(x, h) :
    {U32.is_ne(U32.and(_, 2147483648), 0) == False{} : Bool}
  %Equal.sym(U32, U32.and(U32.and(x, 2147483647), 2147483648), 0, Z.BB.runf0(x)) :
    {U32.is_ne(_, 0) == False{} : Bool}
  {==}

# w0 <= pos, from pos + b = p = d + w0 and b <= d.
law SC.na:
  for +w0: Nat
  for +p: Nat
  for +pos: Nat
  for +b: Nat
  for +d: Nat
  for +hd: {Nat.add(d, w0) == p : Nat}
  for +hpos: {Nat.add(pos, b) == p : Nat}
  for +hb: {Cmp.is_le(Nat.cmp(b, d)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(w0, pos)) == True{} : Bool}

def SC.na(w0, p, pos, b, d, hd, hpos, hb):
  %P.Nat.cmp_add_rr(w0, pos, b) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(pos, b), p, hpos) :
    {Cmp.is_le(Nat.cmp(Nat.add(w0, b), _)) == True{} : Bool}
  %hd :
    {Cmp.is_le(Nat.cmp(Nat.add(w0, b), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, w0), Nat.add(w0, d), P.Nat.add_comm(d, w0)) :
    {Cmp.is_le(Nat.cmp(Nat.add(w0, b), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(w0, b), Nat.add(w0, d)), Nat.cmp(b, d), P.Nat.cmp_add_l(w0, b, d)) :
    {Cmp.is_le(_) == True{} : Bool}
  hb

# pos + (f + b) <= w1, from pos + b = p, f <= m and m + p = w1.
law SC.nb:
  for +pos: Nat
  for +b: Nat
  for +f: Nat
  for +p: Nat
  for +m: Nat
  for +w1: Nat
  for +hpos: {Nat.add(pos, b) == p : Nat}
  for +hf: {Cmp.is_le(Nat.cmp(f, m)) == True{} : Bool}
  for +hm: {Nat.add(m, p) == w1 : Nat}
  {Cmp.is_le(Nat.cmp(Nat.add(pos, Nat.add(f, b)), w1)) == True{} : Bool}

def SC.nb(pos, b, f, p, m, w1, hpos, hf, hm):
  %Equal.sym(Nat, Nat.add(f, b), Nat.add(b, f), P.Nat.add_comm(f, b)) :
    {Cmp.is_le(Nat.cmp(Nat.add(pos, _), w1)) == True{} : Bool}
  %P.Nat.add_assoc(pos, b, f) :
    {Cmp.is_le(Nat.cmp(_, w1)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(pos, b), p, hpos) :
    {Cmp.is_le(Nat.cmp(Nat.add(_, f), w1)) == True{} : Bool}
  %hm :
    {Cmp.is_le(Nat.cmp(Nat.add(p, f), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(m, p), Nat.add(p, m), P.Nat.add_comm(m, p)) :
    {Cmp.is_le(Nat.cmp(Nat.add(p, f), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(p, f), Nat.add(p, m)), Nat.cmp(f, m), P.Nat.cmp_add_l(p, f, m)) :
    {Cmp.is_le(_) == True{} : Bool}
  hf

law SC.large_sl:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w1: U32
  for +E: U32
  for +p: U32
  for +srcpos: U32
  for +mb: U32
  for +hbi: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(srcpos), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), 4n), V.U.N(E))) == True{} : Bool}
  for +hbj: {Cmp.is_le(Nat.cmp(Nat.add(Nat.add(V.U.N(p), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), 4n), V.U.N(E))) == True{} : Bool}
  {S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))) == S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))) : List<&2, U32>}

def SC.large_sl(ts, tt, slen, w1, E, p, srcpos, mb, hbi, hbj):
  %Equal.sym(List<&2, U32>, S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, U32.add(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)))), K.WD.sl_app(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb), {==})) :
    {_ == S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)))), K.WD.sl_app(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb), {==})) :
    {K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, U32.add(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)))) == _ : List<&2, U32>}
  %Equal.sym(U32, U32.add(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)), srcpos, V.U.add_sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))) :
    {K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, _)) == K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)))) : List<&2, U32>}
  %Equal.sym(U32, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), SC.blen(ts, srcpos, tt, p, mb)), p, V.U.add_sub(p, SC.blen(ts, srcpos, tt, p, mb))) :
    {K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, srcpos)) == K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, _)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), MT_.MT.bs0_ok(V.U.N(mb), ts, srcpos, tt, p, mb)) :
    {K.WD.app(_, S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, srcpos)) == K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, p)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), ts, srcpos), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, p), MT_.MT.cs0_ok(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, hbi, hbj)) :
    {K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), _) == K.WD.app(S.S.sl(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), tt, p)) : List<&2, U32>}
  {==}

law SC.large_ok0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +BIG: U32
  for +p: U32
  for +srcpos: U32
  for +mb: U32
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hs: {U32.is_lt(srcpos, slen) == True{} : Bool}
  for +hE4: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  for +hEs: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))) == True{} : Bool}
  for +hmb1: {Cmp.is_le(Nat.cmp(V.U.N(mb), V.U.N(U32.sub(p, w0)))) == True{} : Bool}
  for +hmb2: {Cmp.is_le(Nat.cmp(V.U.N(mb), V.U.N(srcpos))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), U32.and(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 2147483647), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), N.ent.run(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))}) == True{} : Bool}

def SC.large_ok0(ts, tt, slen, w0, w1, E, BIG, p, srcpos, mb, hw, hp, hs, hE4, hEs, hmb1, hmb2, hk, hB):
  %Equal.sym(U32, U32.and(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 2147483647), U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), SC.m31(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), SC.w31(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), w1, BIG, (%Equal.sym(Nat, V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), V.U.add_N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb), w1, (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0))))))), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), _, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), N.ent.run(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))}) == True{} : Bool}
  %Equal.sym(Bool, N.ent.run(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), False{}, SC.run0(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), SC.w31(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), w1, BIG, (%Equal.sym(Nat, V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), V.U.add_N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb), w1, (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))))) : {Cmp.is_le(Nat.cmp(_, V.U.N(w1))) == True{} : Bool}; (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0))))))), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), _}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), True{}, V.U.N_le(w0, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), SC.na(V.U.N(w0), V.U.N(p), V.U.N(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.sub_nat(p, w0, hw), V.U.sub_nat(p, SC.blen(ts, srcpos, tt, p, mb), V.U.N_le(SC.blen(ts, srcpos, tt, p, mb), p, P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1)))) :
    {Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(w1))), Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), Bool.pick(Bool, U32.is_lt(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))), Bool.and(U32.is_lt(U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), U32.sub(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), w0)), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), tt, U32.add(w0, U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(w1))), True{}, (%Equal.sym(Nat, V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), V.U.add_N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb), w1, (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), _), V.U.N(w1))) == True{} : Bool}; SC.nb(V.U.N(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(p), V.U.N(U32.sub(w1, p)), V.U.N(w1), V.U.sub_nat(p, SC.blen(ts, srcpos, tt, p, mb), V.U.N_le(SC.blen(ts, srcpos, tt, p, mb), p, P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.sub_nat(w1, p, hp)))) :
    {Bool.and(True{}, Bool.and(_, Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), Bool.pick(Bool, U32.is_lt(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))), Bool.and(U32.is_lt(U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), U32.sub(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), w0)), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), tt, U32.add(w0, U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), True{}, V.U.le_lt_trans(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), srcpos, slen, V.U.N_le(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), srcpos, (%V.U.sub_nat(srcpos, SC.blen(ts, srcpos, tt, p, mb), V.U.N_le(SC.blen(ts, srcpos, tt, p, mb), srcpos, P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(srcpos), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb2))) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))))), hs)) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))), Bool.and(U32.is_lt(U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), U32.sub(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), w0)), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), tt, U32.add(w0, U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)))), V.U.N(slen))), True{}, (%Equal.sym(Nat, V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), V.U.add_N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb), w1, (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), _), V.U.N(slen))) == True{} : Bool}; SC.nb(V.U.N(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(srcpos), V.U.N(U32.sub(slen, srcpos)), V.U.N(slen), V.U.sub_nat(srcpos, SC.blen(ts, srcpos, tt, p, mb), V.U.N_le(SC.blen(ts, srcpos, tt, p, mb), srcpos, P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(srcpos), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb2))), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(slen, srcpos)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le_r(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.sub_nat(slen, srcpos, V.U.lt_to_le(srcpos, slen, hs))))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), Bool.pick(Bool, True{}, Bool.and(_, S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))), Bool.and(U32.is_lt(U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), U32.sub(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), w0)), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), tt, U32.add(w0, U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))))))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), True{}, (%Equal.sym(Nat, V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), V.U.add_N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb), w1, (%V.U.sub_nat(w1, p, hp) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(SC.blen(ts, srcpos, tt, p, mb))), _)) == True{} : Bool}; MT_.MT.add_le(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos))), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(U32.sub(p, w0)), V.U.N(p), P.Nat.le_trans(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(mb), V.U.N(U32.sub(p, w0)), MT_.MT.bs_le(V.U.N(mb), ts, srcpos, tt, p, mb, MT_.MT.bf(ts, srcpos, tt, p, mb, 0), MT_.MT.bn(ts, srcpos, tt, p, 0)), hmb1), (%V.U.sub_nat(p, w0, hw) : {Cmp.is_le(Nat.cmp(V.U.N(U32.sub(p, w0)), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(U32.sub(p, w0)), V.U.N(w0)))))))) : {S.S.has(S.S.sl(_, ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))) == True{} : Bool}; (%P.Nat.add_comm(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))) : {S.S.has(S.S.sl(_, ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))) == True{} : Bool}; (%Equal.sym(List<&2, U32>, S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), ts, U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb))), S.S.sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))), SC.large_sl(ts, tt, slen, w1, E, p, srcpos, mb, SC.fb(srcpos, slen, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, V.U.lt_to_le(srcpos, slen, hs), MT_.MT.min_le_r(U32.sub(w1, p), U32.sub(slen, srcpos)), hEs), SC.fb(p, w1, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), E, hp, MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos)), hE4))) : {S.S.has(_, tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))) == True{} : Bool}; EM_.EM.has_sl(Nat.add(V.U.N(SC.blen(ts, srcpos, tt, p, mb)), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb))))))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), Bool.pick(Bool, True{}, Bool.and(True{}, _), Bool.and(U32.is_lt(U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen), U32.sub(U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)), w0)), S.S.has(S.S.sl(V.U.N(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb))), tt, U32.add(w0, U32.sub(U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, mb)), slen))), tt, U32.sub(p, SC.blen(ts, srcpos, tt, p, mb)))))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0), True{}), True{}, P.Bool.or_true(U32.is_eq(U32.add(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), SC.blen(ts, srcpos, tt, p, mb)), 0))) :
    {_ == True{} : Bool}
  {==}

def SC.epos(+en: N.Ent) -> U32:
  match en:
    case N.Ent{pos, len, val, run}:
      pos

law SC.ok0_w0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +en: N.Ent
  for +h: {SG_.SG.ok0(ts, tt, slen, w0, w1, en) == True{} : Bool}
  {U32.is_le(w0, SC.epos(en)) == True{} : Bool}

def SC.ok0_w0(ts, tt, slen, w0, w1, en, h):
  match en:
    case N.Ent{pos, len, val, run}:
      P.Bool.and_l(U32.is_le(w0, pos), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(pos), V.U.N(len)), V.U.N(w1))), Bool.or(U32.is_eq(len, 0), SG_.SG.k0(ts, tt, slen, w0, run, pos, len, val))), h)

law SC.large.if_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +srcpos: U32
  for +maxback: U32
  for +fwd: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  for +hz: {Bool.or(Bool.not(z), U32.is_le(4, fwd)) == True{} : Bool}
  for +hpf: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(SC.pp(st)), V.U.N(fwd)), V.U.N(SC.w1(K)))) == True{} : Bool}
  for +hok: {SC.okK(K, ts, tt, N.Ent{U32.sub(SC.pp(st), SC.blen(ts, srcpos, tt, SC.pp(st), maxback)), U32.and(U32.add(fwd, SC.blen(ts, srcpos, tt, SC.pp(st), maxback)), 2147483647), U32.sub(srcpos, SC.blen(ts, srcpos, tt, SC.pp(st), maxback)), N.ent.run(U32.add(fwd, SC.blen(ts, srcpos, tt, SC.pp(st), maxback)))}) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.large.if(z, K, ts, tt, e, srcpos, maxback, fwd, st)) == True{} : Bool}

def SC.large.if_inv(ts, tt, e, K, E, BIG, z, srcpos, maxback, fwd, st, hk, hI, hr, hz, hpf, hok):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, fwd, SC.cont(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), hk,
        SC.cont_inv(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 1n, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})),
          SC.push_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hk,
            SC.erase.if_inv(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hI),
            (%Equal.sym(U32, SC.pp(SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.pp(ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.pp_erase(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : {U32.is_le(_, w1) == True{} : Bool}; SC.r4p(p, w1, hr)),
            SC.ok0_w0(ts, tt, slen, w0, w1, N.Ent{U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.and(U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), 2147483647), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), N.ent.run(U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)))}, hok),
            hok)),
        (%Equal.sym(U32, SC.pp(SC.cont(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))), SC.pp(SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.pp_cont(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, U32.add(U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback))), U32.add(srcpos, fwd), SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), V.U.N(fwd)), V.U.N(w1))) == True{} : Bool};
          (%Equal.sym(U32, SC.pp(SC.push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))), SC.pp(SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.pp_push(e, U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), U32.add(fwd, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(srcpos, SC.blen(ts, srcpos, tt, p, maxback)), SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}))) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), V.U.N(fwd)), V.U.N(w1))) == True{} : Bool};
            (%Equal.sym(U32, SC.pp(SC.erase.if(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.pp(ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.pp_erase(U32.is_lt(0, SC.blen(ts, srcpos, tt, p, maxback)), U32.sub(p, SC.blen(ts, srcpos, tt, p, maxback)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), V.U.N(fwd)), V.U.N(w1))) == True{} : Bool};
              hpf))),
        SC.or4(True{}, fwd, hz, {==}))

law SC.mb1:
  for +e: EM_.ET
  for +w0: U32
  for +p: U32
  for +srcpos: U32
  for +huo: {U32.is_eq(EM_.EM.uo(e), w0) == True{} : Bool}
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0)), V.U.N(U32.sub(p, w0)))) == True{} : Bool}

def SC.mb1(e, w0, p, srcpos, huo, hw):
  %Equal.sym(U32, EM_.EM.uo(e), w0, V.U.is_eq(EM_.EM.uo(e), w0, huo)) :
    {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(U32.is_le(_, p), U32.min(U32.sub(p, _), srcpos), 0)), V.U.N(U32.sub(p, w0)))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, p), True{}, hw) :
    {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(_, U32.min(U32.sub(p, w0), srcpos), 0)), V.U.N(U32.sub(p, w0)))) == True{} : Bool}
  MT_.MT.min_le(U32.sub(p, w0), srcpos)

law SC.mb2:
  for +e: EM_.ET
  for +w0: U32
  for +p: U32
  for +srcpos: U32
  for +huo: {U32.is_eq(EM_.EM.uo(e), w0) == True{} : Bool}
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0)), V.U.N(srcpos))) == True{} : Bool}

def SC.mb2(e, w0, p, srcpos, huo, hw):
  %Equal.sym(U32, EM_.EM.uo(e), w0, V.U.is_eq(EM_.EM.uo(e), w0, huo)) :
    {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(U32.is_le(_, p), U32.min(U32.sub(p, _), srcpos), 0)), V.U.N(srcpos))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, p), True{}, hw) :
    {Cmp.is_le(Nat.cmp(V.U.N(N.u32.pick(_, U32.min(U32.sub(p, w0), srcpos), 0)), V.U.N(srcpos))) == True{} : Bool}
  MT_.MT.min_le_r(U32.sub(p, w0), srcpos)

law SC.zmm.go:
  for +mm: U32
  for +x: U32
  for +c: Bool
  for +ec: {U32.is_le(mm, x) == c : Bool}
  for +hm: {U32.is_le(4, mm) == True{} : Bool}
  {Bool.or(Bool.not(c), U32.is_le(4, x)) == True{} : Bool}

def SC.zmm.go(mm, x, c, ec, hm):
  match c:
    case True{}:
      V.U.N_le(4, x, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(x), V.U.le_N(4, mm, hm), V.U.le_N(mm, x, ec)))
    case False{}:
      {==}

law SC.large.try_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +srcpos: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  for +hz: {Bool.or(Bool.not(z), U32.is_lt(srcpos, N.SK.slen(K))) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.large.try(z, K, ts, tt, e, srcpos, st)) == True{} : Bool}

def SC.large.try_inv(ts, tt, e, K, E, BIG, z, srcpos, st, hk, hI, hr, hz):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.if_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, U32.is_le(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, hr,
        SC.zmm.go(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), U32.is_le(mm, SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), {==}, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)),
        P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), V.U.N(w1), MT_.MT.add_le(V.U.N(p), V.U.N(p), V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.sub(w1, p)), C.CP.le_refl(V.U.N(p)), P.Nat.le_trans(V.U.N(SC.flen(ts, srcpos, tt, p, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)))), V.U.N(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos))), V.U.N(U32.sub(w1, p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 2n), 1)), ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), MT_.MT.cf(ts, srcpos, MT_.MW{tt, p}, U32.min(U32.sub(w1, p), U32.sub(slen, srcpos)), 0), MT_.MT.cn(ts, srcpos, MT_.MW{tt, p}, 0)), MT_.MT.min_le(U32.sub(w1, p), U32.sub(slen, srcpos)))), SC.fb1(p, w1, SC.r4p(p, w1, hr))),
        SC.large_ok0(ts, tt, slen, w0, w1, E, BIG, p, srcpos, N.u32.pick(U32.is_le(EM_.EM.uo(e), p), U32.min(U32.sub(p, EM_.EM.uo(e)), srcpos), 0), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.r4p(p, w1, hr), hz, P.Nat.le_trans(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n), V.U.N(E), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(w1), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk)), SC.kv.sE(e, slen, w0, w1, cpl, E, BIG, hk), SC.mb1(e, w0, p, srcpos, SC.kv.uo(e, slen, w0, w1, cpl, E, BIG, hk), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.mb2(e, w0, p, srcpos, SC.kv.uo(e, slen, w0, w1, cpl, E, BIG, hk), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)))

law SC.large.go_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.large.go(z, K, ts, tt, e, st)) == True{} : Bool}

def SC.large.go_inv(ts, tt, e, K, E, BIG, z, st, hk, hI, hr):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.try_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, Bool.and(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), Bool.not(Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last)))), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, N.u32.pick(Bool.and(Bool.and(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1))), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen)), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last), nio, cont}, hk, hI, hr,
        SC.hit(U32.is_ne(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 0), U32.is_le(N.src.low(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}), U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1)), U32.is_lt(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), slen), Bool.and(U32.is_ne(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), 0), U32.is_eq(U32.sub(A.T.word(tl, N.H.slot(lck, U32.to_nat(lsh), lmask)), 1), last))))

law SC.large_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.large(K, ts, tt, e, st)) == True{} : Bool}

def SC.large_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.large.go_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, Bool.and(U32.is_lt(0, slen), U32.is_le(U32.add(p, 9), w1)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, hr)

# Target matches hold
# -------------------

# The chain search: the position it tries is in the window before p, and
# its best match, if any, is a match in the window before p.
def SC.CIb(+tt: A.Tr, +p: U32, +w0: U32, +w1: U32, +ct: CT) -> Bool:
  match ct:
    case CT{tv, best, off, base, chain}:
      Bool.or(U32.is_eq(best, 0), Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p))))

def SC.cbase(+ct: CT) -> U32:
  match ct:
    case CT{tv, best, off, base, chain}:
      base

def SC.CI(+tt: A.Tr, +p: U32, +w0: U32, +w1: U32, +r: CR) -> Bool:
  match r:
    case CR{g, ct}:
      Bool.and(Bool.or(Bool.not(g), Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p))), SC.CIb(tt, p, w0, w1, ct))

# The next position's facts, when the search goes on.
law SC.ci1:
  for +x: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +pb: U32
  for +base: U32
  for +p: U32
  for +w0: U32
  for +ea4: {U32.is_lt(pb, base) == a4 : Bool}
  for +ea5: {U32.is_le(w0, pb) == a5 : Bool}
  for +hbp: {U32.is_lt(base, p) == True{} : Bool}
  {Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(x, a4), a5), a6)), Bool.and(U32.is_le(w0, pb), U32.is_lt(pb, p))) == True{} : Bool}

def SC.ci1(x, a4, a5, a6, pb, base, p, w0, ea4, ea5, hbp):
  match a4 a5:
    case True{} True{}:
      %Equal.sym(Bool, U32.is_le(w0, pb), True{}, ea5) :
        {Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(x, True{}), True{}), a6)), Bool.and(_, U32.is_lt(pb, p))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(pb, p), True{}, V.U.lt_trans(pb, base, p, ea4, hbp)) :
        {Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(x, True{}), True{}), a6)), Bool.and(True{}, _)) == True{} : Bool}
      P.Bool.or_true(Bool.not(Bool.and(Bool.and(Bool.and(x, True{}), True{}), a6)))
    case True{} False{}:
      %Equal.sym(Bool, Bool.and(Bool.and(x, True{}), False{}), False{}, P.Bool.and_false(Bool.and(x, True{}))) :
        {Bool.or(Bool.not(Bool.and(_, a6)), Bool.and(U32.is_le(w0, pb), U32.is_lt(pb, p))) == True{} : Bool}
      {==}
    case False{} a:
      %Equal.sym(Bool, Bool.and(x, False{}), False{}, P.Bool.and_false(x)) :
        {Bool.or(Bool.not(Bool.and(Bool.and(_, a), a6)), Bool.and(U32.is_le(w0, pb), U32.is_lt(pb, p))) == True{} : Bool}
      {==}

law SC.ci2:
  for +tt: A.Tr
  for +p: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +best: U32
  for +off: U32
  for +base: U32
  for +better: Bool
  for +hwb: {U32.is_le(w0, base) == True{} : Bool}
  for +hbp: {U32.is_lt(base, p) == True{} : Bool}
  for +h2: {Bool.or(U32.is_eq(best, 0), Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  {Bool.or(U32.is_eq(N.u32.pick(better, SC.tlen(tt, base, p, U32.sub(w1, p)), best), 0), Bool.and(Bool.and(U32.is_le(w0, N.u32.pick(better, base, off)), U32.is_lt(N.u32.pick(better, base, off), p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(N.u32.pick(better, SC.tlen(tt, base, p, U32.sub(w1, p)), best))), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(N.u32.pick(better, SC.tlen(tt, base, p, U32.sub(w1, p)), best)), tt, N.u32.pick(better, base, off)), tt, p)))) == True{} : Bool}

def SC.ci2(tt, p, w0, w1, E, best, off, base, better, hwb, hbp, h2, hp, hE):
  match better:
    case False{}:
      h2
    case True{}:
      SC.or_r(U32.is_eq(SC.tlen(tt, base, p, U32.sub(w1, p)), 0), Bool.and(Bool.and(U32.is_le(w0, base), U32.is_lt(base, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p)))), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, base), tt, p))),
        SC.and_tt(Bool.and(U32.is_le(w0, base), U32.is_lt(base, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p)))), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, base), tt, p)),
          SC.and_tt(U32.is_le(w0, base), U32.is_lt(base, p), hwb, hbp),
          SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p)))), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, base), tt, p), P.Nat.le_trans(Nat.add(V.U.N(p), V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p)))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), V.U.N(w1), MT_.MT.add_le(V.U.N(p), V.U.N(p), V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), V.U.N(U32.sub(w1, p)), C.CP.le_refl(V.U.N(p)), MT_.MT.cs_le(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), MT_.MT.cf(tt, base, MT_.MW{tt, p}, U32.sub(w1, p), 0), MT_.MT.cn(tt, base, MT_.MW{tt, p}, 0))), SC.fb1(p, w1, hp)), (%Equal.sym(List<&2, U32>, S.S.sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, base), S.S.sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, p), MT_.MT.cs0_ok(U32.to_nat(U32.add(U32.shrn(U32.sub(w1, p), 2n), 1)), tt, base, MT_.MW{tt, p}, U32.sub(w1, p), E, P.Nat.le_trans(Nat.add(Nat.add(V.U.N(base), V.U.N(U32.sub(w1, p))), 4n), Nat.add(Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), 4n), V.U.N(E), MT_.MT.add_le(Nat.add(V.U.N(base), V.U.N(U32.sub(w1, p))), Nat.add(V.U.N(p), V.U.N(U32.sub(w1, p))), 4n, 4n, MT_.MT.add_le(V.U.N(base), V.U.N(p), V.U.N(U32.sub(w1, p)), V.U.N(U32.sub(w1, p)), P.Nat.lt_to_le(V.U.N(base), V.U.N(p), V.U.lt_N(base, p, hbp)), C.CP.le_refl(V.U.N(U32.sub(w1, p)))), C.CP.le_refl(4n)), SC.fb(p, w1, U32.sub(w1, p), E, hp, C.CP.le_refl(V.U.N(U32.sub(w1, p))), hE)), SC.fb(p, w1, U32.sub(w1, p), E, hp, C.CP.le_refl(V.U.N(U32.sub(w1, p))), hE))) : {S.S.has(_, tt, p) == True{} : Bool}; EM_.EM.has_sl(V.U.N(SC.tlen(tt, base, p, U32.sub(w1, p))), tt, p)))))

law SC.cs.step_inv:
  for +p: U32
  for +w1: U32
  for +w0: U32
  for +tt: A.Tr
  for +E: U32
  for +ct: CT
  for +h1: {Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p)) == True{} : Bool}
  for +h2: {SC.CIb(tt, p, w0, w1, ct) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  {SC.CI(tt, p, w0, w1, SC.cs.step(p, w1, w0, tt, ct)) == True{} : Bool}

def SC.cs.step_inv(p, w1, w0, tt, E, ct, h1, h2, hp, hE):
  match ct:
    case CT{tv, best, off, base, chain}:
      SC.and_tt(Bool.or(Bool.not(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.not(Bool.and(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), Bool.or(U32.is_eq(U32.add(p, SC.tlen(tt, base, p, U32.sub(w1, p))), w1), U32.is_le(35, SC.tlen(tt, base, p, U32.sub(w1, p)))))), U32.is_lt(0, U32.sub(chain, 1))), U32.is_ne(A.T.word(tv, U32.and(base, N.PMASK())), 0)), U32.is_lt(U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1), base)), U32.is_le(w0, U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1))), U32.is_le(U32.sub(p, U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1)), N.PMASK()))), Bool.and(U32.is_le(w0, U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1)), U32.is_lt(U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1), p))), SC.CIb(tt, p, w0, w1, CT{tv, N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), SC.tlen(tt, base, p, U32.sub(w1, p)), best), N.u32.pick(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), base, off), U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1), U32.sub(chain, 1)}),
        SC.ci1(Bool.and(Bool.and(Bool.not(Bool.and(U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), Bool.or(U32.is_eq(U32.add(p, SC.tlen(tt, base, p, U32.sub(w1, p))), w1), U32.is_le(35, SC.tlen(tt, base, p, U32.sub(w1, p)))))), U32.is_lt(0, U32.sub(chain, 1))), U32.is_ne(A.T.word(tv, U32.and(base, N.PMASK())), 0)), U32.is_lt(U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1), base), U32.is_le(w0, U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1)), U32.is_le(U32.sub(p, U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1)), N.PMASK()), U32.sub(A.T.word(tv, U32.and(base, N.PMASK())), 1), base, p, w0, {==}, {==}, P.Bool.and_r(U32.is_le(w0, base), U32.is_lt(base, p), h1)),
        SC.ci2(tt, p, w0, w1, E, best, off, base, U32.is_lt(best, SC.tlen(tt, base, p, U32.sub(w1, p))), P.Bool.and_l(U32.is_le(w0, base), U32.is_lt(base, p), h1), P.Bool.and_r(U32.is_le(w0, base), U32.is_lt(base, p), h1), h2, hp, hE))

law SC.cs.loop_inv:
  for +k: Nat
  for +p: U32
  for +w1: U32
  for +w0: U32
  for +tt: A.Tr
  for +E: U32
  for +r: CR
  for +hc: {SC.CI(tt, p, w0, w1, r) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))) == True{} : Bool}
  {SC.CIb(tt, p, w0, w1, SC.cs.loop(k, p, w1, w0, tt, r)) == True{} : Bool}

def SC.cs.loop_inv(k, p, w1, w0, tt, E, r, hc, hp, hE):
  match k r:
    case 0n CR{g, ct}:
      P.Bool.and_r(Bool.or(Bool.not(g), Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p))), SC.CIb(tt, p, w0, w1, ct), hc)
    case 1n+q CR{False{}, ct}:
      P.Bool.and_r(Bool.or(Bool.not(False{}), Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p))), SC.CIb(tt, p, w0, w1, ct), hc)
    case 1n+q CR{True{}, ct}:
      SC.cs.loop_inv(q, p, w1, w0, tt, E, SC.cs.step(p, w1, w0, tt, ct),
        SC.cs.step_inv(p, w1, w0, tt, E, ct, P.Bool.and_l(Bool.or(Bool.not(True{}), Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p))), SC.CIb(tt, p, w0, w1, ct), hc), P.Bool.and_r(Bool.or(Bool.not(True{}), Bool.and(U32.is_le(w0, SC.cbase(ct)), U32.is_lt(SC.cbase(ct), p))), SC.CIb(tt, p, w0, w1, ct), hc), hp, hE),
        hp, hE)

law SC.orandr:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(Bool.not(Bool.and(Bool.and(a, b), c)), Bool.and(b, c)) == True{} : Bool}

def SC.orandr(a, b, c):
  match b c:
    case True{} True{}:
      P.Bool.or_true(Bool.not(Bool.and(Bool.and(a, True{}), True{})))
    case True{} False{}:
      %Equal.sym(Bool, Bool.and(Bool.and(a, True{}), False{}), False{}, P.Bool.and_false(Bool.and(a, True{}))) :
        {Bool.or(Bool.not(_), Bool.and(True{}, False{})) == True{} : Bool}
      {==}
    case False{} c2:
      %Equal.sym(Bool, Bool.and(a, False{}), False{}, P.Bool.and_false(a)) :
        {Bool.or(Bool.not(Bool.and(_, c2)), Bool.and(False{}, c2)) == True{} : Bool}
      {==}

# x <= d, from x + w0 = off, d + w0 = w1 and off <= w1.
law SC.nd:
  for +x: Nat
  for +w0: Nat
  for +off: Nat
  for +d: Nat
  for +w1: Nat
  for +hx: {Nat.add(x, w0) == off : Nat}
  for +hd: {Nat.add(d, w0) == w1 : Nat}
  for +hle: {Cmp.is_le(Nat.cmp(off, w1)) == True{} : Bool}
  {Cmp.is_le(Nat.cmp(x, d)) == True{} : Bool}

def SC.nd(x, w0, off, d, w1, hx, hd, hle):
  %P.Nat.cmp_add_rr(x, d, w0) :
    {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(x, w0), off, hx) :
    {Cmp.is_le(Nat.cmp(_, Nat.add(d, w0))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, w0), w1, hd) :
    {Cmp.is_le(Nat.cmp(off, _)) == True{} : Bool}
  hle

law SC.addsub:
  for +a: U32
  for +b: U32
  {U32.add(a, U32.sub(b, a)) == b : U32}

def SC.addsub(a, b):
  %Equal.sym(U32, U32.add(a, U32.sub(b, a)), U32.add(U32.sub(b, a), a), V.U.add_comm(a, U32.sub(b, a))) :
    {_ == b : U32}
  V.U.add_sub(b, a)

# A target match of best bytes at p, from off in the window.
law SC.small_ok0:
  for +ts: A.Tr
  for +tt: A.Tr
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +E: U32
  for +BIG: U32
  for +p: U32
  for +best: U32
  for +off: U32
  for +hw: {U32.is_le(w0, p) == True{} : Bool}
  for +hp: {U32.is_le(p, w1) == True{} : Bool}
  for +hoff: {U32.is_le(w0, off) == True{} : Bool}
  for +hop: {U32.is_lt(off, p) == True{} : Bool}
  for +hpb: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))) == True{} : Bool}
  for +hhas: {S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p) == True{} : Bool}
  for +hswE: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E))) == True{} : Bool}
  for +hk: {Cmp.is_le(Nat.cmp(Nat.double(Nat.double(SG_.SG.tri(1n+V.U.N(w1)))), V.U.N(BIG))) == True{} : Bool}
  for +hB: {U32.is_lt(BIG, 2147483648) == True{} : Bool}
  {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(best, 2147483647), U32.add(slen, U32.sub(off, w0)), N.ent.run(best)}) == True{} : Bool}

def SC.small_ok0(ts, tt, slen, w0, w1, E, BIG, p, best, off, hw, hp, hoff, hop, hpb, hhas, hswE, hk, hB):
  %Equal.sym(U32, U32.and(best, 2147483647), best, SC.m31(best, SC.w31(best, w1, BIG, P.Nat.le_trans(V.U.N(best), Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1), P.Nat.le_add_l(V.U.N(p), V.U.N(best)), hpb), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, _, U32.add(slen, U32.sub(off, w0)), N.ent.run(best)}) == True{} : Bool}
  %Equal.sym(Bool, N.ent.run(best), False{}, SC.run0(best, SC.w31(best, w1, BIG, P.Nat.le_trans(V.U.N(best), Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1), P.Nat.le_add_l(V.U.N(p), V.U.N(best)), hpb), hk, hB))) :
    {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, best, U32.add(slen, U32.sub(off, w0)), _}) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(w0, p), True{}, hw) :
    {Bool.and(_, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, U32.is_lt(U32.add(slen, U32.sub(off, w0)), slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(U32.sub(U32.add(slen, U32.sub(off, w0)), slen), U32.sub(p, w0)), S.S.has(S.S.sl(V.U.N(best), tt, U32.add(w0, U32.sub(U32.add(slen, U32.sub(off, w0)), slen))), tt, p)))))) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), True{}, hpb) :
    {Bool.and(True{}, Bool.and(_, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, U32.is_lt(U32.add(slen, U32.sub(off, w0)), slen), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(U32.sub(U32.add(slen, U32.sub(off, w0)), slen), U32.sub(p, w0)), S.S.has(S.S.sl(V.U.N(best), tt, U32.add(w0, U32.sub(U32.add(slen, U32.sub(off, w0)), slen))), tt, p)))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.add(slen, U32.sub(off, w0)), slen), False{}, SC.nlt(slen, U32.add(slen, U32.sub(off, w0)), V.U.N_le(slen, U32.add(slen, U32.sub(off, w0)), (%Equal.sym(Nat, V.U.N(U32.add(slen, U32.sub(off, w0))), Nat.add(V.U.N(slen), V.U.N(U32.sub(off, w0))), V.U.add_N(slen, U32.sub(off, w0), E, P.Nat.le_trans(Nat.add(V.U.N(slen), V.U.N(U32.sub(off, w0))), Nat.add(V.U.N(slen), V.U.N(U32.sub(w1, w0))), V.U.N(E), MT_.MT.add_le(V.U.N(slen), V.U.N(slen), V.U.N(U32.sub(off, w0)), V.U.N(U32.sub(w1, w0)), C.CP.le_refl(V.U.N(slen)), SC.nd(V.U.N(U32.sub(off, w0)), V.U.N(w0), V.U.N(off), V.U.N(U32.sub(w1, w0)), V.U.N(w1), V.U.sub_nat(off, w0, hoff), V.U.sub_nat(w1, w0, V.U.N_le(w0, w1, P.Nat.le_trans(V.U.N(w0), V.U.N(p), V.U.N(w1), V.U.le_N(w0, p, hw), V.U.le_N(p, w1, hp)))), P.Nat.lt_to_le(V.U.N(off), V.U.N(w1), P.Nat.lt_le_trans(V.U.N(off), V.U.N(p), V.U.N(w1), V.U.lt_N(off, p, hop), V.U.le_N(p, w1, hp))))), hswE))) : {Cmp.is_le(Nat.cmp(V.U.N(slen), _)) == True{} : Bool}; P.Nat.cmp_add_r(V.U.N(slen), V.U.N(U32.sub(off, w0))))))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, _, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(U32.sub(U32.add(slen, U32.sub(off, w0)), slen), U32.sub(p, w0)), S.S.has(S.S.sl(V.U.N(best), tt, U32.add(w0, U32.sub(U32.add(slen, U32.sub(off, w0)), slen))), tt, p)))))) == True{} : Bool}
  %Equal.sym(U32, U32.sub(U32.add(slen, U32.sub(off, w0)), slen), U32.sub(off, w0), V.U.sub_add_l(slen, U32.sub(off, w0))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, False{}, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(_, U32.sub(p, w0)), S.S.has(S.S.sl(V.U.N(best), tt, U32.add(w0, _)), tt, p)))))) == True{} : Bool}
  %Equal.sym(U32, U32.add(w0, U32.sub(off, w0)), off, SC.addsub(w0, off)) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, False{}, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(U32.sub(off, w0), U32.sub(p, w0)), S.S.has(S.S.sl(V.U.N(best), tt, _), tt, p)))))) == True{} : Bool}
  %Equal.sym(Bool, S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p), True{}, hhas) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, False{}, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(U32.is_lt(U32.sub(off, w0), U32.sub(p, w0)), _))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(U32.sub(off, w0), U32.sub(p, w0)), True{}, V.U.N_lt(U32.sub(off, w0), U32.sub(p, w0), (%P.Nat.cmp_add_rr(V.U.N(U32.sub(off, w0)), V.U.N(U32.sub(p, w0)), V.U.N(w0)) : {_ == LT{} : Cmp}; (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(off, w0)), V.U.N(w0)), V.U.N(off), V.U.sub_nat(off, w0, hoff)) : {Nat.cmp(_, Nat.add(V.U.N(U32.sub(p, w0)), V.U.N(w0))) == LT{} : Cmp}; (%Equal.sym(Nat, Nat.add(V.U.N(U32.sub(p, w0)), V.U.N(w0)), V.U.N(p), V.U.sub_nat(p, w0, hw)) : {Nat.cmp(V.U.N(off), _) == LT{} : Cmp}; V.U.lt_N(off, p, hop)))))) :
    {Bool.and(True{}, Bool.and(True{}, Bool.or(U32.is_eq(best, 0), Bool.pick(Bool, False{}, Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(U32.add(slen, U32.sub(off, w0))), V.U.N(best)), V.U.N(slen))), S.S.has(S.S.sl(V.U.N(best), ts, U32.add(slen, U32.sub(off, w0))), tt, p)), Bool.and(_, True{}))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_eq(best, 0), True{}), True{}, P.Bool.or_true(U32.is_eq(best, 0))) :
    {_ == True{} : Bool}
  {==}

# A target match to take: 4 bytes at least, in the window, and holding.
def SC.SF(+K: N.SK, +ts: A.Tr, +tt: A.Tr, +len: U32, +addr: U32, +st: ST) -> Bool:
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      Bool.and(U32.is_le(4, len), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)})))

law SC.small.if_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +z: Bool
  for +len: U32
  for +addr: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  for +hz: {Bool.or(Bool.not(z), SC.SF(K, ts, tt, len, addr, st)) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.small.if(z, K, tt, e, len, addr, st)) == True{} : Bool}

def SC.small.if_inv(ts, tt, e, K, E, BIG, z, len, addr, st, hk, hI, hr, hz):
  match K z st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} False{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.and_tt(SC.Is(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, 0n, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.room4(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hI, hr)
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} True{} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.lazy_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, len, SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), hk,
        SC.push_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, SC.r4p(p, w1, hr), SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)}), P.Bool.and_r(U32.is_le(4, len), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)})), hz))),
        (%Equal.sym(U32, SC.pp(SC.push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})), SC.pp(ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}), SC.pp_push(e, p, len, addr, ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) : {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(_), V.U.N(len)), V.U.N(w1))) == True{} : Bool};
          P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)}), P.Bool.and_r(U32.is_le(4, len), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)})), hz))),
        P.Bool.and_l(U32.is_le(4, len), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(len)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(len, 2147483647), addr, N.ent.run(len)})), hz))

law SC.zand:
  for +a: Bool
  for +c: Bool
  for +X: Bool
  for +hX: {Bool.or(Bool.not(c), X) == True{} : Bool}
  {Bool.or(Bool.not(Bool.and(a, c)), X) == True{} : Bool}

def SC.zand(a, c, X, hX):
  match c:
    case True{}:
      SC.or_r(Bool.not(Bool.and(a, True{})), X, hX)
    case False{}:
      %Equal.sym(Bool, Bool.and(a, False{}), False{}, P.Bool.and_false(a)) :
        {Bool.or(Bool.not(_), X) == True{} : Bool}
      {==}

law SC.ne0:
  for +x: U32
  for +h: {U32.is_le(4, x) == True{} : Bool}
  {U32.is_eq(x, 0) == False{} : Bool}

def SC.ne0(x, h):
  SG_.SG.ne_gt(x, 0, P.Nat.lt_le_trans(0n, 4n, V.U.N(x), {==}, V.U.le_N(4, x, h)))

# The facts of a taken target match, from the chain search's.
law SC.zfin:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +E: U32
  for +BIG: U32
  for +slen: U32
  for +w0: U32
  for +w1: U32
  for +cpl: U32
  for +lsh: U32
  for +lmask: U32
  for +ssh: U32
  for +smask: U32
  for +cap: U32
  for +tl: A.Tr
  for +tb: A.Tr
  for +tv: A.Tr
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +rc: U32
  for +rl: U32
  for +lck: U32
  for +last: U32
  for +nio: U32
  for +cont: U32
  for +best: U32
  for +off: U32
  for +c: Bool
  for +ec: {U32.is_le(mm, best) == c : Bool}
  for +hk: {SC.kv(e, slen, w0, w1, cpl, E, BIG) == True{} : Bool}
  for +hI: {SC.Iv(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio) == True{} : Bool}
  for +hr: {Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), 4n), V.U.N(w1))) == True{} : Bool}
  for +hc: {Bool.or(U32.is_eq(best, 0), Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}
  {Bool.or(Bool.not(c), SC.SF(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, best, U32.add(cpl, U32.sub(off, w0)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont})) == True{} : Bool}

def SC.zfin(ts, tt, e, E, BIG, slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap, tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont, best, off, c, ec, hk, hI, hr, hc):
  match c:
    case False{}:
      {==}
    case True{}:
      SC.and_tt(U32.is_le(4, best), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(best, 2147483647), U32.add(cpl, U32.sub(off, w0)), N.ent.run(best)})), V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec))), SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(best, 2147483647), U32.add(cpl, U32.sub(off, w0)), N.ent.run(best)}), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p), P.Bool.and_r(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)), (%SC.ne0(best, V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec)))) : {Bool.or(_, Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}; hc))), (%Equal.sym(U32, cpl, slen, V.U.is_eq(cpl, slen, SC.kv.cpl(e, slen, w0, w1, cpl, E, BIG, hk))) : {SG_.SG.ok0(ts, tt, slen, w0, w1, N.Ent{p, U32.and(best, 2147483647), U32.add(_, U32.sub(off, w0)), N.ent.run(best)}) == True{} : Bool}; SC.small_ok0(ts, tt, slen, w0, w1, E, BIG, p, best, off, SC.Iv.w0(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI), SC.r4p(p, w1, hr), P.Bool.and_l(U32.is_le(w0, off), U32.is_lt(off, p), P.Bool.and_l(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)), (%SC.ne0(best, V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec)))) : {Bool.or(_, Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}; hc))), P.Bool.and_r(U32.is_le(w0, off), U32.is_lt(off, p), P.Bool.and_l(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)), (%SC.ne0(best, V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec)))) : {Bool.or(_, Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}; hc))), P.Bool.and_l(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p), P.Bool.and_r(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)), (%SC.ne0(best, V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec)))) : {Bool.or(_, Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}; hc))), P.Bool.and_r(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p), P.Bool.and_r(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)), (%SC.ne0(best, V.U.N_le(4, best, P.Nat.le_trans(V.U.N(4), V.U.N(mm), V.U.N(best), V.U.le_N(4, mm, SC.Iv.mm(ts, tt, slen, w0, w1, 0n, tio, p, mm, nio, hI)), V.U.le_N(mm, best, ec)))) : {Bool.or(_, Bool.and(Bool.and(U32.is_le(w0, off), U32.is_lt(off, p)), Bool.and(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(p), V.U.N(best)), V.U.N(w1))), S.S.has(S.S.sl(V.U.N(best), tt, off), tt, p)))) == True{} : Bool}; hc))), SC.kv.swE(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.big(e, slen, w0, w1, cpl, E, BIG, hk), SC.kv.B(e, slen, w0, w1, cpl, E, BIG, hk)))))

law SC.small.fin_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +tl: A.Tr
  for +tb: A.Tr
  for +tv0: A.Tr
  for +tio: A.Tr
  for +p: U32
  for +mm: U32
  for +rc: U32
  for +rl: U32
  for +lck: U32
  for +last: U32
  for +nio: U32
  for +cont: U32
  for +ct: CT
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, ST{tl, tb, tv0, tio, p, mm, rc, rl, lck, last, nio, cont}) == True{} : Bool}
  for +hr: {SC.room4(K, ST{tl, tb, tv0, tio, p, mm, rc, rl, lck, last, nio, cont}) == True{} : Bool}
  for +hc: {SC.CIb(tt, p, SC.w0(K), SC.w1(K), ct) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.small.fin(K, tt, e, tl, tb, tio, p, mm, rc, rl, lck, last, nio, cont, ct)) == True{} : Bool}

def SC.small.fin_inv(ts, tt, e, K, E, BIG, tl, tb, tv0, tio, p, mm, rc, rl, lck, last, nio, cont, ct, hk, hI, hr, hc):
  match K ct:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} CT{tv, best, off, base, chain}:
      SC.small.if_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, Bool.and(Bool.not(Bool.or(Bool.and(U32.is_eq(best, 4), U32.is_le(16384, U32.sub(p, off))), Bool.and(U32.is_eq(best, 5), U32.is_le(2097152, U32.sub(p, off))))), U32.is_le(mm, best)), best, U32.add(cpl, U32.sub(off, w0)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}, hk, hI, hr,
        SC.zand(Bool.not(Bool.or(Bool.and(U32.is_eq(best, 4), U32.is_le(16384, U32.sub(p, off))), Bool.and(U32.is_eq(best, 5), U32.is_le(2097152, U32.sub(p, off))))), U32.is_le(mm, best), SC.SF(N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, ts, tt, best, U32.add(cpl, U32.sub(off, w0)), ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}),
          SC.zfin(ts, tt, e, E, BIG, slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap, tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont, best, off, U32.is_le(mm, best), {==}, hk, hI, hr, hc)))

law SC.small_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI2(K, ts, tt, SC.small(K, tt, e, st)) == True{} : Bool}

def SC.small_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.small.fin_inv(ts, tt, e, N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}, E, BIG, tl, A.T.set(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask), U32.add(p, 1)), tv, tio, p, mm, rc, rl, lck, last, nio, cont, SC.cs.loop(5n, p, w1, w0, tt, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}}), hk, hI, hr,
        SC.cs.loop_inv(5n, p, w1, w0, tt, E, CR{Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}},
          SC.and_tt(Bool.or(Bool.not(Bool.and(Bool.and(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1))), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p))), Bool.and(U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1)), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p))), SC.CIb(tt, p, w0, w1, CT{A.T.set(tv, U32.and(p, N.PMASK()), A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask))), 0, 0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), N.u32.pick(U32.is_eq(mm, 4), 4, 1)}), SC.orandr(U32.is_ne(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 0), U32.is_le(w0, U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1)), U32.is_lt(U32.sub(A.T.word(tb, N.H.slot(U32.mul(MT_.MT.W(tt, p), N.H.M()), U32.to_nat(ssh), smask)), 1), p)), {==}),
          SC.r4p(p, w1, hr), P.Nat.le_trans(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n), V.U.N(E), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(w1), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk))))

# The scan keeps the invariant
# ----------------------------

law SC.s3_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +r: R2
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +h: {SC.LI2(K, ts, tt, r) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.s3(K, tt, r)) == True{} : Bool}

def SC.s3_inv(ts, tt, e, K, E, BIG, r, hk, h):
  match r:
    case R2{True{}, q}:
      h
    case R2{False{}, R1{c, st}}:
      SC.next_inv(ts, tt, e, K, E, BIG, st, hk, P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h), P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h))

law SC.s2_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +r: R2
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +h: {SC.LI2(K, ts, tt, r) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.s2(K, tt, e, r)) == True{} : Bool}

def SC.s2_inv(ts, tt, e, K, E, BIG, r, hk, h):
  match r:
    case R2{True{}, q}:
      h
    case R2{False{}, R1{c, st}}:
      SC.s3_inv(ts, tt, e, K, E, BIG, SC.small(K, tt, e, st), hk, SC.small_inv(ts, tt, e, K, E, BIG, st, hk, P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h), P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h)))

law SC.s1_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +r: R2
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +h: {SC.LI2(K, ts, tt, r) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.s1(K, ts, tt, e, r)) == True{} : Bool}

def SC.s1_inv(ts, tt, e, K, E, BIG, r, hk, h):
  match r:
    case R2{True{}, q}:
      h
    case R2{False{}, R1{c, st}}:
      SC.s2_inv(ts, tt, e, K, E, BIG, SC.large(K, ts, tt, e, st), hk, SC.large_inv(ts, tt, e, K, E, BIG, st, hk, P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h), P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), SC.room4(K, st), h)))

law SC.step_inv:
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +st: ST
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +hI: {SC.Is(K, ts, tt, 0n, st) == True{} : Bool}
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {SC.LI(K, ts, tt, SC.step(K, ts, tt, e, st)) == True{} : Bool}

def SC.step_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr):
  SC.s1_inv(ts, tt, e, K, E, BIG, SC.run(K, tt, e, st), hk, SC.run_inv(ts, tt, e, K, E, BIG, st, hk, hI, hr))

# After the loop, the state holds.
law SC.loop_inv:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +r: R1
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +h: {SC.LI(K, ts, tt, r) == True{} : Bool}
  {SC.Is(K, ts, tt, 0n, SC.loop(k, K, ts, tt, e, r)) == True{} : Bool}

def SC.loop_inv(k, ts, tt, e, K, E, BIG, r, hk, h):
  match k r:
    case 0n R1{g, st}:
      P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(g), SC.room4(K, st)), h)
    case 1n+q R1{False{}, st}:
      P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(False{}), SC.room4(K, st)), h)
    case 1n+q R1{True{}, st}:
      SC.loop_inv(q, ts, tt, e, K, E, BIG, SC.step(K, ts, tt, e, st), hk, SC.step_inv(ts, tt, e, K, E, BIG, st, hk, P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(True{}), SC.room4(K, st)), h), P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(True{}), SC.room4(K, st)), h)))

law SC.r4pp:
  for +K: N.SK
  for +st: ST
  for +hr: {SC.room4(K, st) == True{} : Bool}
  {U32.is_le(SC.pp(st), SC.w1(K)) == True{} : Bool}

def SC.r4pp(K, st, hr):
  match K st:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap} ST{tl, tb, tv, tio, p, mm, rc, rl, lck, last, nio, cont}:
      SC.r4p(p, w1, hr)

law SC.kf_okE:
  for +K: N.SK
  for +e: EM_.ET
  for +E: U32
  for +BIG: U32
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  {SC.okE(K, E) == True{} : Bool}

def SC.kf_okE(K, e, E, BIG, hk):
  match K:
    case N.SK{slen, w0, w1, cpl, lsh, lmask, ssh, smask, cap}:
      SC.and_tt(Cmp.is_le(Nat.cmp(Nat.add(V.U.N(slen), 4n), V.U.N(E))), Cmp.is_le(Nat.cmp(Nat.add(V.U.N(w1), 4n), V.U.N(E))), SC.kv.sE(e, slen, w0, w1, cpl, E, BIG, hk),
        P.Nat.le_trans(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n), V.U.N(E), (%Equal.sym(Cmp, Nat.cmp(Nat.add(V.U.N(w1), 4n), Nat.add(V.U.N(w1), 9n)), Nat.cmp(4n, 9n), P.Nat.cmp_add_l(V.U.N(w1), 4n, 9n)) : {Cmp.is_le(_) == True{} : Bool}; {==}), SC.kv.wE(e, slen, w0, w1, cpl, E, BIG, hk)))

# The scan loop, as code.
law SC.loop_code:
  for +k: Nat
  for +ts: A.Tr
  for +tt: A.Tr
  for +e: EM_.ET
  for +K: N.SK
  for +E: U32
  for +BIG: U32
  for +r: R1
  for +hk: {SC.kf(K, e, E, BIG) == True{} : Bool}
  for +h: {SC.LI(K, ts, tt, r) == True{} : Bool}
  {N.sc.loop(k, K, SC.b(ts, tt, e, r)) == SC.sc(ts, tt, e, SC.loop(k, K, ts, tt, e, r)) : N.Sc}

def SC.loop_code(k, ts, tt, e, K, E, BIG, r, hk, h):
  match k r:
    case 0n R1{g, st}:
      {==}
    case 1n+q R1{False{}, st}:
      {==}
    case 1n+q R1{True{}, st}:
      %Equal.sym(Bool & N.Sc, N.sc.step(K, SC.sc(ts, tt, e, st)), SC.b(ts, tt, e, SC.step(K, ts, tt, e, st)), SC.step_code(ts, tt, e, K, E, st, SC.r4pp(K, st, P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(True{}), SC.room4(K, st)), h)), SC.kf_okE(K, e, E, BIG, hk))) :
        {N.sc.loop(q, K, _) == SC.sc(ts, tt, e, SC.loop(q, K, ts, tt, e, SC.step(K, ts, tt, e, st))) : N.Sc}
      SC.loop_code(q, ts, tt, e, K, E, BIG, SC.step(K, ts, tt, e, st), hk, SC.step_inv(ts, tt, e, K, E, BIG, st, hk, P.Bool.and_l(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(True{}), SC.room4(K, st)), h), P.Bool.and_r(SC.Is(K, ts, tt, 0n, st), Bool.or(Bool.not(True{}), SC.room4(K, st)), h)))
