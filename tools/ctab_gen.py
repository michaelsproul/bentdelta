# Generates proofs/ctab.bp: the code-table facts for op.single / op.double.
# usage: python3 tools/ctab_gen.py proofs/ctab.bp proofs/ctab.bp
# (it keeps the header of the given file, up to its first law)
import sys

src = open(sys.argv[1]).read()
HEAD = src[:src.index("\nlaw ")].rstrip() + "\n"

def le(a, b): return f"{{Cmp.is_le(Nat.cmp({a}, {b})) == True{{}} : Bool}}"
def rwlit(v, L, ek): return f"@rwx V.U.eq_N({v}, {L}, {ek}) : {{{v} == {L} : U32}}"

out = [HEAD]
W = out.append

# ---- ADD ----
GA = "{CT.S(N.op.single(1, size, 0), 1, size, 0) == True{} : Bool}"
W(f"""
law CT.add.e:
  for +size: U32
  for +k: Nat
  for +ek: {{V.U.N(size) == k : Nat}}
  for +hb: {le('k', '17n')}
  {GA}

def CT.add.e(size, k, ek, hb):
  match k:""")
for v in range(18):
    W(f"""    case {v}n:
      {rwlit('size', v, 'ek')}
      {{==}}""")
W("""    case 18n+r:
      @absurd hb
""")
W(f"""
law CT.add.c:
  for +size: U32
  for +c: Bool
  for +ec: {{U32.is_le(size, 17) == c : Bool}}
  {GA}

def CT.add.c(size, c, ec):
  match c:
    case True{{}}:
      CT.add.e(size, V.U.N(size), {{==}}, V.U.le_N(size, 17, ec))
    case False{{}}:
      @unfold N.op.single N.u32.pick
      @simp -CT.S
      @rwx ec : {{U32.is_le(size, 17) == False{{}} : Bool}}
      @simp -CT.S
      {{==}}

# An ADD alone.
law CT.add:
  for +size: U32
  {GA}

def CT.add(size):
  CT.add.c(size, U32.is_le(size, 17), {{==}})

# A RUN alone.
law CT.run:
  for +size: U32
  {{CT.S(N.op.single(2, size, 0), 2, size, 0) == True{{}} : Bool}}

def CT.run(size):
  {{==}}
""")

# ---- COPY ----
GC = "{CT.S(N.op.single(3, size, mode), 3, size, mode) == True{} : Bool}"
GCF = "{CT.S(U32.add(U32.add(19, U32.mul(16, mode)), 0), 3, size, mode) == True{} : Bool}"
W(f"""
law CT.copy.e:
  for +size: U32
  for +mode: U32
  for +ks: Nat
  for +km: Nat
  for +eks: {{V.U.N(size) == ks : Nat}}
  for +ekm: {{V.U.N(mode) == km : Nat}}
  for +lo: {le('4n', 'ks')}
  for +hi: {le('ks', '18n')}
  for +hm: {le('km', '8n')}
  {GC}

def CT.copy.e(size, mode, ks, km, eks, ekm, lo, hi, hm):
  match ks km:""")
for s in range(4):
    W(f"""    case {s}n _:
      @absurd lo""")
for s in range(4, 19):
    for m in range(9):
        W(f"""    case {s}n {m}n:
      {rwlit('size', s, 'eks')}
      {rwlit('mode', m, 'ekm')}
      {{==}}""")
    W(f"""    case {s}n 9n+r:
      @absurd hm""")
W("""    case 19n+r _:
      @absurd hi
""")
W(f"""
law CT.copy.f:
  for +size: U32
  for +mode: U32
  for +km: Nat
  for +ekm: {{V.U.N(mode) == km : Nat}}
  for +hm: {le('km', '8n')}
  {GCF}

def CT.copy.f(size, mode, km, ekm, hm):
  match km:""")
for m in range(9):
    W(f"""    case {m}n:
      {rwlit('mode', m, 'ekm')}
      {{==}}""")
W("""    case 9n+r:
      @absurd hm
""")
CB = "Bool.and(U32.is_le(4, size), U32.is_le(size, 18))"
W(f"""
law CT.copy.c:
  for +size: U32
  for +mode: U32
  for +hm: {le('V.U.N(mode)', '8n')}
  for +c: Bool
  for +ec: {{{CB} == c : Bool}}
  {GC}

def CT.copy.c(size, mode, hm, c, ec):
  match c:
    case True{{}}:
      CT.copy.e(size, mode, V.U.N(size), V.U.N(mode), {{==}}, {{==}},
        V.U.le_N(4, size, P.Bool.and_l(U32.is_le(4, size), U32.is_le(size, 18), ec)),
        V.U.le_N(size, 18, P.Bool.and_r(U32.is_le(4, size), U32.is_le(size, 18), ec)), hm)
    case False{{}}:
      @unfold N.op.single N.u32.pick
      @simp -CT.S
      @rwx ec : {{{CB} == False{{}} : Bool}}
      @simp -CT.S
      CT.copy.f(size, mode, V.U.N(mode), {{==}}, hm)

# A COPY alone.
law CT.copy:
  for +size: U32
  for +mode: U32
  for +hm: {le('V.U.N(mode)', '8n')}
  {GC}

def CT.copy(size, mode, hm):
  CT.copy.c(size, mode, hm, {CB}, {{==}})
""")

# ---- doubles ----
CA = "Bool.and(Bool.and(Bool.and(U32.is_eq(t, 1), U32.is_eq(size, 1)), U32.is_eq(pt, 3)), U32.is_eq(ps, 4))"
AC = "Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(t, 3), U32.is_le(4, size)), U32.is_le(size, 18)), U32.is_eq(pt, 1)), U32.is_le(1, ps)), U32.is_le(ps, 4))"
AC1 = f"Bool.and(Bool.and({AC}, U32.is_le(size, 6)), U32.is_le(mode, 5))"
AC2 = f"Bool.and(Bool.and({AC}, U32.is_eq(size, 4)), U32.is_ge(mode, 6))"
X1 = "U32.add(U32.add(U32.add(163, U32.mul(mode, 12)), U32.mul(U32.sub(ps, 1), 3)), U32.sub(size, 4))"
X2 = "U32.add(U32.add(235, U32.mul(U32.sub(mode, 6), 4)), U32.sub(ps, 1))"
def OPD(ca=CA, ac1=AC1, ac2=AC2):
    return f"Bool.pick(U32, {ca}, U32.add(247, pm), Bool.pick(U32, {ac1}, {X1}, Bool.pick(U32, {ac2}, {X2}, 0)))"
GDu = f"{{CT.D({OPD()}, pt, ps, pm, t, size, mode) == True{{}} : Bool}}"
GD = "{CT.D(N.op.double(pt, ps, pm, t, size, mode), pt, ps, pm, t, size, mode) == True{} : Bool}"
PARAMS = """  for +pt: U32
  for +ps: U32
  for +pm: U32
  for +t: U32
  for +size: U32
  for +mode: U32
"""
ARGS = "pt, ps, pm, t, size, mode"

def chain(conj, h):
    """Proofs of each conjunct of a left-nested Bool.and."""
    # conj: list of conjunct texts in order c1..cn; and-term is ((c1 & c2) & c3) ...
    terms = [conj[0]]
    for c in conj[1:]:
        terms.append(f"Bool.and({terms[-1]}, {c})")
    pf = {len(conj) - 1: h}
    for i in range(len(conj) - 1, 0, -1):
        pf[i - 1] = f"P.Bool.and_l({terms[i - 1]}, {conj[i]}, {pf[i]})"
    res = []
    for i in range(len(conj)):
        if i == 0:
            res.append(pf[0])
        else:
            res.append(f"P.Bool.and_r({terms[i - 1]}, {conj[i]}, {pf[i]})")
    return res

# copy then add: t = 1, size = 1, pt = 3, ps = 4.
cac = ["U32.is_eq(t, 1)", "U32.is_eq(size, 1)", "U32.is_eq(pt, 3)", "U32.is_eq(ps, 4)"]
pa = chain(cac, "eca")
W(f"""
law CT.dbl.a.e:
  for +pm: U32
  for +mode: U32
  for +k: Nat
  for +ek: {{V.U.N(pm) == k : Nat}}
  for +hb: {le('k', '8n')}
  {{CT.D({OPD().replace('(t,', '(1,').replace('(size,', '(1,').replace('(pt,', '(3,').replace('(ps,', '(4,').replace('U32.is_le(size', 'U32.is_le(1').replace('U32.sub(size', 'U32.sub(1').replace('U32.sub(ps', 'U32.sub(4').replace('U32.is_le(ps', 'U32.is_le(4').replace('U32.is_le(4, size)', 'U32.is_le(4, 1)').replace('U32.is_le(1, ps)', 'U32.is_le(1, 4)')}, 3, 4, pm, 1, 1, mode) == True{{}} : Bool}}

def CT.dbl.a.e(pm, mode, k, ek, hb):
  match k:""")
for v in range(9):
    W(f"""    case {v}n:
      {rwlit('pm', v, 'ek')}
      {{==}}""")
W("""    case 9n+r:
      @absurd hb
""")

# add then copy, sizes 4-6, modes 0-5.
acc = ["U32.is_eq(t, 3)", "U32.is_le(4, size)", "U32.is_le(size, 18)", "U32.is_eq(pt, 1)", "U32.is_le(1, ps)", "U32.is_le(ps, 4)", "U32.is_le(size, 6)", "U32.is_le(mode, 5)"]
acc2 = acc[:6] + ["U32.is_eq(size, 4)", "U32.is_ge(mode, 6)"]
GD3 = f"{{CT.D({OPD()}, 1, ps, pm, 3, size, mode) == True{{}} : Bool}}"
def sub_tpt(s):
    return s
W(f"""
law CT.dbl.b.e:
  for +pt: U32
  for +ps: U32
  for +pm: U32
  for +t: U32
  for +size: U32
  for +mode: U32
  for +ks: Nat
  for +kp: Nat
  for +km: Nat
  for +eks: {{V.U.N(size) == ks : Nat}}
  for +ekp: {{V.U.N(ps) == kp : Nat}}
  for +ekm: {{V.U.N(mode) == km : Nat}}
  for +et: {{t == 3 : U32}}
  for +ept: {{pt == 1 : U32}}
  for +slo: {le('4n', 'ks')}
  for +shi: {le('ks', '6n')}
  for +plo: {le('1n', 'kp')}
  for +phi: {le('kp', '4n')}
  for +mhi: {le('km', '5n')}
  {GD}

def CT.dbl.b.e(pt, ps, pm, t, size, mode, ks, kp, km, eks, ekp, ekm, et, ept, slo, shi, plo, phi, mhi):
  match ks kp km:""")
for s in range(4):
    W(f"""    case {s}n _ _:
      @absurd slo""")
for s in range(4, 7):
    W(f"""    case {s}n 0n _:
      @absurd plo""")
    for p in range(1, 5):
        for m in range(6):
            W(f"""    case {s}n {p}n {m}n:
      @rwx et : {{t == 3 : U32}}
      @rwx ept : {{pt == 1 : U32}}
      {rwlit('size', s, 'eks')}
      {rwlit('ps', p, 'ekp')}
      {rwlit('mode', m, 'ekm')}
      {{==}}""")
        W(f"""    case {s}n {p}n 6n+r:
      @absurd mhi""")
    W(f"""    case {s}n 5n+r _:
      @absurd phi""")
W("""    case 7n+r _ _:
      @absurd shi
""")
W(f"""
law CT.dbl.c.e:
  for +pt: U32
  for +ps: U32
  for +pm: U32
  for +t: U32
  for +size: U32
  for +mode: U32
  for +kp: Nat
  for +km: Nat
  for +ekp: {{V.U.N(ps) == kp : Nat}}
  for +ekm: {{V.U.N(mode) == km : Nat}}
  for +et: {{t == 3 : U32}}
  for +ept: {{pt == 1 : U32}}
  for +es: {{size == 4 : U32}}
  for +plo: {le('1n', 'kp')}
  for +phi: {le('kp', '4n')}
  for +mlo: {le('6n', 'km')}
  for +mhi: {le('km', '8n')}
  {GD}

def CT.dbl.c.e(pt, ps, pm, t, size, mode, kp, km, ekp, ekm, et, ept, es, plo, phi, mlo, mhi):
  match kp km:
    case 0n _:
      @absurd plo""")
for p in range(1, 5):
    for m in range(6):
        W(f"""    case {p}n {m}n:
      @absurd mlo""")
    for m in range(6, 9):
        W(f"""    case {p}n {m}n:
      @rwx et : {{t == 3 : U32}}
      @rwx ept : {{pt == 1 : U32}}
      @rwx es : {{size == 4 : U32}}
      {rwlit('ps', p, 'ekp')}
      {rwlit('mode', m, 'ekm')}
      {{==}}""")
    W(f"""    case {p}n 9n+r:
      @absurd mhi""")
W("""    case 5n+r _:
      @absurd phi
""")

# the selector
pb = chain(acc, "ec1")
pc = chain(acc2, "ec2")
HD = f"{{U32.is_ne({OPD()}, 0) == True{{}} : Bool}}"
W(f"""
law CT.dbl.c:
{PARAMS}  for +hd: {HD}
  for +hm: {le('V.U.N(mode)', '8n')}
  for +eca: {{{CA} == False{{}} : Bool}}
  for +ec1: {{{AC1} == False{{}} : Bool}}
  for +c2: Bool
  for +ec2: {{{AC2} == c2 : Bool}}
  {GDu}

def CT.dbl.c({ARGS}, hd, hm, eca, ec1, c2, ec2):
  match c2:
    case True{{}}:
      @fold N.op.double
      CT.dbl.c.e({ARGS}, V.U.N(ps), V.U.N(mode), {{==}}, {{==}},
        V.U.is_eq(t, 3, {pc[0]}), V.U.is_eq(pt, 1, {pc[3]}), V.U.is_eq(size, 4, {pc[6]}),
        V.U.le_N(1, ps, {pc[4]}), V.U.le_N(ps, 4, {pc[5]}),
        V.U.le_N(6, mode, V.U.ge_le(mode, 6, {pc[7]})), hm)
    case False{{}}:
      @absurd (%ec2 : {{U32.is_ne(Bool.pick(U32, False{{}}, U32.add(247, pm), Bool.pick(U32, False{{}}, {X1}, Bool.pick(U32, _, {X2}, 0))), 0) == True{{}} : Bool}};
        (%ec1 : {{U32.is_ne(Bool.pick(U32, False{{}}, U32.add(247, pm), Bool.pick(U32, _, {X1}, Bool.pick(U32, {AC2}, {X2}, 0))), 0) == True{{}} : Bool}};
          (%eca : {{U32.is_ne(Bool.pick(U32, _, U32.add(247, pm), Bool.pick(U32, {AC1}, {X1}, Bool.pick(U32, {AC2}, {X2}, 0))), 0) == True{{}} : Bool}}; hd)))

law CT.dbl.b:
{PARAMS}  for +hd: {HD}
  for +hm: {le('V.U.N(mode)', '8n')}
  for +eca: {{{CA} == False{{}} : Bool}}
  for +c1: Bool
  for +ec1: {{{AC1} == c1 : Bool}}
  {GDu}

def CT.dbl.b({ARGS}, hd, hm, eca, c1, ec1):
  match c1:
    case True{{}}:
      @fold N.op.double
      CT.dbl.b.e({ARGS}, V.U.N(size), V.U.N(ps), V.U.N(mode), {{==}}, {{==}}, {{==}},
        V.U.is_eq(t, 3, {pb[0]}), V.U.is_eq(pt, 1, {pb[3]}),
        V.U.le_N(4, size, {pb[1]}), V.U.le_N(size, 6, {pb[6]}),
        V.U.le_N(1, ps, {pb[4]}), V.U.le_N(ps, 4, {pb[5]}),
        V.U.le_N(mode, 5, {pb[7]}))
    case False{{}}:
      CT.dbl.c({ARGS}, hd, hm, eca, ec1, {AC2}, {{==}})

law CT.dbl.a:
{PARAMS}  for +hd: {HD}
  for +hpm: {le('V.U.N(pm)', '8n')}
  for +hm: {le('V.U.N(mode)', '8n')}
  for +ca: Bool
  for +eca: {{{CA} == ca : Bool}}
  {GDu}

def CT.dbl.a({ARGS}, hd, hpm, hm, ca, eca):
  match ca:
    case True{{}}:
      @rwx V.U.is_eq(t, 1, {pa[0]}) : {{t == 1 : U32}}
      @rwx V.U.is_eq(size, 1, {pa[1]}) : {{size == 1 : U32}}
      @rwx V.U.is_eq(pt, 3, {pa[2]}) : {{pt == 3 : U32}}
      @rwx V.U.is_eq(ps, 4, {pa[3]}) : {{ps == 4 : U32}}
      @simp -CT.D
      CT.dbl.a.e(pm, mode, V.U.N(pm), {{==}}, hpm)
    case False{{}}:
      CT.dbl.b({ARGS}, hd, hm, eca, {AC1}, {{==}})

# Two instructions as one double opcode.
law CT.dbl:
{PARAMS}  for +hd: {{U32.is_ne(N.op.double(pt, ps, pm, t, size, mode), 0) == True{{}} : Bool}}
  for +hpm: {le('V.U.N(pm)', '8n')}
  for +hm: {le('V.U.N(mode)', '8n')}
  {GD}

def CT.dbl({ARGS}, hd, hpm, hm):
  @unfold N.op.double N.u32.pick
  @simp -CT.D
  CT.dbl.a({ARGS}, hd, hpm, hm, {CA}, {{==}})
""")

# ---- the decoder's table ----
def half(t, sz, m): return t | (sz << 2) | (m << 10)
def pair(h1, h2): return h1 | (h2 << 16)
def entry(op):
    if op == 0: return pair(half(2, 0, 0), 0)
    if op < 19: return pair(half(1, op - 1, 0), 0)
    if op < 163:
        k = op - 19; sz = k % 16
        return pair(half(3, 0 if sz == 0 else sz + 3, k // 16), 0)
    if op < 235:
        k = op - 163; r = k % 12
        return pair(half(1, r // 3 + 1, 0), half(3, r % 3 + 4, k // 12))
    if op < 247:
        k = op - 235
        return pair(half(1, k % 4 + 1, 0), half(3, 4, k // 4 + 6))
    k = op - 247
    return pair(half(3, 4, k), half(1, 1, 0))
def tree(lo, n):
    if n == 1: return f"A.TL{{{entry(lo)}}}"
    h = n // 2
    return f"A.TN{{{tree(lo, h)}, {tree(lo + h, h)}}}"
W(f"""
# The code table, as a tree.
def CT.TT() -> A.Tr:
  {tree(0, 256)}

law CT.tt:
  {{A.A.to(D.ct.table()) == CT.TT() : A.Tr}}

def CT.tt():
  {{==}}

law CT.tab.e:
  for +c: U32
  for +k: Nat
  for +ek: {{V.U.N(c) == k : Nat}}
  for +hb: {{Cmp.is_le(Nat.cmp(k, 255n)) == True{{}} : Bool}}
  {{A.T.word(CT.TT(), c) == D.ct.entry(c) : U32}}

def CT.tab.e(c, k, ek, hb):
  match k:""")
for v in range(256):
    W(f"""    case {v}n:
      {rwlit('c', v, 'ek')}
      {{==}}""")
W("""    case 256n+r:
      @absurd hb

# The decoder's table holds the code table.
law CT.tab:
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {A.T.word(A.A.to(D.ct.table()), c) == D.ct.entry(c) : U32}

def CT.tab(c, hc):
  @rw CT.tt()
  CT.tab.e(c, V.U.N(c), {==}, P.Nat.lt_succ_le(V.U.N(c), 255n, V.U.lt_N(c, 256, hc)))
""")
open(sys.argv[2], 'w').write('\n'.join(out))
