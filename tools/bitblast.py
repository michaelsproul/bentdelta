#!/usr/bin/env python3
"""bitblast: proofs of bitwise U32 identities, a bit at a time.

An identity {lhs == rhs : U32} over U32 variables, built from and, or, xor,
not and shifts by constant amounts (and single-term defs that unfold to
them), holds when each of its 32 bits does. For each bit k the proof takes
the variables apart into their bits and splits on the few bits that bit k
of either side depends on; every case then computes.

A spec file lists identities, after a header of imports:

  import ...                      (copied to the output)
  id NAME x y                     (the identity's name and U32 variables)
    lhs TERM
    rhs TERM

usage: tools/bitblast.py spec out.bend
The output needs `./u32.bend as V` and `./word.bend as W` among its imports.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bpp  # noqa: E402


# Bits: ('c', bool) or ('s', frozenset of variable bits) for a stuck term.

def c(b):
    return ('c', b)


def deps(x):
    return x[1] if x[0] == 's' else frozenset()


def b_and(a, b):
    if a[0] == 'c':
        return b if a[1] else c(False)
    return ('s', deps(a) | deps(b))


def b_or(a, b):
    if a[0] == 'c':
        return c(True) if a[1] else b
    return ('s', deps(a) | deps(b))


def b_xor(a, b):
    if a[0] == 'c':
        return b_not(b) if a[1] else b
    return ('s', deps(a) | deps(b))


def b_not(a):
    if a[0] == 'c':
        return c(not a[1])
    return a


def nat(e):
    if e[0] == 'lit' and re.fullmatch(r'\d+n', e[1]):
        return int(e[1][:-1])
    if e[0] == 'call' and e[1] in ('Nat.sub', 'Nat.add', 'Nat.mul'):
        a, b = nat(e[2][0]), nat(e[2][1])
        return {'Nat.sub': max(0, a - b), 'Nat.add': a + b, 'Nat.mul': a * b}[e[1]]
    if e[0] == 'succ':
        return int(e[1][:-1]) + nat(e[2])
    raise bpp.Err(f"not a constant Nat: {bpp.show(e)}")


class Sim:
    def __init__(self, cur, words):
        self.cur = cur
        self.words = words      # variable -> bit names

    def word(self, e):
        k = e[0]
        if k == 'var':
            if e[1] in self.words:
                return [('s', frozenset([b])) for b in self.words[e[1]]]
            raise bpp.Err(f"unknown word {e[1]}")
        if k == 'lit':
            v = int(e[1])
            return [c(bool(v >> i & 1)) for i in range(32)]
        if k == 'call':
            f, args = e[1], e[2]
            if f in ('U32.and', 'U32.or', 'U32.xor'):
                a, b = self.word(args[0]), self.word(args[1])
                op = {'U32.and': b_and, 'U32.or': b_or, 'U32.xor': b_xor}[f]
                return [op(x, y) for x, y in zip(a, b)]
            if f == 'U32.not':
                return [b_not(x) for x in self.word(args[0])]
            if f == 'U32.shl':
                a = self.word(args[0])
                return [c(False)] + a[:-1]
            if f == 'U32.shr':
                a = self.word(args[0])
                return a[1:] + [c(False)]
            if f in ('U32.shln', 'U32.shrn'):
                a = self.word(args[0])
                n = nat(args[1])
                for _ in range(n):
                    a = [c(False)] + a[:-1] if f == 'U32.shln' else a[1:] + [c(False)]
                return a
            try:
                ps, body = bpp.def_body(self.cur, f)
            except bpp.Err:
                raise bpp.Err(f"cannot blast {f}")
            t = bpp.run_body(body, dict(zip(ps, args)))
            if t is None:
                raise bpp.Err(f"cannot blast {f}")
            return self.word(t)
        raise bpp.Err(f"cannot blast {bpp.show(e)}")


def pattern(bits):
    s = 'WNil{}'
    for b in reversed(bits):
        s = f'WCon{{{b}, {s}}}'
    return f'U32{{{s}}}'


def gen(cur, name, vs, lhs, rhs):
    words = {v: [f'{v}_{i}' for i in range(32)] for v in vs}
    order = [b for v in vs for b in words[v]]
    sim = Sim(cur, words)
    L, R = sim.word(lhs), sim.word(rhs)
    L_, R_ = bpp.show(lhs), bpp.show(rhs)
    params = ', '.join(f'+{v}: U32' for v in vs)
    args = ', '.join(vs)
    out = []
    out.append(f'law {name}:')
    for v in vs:
        out.append(f'  for +{v}: U32')
    out.append(f'  {{{L_} == {R_} : U32}}')
    out.append('')
    # one def takes every bit as a parameter, so it can split on them
    env = {v: bpp.parse(pattern(words[v])) for v in vs}
    hl = bpp.show(bpp.subst(lhs, env))
    hr = bpp.show(bpp.subst(rhs, env))
    bits = ', '.join(f'+{b}: Bool' for b in order)
    out.append(f'def {name}.h(+k: Nat, {bits}) ->')
    out.append(f'  {{V.U.bit({hl}, k) == V.U.bit({hr}, k) : Bool}}:')
    out.append('  match k:')
    for k in range(32):
        out.append(f'    case {k}n:')
        a, b = L[k], R[k]
        if a[0] == 'c' and b[0] == 'c':
            if a[1] != b[1]:
                raise bpp.Err(f"{name}: bit {k} differs")
            out.append('      {==}')
            continue
        ds = sorted(deps(a) | deps(b), key=order.index)
        if len(ds) > 6:
            raise bpp.Err(f"{name}: bit {k} depends on {len(ds)} bits")
        out.append(f'      match {" ".join(ds)}:')
        for m in range(1 << len(ds)):
            pp = ' '.join('True{}' if m >> (len(ds) - 1 - i) & 1 else 'False{}' for i in range(len(ds)))
            out.append(f'        case {pp}:')
            out.append('          {==}')
    out.append('    case 32n+j:')
    out.append('      {==}')
    out.append('')
    out.append(f'def {name}.b(+k: Nat, {params}) ->')
    out.append(f'  {{V.U.bit({L_}, k) == V.U.bit({R_}, k) : Bool}}:')
    out.append(f'  match {" ".join(vs)}:')
    out.append('    case ' + ' '.join(pattern(words[v]) for v in vs) + ':')
    out.append(f'      {name}.h(k, {", ".join(order)})')
    out.append('')
    out.append(f'def {name}.all({params}, +k: Nat) -> V.U.allb({L_}, {R_}, k):')
    out.append('  match k:')
    out.append('    case 0n:')
    out.append('      Unit{}')
    out.append('    case 1n+j:')
    out.append(f'      W.W.allb.con({{V.U.bit({L_}, j) == V.U.bit({R_}, j) : Bool}},')
    out.append(f'        V.U.allb({L_}, {R_}, j), {name}.b(j, {args}), {name}.all({args}, j))')
    out.append('')
    out.append(f'def {name}({args}):')
    out.append(f'  V.U.ext({L_}, {R_}, {name}.all({args}, 32n))')
    out.append('')
    return '\n'.join(out)


def main():
    spec, dst = sys.argv[1], sys.argv[2]
    lines = open(spec).read().split('\n')
    header = [l for l in lines if l.startswith('import ')]
    cur = bpp.Module(dst, '\n'.join(header))
    bpp.MODULES[cur.path] = cur
    out = header + ['', '# Generated by tools/bitblast.py from ' + os.path.basename(spec) + '.', '']
    i = 0
    items = []
    while i < len(lines):
        l = lines[i].strip()
        if l.startswith('id '):
            parts = l.split()
            name, vs = parts[1], parts[2:]
            lhs = rhs = None
            doc = []
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith('id '):
                t = lines[j].strip()
                if t.startswith('lhs '):
                    lhs = t[4:]
                elif t.startswith('rhs '):
                    rhs = t[4:]
                elif t.startswith('#'):
                    doc.append(t)
                j += 1
            items.append((name, vs, lhs, rhs, doc))
            i = j
        else:
            i += 1
    for name, vs, lhs, rhs, doc in items:
        try:
            text = gen(cur, name, vs, bpp.parse(lhs), bpp.parse(rhs))
        except bpp.Err as e:
            print(f"bitblast: {name}: {e}", file=sys.stderr)
            sys.exit(1)
        out.extend(doc)
        out.append(text)
    open(dst, 'w').write('\n'.join(out))


if __name__ == '__main__':
    main()
