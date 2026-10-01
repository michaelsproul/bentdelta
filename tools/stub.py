#!/usr/bin/env python3
"""tools/stub.py proofs/a.bend ...: writes proofs/stub/a.bend for each proof
file with every law's proof replaced by STUB.cheat (an @unsafe placeholder
of any type), and its imports of the other listed files pointed at their
stubs. A file that imports stubs checks in seconds; it proves nothing until
it is checked against the real files."""
import os, re, sys

files = sys.argv[1:]
names = {os.path.basename(f) for f in files}

def blocks(lines):
    out, cur = [], None
    for l in lines:
        if l and not l[0].isspace() and not l.startswith('#'):
            m = re.match(r'(@unsafe\s+)?(def|law|type)\s+([^(\s:<]+)', l)
            cur = [m.group(2) if m else 'other', m.group(3) if m else None, [l]]
            out.append(cur)
        elif cur is None:
            cur = ['other', None, [l]]
            out.append(cur)
        else:
            cur[2].append(l)
    return out

CHEAT = """
@unsafe def STUB.cheat(-A: Type) -> A:
  STUB.cheat(A)
"""
for f in files:
    out = os.path.join(os.path.dirname(f), 'stub')
    os.makedirs(out, exist_ok=True)
    bs = blocks(open(f).read().split('\n'))
    stmt = {}
    for b in bs:
        if b[0] == 'law':
            items = []
            for l in b[2][1:]:
                if not l.strip() or l.strip().startswith('#'):
                    continue
                if len(l) - len(l.lstrip()) == 2:
                    items.append(l.strip())
                else:
                    items[-1] += ' ' + l.strip()
            stmt[b[1]] = next(t for t in items if not t.startswith('for '))
    res = []
    for b in bs:
        if b[0] == 'def' and b[1] in stmt:
            m = re.match(r'def [^(\s]+\(([^)]*)\)\s*:\s*$', b[2][0])
            if m:
                res += [b[2][0], f'  STUB.cheat({stmt[b[1]]})', '']
                continue
        for l in b[2]:
            m = re.match(r'import \./(\S+) as (.*)', l)
            u = re.match(r'import \.\./(\S+) as (.*)', l)
            if m:
                l = f'import ./{m.group(1)} as {m.group(2)}' if m.group(1) in names else f'import ../{m.group(1)} as {m.group(2)}'
            elif u:
                l = f'import ../../{u.group(1)} as {u.group(2)}'
            res.append(l)
    k = max(i for i, l in enumerate(res) if l.startswith('import '))
    res[k + 1:k + 1] = CHEAT.split('\n')
    open(os.path.join(out, os.path.basename(f)), 'w').write('\n'.join(res))
