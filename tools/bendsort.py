#!/usr/bin/env python3
"""Reorders the top-level items of a Bend file so every def comes after the
defs it uses (Bend requires a def to be declared before its callers).

The order is otherwise kept: the earliest item whose dependencies are all
placed goes next. Comment lines directly above an item move with it.

usage: tools/bendsort.py file.bend [...]   (rewrites the files in place)
"""
import re
import sys

ITEM = re.compile(r'^(def|type|law|@unsafe)\b')
NAME = re.compile(r'^(?:@unsafe\s+)?(?:def|type|law)\s+([A-Za-z_][\w.]*[?]?)')
IDENT = re.compile(r'[A-Za-z_][\w.]*')


def split(text):
    lines = text.split('\n')
    head, items, cur, pending = [], [], None, []
    for line in lines:
        if ITEM.match(line):
            if cur is not None:
                items.append(cur)
            cur = pending + [line]
            pending = []
        elif cur is None:
            if line.startswith('#'):
                pending.append(line)
            else:
                head.extend(pending)
                pending = []
                head.append(line)
        else:
            if line.startswith('#'):
                pending.append(line)
            elif line.strip() == '' and pending:
                pending.append(line)
            elif line.strip() == '':
                cur.append(line)
            else:
                cur.extend(pending)
                pending = []
                cur.append(line)
    if cur is not None:
        items.append(cur)
    tail = pending
    return head, items, tail


def main():
    for path in sys.argv[1:]:
        text = open(path).read()
        head, items, tail = split(text)
        names = []
        for it in items:
            line = next(l for l in it if ITEM.match(l))
            m = NAME.match(line)
            names.append((line.split()[0] if not line.startswith('@') else 'def', m.group(1) if m else None))
        defs = {n: i for i, (k, n) in enumerate(names) if k == 'def' and n}
        deps = []
        for i, it in enumerate(items):
            body = '\n'.join(l for l in it if not l.startswith('#'))
            body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', body)
            refs = set()
            k, n = names[i]
            for tok in IDENT.findall(body):
                j = defs.get(tok)
                if j is not None and j != i and not (k == 'law' and tok == n):
                    refs.add(j)
            # a law's proof (a def of the same name) comes after the law
            k, n = names[i]
            if k == 'def' and n:
                for j, (k2, n2) in enumerate(names):
                    if k2 == 'law' and n2 == n:
                        refs.add(j)
            deps.append(refs)
        placed, order = set(), []
        while len(order) < len(items):
            for i in range(len(items)):
                if i not in placed and deps[i] <= placed:
                    placed.add(i)
                    order.append(i)
                    break
            else:
                left = [names[i][1] for i in range(len(items)) if i not in placed]
                sys.exit(f'{path}: cyclic definitions among {left}')
        out = list(head)
        for i in order:
            it = items[i]
            while it and it[-1].strip() == '':
                it = it[:-1]
            if out and out[-1].strip() != '':
                out.append('')
            out.extend(it)
            out.append('')
        out.extend(tail)
        res = '\n'.join(out).rstrip('\n') + '\n'
        if res != text:
            open(path, 'w').write(res)


main()
