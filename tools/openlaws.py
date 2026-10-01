#!/usr/bin/env python3
"""Lists the laws of Bend files that have no def proving them."""
import re, sys
for path in sys.argv[1:]:
    s = open(path).read()
    laws = re.findall(r'^law ([\w.]+)', s, re.M)
    defs = set(re.findall(r'^def ([\w.]+)', s, re.M))
    for l in laws:
        if l not in defs:
            print(f'{path}: {l}')
    for m in re.finditer(r'\?\w+', s):
        line = s.count('\n', 0, m.start()) + 1
        print(f'{path}:{line}: {m.group(0)}')
