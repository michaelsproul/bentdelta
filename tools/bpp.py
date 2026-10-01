#!/usr/bin/env python3
"""bpp: expands rewrite steps in Bend proofs.

A proof written as a chain of rewrites spends most of its text on motives:
`%Equal.sym(T, a, b, L(x)) : {goal with _ where a was}`. bpp tracks the goal
of each def and writes those lines for it. In a def body:

  @rw L(args)        rewrites the left side of L's equation, instantiated
                     with args, into its right side, wherever it occurs
  @rw- L(args)       rewrites the right side into the left side
  @rwx E : {a == b : T}   the same with any proof E of the equation shown
  @rwx- E : {a == b : T}  b into a
  @goal G            restates the goal (to a form it is convertible with)
  @show              writes the goal as a comment

The goal of a def is its law's claim (the law of the same name), or the
type after `->`. A `match` on parameters replaces them by each case's
pattern. A plain `%e : P` line keeps the goal tracked when e is
`Equal.sym(T, x, y, ..)` (the goal becomes P with y in the holes), and
otherwise needs an @goal before the next step.

Lemmas are looked up through the file's imports, and their claims are
renamed into the file's namespace. Terms are compared after desugaring
operators: `(a + b : T)` is `T.add(a, b)`, and so on.

usage: tools/bpp.py in.bp [out.bend]    (default: in.bp with .bend)
"""
import os
import re
import sys


class Err(Exception):
    pass


# Tokens
# ======

PUNCT = ['.&.', '.|.', '.^.', '<<', '>>', '<=', '>=', '==', '!=', '=>', '<>', '<-',
         '&&', '||', '->', '(', ')', '{', '}', '[', ']', '<', '>', ',', ':',
         '&', '+', '-', '*', '/', '%', '?', '!', '@', '=', '^', '~', ';']
ID = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')
NUM = re.compile(r'\d+(\.\d+)?n?')
SUCC = re.compile(r'\d+n\+')
STR = re.compile(r'"(\\.|[^"\\])*"|\'(\\.|[^\'\\])*\'')


def tokenize(s):
    out = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c in ' \t\n\r':
            i += 1
            continue
        if c == '#':
            while i < n and s[i] != '\n':
                i += 1
            continue
        m = SUCC.match(s, i)
        if m:
            out.append(('succ', m.group(0)[:-1]))
            i = m.end()
            continue
        m = NUM.match(s, i)
        if m:
            out.append(('lit', m.group(0)))
            i = m.end()
            continue
        m = ID.match(s, i)
        if m:
            out.append(('id', m.group(0)))
            i = m.end()
            continue
        m = STR.match(s, i)
        if m:
            out.append(('lit', m.group(0)))
            i = m.end()
            continue
        for p in PUNCT:
            if s.startswith(p, i):
                if p == '<' and out and out[-1][0] == 'id' and i > 0 and s[i - 1] not in ' \t\n':
                    out.append(('gen', '<'))
                else:
                    out.append(('p', p))
                i += len(p)
                break
        else:
            raise Err(f"bad character {c!r} in {s[max(0, i - 20):i + 20]!r}")
    out.append(('end', None))
    return out


# Terms
# =====
#
# ('var', name) ('lit', text) ('hole',) ('call', head, args) ('ctor', name, args)
# ('gen', name, args) ('tuple', a, b) ('nil',) ('cons', h, t) ('succ', k, e)
# ('eq', a, b, T) ('neq', a, b, T) ('refl',) ('ann', e, T) ('pairT', a, b)
# ('arrow', a, b) ('pi', mod, x, A, B) ('sigma', x, A, B) ('lam', mods, body)
# ('arr', v, T, op, d) ('qhole', name) ('index', a, i)

OPS = {'+': 'add', '-': 'sub', '*': 'mul', '/': 'div', '%': 'mod',
       '.&.': 'and', '.|.': 'or', '.^.': 'xor', '<<': 'shln', '>>': 'shrn',
       '<': 'is_lt', '<=': 'is_le', '>': 'is_gt', '>=': 'is_ge'}


class Parser:
    def __init__(self, s):
        self.toks = tokenize(s)
        self.i = 0

    def peek(self, k=0):
        return self.toks[self.i + k]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def isp(self, p, k=0):
        t = self.peek(k)
        return t[0] == 'p' and t[1] == p

    def expect(self, p):
        t = self.next()
        if not (t[0] == 'p' and t[1] == p):
            raise Err(f"expected {p!r}, got {t!r} near {self.context()}")

    def context(self):
        return ' '.join(str(t[1]) for t in self.toks[max(0, self.i - 8):self.i + 8])

    def at_end(self):
        return self.peek()[0] == 'end'

    def expr(self):
        # lambda
        t = self.peek()
        if t[0] == 'id' and self.isp('=>', 1):
            self.next()
            self.next()
            return ('lam', t[1], self.expr())
        if t[0] == 'p' and t[1] in '+-' and self.peek(1)[0] == 'id' and self.isp('=>', 2):
            self.next()
            x = self.next()[1]
            self.next()
            return ('lam', x, self.expr())
        if self.isp('@'):
            self.next()
            mod = ''
            if self.isp('-') or self.isp('+'):
                mod = self.next()[1]
            x = self.next()[1]
            self.expect(':')
            A = self.arrow_lhs()
            self.expect('->')
            return ('pi', mod, x, A, self.expr())
        if self.isp('&') and self.peek(1)[0] == 'id' and self.isp(':', 2):
            self.next()
            x = self.next()[1]
            self.next()
            A = self.arrow_lhs()
            self.expect('->')
            return ('sigma', x, A, self.expr())
        a = self.arrow_lhs()
        if self.isp('->'):
            self.next()
            return ('arrow', a, self.expr())
        return a

    def arrow_lhs(self):
        return self.pairT()

    def pairT(self):
        a = self.boolop()
        if self.isp('&'):
            self.next()
            return ('pairT', a, self.pairT())
        return a

    def boolop(self):
        a = self.cons()
        while self.isp('&&') or self.isp('||'):
            op = self.next()[1]
            b = self.cons()
            a = ('call', 'Bool.and' if op == '&&' else 'Bool.or', (a, b))
        return a

    def cons(self):
        a = self.app()
        if self.isp('<>'):
            self.next()
            return ('cons', a, self.cons())
        return a

    def app(self):
        a = self.atom()
        while True:
            if self.isp('(') and a[0] in ('var', 'call', 'gen', 'index'):
                self.next()
                args = self.args(')')
                head = a[1] if a[0] == 'var' else a
                a = ('call', head, tuple(args))
            elif self.isp('{') and a[0] == 'var':
                self.next()
                args = self.args('}')
                a = ('ctor', a[1], tuple(args))
            elif self.peek()[0] == 'gen' and a[0] == 'var':
                self.next()
                args = self.genargs()
                a = ('gen', a[1], tuple(args))
            elif self.isp('[') and a[0] in ('var', 'call'):
                self.next()
                i = self.expr()
                self.expect(']')
                if self.isp('<-'):
                    self.next()
                    v = self.expr()
                    a = ('call', 'Array.set', (('var', 'U32'), a, i, v))
                else:
                    a = ('call', 'Array.get', (('var', 'U32'), a, i))
            elif self.isp('!') and self.isp('(', 1):
                self.next()
            else:
                break
        return a

    def args(self, close):
        out = []
        if self.isp(close):
            self.next()
            return out
        while True:
            out.append(self.expr())
            if self.isp(','):
                self.next()
                continue
            self.expect(close)
            return out

    def genargs(self):
        out = []
        while True:
            t = self.peek()
            if t[0] == 'p' and t[1] in ('&',) and self.peek(1)[0] == 'lit':
                self.next()
                out.append(('lit', '&' + self.next()[1]))
            else:
                out.append(self.expr())
            if self.isp(','):
                self.next()
                continue
            if self.isp('>'):
                self.next()
                return out
            if self.isp('>>'):
                # close this one and the enclosing one
                self.toks[self.i] = ('p', '>')
                return out
            raise Err(f"bad generic arguments near {self.context()}")

    def atom(self):
        t = self.next()
        k, v = t
        if k == 'id':
            if v == '_':
                return ('hole',)
            return ('var', v)
        if k == 'lit':
            return ('lit', v)
        if k == 'succ':
            return ('succ', v, self.app())
        if k == 'p':
            if v == '(':
                if self.isp(')'):
                    self.next()
                    return ('ctor', 'Unit', ())
                if self.isp('%'):
                    self.next()
                    eq = self.expr()
                    self.expect(':')
                    P = self.app()
                    if self.isp(';'):
                        self.next()
                    body = self.expr()
                    self.expect(')')
                    return ('rwt', eq, P, body)
                a = self.expr()
                if self.isp(','):
                    items = [a]
                    while self.isp(','):
                        self.next()
                        items.append(self.expr())
                    self.expect(')')
                    r = items[-1]
                    for x in reversed(items[:-1]):
                        r = ('tuple', x, r)
                    return r
                if self.isp(')'):
                    self.next()
                    return a
                t2 = self.peek()
                if t2[0] == 'p' and t2[1] in OPS:
                    op = self.next()[1]
                    b = self.expr()
                    self.expect(':')
                    T = self.expr()
                    self.expect(')')
                    if T[0] != 'var':
                        raise Err(f"operator type must be a name near {self.context()}")
                    return ('call', T[1] + '.' + OPS[op], (a, b))
                if t2[0] == 'p' and t2[1] == ':':
                    self.next()
                    T = self.expr()
                    self.expect(')')
                    return ('ann', a, T)
                raise Err(f"bad parenthesized term near {self.context()}")
            if v == '{':
                if self.isp('==') and self.isp('}', 1):
                    self.next()
                    self.next()
                    return ('refl',)
                a = self.expr()
                if self.isp('==') or self.isp('!='):
                    op = self.next()[1]
                    b = self.expr()
                    self.expect(':')
                    T = self.expr()
                    self.expect('}')
                    return ('eq' if op == '==' else 'neq', a, b, T)
                self.expect(':')
                T = self.expr()
                self.expect('}')
                return ('ann', a, T)
            if v == '[':
                if self.isp(']'):
                    self.next()
                    return ('nil',)
                a = self.expr()
                if self.isp(':'):
                    self.next()
                    T = self.app()
                    op = self.next()[1]
                    d = self.app()
                    self.expect(']')
                    return ('arr', a, T, op, d)
                items = [a]
                while self.isp(','):
                    self.next()
                    items.append(self.expr())
                self.expect(']')
                r = ('nil',)
                for x in reversed(items):
                    r = ('cons', x, r)
                return r
            if v == '?':
                return ('qhole', self.next()[1])
            if v in ('+', '-') and self.peek()[0] == 'id':
                # a pattern binder
                return ('var', self.next()[1])
            if v == '&' and self.peek()[0] == 'lit':
                return ('lit', '&' + self.next()[1])
        raise Err(f"unexpected {t!r} near {self.context()}")


def parse(s):
    p = Parser(s)
    e = p.expr()
    if not p.at_end():
        raise Err(f"trailing text after term near {p.context()}")
    return norm(e)


def norm(e):
    """Canonical forms: Tuple{a, b} is (a, b), Nil{} and Con{h, t} lists."""
    if not isinstance(e, tuple) or not e:
        return e
    e = tuple(norm(x) if isinstance(x, tuple) else x for x in e)
    if e[0] == 'succ':
        k = int(e[1][:-1])
        if e[2][0] == 'lit' and re.fullmatch(r'\d+n', e[2][1]):
            return ('lit', f"{k + int(e[2][1][:-1])}n")
        if e[2][0] == 'succ':
            return ('succ', f"{k + int(e[2][1][:-1])}n", e[2][2])
    if e[0] == 'ctor':
        if e[1] == 'Tuple' and len(e[2]) == 2:
            return ('tuple', e[2][0], e[2][1])
        if e[1] == 'Nil' and len(e[2]) == 0:
            return ('nil',)
        if e[1] == 'Con' and len(e[2]) == 2:
            return ('cons', e[2][0], e[2][1])
    return e


def show(e):
    k = e[0]
    if k == 'var':
        return e[1]
    if k == 'lit':
        return e[1]
    if k == 'hole':
        return '_'
    if k == 'qhole':
        return '?' + e[1]
    if k == 'call':
        head = e[1] if isinstance(e[1], str) else show(e[1])
        return head + '(' + ', '.join(show(a) for a in e[2]) + ')'
    if k == 'ctor':
        return e[1] + '{' + ', '.join(show(a) for a in e[2]) + '}'
    if k == 'gen':
        return e[1] + '<' + ', '.join(show(a) for a in e[2]) + '>'
    if k == 'tuple':
        return '(' + show(e[1]) + ', ' + show(e[2]) + ')'
    if k == 'nil':
        return '[]'
    if k == 'cons':
        h = show(e[1])
        if e[1][0] in ('cons', 'lam', 'arrow', 'pairT'):
            h = '(' + h + ')'
        return h + ' <> ' + show(e[2])
    if k == 'succ':
        inner = show(e[2])
        if e[2][0] in ('cons', 'lam', 'arrow', 'pairT'):
            inner = '(' + inner + ')'
        return e[1] + '+' + inner
    if k == 'eq':
        return '{' + show(e[1]) + ' == ' + show(e[2]) + ' : ' + show(e[3]) + '}'
    if k == 'neq':
        return '{' + show(e[1]) + ' != ' + show(e[2]) + ' : ' + show(e[3]) + '}'
    if k == 'refl':
        return '{==}'
    if k == 'ann':
        return '{' + show(e[1]) + ' : ' + show(e[2]) + '}'
    if k == 'pairT':
        a = show(e[1])
        if e[1][0] in ('pairT', 'arrow', 'lam'):
            a = '(' + a + ')'
        return a + ' & ' + show(e[2])
    if k == 'arrow':
        a = show(e[1])
        if e[1][0] in ('arrow', 'lam', 'pi', 'sigma'):
            a = '(' + a + ')'
        return a + ' -> ' + show(e[2])
    if k == 'pi':
        return '@' + e[1] + e[2] + ':' + show(e[3]) + ' -> ' + show(e[4])
    if k == 'sigma':
        return '&' + e[1] + ':' + show(e[2]) + ' -> ' + show(e[3])
    if k == 'lam':
        return e[1] + ' => ' + show(e[2])
    if k == 'arr':
        return '[' + show(e[1]) + ' : ' + show(e[2]) + e[3] + show(e[4]) + ']'
    if k == 'rwt':
        return '(%' + show(e[1]) + ' : ' + show(e[2]) + '; ' + show(e[3]) + ')'
    raise Err(f"cannot show {e!r}")


def subterms_replace(e, old, new, only=None, seen=None):
    """e with every occurrence of old replaced by new (or only the ones
    numbered in only, from 1, in order); and the count replaced."""
    if seen is None:
        seen = [0]
    if e == old:
        seen[0] += 1
        if only is None or seen[0] in only:
            return new, 1
        return e, 0
    if not isinstance(e, tuple):
        return e, 0
    n = 0
    out = []
    for x in e:
        if isinstance(x, tuple):
            y, c = subterms_replace(x, old, new, only, seen)
            n += c
            out.append(y)
        else:
            out.append(x)
    return tuple(out), n


def subst(e, env, bound=()):
    """Replaces free variables (by name) by terms."""
    if not isinstance(e, tuple) or not e:
        return e
    k = e[0]
    if k == 'var':
        return env.get(e[1], e) if e[1] not in bound else e
    if k == 'lam':
        return ('lam', e[1], subst(e[2], env, bound + (e[1],)))
    if k == 'pi':
        return ('pi', e[1], e[2], subst(e[3], env, bound), subst(e[4], env, bound + (e[2],)))
    if k == 'sigma':
        return ('sigma', e[1], subst(e[2], env, bound), subst(e[3], env, bound + (e[1],)))
    if k == 'call':
        head = e[1]
        if isinstance(head, str):
            if head in env and head not in bound:
                h = env[head]
                head = h[1] if h[0] == 'var' else h
        else:
            head = subst(head, env, bound)
        return ('call', head, tuple(subst(a, env, bound) for a in e[2]))
    return tuple(subst(x, env, bound) if isinstance(x, tuple) else x for x in e)


def rename(e, f):
    """Applies f to every global name (calls, constructors, generics, vars)."""
    if not isinstance(e, tuple) or not e:
        return e
    k = e[0]
    if k == 'var':
        return ('var', f(e[1]))
    if k == 'call':
        head = f(e[1]) if isinstance(e[1], str) else rename(e[1], f)
        return ('call', head, tuple(rename(a, f) for a in e[2]))
    if k in ('ctor', 'gen'):
        return (k, f(e[1]), tuple(rename(a, f) for a in e[2]))
    return tuple(rename(x, f) if isinstance(x, tuple) else x for x in e)


# Modules
# =======

TOP = re.compile(r'^(?:@unsafe\s+)?(def|law|type)\s+([A-Za-z_][\w.]*\??)')
IMPORT = re.compile(r'^import\s+(\S+)(?:\s+as\s+(\w+))?')


class Law:
    def __init__(self, name, params, concl, mods):
        self.name = name
        self.params = params      # names, in order
        self.concl = concl        # term
        self.mods = mods


class Module:
    def __init__(self, path, text=None):
        self.path = os.path.abspath(path)
        self.text = open(path).read() if text is None else text
        self.aliases = {}          # alias -> absolute path
        self.names = set()         # top-level names
        self.laws = {}
        self.sigs = {}             # def name -> (params, return type text)
        self.scan()

    def scan(self):
        lines = self.text.split('\n')
        d = os.path.dirname(self.path)
        i = 0
        while i < len(lines):
            line = lines[i]
            m = IMPORT.match(line)
            if m and m.group(2):
                self.aliases[m.group(2)] = os.path.abspath(os.path.join(d, m.group(1)))
            m = TOP.match(line)
            if m:
                kind, name = m.group(1), m.group(2)
                self.names.add(name)
                j = i + 1
                while j < len(lines) and (lines[j].startswith(' ') or lines[j].strip() == ''):
                    j += 1
                block = lines[i:j]
                if kind == 'type':
                    for b in block[1:]:
                        mm = re.match(r'^\s+([A-Za-z_][\w.]*)\s*\{', b)
                        if mm:
                            self.names.add(mm.group(1))
                elif kind == 'law':
                    try:
                        self.laws[name] = self.parse_law(name, block)
                    except (Err, IndexError) as ex:
                        self.laws[name] = Err(f"cannot read law {name}: {ex}")
                elif kind == 'def':
                    self.sigs[name] = block
                i = j
                continue
            i += 1

    def parse_law(self, name, block):
        items = []
        base = None
        for b in block[1:]:
            if not b.strip() or b.strip().startswith('#'):
                continue
            ind = len(b) - len(b.lstrip())
            if base is None:
                base = ind
            st = b.strip()
            if ind == base:
                items.append(st if st.startswith(('for ', 'exs ')) else '@' + st)
            else:
                items[-1] += ' ' + st
        params, mods = [], []
        concl = None
        for it in items:
            if it.startswith('for '):
                m = re.match(r'for\s+([+-]?)(\w+)\s*:', it)
                params.append(m.group(2))
                mods.append(m.group(1))
            elif it.startswith('exs '):
                concl = None
                raise Err(f"law {name} has a witness")
            else:
                concl = parse(it[1:])
        return Law(name, params, concl, mods)


MODULES = {}


def module(path):
    path = os.path.abspath(path)
    if path not in MODULES:
        MODULES[path] = Module(path)
    return MODULES[path]


def alias_of(cur, path):
    for a, p in cur.aliases.items():
        if p == path:
            return a
    return None


def requalify(e, src, cur, local=()):
    """Renames the names of a term written in module src into module cur."""
    if src.path == cur.path or src.path == os.path.abspath(BASE):
        return e
    me = alias_of(cur, src.path)

    def f(name):
        if name in local:
            return name
        if '.' in name:
            head = name.split('.')[0]
            if head in src.aliases:
                target = src.aliases[head]
                if target == cur.path:
                    return name[len(head) + 1:]
                a = alias_of(cur, target)
                if a is None:
                    raise Err(f"{name} (from {src.path}) needs an import of {target}")
                return a + name[len(head):]
        if name in src.names:
            if me is None:
                raise Err(f"{name} needs an import of {src.path}")
            return me + '.' + name
        return name
    return rename(e, f)


def lookup_law(cur, name):
    """The law a call head names, and the module it is in."""
    if name in cur.laws:
        return cur.laws[name], cur
    head = name.split('.')[0]
    if head in cur.aliases:
        m = module(cur.aliases[head])
        rest = name[len(head) + 1:]
        if rest in m.laws:
            return m.laws[rest], m
    b = base()
    if name in b.laws:
        return b.laws[name], b
    raise Err(f"no law {name}")


def instance(cur, call):
    """The equation (a, b, T) that a lemma call proves."""
    if call[0] != 'call' or not isinstance(call[1], str):
        raise Err(f"not a lemma call: {show(call)}")
    law, m = lookup_law(cur, call[1])
    if isinstance(law, Err):
        raise law
    if len(law.params) != len(call[2]):
        raise Err(f"{call[1]} takes {len(law.params)} arguments, given {len(call[2])}")
    c = requalify(law.concl, m, cur, set(law.params))
    c = fold_all(norm(subst(c, dict(zip(law.params, call[2])))))
    if c[0] != 'eq':
        raise Err(f"{call[1]} is not an equation: {show(c)}")
    return c[1], c[2], c[3]


BASE = os.path.expanduser('~/.bend/bend2/base.bend')


def base():
    return module(BASE)


def lookup_def(cur, name):
    if name in cur.sigs:
        return cur.sigs[name], cur
    head = name.split('.')[0]
    if head in cur.aliases:
        m = module(cur.aliases[head])
        rest = name[len(head) + 1:]
        if rest in m.sigs:
            return m.sigs[rest], m
    b = base()
    if name in b.sigs:
        return b.sigs[name], b
    raise Err(f"no def {name}")


def def_body(cur, name):
    """The parameters and body of a def whose body is one term."""
    block, m = lookup_def(cur, name)
    sig = ''
    k = 0
    while True:
        sig += block[k] + '\n'
        k += 1
        st = sig.strip()
        depth = sum(st.count(c) for c in '([{') - sum(st.count(c) for c in ')]}')
        if st.endswith(':') and depth == 0:
            break
    st = st[:-1]
    po = st.index('(')
    depth = 0
    for q in range(po, len(st)):
        if st[q] in '([{':
            depth += 1
        elif st[q] in ')]}':
            depth -= 1
            if depth == 0:
                break
    ps = [x.strip().lstrip('+-~').split(':')[0].strip() for x in split_top(st[po + 1:q], ',', True)]
    body = [l for l in block[k:] if l.strip() and not l.strip().startswith('#')]
    if not body:
        raise Err(f"def {name} has no body")
    return ps, match_body(body, m, cur, ps, [])


def match_body(body, m, cur, ps, outer_pats):
    """A body that is a match (with cases that are terms or matches), or a
    term with lets; None if it is neither."""
    ind = indent_of(body[0])
    if body[0].strip().startswith('match '):
        scrut = split_top(body[0].strip()[6:-1], ' ')
        cases = []
        for case in statements(body[1:], indent_of(body[1])):
            k = 0
            while True:
                k += 1
                h = ' '.join(l.strip() for l in case[:k])
                depth = sum(h.count(c) for c in '([{') - sum(h.count(c) for c in ')]}')
                if h.endswith(':') and depth == 0:
                    break
            pats = split_top(h[5:-1].strip(), ' ')
            while '<>' in pats:
                q = pats.index('<>')
                pats[q - 1:q + 2] = [' '.join(pats[q - 1:q + 2])]
            pats = [requalify(parse(x), m, cur, set(ps) | binders(parse(x))) for x in pats]
            rest = [l for l in case[k:] if l.strip() and not l.strip().startswith('#')]
            if rest and rest[0].strip().startswith('match '):
                b = match_body(rest, m, cur, ps, outer_pats + pats)
            else:
                b = case_body(case[k:], m, cur, ps, outer_pats + pats)
            cases.append((pats, b))
        return ('match', scrut, cases)
    return case_body(body, m, cur, ps, outer_pats)


def binders(p):
    """The variables a pattern binds."""
    if not isinstance(p, tuple) or not p:
        return set()
    if p[0] == 'var':
        return {p[1]}
    if p[0] == 'call':
        return set().union(*[binders(a) for a in p[2]]) if p[2] else set()
    if p[0] == 'ctor':
        return set().union(*[binders(a) for a in p[2]]) if p[2] else set()
    out = set()
    for x in p[1:]:
        out |= binders(x)
    return out


def case_body(lines, m, cur, ps, pats):
    """A case body of lets and a term: ('lets', [binding], term), where a
    binding is (names, value) and names has one name, or two for a tuple;
    None if it has other statements."""
    lines = [l for l in lines if l.strip() and not l.strip().startswith('#')]
    if not lines:
        return None
    ind = indent_of(lines[0])
    sts = statements(lines, ind)
    local = set(ps)
    for p in pats:
        local |= binders(p)
    binds = []
    for st in sts[:-1]:
        t = ' '.join(l.strip() for l in st)
        mm = re.match(r'^\(\s*[+-]?(\w+)\s*,\s*[+-]?(\w+)\s*\)\s*=\s*(.*)$', t, re.S)
        if mm:
            v = requalify(parse(mm.group(3)), m, cur, local)
            local.add(mm.group(1))
            local.add(mm.group(2))
            binds.append(((mm.group(1), mm.group(2)), v))
            continue
        mm = re.match(r'^[+-]?(\w+)\s*=\s*(.*)$', t, re.S)
        if not mm or mm.group(2).startswith('='):
            return None
        v = requalify(parse(mm.group(2)), m, cur, local)
        local.add(mm.group(1))
        binds.append(((mm.group(1),), v))
    t = ' '.join(l.strip() for l in sts[-1])
    if t.startswith('match '):
        return None
    return ('lets', binds, requalify(parse(t), m, cur, local))


def nat_lit(e):
    if e[0] == 'lit' and re.fullmatch(r'\d+n', e[1]):
        return int(e[1][:-1])
    return None


def pmatch(p, a):
    """Bindings when the term a matches pattern p, None when it cannot,
    'unknown' when it is not known."""
    k = p[0]
    if k == 'hole':
        return {}
    if k == 'var':
        return {p[1]: a}
    if k == 'lit':
        if a[0] == 'lit':
            return {} if a[1] == p[1] else None
        if a[0] == 'succ' and nat_lit(p) is not None:
            return None
        return 'unknown'
    if k == 'succ':
        n = int(p[1][:-1])
        if a[0] == 'succ':
            m = int(a[1][:-1])
            if m >= n:
                rest = a[2] if m == n else ('succ', f"{m - n}n", a[2])
                return pmatch(p[2], rest)
            return pmatch(('succ', f"{n - m}n", p[2]), a[2])
        v = nat_lit(a)
        if v is not None:
            return pmatch(p[2], ('lit', f"{v - n}n")) if v >= n else None
        return 'unknown'
    if k in ('ctor', 'tuple', 'nil', 'cons'):
        if a[0] not in ('ctor', 'tuple', 'nil', 'cons'):
            return 'unknown'
        if a[0] != k or (k == 'ctor' and (a[1] != p[1] or len(a[2]) != len(p[2]))):
            return None
        ps_, as_ = (p[2], a[2]) if k == 'ctor' else (p[1:], a[1:])
        env = {}
        for x, y in zip(ps_, as_):
            r = pmatch(x, y)
            if r is None or r == 'unknown':
                return r
            env.update(r)
        return env
    return 'unknown'


def run_body(body, env):
    """The body's term under env, or None when a match is not decided."""
    if body is None:
        return None
    if body[0] == 'lets':
        env = dict(env)
        for names, v in body[1]:
            v = norm(subst(v, env))
            if len(names) == 1:
                env[names[0]] = v
            elif v[0] == 'tuple':
                env[names[0]] = v[1]
                env[names[1]] = v[2]
            else:
                return None
        return subst(body[2], env)
    if body[0] != 'match':
        return subst(body, env)
    _, scrut, cases = body
    for pats, b in cases:
        benv = {}
        for sname, p in zip(scrut, pats):
            if sname not in env:
                return None
            r = pmatch(p, env[sname])
            if r is None or r == 'unknown':
                benv = r
                break
            benv.update(r)
        if benv is None:
            continue
        if benv == 'unknown':
            return None
        env2 = dict(env)
        env2.update(benv)
        return run_body(b, env2)
    return None


def unfold(e, name, ps, body):
    if not isinstance(e, tuple) or not e:
        return e
    if e[0] == 'call' and e[1] == name and len(e[2]) == len(ps):
        args = tuple(unfold(a, name, ps, body) for a in e[2])
        env = dict(zip(ps, args))
        r = run_body(body, env)
        return ('call', e[1], args) if r is None else norm(r)
    return tuple(unfold(x, name, ps, body) if isinstance(x, tuple) else x for x in e)


def u32_lit(e):
    if e[0] == 'lit' and re.fullmatch(r'\d+', e[1]):
        return int(e[1])
    return None


def fold(e):
    """Constant folding of U32 operations on literals."""
    if e[0] != 'call' or not isinstance(e[1], str):
        return None
    if e[1] in ('Nat.mul', 'Nat.add', 'Nat.sub') and len(e[2]) == 2:
        a, b = nat_lit(e[2][0]), nat_lit(e[2][1])
        if a is not None and b is not None:
            r = {'Nat.mul': a * b, 'Nat.add': a + b, 'Nat.sub': max(0, a - b)}[e[1]]
            return ('lit', f"{r}n")
        return None
    if re.fullmatch(r'(\w+\.)?U\.N', e[1]):
        op = 'to_nat'
    elif e[1].startswith('U32.'):
        op = e[1][4:]
    else:
        return None
    args = e[2]
    M = 1 << 32
    if op in ('add', 'sub', 'mul', 'and', 'or', 'xor', 'min', 'max', 'div', 'mod') and len(args) == 2:
        a, b = u32_lit(args[0]), u32_lit(args[1])
        if a is None or b is None:
            return None
        if op in ('div', 'mod') and b == 0:
            return None
        r = {'add': (a + b) % M, 'sub': (a - b) % M, 'mul': (a * b) % M, 'and': a & b,
             'or': a | b, 'xor': a ^ b, 'min': min(a, b), 'max': max(a, b),
             'div': a // b if b else 0, 'mod': a % b if b else a}[op]
        return ('lit', str(r))
    if op in ('shln', 'shrn') and len(args) == 2:
        a, k = u32_lit(args[0]), nat_lit(args[1])
        if a is None or k is None:
            return None
        return ('lit', str((a << k) % M if op == 'shln' else a >> k))
    if op in ('is_lt', 'is_le', 'is_gt', 'is_ge', 'is_eq', 'is_ne') and len(args) == 2:
        a, b = u32_lit(args[0]), u32_lit(args[1])
        if a is None or b is None:
            return None
        r = {'is_lt': a < b, 'is_le': a <= b, 'is_gt': a > b, 'is_ge': a >= b,
             'is_eq': a == b, 'is_ne': a != b}[op]
        return ('ctor', 'True' if r else 'False', ())
    if op == 'to_nat' and len(args) == 1:
        a = u32_lit(args[0])
        if a is not None and a < 4096:
            return ('lit', f"{a}n")
    return None


def fold_all(e):
    """Constant folding everywhere in e."""
    if not isinstance(e, tuple) or not e:
        return e
    e = norm(tuple(fold_all(x) if isinstance(x, tuple) else x for x in e))
    c = fold(e)
    return c if c is not None else e


DEFCACHE = {}
NOSIMP = {'U32.shrn', 'U32.shln', 'Nat.mul'}


def simp(cur, e, fuel=None, skip=frozenset()):
    """Evaluates the calls whose match the arguments decide."""
    if fuel is None:
        fuel = [2000]
    if not isinstance(e, tuple) or not e:
        return e
    e = norm(tuple(simp(cur, x, fuel, skip) if isinstance(x, tuple) else x for x in e))
    c = fold(e)
    if c is not None:
        return c
    if e[0] == 'call' and isinstance(e[1], str) and fuel[0] > 0 and e[1] not in skip:
        key = (cur.path, e[1])
        if key not in DEFCACHE:
            try:
                DEFCACHE[key] = def_body(cur, e[1])
            except (Err, IndexError, ValueError):
                DEFCACHE[key] = None
        d = DEFCACHE[key]
        if d is not None and d[1] is not None and d[1][0] == 'match':
            r = unfold(e, e[1], d[0], d[1])
            if r != e:
                fuel[0] -= 1
                return simp(cur, r, fuel, skip)
    return e


# Proof bodies
# ============

def indent_of(line):
    return len(line) - len(line.lstrip())


def depth_of(text):
    d = 0
    for c in re.sub(r'#.*', '', text):
        if c in '([{':
            d += 1
        elif c in ')]}':
            d -= 1
    return d


def statements(lines, ind):
    """Splits lines of a block (indented by ind) into statements; a line
    continues the statement before it while its brackets are open."""
    out = []
    depth = 0
    for line in lines:
        if line.strip() == '':
            if out:
                out[-1].append(line)
            continue
        if (indent_of(line) == ind and not line.lstrip().startswith('#') and depth == 0) or not out:
            out.append([line])
        else:
            out[-1].append(line)
        depth += depth_of(line)
    return out


def pattern_term(p):
    return parse(p)


def split_top(s, sep=' ', angles=False):
    """Splits s at top-level separators (outside brackets, and outside
    generic arguments when angles)."""
    out, depth, cur = [], 0, ''
    for i, c in enumerate(s):
        if c in '([{' or angles and c == '<':
            depth += 1
        elif c in ')]}' or angles and c == '>' and s[i - 1] != '-':
            depth -= 1
        if c == sep and depth == 0:
            if cur.strip():
                out.append(cur.strip())
            cur = ''
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


class Ctx:
    def __init__(self, cur, name):
        self.cur = cur
        self.name = name


def rewrite(ctx, goal, old, new, eq_text, T, ind, out, only=None):
    if goal is None:
        raise Err(f"{ctx.name}: no goal tracked here (use @goal)")
    motive, n = subterms_replace(goal, old, ('hole',), only)
    if n == 0:
        raise Err(f"{ctx.name}: {show(old)} is not in the goal\n  goal: {show(goal)}")
    out.append(' ' * ind + f"%{eq_text} :")
    out.append(' ' * (ind + 2) + show(motive))
    g, _ = subterms_replace(goal, old, new, only)
    return g


def directive(ctx, text, goal, ind, out):
    m = re.match(r'@(\w+-?)(?:\[([\d,]+)\])?\s*(.*)$', text, re.S)
    cmd, arg = m.group(1), m.group(3).strip()
    only = set(int(x) for x in m.group(2).split(',')) if m.group(2) else None
    if cmd in ('rw', 'rw-'):
        call = parse(arg)
        a, b, T = instance(ctx.cur, call)
        if cmd == 'rw':
            return rewrite(ctx, goal, a, b, f"Equal.sym({show(T)}, {show(a)}, {show(b)}, {show(call)})", T, ind, out, only)
        return rewrite(ctx, goal, b, a, show(call), T, ind, out, only)
    if cmd in ('rwx', 'rwx-'):
        parts = split_top(arg, ':')
        if len(parts) < 2:
            raise Err(f"{ctx.name}: @rwx needs E : {{a == b : T}}")
        proof = parse(parts[0])
        eq = parse(':'.join(parts[1:]))
        if eq[0] != 'eq':
            raise Err(f"{ctx.name}: @rwx needs an equation")
        a, b, T = eq[1], eq[2], eq[3]
        if cmd == 'rwx':
            return rewrite(ctx, goal, a, b, f"Equal.sym({show(T)}, {show(a)}, {show(b)}, {show(proof)})", T, ind, out, only)
        return rewrite(ctx, goal, b, a, show(proof), T, ind, out, only)
    if cmd == 'goal':
        if arg == '?':
            raise Err(f"{ctx.name}: goal is\n  {show(goal) if goal is not None else '?'}")
        return parse(arg)
    if cmd == 'simp':
        if goal is None:
            raise Err(f"{ctx.name}: no goal tracked here (use @goal)")
        skip = set(NOSIMP)
        for w in arg.split():
            if w.startswith('-'):
                skip.add(w[1:])
            elif w.startswith('+'):
                skip.discard(w[1:])
        return simp(ctx.cur, goal, skip=skip)
    if cmd == 'rename':
        if goal is None:
            raise Err(f"{ctx.name}: no goal tracked here (use @goal)")
        f, g = arg.split()
        return rename(goal, lambda n: g if n == f else n)
    if cmd == 'unfold':
        if goal is None:
            raise Err(f"{ctx.name}: no goal tracked here (use @goal)")
        for name in arg.split():
            ps, body = def_body(ctx.cur, name)
            goal = unfold(goal, name, ps, body)
        return goal
    if cmd == 'show':
        out.append(' ' * ind + '# goal: ' + (show(goal) if goal is not None else '?'))
        return goal
    raise Err(f"{ctx.name}: unknown directive @{cmd}")


EQSYM = re.compile(r'^%\s*Equal\.sym\(')


def plain_rewrite(ctx, text, goal):
    """The goal after a hand-written `%e : P` line, if it can be known."""
    body = text.strip()[1:]
    parts = split_top(body, ':')
    if len(parts) < 2:
        return None
    try:
        e = parse(parts[0])
        P = parse(':'.join(parts[1:]))
    except Err:
        return None
    if e[0] == 'call' and e[1] == 'Equal.sym' and len(e[2]) == 4:
        g, _ = subterms_replace(P, ('hole',), e[2][2])
        return g
    return None


def block(ctx, lines, ind, goal, out):
    for st in statements(lines, ind):
        first = st[0].strip()
        text = '\n'.join(st)
        if first.startswith('@'):
            goal = directive(ctx, ' '.join(l.strip() for l in st if not l.strip().startswith('#')), goal, ind, out)
            continue
        if first.startswith('match ') and first.endswith(':'):
            out.append(st[0])
            scrut = split_top(first[6:-1].strip(), ' ')
            body = st[1:]
            cind = None
            for l in body:
                if l.strip() and not l.strip().startswith('#'):
                    cind = indent_of(l)
                    break
            for case in statements(body, cind):
                head = case[0].strip()
                if not head.startswith('case '):
                    out.extend(case)
                    continue
                k = 0
                while True:
                    out.append(case[k])
                    k += 1
                    h = ' '.join(l.strip() for l in case[:k])
                    depth = sum(h.count(c) for c in '([{') - sum(h.count(c) for c in ')]}')
                    if h.endswith(':') and depth == 0:
                        break
                head = h
                pats = split_top(head[5:-1].strip(), ' ')
                while '<>' in pats:
                    q = pats.index('<>')
                    pats[q - 1:q + 2] = [' '.join(pats[q - 1:q + 2])]
                g = goal
                if len(pats) != len(scrut):
                    g = None
                if g is not None:
                    env = {}
                    for s, p in zip(scrut, pats):
                        if p == '_':
                            continue
                        try:
                            env[s] = pattern_term(p)
                        except Err:
                            g = None
                            break
                    if g is not None:
                        g = subst(g, env)
                rest = case[k:]
                bind = None
                for l in rest:
                    if l.strip() and not l.strip().startswith('#'):
                        bind = indent_of(l)
                        break
                if bind is None:
                    out.extend(rest)
                else:
                    block(ctx, rest, bind, g, out)
            goal = None
            continue
        if first.startswith('%'):
            out.extend(st)
            goal = plain_rewrite(ctx, ' '.join(l.strip() for l in st), goal)
            continue
        out.extend(st)


def def_goal(cur, name, params_text, ret_text):
    if ret_text:
        return parse(ret_text)
    law = cur.laws.get(name)
    if law is None:
        return None
    if isinstance(law, Err):
        raise law
    ps = [p.strip().lstrip('+-').split(':')[0].strip() for p in split_top(params_text, ',', True)]
    if len(ps) != len(law.params):
        raise Err(f"def {name}: {len(ps)} parameters, law has {len(law.params)}")
    env = {a: ('var', b) for a, b in zip(law.params, ps) if a != b}
    return subst(law.concl, env)


DEF = re.compile(r'^def\s+([A-Za-z_][\w.]*)\s*\(')


def process(path, text):
    cur = Module(path, text)
    MODULES[cur.path] = cur
    lines = text.split('\n')
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = DEF.match(line)
        if not m:
            out.append(line)
            i += 1
            continue
        j = i + 1
        while j < len(lines) and (lines[j].startswith(' ') or lines[j].strip() == ''):
            j += 1
        item = lines[i:j]
        if not any(l.strip().startswith('@') for l in item[1:]):
            out.extend(item)
            i = j
            continue
        # the signature runs to the line ending in ':' at depth 0
        sig = ''
        k = 0
        while True:
            sig += item[k] + '\n'
            k += 1
            s = sig.strip()
            depth = sum(s.count(c) for c in '([{') - sum(s.count(c) for c in ')]}')
            if s.endswith(':') and depth == 0:
                break
        name = m.group(1)
        s = sig.strip()[:-1]
        po = s.index('(')
        depth = 0
        for q in range(po, len(s)):
            if s[q] in '([{':
                depth += 1
            elif s[q] in ')]}':
                depth -= 1
                if depth == 0:
                    break
        params_text = s[po + 1:q]
        ret = s[q + 1:].strip()
        ret_text = ret[2:].strip() if ret.startswith('->') else ''
        ctx = Ctx(cur, name)
        goal = def_goal(cur, name, params_text, ret_text)
        out.extend(item[:k])
        body = item[k:]
        bind = None
        for l in body:
            if l.strip() and not l.strip().startswith('#'):
                bind = indent_of(l)
                break
        block(ctx, body, bind, goal, out)
        i = j
    return '\n'.join(out)


def main():
    src = sys.argv[1]
    dst = sys.argv[2] if len(sys.argv) > 2 else re.sub(r'\.bp$', '.bend', src)
    text = open(src).read()
    try:
        res = process(dst, text)
    except Err as e:
        print(f"bpp: {src}: {e}", file=sys.stderr)
        sys.exit(1)
    with open(dst, 'w') as f:
        f.write(res)


if __name__ == '__main__':
    main()
