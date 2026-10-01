"""Reorders the arguments of calls to a def in Bend sources.

  python3 tools/permargs.py FILE NAME 2,0,1   # NAME(a, b, c) -> NAME(c, a, b)

Only calls (NAME followed by '(') change; the new order lists old indices.
"""
import sys


def split_args(s):
    """Splits the text of an argument list at top-level commas."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{<" and not (ch == "<" and cur.endswith(" ")):
            depth += 1
        elif ch in ")]}>" and not (ch == ">" and cur.endswith(" ")) and not (ch == ">" and cur.endswith("-")):
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [a.strip() for a in out]


def find_close(s, i):
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    raise ValueError("unbalanced")


def permute(text, name, order):
    out, i = "", 0
    key = name + "("
    while True:
        k = text.find(key, i)
        if k < 0:
            return out + text[i:]
        prev = text[k - 1] if k > 0 else " "
        if prev.isalnum() or prev in "._":
            out += text[i:k + len(key)]
            i = k + len(key)
            continue
        close = find_close(text, k + len(name))
        inner = permute(text[k + len(key):close], name, order)
        args = split_args(inner)
        if len(args) != len(order):
            raise ValueError(f"{name}: {len(args)} args at {text[k:k+80]!r}")
        out += text[i:k] + key + ", ".join(args[o] for o in order) + ")"
        i = close + 1


if __name__ == "__main__":
    path, name, spec = sys.argv[1:4]
    order = [int(x) for x in spec.split(",")]
    src = open(path).read()
    open(path, "w").write(permute(src, name, order))
