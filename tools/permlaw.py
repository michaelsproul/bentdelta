"""Reorders the `for` lines of a law to match a new parameter order.

  python3 tools/permlaw.py FILE NAME 2,0,1
"""
import sys


def permlaw(text, name, order):
    lines = text.split("\n")
    i = lines.index(f"law {name}:")
    j = i + 1
    fors = []
    while lines[j].startswith("  for "):
        fors.append(lines[j])
        j += 1
    assert len(fors) == len(order), (name, len(fors))
    lines[i + 1:j] = [fors[o] for o in order]
    return "\n".join(lines)


if __name__ == "__main__":
    path, name, spec = sys.argv[1:4]
    src = open(path).read()
    open(path, "w").write(permlaw(src, name, [int(x) for x in spec.split(",")]))
