"""Helpers for writing Bend proofs by rewriting.

A Goal tracks the text of an equation {lhs == rhs : T}. Each step replaces
every occurrence of a subterm and emits the Bend rewrite that does it:

  g = Goal("U32", "U32.and(x, 255)", "x")
  g.fw("Nat", "Nat.add(i, 0n)", "i", "P.Nat.add_zero_r(i)")  # proof : {old == new}
  g.bw("Nat", "i", "Nat.add(i, 0n)", "P.Nat.add_zero_r(i)")  # proof : {new == old}
  g.done("{==}")

In Bend, `%e : P` with e : {a == b} needs the goal to be P with b at the
holes, and leaves P with a there; fw and bw pick the right orientation.
"""


class Goal:
    def __init__(self, T, lhs, rhs, indent="  "):
        self.T = T
        self.lhs = lhs
        self.rhs = rhs
        self.indent = indent
        self.lines = []

    def text(self):
        return f"{{{self.lhs} == {self.rhs} : {self.T}}}"

    def _pattern(self, old):
        if old not in self.lhs and old not in self.rhs:
            raise ValueError(f"no {old!r} in goal {self.text()}")
        return f"{{{self.lhs.replace(old, '_')} == {self.rhs.replace(old, '_')} : {self.T}}}"

    def fw(self, T, old, new, proof, side=None):
        """Rewrites old into new, given proof : {old == new : T}."""
        self._step(f"Equal.sym({T}, {old}, {new}, {proof})", old, new, side)
        return self

    def bw(self, T, old, new, proof, side=None):
        """Rewrites old into new, given proof : {new == old : T}."""
        self._step(proof, old, new, side)
        return self

    def _step(self, eq, old, new, side):
        lhs, rhs = self.lhs, self.rhs
        if side == "l":
            P = f"{{{lhs.replace(old, '_')} == {rhs} : {self.T}}}"
            self.lhs = lhs.replace(old, new)
        elif side == "r":
            P = f"{{{lhs} == {rhs.replace(old, '_')} : {self.T}}}"
            self.rhs = rhs.replace(old, new)
        else:
            P = self._pattern(old)
            self.lhs = lhs.replace(old, new)
            self.rhs = rhs.replace(old, new)
        if old not in (lhs if side == "l" else rhs if side == "r" else lhs + rhs):
            raise ValueError(f"no {old!r} on side {side} of {{{lhs} == {rhs}}}")
        self.lines.append(f"{self.indent}%{eq} :\n{self.indent}  {P}")

    def set(self, lhs=None, rhs=None):
        """Restates the goal (to a form it normalizes to)."""
        if lhs is not None:
            self.lhs = lhs
        if rhs is not None:
            self.rhs = rhs
        return self

    def done(self, last):
        self.lines.append(f"{self.indent}{last}")
        return "\n".join(self.lines)


def term(T, P_lhs, P_rhs, old, new, proof, body, mode="fw"):
    """A term rewriting a hypothesis: body : {P[old]} gives {P[new]}.

    fw: proof : {old == new}; bw: proof : {new == old}."""
    eq = proof if mode == "fw" else f"Equal.sym({T}, {new}, {old}, {proof})"
    P = f"{{{P_lhs.replace(old, '_')} == {P_rhs.replace(old, '_')}}}"
    return f"(%{eq} : {P}\n  {body})"
