"""Exact infinite wallpaper groups, and their continuous spin factor."""
from dataclasses import dataclass
from itertools import product
import re


@dataclass(frozen=True)
class SpaceGroup:
    n: int
    mirror: bool = False

    @classmethod
    def parse(cls, name):
        s = re.sub(r"\s+", "", name).replace("×", "*").replace("x", "*")
        s = s.replace("SO(3)*Z2T", "O(3)").replace("SO(3)*Z_2^T", "O(3)")
        choices = {"p4*SO(3)": (4, False), "p6*SO(3)": (6, False),
                   "p4m*O(3)": (4, True), "p6m*O(3)": (6, True)}
        if s not in choices:
            raise ValueError("Supported groups: p4*SO(3), p6*SO(3), p4m*O(3), p6m*O(3)")
        return cls(*choices[s])

    @property
    def name(self):
        return f"p{self.n}{'m*O(3)' if self.mirror else '*SO(3)'}"

    @property
    def names(self):
        return ("T1", "T2", f"C{self.n}") + (("M", "T") if self.mirror else ())

    @property
    def orders(self):
        return (0, 0, self.n) + ((2, 2) if self.mirror else ())

    def conjugate_word(self, i, j):
        """Word for generator i * generator j * generator i^-1."""
        w = [0] * i
        if i == 2:
            if j == 0:
                w[:2] = [int(self.n == 6), 1]
            else:
                w[0] = -1
        elif i == 3 and j == 2:
            w[2] = -1
        elif i == 3 and j < 2:
            if self.n == 6:
                w[1-j] = 1
            else:
                w[j] = -1 if j == 0 else 1
        else:
            w[j] = 1
        return tuple(w)

    def element(self, x=0, y=0, c=0, m=0, t=0):
        if any(type(v) is not int for v in (x, y, c, m, t)):
            raise ValueError("Wallpaper coordinates must be integers")
        if not self.mirror and (m or t):
            raise ValueError("This group has no mirror or time reversal generator")
        return (x, y, c % self.n) + ((m % 2, t % 2) if self.mirror else ())

    def multiply(self, g, h):
        if len(g) != len(self.names) or len(h) != len(self.names):
            raise ValueError("Wrong number of wallpaper coordinates")
        x, y = h[:2]
        m = g[3] if self.mirror else 0
        if m:
            x, y = (y, x) if self.n == 6 else (-x, y)
        for _ in range(g[2] % self.n):
            x, y = (x-y, x) if self.n == 6 else (-y, x)
        return self.element(g[0]+x, g[1]+y, g[2]+(-1)**m*h[2],
                            m+(h[3] if self.mirror else 0),
                            (g[4]+h[4]) if self.mirror else 0)

    def lattice(self, iwps):
        if not isinstance(iwps, (list, tuple)):
            raise ValueError("IWPs must be a list, e.g. ['1 a', '1 b']")
        multiplicities = {"a": 1, "b": 1 if self.n == 4 else 2,
                          "c": 2 if self.n == 4 else 3}
        parity = {k: 0 for k in multiplicities}
        for item in iwps:
            if not isinstance(item, str):
                raise ValueError("Each IWP must be a string")
            match = re.fullmatch(r"\s*(\d+)?\s*([abc])\s*", item)
            if not match or (match[1] and int(match[1]) != multiplicities[match[2]]):
                raise ValueError(f"Invalid IWP {item!r} for {self.name}: expected {multiplicities}")
            parity[match[2]] ^= 1
        if self.n == 6:
            parity["b"] = 0  # The odd-order site stabilizer has no Z2 LSM charge.
        return parity


class Intrinsic:
    def __init__(self, category):
        self.sym = category.symmetry
        self.elements = self.sym.elements if self.sym else ("1",)
        self.identity = self.sym.identity if self.sym else "1"
        self.positions = {g: i for i, g in enumerate(self.elements)}
        self.unitary = tuple(g for g in self.elements if not self.parity(g))
        self.anti = tuple(g for g in self.elements if self.parity(g))

    def parity(self, g):
        return self.sym.rho(g) if self.sym else 0

    def mul(self, g, h):
        return self.sym.multiplication_table[self.positions[g]][self.positions[h]] if self.sym else "1"

    def power(self, g, n):
        if n < 0:
            g = next(h for h in self.elements if self.mul(g, h) == self.identity)
            n = -n
        out = self.identity
        while n:
            if n & 1:
                out = self.mul(out, g)
            g = self.mul(g, g)
            n //= 2
        return out

    def word(self, images, word):
        out = self.identity
        for g, n in zip(images, word):
            out = self.mul(out, self.power(g, n))
        return out

    def action(self, g, a):
        return self.sym.action(g, a) if self.sym else a

    def homomorphisms(self, space):
        options = [self.unitary] * 3 + ([self.anti] * 2 if space.mirror else [])
        for images in product(*options):
            if any(n and self.power(g, n) != self.identity for g, n in zip(images, space.orders)):
                continue
            if all(self.mul(images[i], images[j]) ==
                   self.mul(self.word(images[:i], space.conjugate_word(i, j)), images[i])
                   for i in range(len(images)) for j in range(i)):
                yield images

    def conjugated(self, images, k):
        return tuple(self.mul(self.mul(k, g), self.power(k, -1)) for g in images)
