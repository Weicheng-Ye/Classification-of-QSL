"""Finite Abelian modules and exact integral-lattice quotients."""
from itertools import product
from math import gcd, prod
import numpy as np
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import hermite_normal_form
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp


class AnyonModule:
    def __init__(self, category, intrinsic):
        self.category = category
        self.anyons = tuple(a for a in category.anyons if abs(category.quantum_dimension(a)-1) < 1e-8)
        self.zero = category.vacuum
        self.add_table = {(a, b): next(iter(category.fusion(a, b))) for a in self.anyons for b in self.anyons}
        powers = {}
        for a in self.anyons:
            p = [self.zero]
            b = a
            while b != self.zero:
                p.append(b)
                b = self.add_table[b, a]
                if len(p) > len(self.anyons):
                    raise ValueError("Dimension-one anyons do not form a finite group")
            powers[a] = p

        def basis(span):
            if len(span) == len(self.anyons):
                return []
            for a in sorted(self.anyons, key=lambda a: -len(powers[a])):
                if len(powers[a]) == 1 or any(b in span for b in powers[a][1:]):
                    continue
                enlarged = {self.add_table[b, c] for b in span for c in powers[a]}
                if len(enlarged) != len(span)*len(powers[a]):
                    continue
                rest = basis(enlarged)
                if rest is not None:
                    return [a] + rest
            return None

        self.basis = tuple(basis({self.zero}))
        self.moduli = tuple(len(powers[a]) for a in self.basis)
        self.rank = len(self.basis)
        self.labels = {}
        self.coords = {}
        for c in product(*(range(m) for m in self.moduli)):
            a = self.zero
            for b, n in zip(self.basis, c):
                a = self.add_table[a, powers[b][n]]
            self.labels[c] = a
            self.coords[a] = c
        self.actions = {g: np.array([self.coords[intrinsic.action(g, b)] for b in self.basis],
                                   dtype=np.int64).T.reshape(self.rank, self.rank)
                        for g in intrinsic.elements}
        self.braiding = {}
        for a in category.anyons:
            for b in self.anyons:
                fusion = category.fusion(a, b)
                if len(fusion) != 1 or next(iter(fusion.values())) != 1:
                    raise ValueError("Fusion with an invertible anyon must be simple")
                c = next(iter(fusion))
                self.braiding[a, b] = category.spin(c)/(category.spin(a)*category.spin(b))

    def label(self, coords):
        return self.labels[tuple(int(c) % m for c, m in zip(coords, self.moduli))]


def _egcd(a, b):
    if b == 0:
        return abs(a), 1 if a >= 0 else -1, 0
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b)*y


class CohomologyQuotient:
    """ker(C: product Z/m -> product Z/q) / im(B), including projection."""
    def __init__(self, variable_moduli, equations, equation_moduli, gauge):
        n = len(variable_moduli)
        self.n = n
        if n == 0:
            self.orders = ()
            self.lifts = np.zeros((0, 0), dtype=np.int64)
            self._projection = Matrix.zeros(0, 0)
            self.size = 1
            return
        K = Matrix.eye(n)
        for row, modulus in zip(equations, equation_moduli):
            r = [int(x) % modulus for x in (Matrix([list(row)]) * K)]
            if not any(r):
                continue
            V = Matrix.eye(n)
            for j in range(1, n):
                a, b = r[0], r[j]
                if b == 0:
                    continue
                d, u, v = _egcd(a, b)
                c0, cj = V[:, 0], V[:, j]
                V[:, 0] = u*c0 + v*cj
                V[:, j] = (-b//d)*c0 + (a//d)*cj
                r[0], r[j] = d, 0
            V[:, 0] *= modulus // gcd(r[0], modulus)
            K = hermite_normal_form(K*V)
        Ki = K.inv()
        B = Matrix(gauge.tolist()) if gauge.shape[1] else Matrix.zeros(n, 0)
        relations = Ki * Matrix.diag(*variable_moduli).row_join(B)
        if any(x.q != 1 for x in relations):
            raise ArithmeticError("Generator gauge shifts do not preserve extension consistency")
        relations = Matrix(relations.rows, relations.cols, [int(x) for x in relations])
        H = hermite_normal_form(relations)
        D, U, _ = smith_normal_decomp(DomainMatrix.from_Matrix(H).convert_to(ZZ))
        D, U = D.to_Matrix(), U.to_Matrix()
        active = [i for i in range(n) if abs(D[i, i]) > 1]
        self.orders = tuple(abs(int(D[i, i])) for i in active)
        self.size = prod(self.orders)
        self._projection = (U*Ki)[active, :]
        L = (K*U.inv())[:, active]
        self.lifts = np.array(L.tolist(), dtype=np.int64).reshape(n, len(active))
        self.lifts %= np.array(variable_moduli, dtype=np.int64)[:, None]

    def project(self, vector):
        out = self._projection * Matrix(list(map(int, vector)))
        if any(x.q != 1 for x in out):
            raise ValueError("The parameter vector is not a consistent extension")
        return tuple(int(c) % m for c, m in zip(out, self.orders))

    def induced(self, transform):
        columns = [self.project(transform @ self.lifts[:, j]) for j in range(len(self.orders))]
        return np.array(columns, dtype=np.int64).T.reshape(len(self.orders), len(self.orders))
