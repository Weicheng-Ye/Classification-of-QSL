"""Polycyclic extension collector for H² of infinite wallpaper groups.

Each lifted conjugation/power relation has an unknown Abelian-anyon tail.
Consistency of the iterated cyclic extensions gives linear congruences. A
change of generator lifts gives precisely the coboundary subgroup.
"""
from functools import lru_cache
import numpy as np
from .algebra import CohomologyQuotient


class ExtensionCollector:
    def __init__(self, space, module, intrinsic, images, *, gauge=False):
        self.space, self.module, self.intrinsic, self.images = space, module, intrinsic, images
        self.d = module.rank
        self.k = len(images)
        self.relations = [(i, j) for i in range(self.k) for j in range(i)]
        self.relations += [(i, i) for i, n in enumerate(space.orders) if n]
        self.names = [f"{space.names[i]}:{space.names[j]}" if i != j else f"{space.names[i]}^{space.orders[i]}"
                      for i, j in self.relations] + ["spin_lift_squared"]
        self.width = (self.k if gauge else len(self.relations)+1)*self.d
        self.mod = np.array(module.moduli, dtype=np.int64)[:, None]
        self.zero = np.zeros((self.d, self.width), dtype=np.int64)
        self.gauge = gauge
        self.tails = {}
        for q, r in enumerate(self.relations):
            value = self.zero.copy()
            if not gauge:
                value[:, q*self.d:(q+1)*self.d] = np.eye(self.d, dtype=np.int64)
            self.tails[r] = value
        self.spin = self.zero.copy()
        if not gauge:
            self.spin[:, -self.d:] = np.eye(self.d, dtype=np.int64) if self.d else self.zero
        self.rho = [module.actions[g] for g in images]
        self.rho_inverse = [module.actions[intrinsic.power(g, -1)] for g in images]
        self.image = lru_cache(maxsize=None)(self.image)
        self.power_element = lru_cache(maxsize=None)(self.power_element)

    def reduce(self, a):
        return a % self.mod

    def identity(self, k):
        return self.zero, (0,)*k

    def generator(self, k, j):
        e = [0]*k
        e[j] = 1
        return self.zero, tuple(e)

    def action(self, word, a):
        g = self.intrinsic.word(self.images, word)
        return self.reduce(self.module.actions[g] @ a)

    def mul(self, k, left, right):
        a, e = left
        b, f = right
        if k == 0:
            return self.reduce(a+b), ()
        i = k-1
        transformed = self.alpha_power(i, (b, f[:-1]), e[-1])
        out, word = self.mul(i, (a, e[:-1]), transformed)
        power = e[-1] + f[-1]
        n = self.space.orders[i]
        if n:
            carry, power = divmod(power, n)
            if carry:
                out, word = self.mul(i, (out, word), self.power(i, self.power_element(i), carry))
        return out, word+(power,)

    def power_element(self, i):
        a, word = self.word_element(i, self.space.power_word(i))
        return self.reduce(a+self.tails[i, i]), word

    def primitive_power(self, k, j, n):
        e = [0]*k
        out = self.zero
        order = self.space.orders[j]
        if order:
            q, n = divmod(n, order)
            if q:
                out, word = self.power(j, self.power_element(j), q)
                e[:j] = word
        e[j] = n
        return out, tuple(e)

    def inverse(self, k, element):
        a, word = element
        out = self.identity(k)
        for j in reversed(range(k)):
            out = self.mul(k, out, self.primitive_power(k, j, -word[j]))
        return self.mul(k, out, (self.reduce(-a), (0,)*k))

    def power(self, k, element, n):
        if n < 0:
            element = self.inverse(k, element)
            n = -n
        result = self.identity(k)
        while n:
            if n & 1:
                result = self.mul(k, result, element)
            n //= 2
            if n:
                element = self.mul(k, element, element)
        return result

    def image(self, i, j, inverse=False):
        if inverse:
            # Only the infinite translation Y needs inverse conjugation.
            if i != 1 or j != 0:
                raise ArithmeticError("Unexpected inverse automorphism")
            return self.reduce(-self.rho_inverse[i] @ self.tails[i, j]), (1,)
        a, e = self.word_element(i, self.space.conjugate_word(i, j))
        return self.reduce(a + self.tails[i, j]), e

    def word_element(self, k, word):
        result = self.identity(k)
        for j, exponent in enumerate(word):
            result = self.mul(k, result, self.primitive_power(k, j, exponent))
        return result

    def alpha(self, i, element, inverse=False):
        a, word = element
        rho = self.rho_inverse[i] if inverse else self.rho[i]
        out = self.reduce(rho @ a), (0,)*i
        for j, n in enumerate(word):
            if n:
                out = self.mul(i, out, self.power(i, self.image(i, j, inverse), n))
        return out

    def alpha_power(self, i, element, n):
        if not n:
            return element
        if i == 0:
            rho = self.module.actions[self.intrinsic.power(self.images[0], n)]
            return self.reduce(rho @ element[0]), ()
        # At higher finite layers exponents are reduced. Infinite Y is handled
        # by its affine automorphism; binary powering avoids large translations.
        if i == 1:
            b, word = element
            x = word[0]
            rho_g = self.intrinsic.power(self.images[1], n)
            out = self.reduce(self.module.actions[rho_g] @ b), (0,)
            # Sum rho_Y^j(tail), including the signed range for negative n.
            tail = self.zero.copy()
            base = self.tails[1, 0] if n > 0 else self.reduce(-self.rho_inverse[1] @ self.tails[1, 0])
            action = self.rho[1] if n > 0 else self.rho_inverse[1]
            count, current = abs(n), base
            acc_action = np.eye(self.d, dtype=np.int64)
            while count:
                if count & 1:
                    tail = self.reduce(tail + acc_action @ current)
                    acc_action = self.reduce_matrix(acc_action @ action)
                current = self.reduce(current + action @ current)
                action = self.reduce_matrix(action @ action)
                count //= 2
            return self.mul(1, out, self.power(1, (tail, (1,)), x))
        if n < 0:
            raise ArithmeticError("Finite generator exponent was not reduced")
        for _ in range(n):
            element = self.alpha(i, element)
        return element

    def reduce_matrix(self, matrix):
        return matrix % self.mod

    def equations(self):
        rows, mods = [], []
        def equal(left, right):
            if left[1] != right[1]:
                raise ArithmeticError("Inconsistent wallpaper presentation")
            matrix = self.reduce(left[0]-right[0])
            for row, m in zip(matrix, self.module.moduli):
                if np.any(row):
                    rows.append(row)
                    mods.append(m)
        for i in range(self.k):
            # The new automorphism must preserve all earlier relations.
            for j in range(i):
                for l in range(j):
                    # Do not first collect lhs: that would erase the relation.
                    lhs = self.mul(i, self.image(i, j), self.image(i, l))
                    rhs_word = self.space.conjugate_word(j, l)+(0,)*(i-j)
                    rhs = self.word_element(i, rhs_word)
                    rhs = (self.reduce(rhs[0]+self.tails[j, l]), rhs[1])
                    rhs = self.mul(i, self.alpha(i, rhs), self.image(i, j))
                    equal(lhs, rhs)
                n = self.space.orders[j]
                if n:
                    p, w = self.power_element(j)
                    equal(self.power(i, self.image(i, j), n),
                          self.alpha(i, (p, w+(0,)*(i-j))))
            n = self.space.orders[i]
            if n:
                p = self.power_element(i)
                equal(self.alpha(i, p), p)
                for j in range(i):
                    g = self.generator(i, j)
                    equal(self.mul(i, self.alpha_power(i, g, n), p),
                          self.mul(i, p, g))
        equal((self.reduce(2*self.spin), ()), (self.zero, ()))
        for rho in self.rho:
            equal((self.reduce(rho @ self.spin), ()), (self.spin, ()))
        return np.array(rows, dtype=np.int64).reshape(-1, self.width), mods

    def gauge_matrix(self):
        collector = ExtensionCollector(self.space, self.module, self.intrinsic, self.images, gauge=True)
        shifted = []
        for i in range(self.k):
            coeff = collector.zero.copy()
            coeff[:, i*self.d:(i+1)*self.d] = np.eye(self.d, dtype=np.int64)
            shifted.append((coeff, collector.generator(self.k, i)[1]))
        def lifted_word(word):
            out = collector.identity(self.k)
            for i, n in enumerate(word):
                out = collector.mul(self.k, out, collector.power(self.k, shifted[i], n))
            return out
        tails = []
        for i, j in self.relations:
            if i == j:
                w = self.space.power_word(i)+(0,)*(self.k-i)
                tail = collector.reduce(collector.power(self.k, shifted[i], self.space.orders[i])[0]
                                        - lifted_word(w)[0])
            else:
                left = collector.mul(self.k, shifted[i], shifted[j])
                w = self.space.conjugate_word(i, j)+(0,)*(self.k-i)
                right = collector.mul(self.k, lifted_word(w), shifted[i])
                tail = collector.reduce(left[0]-right[0])
            tails.append(tail)
        tails.append(collector.zero)
        return np.vstack(tails)

    def cohomology(self):
        if not self.d:
            return CohomologyQuotient([], [], [], np.zeros((0, 0), dtype=np.int64))
        equations, mods = self.equations()
        return CohomologyQuotient(self.module.moduli*(len(self.relations)+1), equations,
                                  mods, self.gauge_matrix())

    @lru_cache(maxsize=8192)
    def cocycle_matrix(self, g, h):
        # The canonical section is the ordered product of the chosen lifts.
        left, right = (self.zero, g), (self.zero, h)
        a, word = self.mul(self.k, left, right)
        if word != self.space.multiply(g, h):
            raise ArithmeticError("Collector disagrees with wallpaper multiplication")
        return a
