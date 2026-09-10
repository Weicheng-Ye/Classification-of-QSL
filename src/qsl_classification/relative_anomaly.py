"""Relative obstruction and RP2 product cycles.

The six-F, one-R, two-U, one-eta expression is Eq. (50) of
arXiv:1906.10691 in the internal antiunitary convention. Its transport is
the direct anyon action: the reflection/charge-conjugation conversion
cancels the extra dual in that equation. Reference eta must be retained.
"""
from functools import lru_cache
import numpy as np


class RelativeObstruction:
    def __init__(self, system, coordinates):
        self.s = system
        self.cat, self.intr = system.cat, system.intr
        self.space = system.e.space
        self.parameters = system.q.lifts @ coordinates
        self.module = system.e.module
        self.t = lru_cache(maxsize=None)(self.t)
        self._evaluate = lru_cache(maxsize=None)(self.obstruction)

    def t(self, g, h):
        return self.module.label(self.s.e.cocycle_matrix(g,h) @ self.parameters)

    def image(self, g):
        return self.intr.word(self.s.e.images,g)

    def act(self, g, a):
        return self.intr.action(self.image(g),a)

    def fuse(self, a, b):
        return self.module.add_table[a,b]

    def F(self, a, b, c):
        ab,bc = self.fuse(a,b),self.fuse(b,c)
        return self.cat.F(a,b,c,self.fuse(ab,c),ab,bc)

    def U(self, g, a, b):
        sym = self.intr.sym
        return sym.U(self.image(g),a,b,self.fuse(a,b)) if sym else 1

    def __call__(self, g, h, k, l):
        return self._evaluate(g,h,k,l)

    def obstruction(self, g, h, k, l):
        mul, t = self.space.multiply, self.t
        gh,hk,kl = mul(g,h),mul(h,k),mul(k,l)
        ghk,hkl = mul(gh,k),mul(h,kl)
        a = t(ghk,l)
        b = t(gh,k)
        c = t(g,h)
        d = t(g,hk)
        e = self.act(g,t(h,k))
        f = t(g,hkl)
        u = self.act(g,t(hk,l))
        v = self.act(g,t(h,kl))
        w = self.act(gh,t(k,l))
        z = t(gh,kl)
        result = self.cat.R(w,c,self.fuse(w,c))
        if self.intr.sym:
            result *= self.intr.sym.eta(w,self.image(g),self.image(h))
        result *= self.U(g,u,e).conjugate()*self.U(g,v,w)
        return (result*self.F(a,b,c)*self.F(a,d,e).conjugate()
                *self.F(f,u,e)*self.F(f,v,w).conjugate()
                *self.F(z,c,w)*self.F(z,w,c).conjugate())

    def xi(self, a, g, h):
        o = self
        return o(a,a,g,h)*o(a,g,h,a)*o(g,a,a,h)*o(g,h,a,a)/(o(a,g,a,h)*o(g,a,h,a))

    def torus(self, a, b, c):
        return self.xi(a,b,c)/self.xi(a,c,b)

    def klein(self, a, b, l):
        inverse = self.space.inverse(b)
        return self.xi(a,l,b)*self.xi(a,inverse,b)/self.xi(a,inverse,l)


class ProductAnomaly:
    def __init__(self, system, a, b, c, *, klein=False):
        self.s, self.a, self.b, self.c, self.klein = system,a,b,c,klein
        self.reference = self.reference_value()

    def reference_old(self, kind, *words):
        # Only the pulled-back reference is evaluated here. Image involutions
        # need not be involutions in the infinite wallpaper group.
        args = [(g,(1.,0.,0.,0.)) for g in words]
        return self.s.compile(kind,*args).values(np.zeros((1,self.s.rank),dtype=np.int64))[0]

    def reference_value(self):
        intr, space = self.s.intr,self.s.space
        def image(g):
            return intr.word(self.s.e.images,g)
        def even_part(g):
            order = 1
            while intr.power(image(g),order) != intr.identity:
                order += 1
            while order % 2 == 0:
                order //= 2
            # An odd cover multiplies a sign-valued characteristic number by
            # an odd integer. It removes odd-order reference holonomy only.
            return space.power(g,order)
        a,b,c = self.a,even_part(self.b),even_part(self.c)
        if image(b) == intr.identity:
            return 1+0j
        if not self.klein and image(c) == intr.identity:
            return 1+0j
        if self.klein and intr.power(image(c),2) == intr.identity:
            return self.reference_old(2,a,c)*self.reference_old(2,a,space.multiply(b,c))
        if not self.klein and all(intr.power(image(g),2) == intr.identity for g in (b,c)):
            ab,ac = space.multiply(a,b),space.multiply(a,c)
            abc = space.multiply(ab,c)
            return (self.reference_old(0)*self.reference_old(2,abc,a)
                    /(self.reference_old(2,ab,a)*self.reference_old(2,ac,a)))
        if not self.klein:
            # A torus map into a cyclic subgroup factors through S1.
            for generator in intr.unitary:
                powers = {intr.power(generator,n) for n in range(len(intr.elements))}
                if image(b) in powers and image(c) in powers:
                    return 1+0j
        from .product_state_sum import reference_partition
        return reference_partition(self.s.w,image(a),image(b),image(c),klein=self.klein)

    def __call__(self, coordinates):
        relative = RelativeObstruction(self.s,coordinates)
        value = relative.klein(self.a,self.b,self.c) if self.klein else relative.torus(self.a,self.b,self.c)
        return self.reference*value
