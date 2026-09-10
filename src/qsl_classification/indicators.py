"""Universal anomaly indicators, arXiv:2309.15118, Eqs. (209)-(213).

The tensor contractions retain every fusion-multiplicity index. Expensive
topological contractions are independent of the fractionalization class and
are cached. Dependence on eta is kept as a finite Fourier polynomial.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import lcm
import numpy as np
from .symbols import spin_cocycle


class IndicatorError(ArithmeticError):
    pass


class TopologicalWeights:
    def __init__(self, category, intrinsic):
        self.c, self.intr = category, intrinsic
        self.D = category.total_quantum_dimension
        self.fusion = {(a,b): tuple(category.fusion(a,b)) for a in category.anyons for b in category.anyons}
        self.N = category.N

    @lru_cache(maxsize=16384)
    def F(self, a, b, c, d, e, f):
        shape = (self.N(a,b,e), self.N(e,c,d), self.N(b,c,f), self.N(a,f,d))
        out = np.empty(shape, dtype=complex)
        for indices in np.ndindex(shape):
            out[indices] = self.c.F(a,b,c,d,e,f,*indices)
        return out

    @lru_cache(maxsize=16384)
    def Uinv(self, g, a, b, c):
        if self.intr.sym is None:
            return np.eye(self.N(a,b,c), dtype=complex)
        return np.asarray(self.intr.sym.U_matrix(g,a,b,c)).conj().T

    @lru_cache(maxsize=256)
    def i3(self, g, h):
        c, act = self.c, self.intr.action
        terms = defaultdict(complex)
        for a in c.anyons:
            if act(g,a) != a:
                continue
            ha = act(h,a)
            for b in c.anyons:
                gb = act(g,b)
                for x in self.fusion[a,b]:
                    if not self.N(x,gb,ha):
                        continue
                    gx = act(g,x)
                    u1, u2 = self.Uinv(g,a,b,x), self.Uinv(g,x,gb,ha)
                    for u in self.fusion[b,gb]:
                        if not self.N(a,u,ha):
                            continue
                        R = np.asarray(c.R_matrix(b,gb,u))
                        f1, f2 = self.F(a,b,gb,ha,x,u).conj(), self.F(a,gb,b,ha,gx,u)
                        value = np.einsum('rs,ijsa,klra,ik,jl->',R,f1,f2,u1,u2,optimize=True)
                        terms[a,b] += c.quantum_dimension(b)*c.spin(x)/c.spin(a)*value/self.D**2
        return tuple((key,z) for key,z in terms.items() if abs(z)>1e-10)

    @lru_cache(maxsize=256)
    def i2(self, g, h):
        cat, act = self.c, self.intr.action
        terms = defaultdict(complex)
        for a,b,c in product(cat.anyons, repeat=3):
            ga, gb, gc = act(g,a), act(h,b), act(g,c)
            hc, ghc = act(h,c), act(g,act(h,c))
            for x in self.fusion[ga,hc]:
                if not self.N(x,c,a):
                    continue
                gx = act(g,x)
                ux, vx = self.Uinv(g,ga,hc,x), self.Uinv(g,x,c,a)
                for y in self.fusion[c,b]:
                    if not self.N(gc,y,gb):
                        continue
                    hy = act(h,y)
                    uy, vy = self.Uinv(h,gc,y,gb).conj(), self.Uinv(h,c,b,y).conj()
                    for u in self.fusion[gc,hc]:
                        for v in self.fusion[a,b]:
                            if not self.N(x,y,v):
                                continue
                            R = np.asarray(cat.R_matrix(gc,hc,u))
                            fs = [self.F(a,ghc,hy,v,gx,b), self.F(hc,gc,y,hy,u,gb),
                                  self.F(gx,gc,hc,x,ga,u), self.F(gx,u,y,v,x,hy),
                                  self.F(x,c,b,v,a,y)]
                            if any(not f.size for f in fs):
                                continue
                            value = np.einsum('rs,mAot,rBkp,nisC,CDBA,jtlD,im,jn,ko,lp->',
                                              R,*(f.conj() for f in fs),ux,vx,uy,vy,optimize=True)
                            terms[a,b,c] += (cat.quantum_dimension(c)*cat.quantum_dimension(v)*
                                            cat.spin(v)/(cat.spin(a)*cat.spin(b))*value/self.D**3)
        return tuple((key,z) for key,z in terms.items() if abs(z)>1e-10)


class FourierIndicator:
    def __init__(self, terms, exponent, rank):
        combined = defaultdict(complex)
        for key,z in terms:
            combined[tuple(int(v) % exponent for v in key)] += z
        combined = {k:z for k,z in combined.items() if abs(z)>1e-9}
        self.vectors = np.array(list(combined),dtype=np.int64).reshape(len(combined),rank)
        self.weights = np.array(list(combined.values()),dtype=complex)
        self.exponent = exponent
        self.roots = np.exp(2j*np.pi*np.arange(exponent)/exponent)

    def values(self, coordinates):
        return self.roots[(np.asarray(coordinates,dtype=np.int64) @ self.vectors.T) % self.exponent] @ self.weights


class AnomalySystem:
    def __init__(self, collector, quotient, weights):
        self.e, self.q, self.w = collector, quotient, weights
        self.cat, self.intr = weights.c, weights.intr
        self.rank = len(quotient.orders)
        self.exponent = lcm(*collector.module.moduli) if collector.d else 1
        self.characters = {}
        for a in self.cat.anyons:
            chars = []
            for b in collector.module.basis:
                z = collector.module.braiding[a,b]
                n = round(np.angle(z)*self.exponent/(2*np.pi)) % self.exponent
                if abs(z-np.exp(2j*np.pi*n/self.exponent)) > 1e-7:
                    raise IndicatorError("Monodromy does not define the expected Abelian character")
                chars.append(n)
            self.characters[a] = np.array(chars,dtype=np.int64)
        self.spin = collector.spin @ quotient.lifts
        self.specs = self.specifications()
        self.indicators = [self.compile(*spec) for spec in self.specs]

    def specs_element(self, x=0,y=0,c=0,m=0,t=0,spin=0):
        q = ((1.,0.,0.,0.),(0.,1.,0.,0.),(0.,0.,1.,0.))[spin]
        return self.e.space.element(x,y,c,m,t), q

    def specifications(self):
        S, n = self.specs_element, self.e.space.n
        if not self.e.space.mirror:
            points = [(0,0),(1,1),(1,0)] if n == 4 else [(0,0),(1,0)]
            return [(3,S(x,y,n//2,spin=1),S(x,y,n//2,spin=2)) for x,y in points]
        T,M,Ct = S(t=1),S(m=1),S(c=n//2,t=1)
        if n == 6:
            Cm, Bt = S(c=3,m=1), S(1,1,3,t=1)
            specs = [(0,), (1,T),(1,M),(1,Ct),(1,Cm),
                     (2,T,Ct),(2,T,M),(2,Ct,M),(2,Ct,Cm),(2,M,Cm),
                     (1,Bt),(2,M,Bt),(2,T,Bt),(2,M,S(1,1,3,m=1)),
                     (1,S(t=1,spin=1)),(1,S(m=1,spin=1)),(1,S(c=3,t=1,spin=1)),
                     (1,S(c=3,m=1,spin=1)),(1,S(1,1,3,t=1,spin=1)),(4,),
                     (3,S(c=3,spin=1),S(spin=2)),(3,S(m=1,t=1,spin=1),S(spin=2))]
        else:
            Cm,Xm,Xt,Bt = S(c=1,m=1),S(1,m=1),S(1,c=2,t=1),S(1,1,2,t=1)
            specs = [(0,), (1,T),(1,M),(1,Ct),(1,Cm),
                     (2,T,Ct),(2,T,M),(2,T,Cm),(2,Ct,M),(2,Ct,Cm),
                     (1,Xm),(1,Xt),(1,Bt),(2,T,Xm),(2,T,Xt),(2,T,Bt),
                     (2,S(0,1,2,t=1),M),(2,M,S(0,1,2,m=1)),
                     (2,S(1,-1,2,t=1),Cm),(2,Bt,Xm),(4,),
                     (1,S(t=1,spin=1)),(1,S(m=1,spin=1)),(1,S(c=2,t=1,spin=1)),
                     (1,S(c=1,m=1,spin=1)),(1,S(1,m=1,spin=1)),
                     (1,S(1,c=2,t=1,spin=1)),(1,S(1,1,2,t=1,spin=1)),
                     (3,S(c=1,m=1,t=1,spin=1),S(spin=2)),
                     (3,S(m=1,t=1,spin=1),S(spin=2)),
                     (3,S(1,m=1,t=1,spin=1),S(spin=2))]
        return specs

    def target(self, parity):
        a,b,c = (parity.get(x,0) for x in 'abc')
        if not self.e.space.mirror:
            return [a,b,c] if self.e.space.n == 4 else [a,c]
        result = [0]*len(self.specs)
        indices = {3:a,5:a,10:c,12:c,20:a} if self.e.space.n == 6 else {3:a,5:a,11:c,12:b,14:c,15:b}
        for i, v in indices.items():
            result[i] = v
        return result

    @lru_cache(maxsize=128)
    def t(self, g, h):
        return (self.e.cocycle_matrix(g[0],h[0]) @ self.q.lifts + spin_cocycle(g[1],h[1])*self.spin)

    def compile(self, kind, g=None, h=None):
        cat, D = self.cat, self.w.D
        z = np.zeros(self.rank,dtype=np.int64)
        if kind == 0:
            terms = [(z,sum(cat.quantum_dimension(a)**2*cat.spin(a) for a in cat.anyons)/D)]
        elif kind == 4:
            terms = [(self.characters[a] @ self.spin,cat.quantum_dimension(a)**2*cat.spin(a)/D) for a in cat.anyons]
        else:
            G = self.intr.word(self.e.images,g[0])
            H = self.intr.word(self.e.images,h[0]) if h else None
            def eta(a,k,l):
                return self.intr.sym.eta(a,k,l) if self.intr.sym else 1
            gg = self.t(g,g)
            if kind == 1:
                terms = [(self.characters[a] @ gg,cat.quantum_dimension(a)*cat.spin(a)*eta(a,G,G)/D)
                         for a in cat.anyons if self.intr.action(G,a) == a]
            elif kind == 3:
                comm = self.t(h,g)-self.t(g,h)
                terms = [(self.characters[a] @ comm-self.characters[b] @ gg,
                          v/eta(b,G,G)*eta(a,H,G)/eta(a,G,H)) for (a,b),v in self.w.i3(G,H)]
            else:
                hh, comm = self.t(h,h), self.t(h,g)-self.t(g,h)
                terms = [(self.characters[a] @ gg+self.characters[b] @ hh+self.characters[c] @ comm,
                          v*eta(a,G,G)*eta(b,H,H)*eta(c,H,G)/eta(c,G,H))
                         for (a,b,c),v in self.w.i2(G,H)]
        return FourierIndicator(terms,self.exponent,self.rank)

    def values(self, coordinates):
        coordinates = np.asarray(coordinates,dtype=np.int64).reshape(-1,self.rank) if self.rank else np.zeros((len(coordinates),0),dtype=np.int64)
        return np.array([f.values(coordinates) for f in self.indicators]).T

    def quadratic(self):
        """Polarize the relative obstruction, a quadratic function on H².

        A diagonal polarization term multiplies binomial(n_i,2), so Z4
        factors are not incorrectly reduced to Z2. Non-sign indicators are
        rejected instead of rounding a malformed category to a classification.
        """
        r = self.rank
        points = [np.zeros(r,dtype=np.int64)]
        points += [np.eye(r,dtype=np.int64)[i] for i in range(r)]
        pairs = [(i,j) for i in range(r) for j in range(i,r)]
        points += [np.eye(r,dtype=np.int64)[i]+np.eye(r,dtype=np.int64)[j] for i,j in pairs]
        vals = self.values(points)
        bits = self._bits(vals)
        base = bits[0]
        linear = bits[1:r+1] ^ base
        quad = bits[r+1:] ^ base
        for k,(i,j) in enumerate(pairs):
            quad[k] ^= linear[i] ^ linear[j]
        model = QuadraticIndicators(base,linear,pairs,quad)
        rng = np.random.default_rng(230915118)
        probes = np.array([[rng.integers(m) for m in self.q.orders] for _ in range(24)],dtype=np.int64)
        if not np.array_equal(self._bits(self.values(probes)),model.evaluate(probes)):
            raise IndicatorError("Relative anomaly failed the quadratic polarization check")
        return model

    @staticmethod
    def _bits(values):
        if np.max(np.minimum(abs(values-1),abs(values+1)),initial=0) > 2e-7:
            bad = values[np.minimum(abs(values-1),abs(values+1))>2e-7][0]
            raise IndicatorError(f"An anomaly indicator is {bad!r}, not ±1; check category and symmetry coherence")
        return (values.real < 0).astype(np.uint8)


class QuadraticIndicators:
    def __init__(self, base, linear, pairs, quad):
        self.base, self.linear, self.pairs, self.quad = base,linear,pairs,quad

    def evaluate(self, coords):
        out = np.broadcast_to(self.base,(len(coords),len(self.base))).copy()
        for i, v in enumerate(self.linear):
            if v.any():
                out ^= ((coords[:,i] % 2)[:,None]*v).astype(np.uint8)
        for (i,j),v in zip(self.pairs,self.quad):
            if v.any():
                p = coords[:,i]*(coords[:,i]-1)//2 if i==j else coords[:,i]*coords[:,j]
                out ^= ((p % 2)[:,None]*v).astype(np.uint8)
        return out
