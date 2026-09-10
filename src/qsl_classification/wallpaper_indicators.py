"""Anomaly coordinates for all wallpaper groups, with optional independent T.

Recipes and target bases are in docs/anomaly-indicators-all-wallpaper-groups.md.
I0--I4 retain the full F,R,U contractions in indicators.py. S2 insertions
use the invariant spin-flux anyon. The remaining two product manifolds use
the reference partition function and the relative obstruction.
"""
from functools import lru_cache
import re
import numpy as np
from .indicators import AnomalySystem, IndicatorError


# Surfaces dual to the ordered H²(P,Z2) basis; LSM coordinates come first.
SURFACES = {
    1: [('tor','X','Y')],
    2: [('rp',g) for g in ('C2','XC2','YC2','XYC2')],
    3: [('mtor','M','Y'),('mtor','XM','Y'),('rp','M'),('rp','XM')],
    4: [('kl','X','L')],
    5: [('mtor','M','XY'),('rp','M')],
    6: [('rp',g) for g in ('C2','XYC2','XC2','YC2','M','C2M','XM','YC2M')],
    7: [('rp','C2'),('rp','XYC2'),('mtor','M','Y'),('rp','M')],
    8: [('rp','C2'),('rp','XC2')],
    9: [('rp',g) for g in ('C2','XYC2','XC2','M','C2M')],
    10: [('rp',g) for g in ('R','XYR','XR')],
    11: [('rp',g) for g in ('R','XYR','XR','M','XM','C4M')],
    12: [('rp',g) for g in ('R','XR','X^-1L')],
    13: [('tor','X','Y')],
    14: [('mtor','M','XY^-1'),('rp','M')],
    15: [('mtor','M','XY'),('rp','M')],
    16: [('rp','R'),('rp','XR')],
    17: [('rp',g) for g in ('R','XR','M','RM')],
}

# Degree-one representatives. A tuple denotes a product of OLD W_o terms;
# a string uses the spin-flux reduction of N1(TU;hat(g),V).
DEGREE_ONE = {
    1:['X','Y'], 2:[('C2','XC2'),('C2','YC2'),('C2',)],
    3:[('M','XM'),'Y',('M',)], 4:['X','L'], 5:['X',('M',)],
    6:[('C2','XC2'),('XYC2','XC2'),('C2',),('M',)],
    7:[('C2','XYC2'),('C2',),('M',)], 8:[('C2',),'L'],
    9:[('C2','XC2'),('C2',),('M',)], 10:['C4',('XR',)],
    11:[('M','C4M'),('XR',),('M',)], 12:['C4',('X^-1L',)],
    13:[], 14:[('M',)], 15:[('M',)], 16:[('R',)], 17:[('R',),('M',)],
}

# (old indicator, spatial words, one-based LSM target coordinate or 0).
SPATIAL_T = {
    1:[], 2:[('F',g,i+1) for i,g in enumerate(('C2','XC2','YC2','XYC2'))],
    3:[('F','M',0),('F','XM',0),('J','M','Y',1),('J','XM','Y',2)],
    4:[], 5:[('F','M',0),('J','M','XY',1)],
    6:[('F',g,0) for g in ('M','C2M','XM','YC2M')]
      +[('F',g,i+1) for i,g in enumerate(('C2','XYC2','XC2','YC2'))],
    7:[('F','M',0),('F','C2',1),('F','XYC2',2),('J','M','Y',3)],
    8:[('F','C2',1),('F','XC2',2)],
    9:[('F','M',0),('F','C2M',0),('F','C2',1),('F','XYC2',2),('F','XC2',3),
       ('H','M','C2M',0),('H','M','XYC2M',0),('J','M','C2M',1),('J','M','XYC2M',2)],
    10:[('F','R',1),('F','XYR',2),('F','XR',3)],
    11:[('F','M',0),('F','XM',0),('F','C4M',0),('F','R',1),('F','XYR',2),('F','XR',3),
        ('J','M','RM',1),('J','C4M','C4^3M',1),('J','XM','YRM',2),
        ('J','XYC4M','C4^3M',2),('H','XM','RM',0),('J','XM','RM',3)],
    12:[('F','X^-1L',0),('F','R',1),('F','XR',2),('H','X^-1L','RL',0),('J','X^-1L','RL',2)],
    13:[],14:[('F','M',0),('J','M','XY^-1',1)],15:[('F','M',0),('J','M','XY',1)],
    16:[('F','R',1),('F','XR',2)],
    17:[('F','M',0),('F','RM',0),('F','R',1),('F','XYR',2),
        ('H','M','RM',0),('H','M','XYRM',0),('J','M','RM',1),('J','M','XYRM',2)],
}
for i,(g,h) in enumerate((('M','C2M'),('XM','YC2M'),('XM','C2M'),('M','YC2M'))):
    SPATIAL_T[6].append(('H',g,h,0))
for i,(g,h) in enumerate((('M','C2M'),('XM','YC2M'),('XM','C2M'),('M','YC2M'))):
    SPATIAL_T[6].append(('J',g,h,i+1))

SPATIAL_NO_T = {
    3:[(1,'M'),(1,'XM')],5:[(1,'M')],
    6:[(1,g) for g in ('M','C2M','XM','YC2M')]
      +[(2,g,h) for g,h in (('M','C2M'),('XM','YC2M'),('XM','C2M'),('M','YC2M'))],
    7:[(1,'M')],9:[(1,'M'),(1,'C2M'),(2,'M','C2M'),(2,'M','XYC2M')],
    11:[(1,'M'),(1,'XM'),(1,'C4M'),(2,'M','RM'),(2,'XM','YRM'),(2,'XM','RM')],
    12:[(1,'X^-1L'),(2,'X^-1L','RL')],
    14:[(1,'M')],15:[(1,'M')],
    17:[(1,'M'),(1,'RM'),(2,'M','RM'),(2,'M','XYRM')],
}


class Expression:
    def __init__(self, factors=(), function=None):
        self.factors, self.function = tuple(factors), function

    def values(self, coordinates):
        if self.function is not None:
            return np.array([self.function(q) for q in coordinates],dtype=complex)
        result = np.ones(len(coordinates),dtype=complex)
        for f,power in self.factors:
            result *= f.values(coordinates)**power
        return result

    def __mul__(self, other):
        return Expression(((self,1),(other,1)))

    def __truediv__(self, other):
        return Expression(((self,1),(other,-1)))


class WallpaperAnomalySystem(AnomalySystem):
    def specifications(self):
        return []

    def __init__(self, collector, quotient, weights):
        super().__init__(collector,quotient,weights)
        self.space = collector.space
        self.I, self.U, self.V = ((1.,0.,0.,0.),(0.,1.,0.,0.),(0.,0.,1.,0.))
        self.word = lru_cache(maxsize=None)(self.word)
        self.old = lru_cache(maxsize=None)(self.old)
        self.targets = []
        self.build()

    def word(self, text):
        aliases = {'X':'T1','Y':'T2'}
        out = self.space.identity
        pos = 0
        for token in re.finditer(r'(C[2346]|X|Y|R|M|L|T)(?:\^(-?\d+))?',text):
            if token.start() != pos:
                raise ValueError(f'Invalid generator word {text!r}')
            name, power = token[1], int(token[2] or 1)
            if name == 'R':
                name, power = f'C{self.space.n}', power*(self.space.n//2)
            g = self.space.generator(aliases.get(name,name))
            out = self.space.multiply(out,self.space.power(g,power))
            pos = token.end()
        if pos != len(text):
            raise ValueError(f'Invalid generator word {text!r}')
        return out

    def hat(self, g):
        return self.space.multiply(g,self.word('T')) if self.space.parity(g) else g

    def anti(self, g):
        return self.space.multiply(self.word('T'),self.hat(g))

    def old(self, kind, g=None, h=None, spin_g=0, spin_h=0):
        spins = (self.I,self.U,self.V)
        g = (g,spins[spin_g]) if g is not None else None
        h = (h,spins[spin_h]) if h is not None else None
        if kind in (1,2):
            for v in (g,h):
                if v is not None and (self.space.multiply(v[0],v[0]) != self.space.identity
                                      or self.space.parity(v[0]) != 1):
                    raise IndicatorError('RP indicators require antiunitary involutions')
        if kind == 3 and (self.space.multiply(g[0],g[0]) != self.space.identity
                          or self.space.parity(g[0]) or self.space.parity(h[0])):
            raise IndicatorError('I3/J requires a unitary first involution and a unitary second argument')
        if h is not None and self.space.multiply(g[0],h[0]) != self.space.multiply(h[0],g[0]):
            raise IndicatorError('Product-manifold holonomies must commute')
        return Expression(((self.compile(kind,g,h),1),))

    def eta(self, a, g, h, q):
        G,H = (self.intr.word(self.e.images,w) for w in (g,h))
        ref = self.intr.sym.eta(a,G,H) if self.intr.sym else 1
        t = self.e.cocycle_matrix(g,h) @ self.q.lifts @ q
        return ref*np.exp(2j*np.pi*(self.characters[a] @ t)/self.exponent)

    def spin_flux(self, q):
        return self.e.module.label(self.spin @ q)

    def flux_commutator(self, g, h, *, crosscap=False):
        def value(q):
            v = self.spin_flux(q)
            out = self.eta(v,g,h,q)/self.eta(v,h,g,q)
            if crosscap and self.intr.sym:
                H = self.intr.word(self.e.images,h)
                out /= self.intr.sym.U_matrix(H,v,v,self.cat.vacuum)[0][0]
            return out
        return Expression(function=value)

    def klein_flux(self, b, l):
        inverse = self.space.inverse(b)
        def value(q):
            v = self.spin_flux(q)
            return self.eta(v,l,b,q)*self.eta(v,inverse,b,q)/self.eta(v,inverse,l,q)
        return Expression(function=value)

    def product_manifold(self, a, b, c, *, klein=False):
        from .relative_anomaly import ProductAnomaly
        return Expression(function=ProductAnomaly(self,a,b,c,klein=klein))

    def s_rp(self, g):
        if self.space.time_reversal:
            a = self.anti(g)
            t = self.word('T')
            return self.old(1,a,spin_g=1)*self.old(1,t)/(self.old(1,a)*self.old(1,t,spin_g=1))
        if self.space.parity(g):
            return self.old(1,g,spin_g=1)/(self.old(1,g)*self.B)
        return self.old(3,g,g,1,2)

    def w_rp(self, g):
        return self.old(3,self.hat(g),self.hat(g),1,2)/self.s_rp(g)

    def add(self, expression, target=0):
        self.indicators.append(expression)
        self.targets.append(target)

    def build(self):
        s, num = self.space, self.space.number
        self.G = self.old(0)
        self.B = self.old(4)/self.G
        if s.time_reversal:
            t = self.word('T')
            self.add(self.G)
            self.add(self.old(1,t))
            self.add(self.B)
            self.add(self.old(1,t,spin_g=1)/(self.old(1,t)*self.B))
            for representative in DEGREE_ONE[num]:
                if isinstance(representative,str):
                    expression = self.flux_commutator(t,self.hat(self.word(representative)),crosscap=True)
                else:
                    expression = Expression()
                    for g in representative:
                        expression = expression*self.w_rp(self.word(g))
                self.add(expression)
        elif s.mirror:
            self.add(self.G)
            self.add(self.B)
        for j,surface in enumerate(SURFACES[num]):
            kind,*words = surface
            g = self.word(words[0])
            h = self.word(words[1]) if len(words)>1 else None
            target = j+1 if j < s.lattice_rank else 0
            if kind == 'rp':
                spin = self.s_rp(g)
                if s.time_reversal:
                    kramers = self.old(2,self.anti(g),t)/self.G
            elif kind == 'tor':
                spin = self.flux_commutator(g,h)
                if s.time_reversal:
                    kramers = self.product_manifold(t,g,h)
            elif kind == 'mtor':
                if s.time_reversal:
                    spin = self.old(3,self.hat(g),h,1)/self.old(3,self.hat(g),h)
                    kramers = self.product_manifold(t,h,self.hat(g))
                else:
                    spin = self.flux_commutator(g,h,crosscap=True)
            else:
                spin = self.klein_flux(g,h)
                if s.time_reversal:
                    kramers = self.product_manifold(t,g,h,klein=True)
            self.add(spin,target)
            if s.time_reversal:
                self.add(kramers,target)
        if s.time_reversal:
            for kind,*words,target in SPATIAL_T[num]:
                g = self.word(words[0])
                h = self.word(words[1]) if len(words)>1 else None
                if kind == 'F':
                    expression = self.old(1,self.anti(g))
                elif kind == 'H':
                    expression = self.old(2,self.anti(g),self.anti(h))
                else:
                    expression = self.old(3,self.hat(g),self.hat(h))
                self.add(expression,target)
        else:
            for kind,*words in SPATIAL_NO_T.get(num,()):
                self.add(self.old(kind,*(self.word(g) for g in words)))

    def target(self, parity):
        values = [0]+[parity[k] for k in self.space.lattice_keys]
        return [values[j] for j in self.targets]
