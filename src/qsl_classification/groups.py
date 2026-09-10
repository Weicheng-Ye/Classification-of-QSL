"""Exact infinite wallpaper groups, and their continuous spin factor."""
from dataclasses import dataclass
from functools import cached_property, lru_cache
from itertools import product
import re


WALLPAPER_NAMES = ('p1','p2','pm','pg','cm','pmm','pmg','pgg','cmm',
                   'p4','p4m','p4g','p3','p3m1','p31m','p6','p6m')
BILBAO_NAMES = ('p1','p2','p1m1','p1g1','c1m1','p2mm','p2mg','p2gg',
                'c2mm','p4','p4mm','p4gm','p3','p3m1','p31m','p6','p6mm')
ROTATIONS = (1,2,1,1,1,2,2,2,2,4,4,4,3,3,3,6,6)
MIRRORS = {3,4,5,6,7,8,9,11,12,14,15,17}
IDENTITY_MATRIX = (1,0,0,1)


def matmul(a, b):
    return (a[0]*b[0]+a[1]*b[2], a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2], a[2]*b[1]+a[3]*b[3])


def matvec(a, v):
    return (a[0]*v[0]+a[1]*v[1], a[2]*v[0]+a[3]*v[1])


@dataclass(frozen=True)
class SpaceGroup:
    """Primitive affine presentations, Appendix E of arXiv:2111.12097.

    The first two constructor arguments retain the v0.1 API. Translations
    are arbitrary integers; doubled displacements keep glides exact.
    """
    n: int = 4
    mirror: bool = False
    number: int = 0
    time_reversal: bool | None = None

    def __post_init__(self):
        number = self.number or {(4,False):10,(6,False):16,(4,True):11,(6,True):17}.get((self.n,self.mirror))
        if type(number) is not int or not 1 <= number <= 17:
            raise ValueError('Plane-group IT number must be an integer from 1 to 17')
        object.__setattr__(self, 'number', number)
        object.__setattr__(self, 'n', ROTATIONS[number-1])
        object.__setattr__(self, 'mirror', number in MIRRORS)
        if self.time_reversal is None:
            object.__setattr__(self, 'time_reversal', self.mirror)
        if type(self.time_reversal) is not bool:
            raise TypeError('time_reversal must be a boolean')

    @classmethod
    def parse(cls, name, time_reversal=None):
        if type(name) is int or isinstance(name,str) and name.strip().isdigit():
            if not 1 <= int(name) <= 17:
                raise ValueError('Plane-group IT number must be between 1 and 17')
            return cls(number=int(name), time_reversal=True if time_reversal is None else time_reversal)
        if not isinstance(name,str):
            raise ValueError('Use a plane-group IT number (1–17) or wallpaper group name')
        s = re.sub(r'\s+', '', name).replace('×','*').replace('x','*')
        s = s.replace('SO(3)*Z2T','O(3)').replace('SO(3)*Z_2^T','O(3)')
        base, *factors = s.split('*')
        aliases = dict(zip(WALLPAPER_NAMES,range(1,18))) | dict(zip(BILBAO_NAMES,range(1,18)))
        if base not in aliases or factors not in ([],['SO(3)'],['O(3)']):
            raise ValueError('Use a plane-group IT number (1–17), optionally with SO(3) or O(3)')
        specified = factors == ['O(3)'] if factors else None
        if time_reversal is not None and specified is not None and time_reversal != specified:
            raise ValueError('time_reversal conflicts with the symmetry-group suffix')
        tr = time_reversal if time_reversal is not None else specified if specified is not None else True
        return cls(number=aliases[base],time_reversal=tr)

    @property
    def name(self):
        return WALLPAPER_NAMES[self.number-1] + ('*O(3)' if self.time_reversal else '*SO(3)')

    @cached_property
    def names(self):
        return ('T1','T2') + ((f'C{self.n}',) if self.n > 1 else ()) + \
            (('L' if self.number in (4,8,12) else 'M',) if self.mirror else ()) + \
            (('T',) if self.time_reversal else ())

    @cached_property
    def orders(self):
        return (0,0) + ((self.n,) if self.n > 1 else ()) + ((2,) if self.mirror else ()) + ((2,) if self.time_reversal else ())

    @property
    def gradings(self):
        return tuple(int(g in ('M','L','T')) for g in self.names)

    def parity(self, g):
        return sum(a*b for a,b in zip(g,self.gradings)) % 2

    @cached_property
    def rotation_matrix(self):
        return {1:IDENTITY_MATRIX,2:(-1,0,0,-1),3:(0,-1,1,-1),
                4:(0,-1,1,0),6:(1,-1,1,0)}[self.n]

    @cached_property
    def mirror_matrix(self):
        if self.number == 14:
            return (0,-1,-1,0)
        return (0,1,1,0) if self.number in (5,9,12,15,17) else (-1,0,0,1)

    @property
    def mirror_shift(self):
        return {4:(0,1),7:(1,0),8:(1,1),12:(1,1)}.get(self.number,(0,0))

    @lru_cache(maxsize=128)
    def point_affine(self, c, m):
        r = IDENTITY_MATRIX
        for _ in range(c % self.n):
            r = matmul(r,self.rotation_matrix)
        shift = matvec(r,self.mirror_shift) if m else (0,0)
        return matmul(r,self.mirror_matrix) if m else r, shift

    @property
    def identity(self):
        return (0,)*len(self.names)

    def element(self, x=0, y=0, c=0, m=0, t=0):
        if any(type(v) is not int for v in (x,y,c,m,t)):
            raise ValueError('Wallpaper coordinates must be integers')
        if self.n == 1 and c or not self.mirror and m or not self.time_reversal and t:
            raise ValueError('This group does not have the requested rotation, mirror, or time reversal generator')
        if self.mirror:
            carry, m = divmod(m,2)
            displacement = matvec(self.point_affine(c,0)[0],
                                   {4:(0,1),8:(0,1),12:(1,1)}.get(self.number,(0,0)))
            x, y = x+carry*displacement[0], y+carry*displacement[1]
        return (x,y) + ((c % self.n,) if self.n > 1 else ()) + ((m,) if self.mirror else ()) + ((t % 2,) if self.time_reversal else ())

    def coordinates(self, g):
        if len(g) != len(self.names) or any(type(v) is not int for v in g):
            raise ValueError(f'Use integer coordinates for {self.names}')
        return self.element(*self.components(g))

    def components(self, g):
        d = dict(zip(self.names,g))
        return g[0],g[1],d.get(f'C{self.n}',0),d.get('M',d.get('L',0)),d.get('T',0)

    def multiply(self, g, h):
        if len(g) != len(self.names) or len(h) != len(self.names):
            raise ValueError('Wrong number of wallpaper coordinates')
        x,y,c,m,t = self.components(g)
        X,Y,C,M,T = self.components(h)
        a,u = self.point_affine(c,m)
        _,v = self.point_affine(C,M)
        rx,ry = matvec(a,(2*X+v[0],2*Y+v[1]))
        nc,nm = (c+(-1)**m*C) % self.n,(m+M) % 2
        _,w = self.point_affine(nc,nm)
        dx,dy = rx+u[0]-w[0],ry+u[1]-w[1]
        if dx % 2 or dy % 2:
            raise ArithmeticError('Affine product left the primitive translation lattice')
        return self.element(x+dx//2,y+dy//2,nc,nm,t+T)

    def power(self, g, n):
        if n < 0:
            g, n = self.inverse(g), -n
        out = self.identity
        while n:
            if n & 1:
                out = self.multiply(out,g)
            g = self.multiply(g,g)
            n //= 2
        return out

    def inverse(self, g):
        x,y,c,m,t = self.components(g)
        nc = -(-1)**m*c % self.n
        trial = self.element(c=nc,m=m,t=t)
        residual = self.multiply(g,trial)
        matrix,_ = self.point_affine(nc,m)
        dx,dy = matvec(matrix,(-residual[0],-residual[1]))
        return self.element(dx,dy,nc,m,t)

    def generator(self, name):
        if name not in self.names:
            raise ValueError(f'No generator {name!r} in {self.name}')
        return tuple(int(g == name) for g in self.names)

    def power_word(self, i):
        if self.names[i] == 'L':
            return {4:(0,1),8:(0,1),12:(1,1)}[self.number]+(0,)*(i-2)
        return (0,)*i

    def conjugate_word(self, i, j):
        w = [0]*i
        ni,nj = self.names[i],self.names[j]
        if ni.startswith('C') and j < 2:
            a = self.rotation_matrix
            w[:2] = (a[j],a[2+j])
        elif ni in ('M','L') and j < 2:
            a = self.mirror_matrix
            w[:2] = (a[j],a[2+j])
        elif ni in ('M','L') and nj.startswith('C'):
            w[j] = -1
            w[:2] = {7:(1,0),8:(1,1),12:(0,1)}.get(self.number,(0,0))
        else:
            w[j] = 1
        return tuple(w)

    @property
    def lattice_rank(self):
        return (1,4,2,1,1,4,3,2,3,3,3,2,1,1,1,2,2)[self.number-1]

    @property
    def legacy_indicators(self):
        return (self.number,self.time_reversal) in ((10,False),(16,False),(11,True),(17,True))

    @property
    def lattice_keys(self):
        if self.legacy_indicators:
            return tuple('abc' if self.n == 4 else 'ac')
        return tuple(f'l{i+1}' for i in range(self.lattice_rank))

    def lattice(self, wps):
        from .wyckoff import lattice_class
        return lattice_class(self,wps)


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
        options = [self.anti if p else self.unitary for p in space.gradings]
        for images in product(*options):
            if any(n and self.power(g, n) != self.word(images[:i],space.power_word(i))
                   for i,(g,n) in enumerate(zip(images,space.orders))):
                continue
            if all(self.mul(images[i], images[j]) ==
                   self.mul(self.word(images[:i], space.conjugate_word(i, j)), images[i])
                   for i in range(len(images)) for j in range(i)):
                yield images

    def conjugated(self, images, k):
        return tuple(self.mul(self.mul(k, g), self.power(k, -1)) for g in images)
