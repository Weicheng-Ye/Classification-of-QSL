"""Reference RP2 x (torus or Klein bottle) partition functions.

Uses a branched product Delta-complex with 24 four-simplices. Face keys
include local incidence data: vertices alone cannot identify loop edges
or the multiple faces in this triangulation.
"""
from collections import defaultdict, deque
from functools import lru_cache
from itertools import combinations, product
import numpy as np


class ProductComplex:
    def __init__(self, intr, a, b, c, *, klein=False):
        self.intr = intr
        one = intr.identity
        # Each entry gives vertices, then edges 01, 02, 12.
        self.rp = [((0,0,1),(0,1,2)),((0,0,1),(0,2,1))]
        self.surface = [((0,0,0),(0,2,1)),
                        ((0,0,0),(2,1,0) if klein else (1,2,0))]
        self.holonomies = ((a,one,a),(b,c,intr.mul(b,c)))
        self.faces = [set() for _ in range(5)]
        tops = []
        for p,q in product(range(2),repeat=2):
            for horizontal in combinations(range(4),2):
                x=y=0
                path=[(x,y)]
                for k in range(4):
                    if k in horizontal:
                        x+=1
                    else:
                        y+=1
                    path.append((x,y))
                top = (p,q,tuple(path))
                tops.append(top)
                for n in range(1,6):
                    for subset in combinations(range(5),n):
                        self.faces[n-1].add(self.face(top,subset))
        self.faces = [tuple(sorted(fs)) for fs in self.faces]
        self.indices = [{f:i for i,f in enumerate(fs)} for fs in self.faces]
        self.tops = tuple(tops)
        self.local = []
        for top in tops:
            self.local.append({subset:self.indices[len(subset)-1][self.face(top,subset)]
                               for n in range(1,6) for subset in combinations(range(5),n)})
        self.edges = [self.edge_holonomy(f) for f in self.faces[1]]
        self.orientation = self.orient()
        counts = tuple(map(len,self.faces))
        if counts != (2,18,52,60,24):
            raise ArithmeticError(f'Incorrect product Delta-complex: {counts}')

    def factor(self, side, triangle, subset):
        vertices,edges = (self.rp if side == 0 else self.surface)[triangle]
        if len(subset) == 1:
            return (0,vertices[subset[0]])
        if len(subset) == 2:
            return (1,edges[((0,1),(0,2),(1,2)).index(tuple(subset))])
        return (2,triangle)

    def face(self, top, subset):
        p,q,path = top
        points = [path[i] for i in subset]
        xs,ys = sorted({v[0] for v in points}),sorted({v[1] for v in points})
        word = tuple((xs.index(x),ys.index(y)) for x,y in points)
        return self.factor(0,p,xs),self.factor(1,q,ys),word

    def edge_holonomy(self, face):
        r,s,_ = face
        a = self.holonomies[0][r[1]] if r[0] else self.intr.identity
        b = self.holonomies[1][s[1]] if s[0] else self.intr.identity
        return self.intr.mul(a,b)

    def orient(self):
        incidences = defaultdict(list)
        for i,local in enumerate(self.local):
            for omitted in range(5):
                subset = tuple(j for j in range(5) if j != omitted)
                grade = self.intr.parity(self.edges[local[3,4]]) if omitted == 4 else 0
                incidences[local[subset]].append((i,(-1)**(omitted+grade)))
        adjacency = defaultdict(list)
        for pair in incidences.values():
            if len(pair) != 2:
                raise ArithmeticError('Product complex is not a closed pseudomanifold')
            (i,x),(j,y) = pair
            adjacency[i].append((j,-x*y))
            adjacency[j].append((i,-x*y))
        orientation={0:1}
        queue=deque([0])
        while queue:
            i=queue.popleft()
            for j,sign in adjacency[i]:
                expected=orientation[i]*sign
                if j in orientation:
                    if orientation[j] != expected:
                        raise ArithmeticError('Holonomy grading does not match the orientation bundle')
                else:
                    orientation[j]=expected
                    queue.append(j)
        if len(orientation) != len(self.tops):
            raise ArithmeticError('Disconnected product complex')
        return tuple(orientation[i] for i in range(len(self.tops)))

    def incidence(self, dimension):
        """Ordered subfaces of every simplex, read from any top incidence."""
        result = {}
        for local in self.local:
            for vertices in combinations(range(5),dimension+1):
                result[local[vertices]] = {
                    subset:local[tuple(vertices[i] for i in subset)]
                    for n in range(1,dimension+2)
                    for subset in combinations(range(dimension+1),n)}
        return [result[i] for i in range(len(self.faces[dimension]))]


class SimplexWeight:
    """The quantum trace (S4) in the companion partition-function document."""
    def __init__(self, weights):
        self.w, self.cat, self.intr = weights,weights.c,weights.intr

    @lru_cache(maxsize=8192)
    def tensor(self, faces, tetrahedra, h23, h34):
        c,w,intr = self.cat,self.w,self.intr
        a012,a013,a014,a023,a024,a034,a123,a124,a134,a234 = faces
        b0,b1,b2,b3,b4 = tetrahedra
        h24 = intr.mul(h23,h34)
        def act(g,a):
            return intr.action(intr.power(g,-1),a)
        z,barb0 = act(h24,a012),act(h34,b0)
        q = intr.parity(h34)
        uminus = w.Uinv(h34,a023,act(h23,a012),b0)
        uplus = w.Uinv(h34,a013,a123,b0).conj().T
        if q:
            uminus,uplus = uminus.conj(),uplus.conj()
        eta = intr.sym.eta(a012,h23,h34) if intr.sym else 1
        if intr.parity(h24):
            eta = eta.conjugate()
        shape = (c.N(a023,act(h23,a012),b0),c.N(a013,a123,b0),
                 c.N(a024,z,b1),c.N(a014,a124,b1),
                 c.N(a034,act(h34,a013),b2),c.N(a014,a134,b2),
                 c.N(a034,act(h34,a023),b3),c.N(a024,a234,b3),
                 c.N(a134,act(h34,a123),b4),c.N(a124,a234,b4))
        result = np.zeros(shape,dtype=complex)
        if not all(shape):
            return result
        for t in c.anyons:
            for x in c.fusion(z,a234):
                fs = (
                    w.F(a024,a234,z,t,b3,x),
                    w.F(a024,z,a234,t,b1,x),
                    w.F(a014,a124,a234,t,b1,b4),
                    w.F(a014,a134,act(h34,a123),t,b2,b4),
                    w.F(a034,act(h34,a013),act(h34,a123),t,b2,barb0),
                    w.F(a034,act(h34,a023),z,t,b3,barb0))
                if any(not f.size for f in fs):
                    continue
                r = np.asarray(c.R_matrix(z,a234,x))
                result += c.quantum_dimension(t)*np.einsum(
                    'hpAr,AB,cqBr,dqjs,ftis,etNu,gpMu,aM,Nb->abcdefghij',
                    fs[0],r,fs[1].conj(),fs[2],fs[3].conj(),fs[4],fs[5].conj(),
                    uminus,uplus,optimize=True)
        return result/eta


def pointed_partition(weights, triangulation):
    """Gauge-reduced two-form Gauss sum, with arbitrary pointed F,R,U,eta."""
    from .algebra import AnyonModule, CohomologyQuotient
    module = AnyonModule(weights.c,weights.intr)
    d = module.rank
    nt,ne,nf = (len(triangulation.faces[k]) for k in (3,1,2))
    if not d:
        return 1+0j
    triangles,tetrahedra = triangulation.incidence(2),triangulation.incidence(3)
    differential1 = np.zeros((nf*d,ne*d),dtype=np.int64)
    differential2 = np.zeros((nt*d,nf*d),dtype=np.int64)
    eye = np.eye(d,dtype=np.int64)
    def transport(edge):
        return module.actions[weights.intr.power(triangulation.edges[edge],-1)]
    for i,local in enumerate(triangles):
        for edge,matrix in (((1,2),eye),((0,2),-eye),((0,1),transport(local[1,2]))):
            j=local[edge]
            differential1[i*d:(i+1)*d,j*d:(j+1)*d] += matrix
    for i,local in enumerate(tetrahedra):
        for face,matrix in (((1,2,3),eye),((0,2,3),-eye),((0,1,3),eye),
                            ((0,1,2),-transport(local[2,3]))):
            j=local[face]
            differential2[i*d:(i+1)*d,j*d:(j+1)*d] += matrix
    mod = np.array(module.moduli*nt,dtype=np.int64)[:,None]
    if np.any((differential2 @ differential1) % mod):
        raise ArithmeticError('Twisted simplicial coboundaries do not square to zero')
    cohomology = CohomologyQuotient(module.moduli*nf,differential2,
                                  module.moduli*nt,differential1)
    closed1 = CohomologyQuotient(module.moduli*ne,differential1,
                               module.moduli*nf,np.zeros((ne*d,0),dtype=np.int64))
    normalization = len(module.anyons)**len(triangulation.faces[0])/closed1.size
    simplex = SimplexWeight(weights)
    result = 0j
    for coordinates in product(*(range(n) for n in cohomology.orders)):
        labels = (cohomology.lifts @ np.array(coordinates,dtype=np.int64)).reshape(nf,d)
        anyons = [module.label(row) for row in labels]
        bs = []
        for local in tetrahedra:
            a = anyons[local[0,2,3]]
            b = weights.intr.action(weights.intr.power(triangulation.edges[local[2,3]],-1),
                                   anyons[local[0,1,2]])
            bs.append(module.add_table[a,b])
        value = 1+0j
        for local,orientation in zip(triangulation.local,triangulation.orientation):
            aa=tuple(anyons[local[x]] for x in combinations(range(5),3))
            bb=tuple(bs[local[x]] for x in combinations(range(5),4))
            tensor=simplex.tensor(aa,bb,triangulation.edges[local[2,3]],triangulation.edges[local[3,4]])
            z=tensor.reshape(-1)[0]
            value *= z if orientation>0 else z.conjugate()
        result += value
    return normalization*result


def reference_partition(weights, a, b, c, *, klein=False):
    triangulation = ProductComplex(weights.intr,a,b,c,klein=klein)
    if all(abs(weights.c.quantum_dimension(x)-1)<1e-8 for x in weights.c.anyons):
        return pointed_partition(weights,triangulation)
    return general_partition(weights,triangulation)


def contract_factors(factors):
    """Exact dense variable elimination with a greedy intermediate-size order."""
    factors=list(factors)
    while any(axes for axes,_ in factors):
        sizes={axis:array.shape[j] for axes,array in factors for j,axis in enumerate(axes)}
        scopes={axis:set().union(*(set(axes) for axes,_ in factors if axis in axes))
                for axis in sizes}
        variable=min(sizes,key=lambda v: np.prod([float(sizes[a]) for a in scopes[v]]))
        selected=[(axes,array) for axes,array in factors if variable in axes]
        factors=[(axes,array) for axes,array in factors if variable not in axes]
        axes=tuple(sorted(scopes[variable]))
        result=np.ones(tuple(sizes[a] for a in axes),dtype=complex)
        for old,array in selected:
            ordered=tuple(a for a in axes if a in old)
            array=np.transpose(array,tuple(old.index(a) for a in ordered))
            shape=tuple(sizes[a] if a in old else 1 for a in axes)
            result *= array.reshape(shape)
        result=result.sum(axis=axes.index(variable))
        factors.append((tuple(a for a in axes if a != variable),result))
    return np.prod([array.item() for _,array in factors])


def general_partition(weights, triangulation):
    """Full fusion-multiplicity state sum, without a pointed-category assumption.

    Admissibility prunes face labels before the five-tetrahedron tensors are
    assembled. This reference fallback is exponential; callers first use
    exact old-indicator and odd-cover reductions whenever applicable.
    """
    c,intr = weights.c,weights.intr
    tetrahedra=triangulation.incidence(3)
    nf=len(triangulation.faces[2])
    incidence=[tuple(local[x] for x in combinations(range(4),3)) for local in tetrahedra]
    byface=[[] for _ in range(nf)]
    for i,faces in enumerate(incidence):
        for f in set(faces):
            byface[f].append(i)
    simplex=SimplexWeight(weights)
    labels=[None]*nf
    domains=[None]*len(tetrahedra)
    chi=sum((-1)**i*len(faces) for i,faces in enumerate(triangulation.faces))
    normalization=weights.D**(2*(len(triangulation.faces[0])-len(triangulation.faces[1]))-chi)

    def domain(i):
        a012,a013,a023,a123=(labels[j] for j in incidence[i])
        h=triangulation.edges[tetrahedra[i][2,3]]
        transformed=intr.action(intr.power(h,-1),a012)
        result=[]
        for b in c.fusion(a023,transformed):
            for mu in range(c.N(a023,transformed,b)):
                for nu in range(c.N(a013,a123,b)):
                    result.append((b,mu,nu))
        return tuple(result)

    def evaluate():
        factors=[]
        for i,states in enumerate(domains):
            factors.append(((i,),np.array([1/c.quantum_dimension(b) for b,_,_ in states])))
        for local,orientation in zip(triangulation.local,triangulation.orientation):
            face_anyons=tuple(labels[local[x]] for x in combinations(range(5),3))
            axes=tuple(local[x] for x in combinations(range(5),4))
            unique=tuple(dict.fromkeys(axes))
            tensor=np.empty(tuple(len(domains[i]) for i in unique),dtype=complex)
            for index in np.ndindex(tensor.shape):
                chosen=dict(zip(unique,index))
                states=[domains[i][chosen[i]] for i in axes]
                bs=tuple(state[0] for state in states)
                fusion_indices=tuple(v for state in states for v in state[1:])
                value=simplex.tensor(face_anyons,bs,triangulation.edges[local[2,3]],
                                     triangulation.edges[local[3,4]])[fusion_indices]
                tensor[index]=value if orientation>0 else value.conjugate()
            factors.append((unique,tensor))
        return contract_factors(factors)

    def visit(remaining, dimension_weight):
        if not remaining:
            return dimension_weight*evaluate()
        face=max(remaining,key=lambda f:sum(2**sum(labels[j] is not None for j in incidence[i])
                                            for i in byface[f]))
        rest=remaining-{face}
        total=0j
        for label in c.anyons:
            labels[face]=label
            completed=[]
            admissible=True
            for i in byface[face]:
                if all(labels[j] is not None for j in incidence[i]):
                    domains[i]=domain(i)
                    completed.append(i)
                    if not domains[i]:
                        admissible=False
                        break
            if admissible:
                total += visit(rest,dimension_weight*c.quantum_dimension(label))
            for i in completed:
                domains[i]=None
        labels[face]=None
        return total
    return normalization*visit(set(range(nf)),1.)
