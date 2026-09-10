"""Product-manifold checks independent of the classifier's target tables."""
from itertools import product, combinations
from functools import lru_cache
import numpy as np
import pytest
from umtc import UMTC, load_json
from qsl_classification.groups import SpaceGroup, Intrinsic
from qsl_classification.algebra import AnyonModule
from qsl_classification.extensions import ExtensionCollector
from qsl_classification.indicators import AnomalySystem, TopologicalWeights
from qsl_classification.relative_anomaly import ProductAnomaly
from qsl_classification.product_state_sum import ProductComplex, pointed_partition, general_partition
from qsl_classification.classifier import Engine


class BareSystem(AnomalySystem):
    def specifications(self):
        return []


@pytest.mark.parametrize('name',['toric_code','double_semion','u1_4','su2_k6'])
def test_relative_FRUeta_against_old_absolute_indicators(examples,name):
    engine=Engine(examples/(name+'.json'))
    space=SpaceGroup(number=6,time_reversal=True)
    for images in list(engine.intrinsic.homomorphisms(space))[:8]:
        collector=ExtensionCollector(space,engine.module,engine.intrinsic,images)
        quotient=collector.cohomology()
        system=BareSystem(collector,quotient,engine.weights)
        system.space=space
        a,b,l=(space.generator(g) for g in ('T','C2','M'))
        c=space.multiply(l,a)
        rng=np.random.default_rng(0)
        points=np.array([[rng.integers(n) for n in quotient.orders] for _ in range(10)],dtype=np.int64)
        def old(kind,*words):
            return system.compile(kind,*[(g,(1.,0.,0.,0.)) for g in words]).values(points)
        for klein in (False,True):
            evaluate=ProductAnomaly(system,a,b,l if klein else c,klein=klein)
            actual=np.array([evaluate(x) for x in points])
            expected=(old(2,a,l)*old(2,a,space.multiply(b,l)) if klein else
                      old(0)*old(2,space.multiply(space.multiply(a,b),c),a)/
                      (old(2,space.multiply(a,b),a)*old(2,space.multiply(a,c),a)))
            assert np.allclose(actual,expected,atol=1e-8)


def toric_reference(examples,klein,gauged,orders=(2,2,2)):
    base=load_json(examples/'toric_code.json')
    intr=Intrinsic(base)
    module=AnyonModule(base,intr)
    elements=tuple(''.join(map(str,bits)) for bits in product(*(range(n) for n in orders)))
    def bits(g):
        return tuple(map(int,g))
    def mul(g,h):
        x,y=bits(g),bits(h)
        return ''.join(map(str,((x[0]+y[0])%orders[0],
                    (x[1]+(-1)**(klein*x[2])*y[1])%orders[1],
                    (x[2]+y[2])%orders[2])))
    def grade(g):
        return (bits(g)[0]+klein*bits(g)[2]) % 2
    # k=e on RP2; b=m on the spatial surface. Their monodromy is -1.
    def twist(g,h):
        x,y=bits(g),bits(h)
        return module.label((x[0]*y[0],x[1]*y[2]))
    rng=np.random.default_rng(194)
    @lru_cache(None)
    def gamma(a,g):
        return (np.exp(1j*rng.uniform(-np.pi,np.pi))
                if gauged and a != base.vacuum and g != '000' else 1+0j)
    def eta(a,g,h):
        z=gamma(a,h)
        if grade(g):
            z=z.conjugate()
        return module.braiding[a,twist(g,h)]*gamma(a,mul(g,h))/(gamma(a,g)*z)
    data={'schema_version':1,'name':'toric reference with mixed anomaly',
          'anyons':[list(a) for a in base.anyons],'vacuum':list(base.vacuum),
          'symmetry':{'elements':list(elements),'identity':'000',
                      'multiplication_table':[[mul(g,h) for h in elements] for g in elements],
                      'antiunitary':[g for g in elements if grade(g)]}}
    return UMTC.from_functions(data,F=base.F,R=base.R,N=base.N,
            quantum_dimension=base.quantum_dimension,spin=base.spin,
            action=lambda g,a:a,U=lambda g,a,b,c:gamma(a,g)*gamma(b,g)/gamma(c,g),
            eta=eta)


@pytest.mark.parametrize('klein,gauged',list(product((False,True),repeat=2)))
def test_full_product_state_sum_nontrivial_reference_and_complex_U(examples,klein,gauged):
    category=toric_reference(examples,klein,gauged)
    intr=Intrinsic(category)
    weights=TopologicalWeights(category,intr)
    triangulation=ProductComplex(intr,'100','010','001',klein=klein)
    assert tuple(map(len,triangulation.faces))==(2,18,52,60,24)
    for local in triangulation.local:
        for i,j,k in combinations(range(5),3):
            assert intr.mul(triangulation.edges[local[i,j]],triangulation.edges[local[j,k]]) == triangulation.edges[local[i,k]]
    assert np.allclose(pointed_partition(weights,triangulation),-1,atol=1e-8)


@pytest.mark.parametrize('name',['double_semion','u1_4_x_u1_minus4'])
def test_product_sum_with_permutations_and_nontrivial_F(examples,name):
    engine=Engine(examples/(name+'.json'))
    intr=engine.intrinsic
    a=next(g for g in intr.anti if intr.power(g,2)==intr.identity)
    triangulation=ProductComplex(intr,a,intr.identity,a,klein=True)
    assert np.allclose(pointed_partition(engine.weights,triangulation),1,atol=1e-8)


def test_full_nonabelian_state_sum_on_four_sphere(examples):
    from types import SimpleNamespace
    engine=Engine(examples/'fibonacci.json')
    faces=[tuple(combinations(range(5),n)) for n in range(1,5)]+[(0,1)]
    indices=[{f:i for i,f in enumerate(fs)} for fs in faces[:4]]
    local={subset:indices[n-1][subset] for n in range(1,5)
           for subset in combinations(range(5),n)}
    tetrahedra=[]
    for vertices in faces[3]:
        tetrahedra.append({subset:indices[n-1][tuple(vertices[i] for i in subset)]
                           for n in range(1,5) for subset in combinations(range(4),n)})
    sphere=SimpleNamespace(faces=faces,local=(local,local),orientation=(1,-1),
             edges=(engine.intrinsic.identity,)*10,incidence=lambda d:tetrahedra)
    assert np.allclose(general_partition(engine.weights,sphere),1,atol=1e-8)


@pytest.mark.parametrize('klein',[False,True])
def test_higher_order_reference_holonomies_use_full_state_sum(examples,klein):
    category=toric_reference(examples,klein,True,orders=(2,4,4))
    intr=Intrinsic(category)
    module=AnyonModule(category,intr)
    space=SpaceGroup(number=4 if klein else 1,time_reversal=True)
    images=('010','002','001','100') if klein else ('010','001','100')
    collector=ExtensionCollector(space,module,intr,images)
    quotient=collector.cohomology()
    weights=TopologicalWeights(category,intr)
    system=BareSystem(collector,quotient,weights)
    system.space=space
    a,b,c=(space.generator(g) for g in ('T','T1','L' if klein else 'T2'))
    evaluate=ProductAnomaly(system,a,b,c,klein=klein)
    assert np.allclose(evaluate.reference,-1,atol=1e-8)
    assert np.allclose(evaluate(np.zeros(system.rank,dtype=np.int64)),-1,atol=1e-8)
