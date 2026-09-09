"""A new doubled-Ising input exercises non-Abelian antiunitary contractions."""
from itertools import product
import numpy as np
from umtc import UMTC,load_json
from qsl_classification.groups import SpaceGroup,Intrinsic
from qsl_classification.algebra import AnyonModule
from qsl_classification.extensions import ExtensionCollector
from qsl_classification.indicators import TopologicalWeights,AnomalySystem


def test_doubled_ising_reference_has_no_anomaly(examples):
    c=load_json(examples/'ising_nu1.json')
    labels=c.anyons
    data={'schema_version':1,'name':'Ising x conjugate Ising',
          'anyons':[list(a) for a in product(range(3),repeat=2)],'vacuum':[0,0],
          'symmetry':{'elements':['1','T'],'identity':'1',
                      'multiplication_table':[['1','T'],['T','1']],'antiunitary':['T']}}
    def F(a,b,cc,d,e,f):
        xs=(a,b,cc,d,e,f)
        return c.F(*(labels[x[0]] for x in xs))*c.F(*(labels[x[1]] for x in xs)).conjugate()
    def R(a,b,cc):
        xs=(a,b,cc)
        return c.R(*(labels[x[0]] for x in xs))*c.R(*(labels[x[1]] for x in xs)).conjugate()
    cat=UMTC.from_functions(data,F=F,R=R,
        N=lambda a,b,cc:c.N(labels[a[0]],labels[b[0]],labels[cc[0]])*c.N(labels[a[1]],labels[b[1]],labels[cc[1]]),
        quantum_dimension=lambda a:c.quantum_dimension(labels[a[0]])*c.quantum_dimension(labels[a[1]]),
        spin=lambda a:c.spin(labels[a[0]])*c.spin(labels[a[1]]).conjugate(),
        action=lambda g,a:a[::-1] if g=='T' else a,
        U=lambda g,a,b,cc:1,eta=lambda a,g,h:1)
    intr=Intrinsic(cat);module=AnyonModule(cat,intr);space=SpaceGroup(6,True)
    hom=next(intr.homomorphisms(space))
    collector=ExtensionCollector(space,module,intr,hom);q=collector.cohomology()
    weights=TopologicalWeights(cat,intr);ind=AnomalySystem(collector,q,weights)
    assert np.allclose(ind.values([np.zeros(len(q.orders),dtype=np.int64)]),1,atol=1e-8)
    # Check the polarized result against direct tensor-derived indicators.
    model=ind.quadratic()
    coords=np.array(list(product(*(range(m) for m in q.orders))))
    assert np.array_equal(ind._bits(ind.values(coords)),model.evaluate(coords))
