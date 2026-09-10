"""Independent presentation, cohomology, and Bilbao-convention checks."""
from itertools import product
import json
import random
from pathlib import Path
import numpy as np
import pytest
from umtc import load_json
from qsl_classification import classify, eta_from_json, wallpaper_groups
from qsl_classification.groups import SpaceGroup, Intrinsic
from qsl_classification.algebra import AnyonModule
from qsl_classification.extensions import ExtensionCollector

B1=(2,3,3,2,2,4,3,2,3,2,3,2,0,1,1,1,2)
B2=(1,4,4,1,2,8,4,2,5,3,6,3,1,2,2,2,4)


@pytest.mark.parametrize('number,tr',list(product(range(1,18),(False,True))))
def test_presentations_and_mod_two_cohomology(examples,number,tr):
    cat=load_json(examples/'z2_gauge.json')
    intr=Intrinsic(cat)
    module=AnyonModule(cat,intr)
    anti=next(g for g in intr.anti if all(intr.action(g,a)==a for a in cat.anyons)
              and intr.power(g,2)==intr.identity)
    space=SpaceGroup(number=number,time_reversal=tr)
    images=tuple(anti if p else intr.identity for p in space.gradings)
    assert images in set(intr.homomorphisms(space))
    collector=ExtensionCollector(space,module,intr,images)
    q=collector.cohomology()
    # Kunneth: H²(P×SO3×T,Z2) has b2+1+(b1+1)·T generators.
    expected=2*(B2[number-1]+1+tr*(B1[number-1]+1))
    assert q.orders == (2,)*expected
    rng=random.Random(1700+number)
    parameters=q.lifts @ np.array([rng.randrange(m) for m in q.orders],dtype=np.int64)
    def element():
        return space.element(rng.randrange(-20,21),rng.randrange(-20,21),
                             rng.randrange(space.n),rng.randrange(2) if space.mirror else 0,
                             rng.randrange(2) if tr else 0)
    def cocycle(g,h):
        return collector.cocycle_matrix(g,h) @ parameters
    for _ in range(5):
        g,h,k=element(),element(),element()
        assert space.multiply(g,space.inverse(g)) == space.identity
        assert space.multiply(g,space.multiply(h,k)) == space.multiply(space.multiply(g,h),k)
        assert space.parity(space.multiply(g,h)) == (space.parity(g)+space.parity(h)) % 2
        residual=(module.actions[intr.word(images,g)] @ cocycle(h,k)
                  +cocycle(g,space.multiply(h,k))-cocycle(g,h)-cocycle(space.multiply(g,h),k))
        assert not np.any(residual % np.array(module.moduli))


def test_bilbao_labels_and_lattice_classes():
    assert len(wallpaper_groups()) == 17
    expected=((1,),(1,1,1,1,2),(1,1,2),(2,),(2,4),(1,1,1,1,2,2,2,2,4),
              (2,2,2,4),(2,2,4),(2,2,4,4,4,8),(1,1,2,4),(1,1,2,4,4,4,8),
              (2,2,4,8),(1,1,1,3),(1,1,1,3,6),(1,2,3,6),(1,2,3,6),(1,2,3,6,6,12))
    for info,multiplicities in zip(wallpaper_groups(),expected):
        assert tuple(p['multiplicity'] for p in info['wyckoff_positions'].values()) == multiplicities
        space=SpaceGroup.parse(info['it_number'])
        for letter,position in info['wyckoff_positions'].items():
            wp=f"{position['multiplicity']} {letter}"
            assert not any(space.lattice([wp,wp]).values())
        with pytest.raises(ValueError):
            space.lattice(['999 a'])
    # Bilbao p2 b is (0,1/2), c is (1/2,0); the surface order is C2,XC2,YC2,XYC2.
    assert SpaceGroup.parse(2).lattice(['1 b']) == dict(l1=0,l2=0,l3=1,l4=0)
    assert SpaceGroup.parse(2).lattice(['1 c']) == dict(l1=0,l2=1,l3=0,l4=0)
    assert SpaceGroup.parse(4).lattice(['2 a']) == {'l1':1}
    assert SpaceGroup.parse(5).lattice(['2 a']) == {'l1':1}
    assert SpaceGroup.parse(13).lattice(['3 d']) == {'l1':1}
    assert SpaceGroup.parse(14).lattice(['3 d']) == {'l1':1}
    assert SpaceGroup.parse(15).lattice(['2 b']) == {'l1':0}


def test_glide_eta_round_trip_and_large_powers(examples):
    path=examples/'toric_code.json'
    result=classify(4,[],path,time_reversal=False,verbose=True)
    count=0
    for hom in result['homomorphisms']:
        assert len(hom['realizations']) == hom['number_of_realizations']
        for realization in hom['realizations']:
            eta=eta_from_json(json.loads(json.dumps(realization['eta_symbol'])),path)
            s=eta.space
            L=s.generator('L')
            assert s.power(L,2)==s.generator('T2')
            huge=s.power(L,-10**30-1)
            assert s.multiply(huge,s.power(L,10**30+1))==s.identity
            for a in eta.module.category.anyons:
                assert np.isclose(abs(eta(a,huge,s.element(10**40,-10**25,m=1))),1)
            count+=1
    assert count == sum(h['number_of_realizations'] for h in result['homomorphisms'])


def test_it_aliases_and_independent_time_reversal(examples):
    p=examples/'u1_2.json'
    assert classify(10,[],p,time_reversal=False)==classify('p4*SO(3)',[],p)
    assert classify(10,[],p,False,False)==classify('p4*SO(3)',[],p,False)
    assert classify('p4 × SO(3)',[],p,True)==classify(10,[],p,False,True)
    assert classify(10,[],p)['number_of_homomorphisms']==0
    with pytest.raises(ValueError):
        classify('p4*SO(3)',[],p,time_reversal=True)
    for x in (0,18,True,'p7',3.0):
        with pytest.raises(ValueError):
            SpaceGroup.parse(x)


def test_all_34_toric_code_classifications(examples):
    reference=json.loads((Path(__file__).parent/'fixtures/v0_2_0_wallpaper.json').read_text())['toric_code']
    for tr in (False,True):
        rows=reference['with_time_reversal' if tr else 'without_time_reversal']
        for number,expected in enumerate(rows,1):
            result=classify(number,[],examples/'toric_code.json',time_reversal=tr)
            assert result['number_of_homomorphisms']==expected['homomorphisms']
            assert result['total_realizations']==expected['realizations']
