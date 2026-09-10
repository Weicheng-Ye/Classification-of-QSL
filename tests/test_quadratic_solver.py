import numpy as np
from qsl_classification.indicators import QuadraticIndicators
from qsl_classification.quadratic_solver import binary_solutions, binary_encoding


def test_boolean_solver_against_exhaustive_enumeration():
    rng=np.random.default_rng(4)
    for n in range(1,10):
        for _ in range(5):
            pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
            model=QuadraticIndicators(rng.integers(2,size=5,dtype=np.uint8),
                    rng.integers(2,size=(n,5),dtype=np.uint8),pairs,
                    rng.integers(2,size=(len(pairs),5),dtype=np.uint8))
            target=rng.integers(2,size=5,dtype=np.uint8)
            ids=np.arange(2**n)
            coords=(ids[:,None]>>np.arange(n))&1
            expected=set(ids[np.all(model.evaluate(coords)==target,axis=1)])
            assert set(binary_solutions(model,target))==expected


def test_cyclic_four_and_eight_factors_keep_diagonal_terms():
    rng=np.random.default_rng(8)
    orders=(4,2,8)
    pairs=[(i,j) for i in range(3) for j in range(i,3)]
    quad=rng.integers(2,size=(6,4),dtype=np.uint8)
    quad[pairs.index((1,1))]=0
    model=QuadraticIndicators(rng.integers(2,size=4,dtype=np.uint8),
            rng.integers(2,size=(3,4),dtype=np.uint8),pairs,quad)
    binary=binary_encoding(model,orders)
    ids=np.arange(64)
    coords=(ids[:,None]//np.array([1,4,8])) % orders
    bits=(ids[:,None]>>np.arange(6))&1
    assert np.array_equal(model.evaluate(coords),binary.evaluate(bits))
