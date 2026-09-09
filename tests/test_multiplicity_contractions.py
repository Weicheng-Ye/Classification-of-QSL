"""Check multiplicity-index contractions against explicit equation sums.

Random tensors here are test tensors, not a claim to construct a UMTC.
"""
from itertools import product
from types import SimpleNamespace
import numpy as np
from qsl_classification.indicators import TopologicalWeights


def test_multiplicity_two_equation_211_and_212():
    rng=np.random.default_rng(211212)
    def unitary(n):
        q,_=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))
        return q
    F=unitary(4).reshape(2,2,2,2);R=unitary(2);U={'g':unitary(2),'h':unitary(2)}
    c=SimpleNamespace(anyons=(0,),total_quantum_dimension=1.,N=lambda a,b,c:2,
                      fusion=lambda a,b:{0:2},F=lambda a,b,c,d,e,f,*i:F[i],
                      R_matrix=lambda a,b,c:R,spin=lambda a:1.,quantum_dimension=lambda a:1.)
    intrinsic=SimpleNamespace(action=lambda g,a:a,sym=SimpleNamespace(U_matrix=lambda g,a,b,c:U[g]))
    weights=TopologicalWeights(c,intrinsic)
    V=U['g'].conj().T;W=U['h'].conj().T
    expected3=0j
    for mu,nu,tmu,tnu,rho,sigma,alpha in product(range(2),repeat=7):
        expected3+=(R[rho,sigma]*F[tmu,tnu,sigma,alpha].conjugate()*F[mu,nu,rho,alpha]*
                    V[tmu,mu]*V[tnu,nu])
    assert np.allclose(dict(weights.i3('g','h'))[0,0],expected3,atol=1e-12)
    expected2=0j
    for mx,nx,my,ny,tmx,tnx,tmy,tny,r,s,t,a,b,g,d in product(range(2),repeat=15):
        expected2+=(R[r,s]*F[tmx,a,tmy,t].conjugate()*F[r,b,my,tny].conjugate()*
                    F[tnx,mx,s,g].conjugate()*F[g,d,b,a].conjugate()*F[nx,t,ny,d].conjugate()*
                    V[mx,tmx]*V[nx,tnx]*W[my,tmy].conjugate()*W[ny,tny].conjugate())
    assert np.allclose(dict(weights.i2('g','h'))[0,0,0],expected2,atol=1e-12)
