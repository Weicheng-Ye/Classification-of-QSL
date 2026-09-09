"""Independent order-three extension witness, using only integer matrices.

This calculation does not import the classifier or its cohomology solver.
"""
from itertools import product
import json
from pathlib import Path
import numpy as np


def main():
    # Conjugation by C6 on (anyon charge, translation x, translation y).
    A = np.array([[-1,0,1],[0,1,-1],[0,1,0]],dtype=np.int64)
    powers = [np.linalg.matrix_power(A,k) for k in range(7)]
    assert np.array_equal(powers[6],np.eye(3,dtype=np.int64))
    # The same witness extends to p6m. M swaps X,Y, fixes z, and has
    # conjugation matrix B. Equalities are exact on translation rows and
    # modulo three on the coefficient row, without reducing translations.
    B=np.array([[1,1,-1],[0,0,1],[0,1,0]],dtype=np.int64)
    assert np.array_equal(B@B,np.eye(3,dtype=np.int64))
    difference=B@A@B-powers[5]
    assert not difference[1:,:].any() and not (difference[0,:]%3).any()
    # Thus Z^3 ⋊_A C6 is an actual infinite group, projecting onto p6;
    # reducing only the first coordinate mod 3 gives an extension by Z3.
    # Its section is (0,x,y,c); the following omega is the exact section defect.
    def omega(g,h):
        return int((powers[g[2]] @ np.array([0,h[0],h[1]]))[0]) % 3
    def multiply(g,h):
        moved = powers[g[2]] @ np.array([0,h[0],h[1]])
        return ((g[0]+int(moved[1]))%3,(g[1]+int(moved[2]))%3,(g[2]+h[2])%6)
    group = list(product(range(3),range(3),range(6)))
    for g,h,k in product(group,repeat=3):
        assert (((-1)**g[2])*omega(h,k)+omega(g,multiply(h,k))-
                omega(g,h)-omega(multiply(g,h),k))%3 == 0
    # If the infinite-group cocycle were a coboundary, changing the lifts
    # X->a^u X, Y->a^v Y, C6->a^w C6 could remove both conjugation tails.
    # Their shifts are (-2u-v, u-v). Their difference is 3u, so (0,1)
    # cannot be removed. This is exhaustive even when translations are infinite.
    shifts = {((-2*u-v)%3,(u-v)%3) for u,v in product(range(3),repeat=2)}
    assert (0,1) not in shifts
    report = {'alpha_matrix':A.tolist(),'alpha_order':6,'coefficient_group':'Z3 with C6 acting by -1',
              'finite_quotient_order':len(group),'cocycle_identities_checked':len(group)**3,
              'all_identities_passed':True,'conjugation_tails':[0,1],
              'coboundary_tail_shifts':sorted(shifts),'nontrivial_class':True,
              'mirror_matrix':B.tolist(),'mirror_relations_passed':True,
              'infinite_group_argument':'Integer alpha^6=I; tail difference is invariant modulo 3 under every generator-lift change.'}
    Path('validation').mkdir(exist_ok=True)
    Path('validation/order-three-witness.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
