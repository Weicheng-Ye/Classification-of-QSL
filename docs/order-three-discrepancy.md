# Five comparisons that do not match the first paper

The classifier retains a nontrivial order-three sector of the p6 twisted
cohomology. It is absent from Eq. (31), Eq. (145), and Table XI of
[Ye and Zou, arXiv:2309.15118v3](https://arxiv.org/html/2309.15118v3).
This affects the supplied U(1)₆ and Z₃-gauge examples. The discrepancy is
reported explicitly; expected counts are not used to modify the algorithm.

| Category and group | Lattice class | Printed count | Computed count |
|---|---|---:|---:|
| U(1)₆, p6 × SO(3) | 0 | 30 | 35 |
| U(1)₆, p6 × SO(3) | a | 6 | 7 |
| U(1)₆, p6 × SO(3) | c | 6 | 7 |
| U(1)₆, p6 × SO(3) | a+c | 6 | 7 |
| Z₃ gauge, p6m × O(3) | 0 | 8 | 9 |

All supplied SU(2) examples agree with the second paper. The other comparisons
in the first paper agree, including U(1)₂,₄,₈,₁₀, every Ising chirality, the
Z₂ and Z₄ mirror cases, and both doubled-U(1) examples.

## Independent extension witness

Let X,Y generate the translation subgroup and R=C₆. Use the paper's relations
RXR⁻¹=XY and RYR⁻¹=X⁻¹. Let z be an Abelian coefficient generator with
RzR⁻¹=z⁻¹ and with X,Y acting trivially on z. Consider lifted relations

```
RXR^-1 = XY
RYR^-1 = z X^-1
[X,Y] = [X,z] = [Y,z] = 1
R^6 = 1.
```

On exponent vectors `(z,x,y)`, conjugation by R is the integer matrix

```
    [-1  0  1]
A = [ 0  1 -1],       A^6 = I.
    [ 0  1  0]
```

Consequently Z³ ⋊ₐ C₆ is an actual infinite group. Quotienting its z coordinate
modulo three gives an extension of the infinite p6 group by Z₃ with the
specified coefficient action. This supplies a cocycle independently of the
classifier's collector and Smith calculation:

```
omega((x,y,c),(x',y',c')) = first_coordinate(A^c (0,x',y')) mod 3.
```

This class is not a coboundary. Write the tails of RXR⁻¹=… and RYR⁻¹=…
as `(u₁,u₂)`. Changing lifts X→zᵖX, Y→zᑫY shifts these tails by
`(-2p-q,p-q)`; changing R's lift has no effect. The difference of the two
tail shifts is `3p`, hence is zero modulo three. The displayed extension's
tail difference is one and cannot be gauged away. Its class has order three.
The same integer argument gives a Z₃ quotient in H²(p6,Z_sign), contrary
to the zero group printed in Eq. (145).

`scripts/check_order_three.py` constructs this matrix without importing the
classifier. It verifies A⁶=I over the integers and all 54³=157,464 twisted
cocycle identities on `(Z₃×Z₃) ⋊ C₆`, in addition to the lift-change test.
Its result is saved in `validation/order-three-witness.json`.

The witness also extends independently to p6m. Let the mirror act on the
lower `(z,x,y)` group by

```
    [1 1 -1]
B = [0 0  1].
    [0 1  0]
```

Then B²=I and BAB=A⁻¹, with the coefficient row interpreted modulo three
and translation rows over the integers. This gives an actual p6m extension
by Z₃ with R acting on z by inversion and M fixing z. A commuting T can
also fix z. In Z₃ gauge theory this embeds as z=e with R inverting e,m and
M,T acting as `(e,m)→(e,-m)`. Restriction to p6 is the nontrivial class
already proved above, so this mirror-group class cannot be a coboundary.

## Consequences for the examples

For U(1)₆ with R acting as charge conjugation, the computed group is
Z₂×Z₂×Z₆, of order 24, rather than the order-eight group printed in Eq. (31).
The unitary anyon relabeling identifies the two nonzero elements of the
additional Z₃ sector. The nonpermuting sector still has counts `(25,5,5,5)`;
the charge-conjugating sector has `(10,2,2,2)`, giving the totals above.
Restricting the latter to its subgroup of elements killed by two reproduces
the paper's `(5,1,1,1)` exactly, but omits valid classes.

For Z₃ gauge theory, one p6m permutation pattern likewise has H²=Z₃ where
the paper records a trivial group. After unitary relabeling it contributes two
realizations instead of one. The other three patterns contribute `(1,5,1)`.
The missing sector is again an order-three extension sector, and its anomaly
indicators are all trivial.

These independent checks support an omission in the first paper's cohomology
calculation. They are not an author-confirmed erratum. The package preserves
the general calculation and leaves the five printed comparisons marked as
disagreements rather than claiming that every published count matches.
