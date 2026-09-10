# Wallpaper groups and Wyckoff conventions

The API uses plane-group International Tables numbers 1–17 and the standard
conventional-cell Wyckoff letters and multiplicities used by the
[Bilbao plane-group server](https://cryst.ehu.es/plane/get_plane_wp.html).
The complete position lists were cross-checked with the International Tables
conventions reproduced in Hicks et al., [AFLOW Prototypes, Part 2, section 4](https://pure.mpg.de/rest/items/item_3064875/component/file_3070437/content).
Bilbao's live listing requested human verification during this release; no
live-server download is required by the package.

Each supplied WP represents one orbit of half-odd-integer spins. Multiplicity
is part of the crystallographic label, not a count of independently occupied
orbits. Repeated entries add modulo two. Omitting a multiplicity, for example
`a`, is accepted, but an explicitly supplied wrong multiplicity is rejected.

The nonzero entries below give the orbit's lattice-homotopy coordinates in
the ordered degree-two surface basis of the
[anomaly catalogue](anomaly-indicators-all-wallpaper-groups.md#degree-two-coordinates-with-and-without-time-reversal).
Unlisted entries in that column have zero lattice-homotopy class. These
coordinates are derived from the site/line stabilizers in Appendix F of
[arXiv:2111.12097](https://arxiv.org/abs/2111.12097); the position labels are
crystallographic data. For the four legacy settings the JSON keeps its
original `a`, `b`, `c` lattice-class names.

| IT | Short name | Bilbao name | All WPs | Nonzero LSM coordinates |
|---:|---|---|---|---|
| 1 | p1 | p1 | 1a | 1a → ℓ1 |
| 2 | p2 | p2 | 1a, 1b, 1c, 1d, 2e | 1a → ℓ1, 1b → ℓ3, 1c → ℓ2, 1d → ℓ4 |
| 3 | pm | p1m1 | 1a, 1b, 2c | 1a → ℓ1, 1b → ℓ2 |
| 4 | pg | p1g1 | 2a | 2a → ℓ1 |
| 5 | cm | c1m1 | 2a, 4b | 2a → ℓ1 |
| 6 | pmm | p2mm | 1a, 1b, 1c, 1d, 2e, 2f, 2g, 2h, 4i | 1a → ℓ1, 1b → ℓ4, 1c → ℓ3, 1d → ℓ2 |
| 7 | pmg | p2mg | 2a, 2b, 2c, 4d | 2a → ℓ1, 2b → ℓ2, 2c → ℓ3 |
| 8 | pgg | p2gg | 2a, 2b, 4c | 2a → ℓ1, 2b → ℓ2 |
| 9 | cmm | c2mm | 2a, 2b, 4c, 4d, 4e, 8f | 2a → ℓ1, 2b → ℓ2, 4c → ℓ3 |
| 10 | p4 | p4 | 1a, 1b, 2c, 4d | 1a → ℓ1, 1b → ℓ2, 2c → ℓ3 |
| 11 | p4m | p4mm | 1a, 1b, 2c, 4d, 4e, 4f, 8g | 1a → ℓ1, 1b → ℓ2, 2c → ℓ3 |
| 12 | p4g | p4gm | 2a, 2b, 4c, 8d | 2a → ℓ1, 2b → ℓ2 |
| 13 | p3 | p3 | 1a, 1b, 1c, 3d | 1a → ℓ1, 1b → ℓ1, 1c → ℓ1, 3d → ℓ1 |
| 14 | p3m1 | p3m1 | 1a, 1b, 1c, 3d, 6e | 1a → ℓ1, 1b → ℓ1, 1c → ℓ1, 3d → ℓ1 |
| 15 | p31m | p31m | 1a, 2b, 3c, 6d | 1a → ℓ1, 3c → ℓ1 |
| 16 | p6 | p6 | 1a, 2b, 3c, 6d | 1a → ℓ1, 3c → ℓ2 |
| 17 | p6m | p6mm | 1a, 2b, 3c, 6d, 6e, 12f | 1a → ℓ1, 3c → ℓ2 |

For example, p2's `1b` is (0, 1/2), while `1c` is (1/2, 0).
They pair with the YC2 and XC2 surfaces, respectively. In pg, the general
`2a` orbit is nontrivial. In p3 every WP has the same nontrivial parity;
in p6 the `2b` orbit has zero parity.

## Generator coordinates

The exact infinite presentations follow Appendix E of
[arXiv:2111.12097](https://arxiv.org/abs/2111.12097).
The ordered section is X^x Y^y C_n^c M^m T^t, omitting absent factors;
L replaces M in pg, pgg, and p4g. `generator_images` gives that order.
X and Y are `T1` and `T2`. All translation exponents are arbitrary signed
integers. In dictionaries, `rotation` is the exponent of C_n, and `mirror`
is the exponent of M or L, not a statement that L has order two.

For primitive rectangular and square groups X=(1,0), Y=(0,1) in the
conventional cell. For centered cm and cmm use X=(1/2,1/2), Y=(-1/2,1/2):
a translation tuple (x,y) has conventional coordinates ((x-y)/2,(x+y)/2).
Wyckoff multiplicities still count sites in the conventional cell.
The triangular/hexagonal groups use the conventional primitive basis with
angle 120 degrees. Rotations act by

- C2: (x,y) → (-x,-y).
- C3: (x,y) → (-y,x-y).
- C4: (x,y) → (-y,x).
- C6: (x,y) → (x-y,x).

The spatial orientation-reversing generator has the following affine action:

| Groups | Generator | Action in primitive coordinates | Square |
|---|---|---|---|
| pm, pmm, p4m | M | (-x,y) | 1 |
| pmg | M | (-x+1/2,y) | 1 |
| cm, cmm, p31m, p6m | M | (y,x) | 1 |
| p3m1 | M | (-y,-x) | 1 |
| pg | L | (-x,y+1/2) | Y |
| pgg | L | (-x+1/2,y+1/2) | Y |
| p4g | L | (y+1/2,x+1/2) | XY |

An independent T commutes with all spatial generators and has T²=1.
Under crystalline equivalence, q(g)=epsilon(g)+t(g) modulo two, where
epsilon is the determinant parity of the spatial linear action. Thus M and
L must map to antiunitary intrinsic symmetries even when T is absent.
The relation L²=Y or XY constrains the intrinsic translation image and is
also retained in every reconstructed eta function.
