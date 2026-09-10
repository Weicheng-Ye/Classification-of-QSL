# Anomaly indicators for all wallpaper groups with spin rotation

Quick navigation: [all-case index](#index-of-all-34-cases),
[group bases and targets](#group-by-group-bases-and-target-tables),
[published lists](#explicit-umtc-lists-in-the-four-published-conventions),
[OLD formula replacements](#evaluation-recipes-using-published-indicators),
[coverage and per-group recipes](#coverage-and-per-group-evaluation-recipes),
[spatial lists](#explicit-spatial-evaluation-lists-for-all-17-groups),
[NEW formulas and remaining calculations](#new-anomaly-indicators-formulas-and-remaining-calculations),
[RP² product calculations](rp2-product-partition-functions.md).

## Scope and status

This document concerns bosonic UMTCs and the 17 **two-dimensional** International
Tables plane groups, with symmetry

$$
\Gamma_+=P\times SO(3)\times\mathbb Z_2^T,
\qquad \Gamma_-=P\times SO(3).
$$

The operational lists prioritize the **OLD** anomaly formulas. Every evaluation
is labelled by the following convention:

- **OLD:** the published $\mathcal I_0,\ldots,\mathcal I_4$ functions,
  with their stated argument conditions, or explicit products and ratios of
  those functions. Their numbering is that of [YZ23], Eqs. (209)–(213).
- **EXTENDED:** the existing $\mathcal I_3$ contraction with an arbitrary
  commuting unitary element in its circle slot. This uses the same tensor sum,
  with an extension of its stated domain explained below. It is not labelled
  OLD, and the extension is not attributed to the published theorem.
- **NEW:** an evaluation outside the OLD/EXTENDED recipes above. This label
  records formula provenance, rather than whether a formula is still missing.
  All such entries refer to four shared templates,
  $\mathcal N_1,\ldots,\mathcal N_4$, at the **end of this document**.
  That section derives spin-flux formulas for 21 of the 30 NEW entries.
  The other nine have explicit triangulated contractions in the
  [product-partition-function note](rp2-product-partition-functions.md#2a-explicit-contraction-in-frueta).

The group tables retain the complete characteristic-number bases and lattice
signs. The operational recipes replace geometric evaluations by OLD formulas
wherever they are supplied here; the spatial lists use OLD or EXTENDED
formulas only. The four original published lists retain their original
indicator numbering for comparison.

The catalogue is complete at the level of geometric detecting lists in the
convention below. The final section supplies a reduction of $\mathcal N_1$
to OLD indicators when both circle holonomies are involutions, explicit
$U,\eta$ formulas for its required spin-dependent instances, and explicit
$\eta$ formulas for $\mathcal N_3,\mathcal N_4$. The companion note now
supplies explicit $F,R,U,\eta$ state sums for the spin-free instances of
$\mathcal N_1$ and $\mathcal N_2$, including full group words and fusion
multiplicities. Compact handle formulas for these instances are still
unsimplified.
The derivations and their checks are distinguished from equations quoted
from the papers. Version 0.2.0 implements these recipes for all 34 settings.
See [release validation](validation.md) and [WP conventions](wallpaper-groups.md).

All results here use the global topological anomaly/bordism convention of [YZ22]
and [YZ23]. Without an orientation-reversing symmetry, the free bordism
directions describing gravitational and spin Hall responses are not binary
obstructions and are not constrained to have partition function +1. The
no-time-reversal tables concern the torsion anomaly sector in that convention;
they are not a classification of perturbative anomalies of arbitrary gapless
theories. Additional SPT stacking is not counted as another realization.

The microscopic convention is a half-integer spin at each listed site, with
$T^2=-1$ when time reversal is present. Independently assigned SO(3) and
Kramers projective representations require two occupancy labels instead.
Evaluations assume consistent symmetry data $(\rho,U,\eta)$: the action
respects the crystalline antiunitary grading and the preceding categorical
symmetry-localization obstruction has been resolved. The indicators test the
remaining four-dimensional anomaly; they do not replace those consistency
conditions or enumerate fractionalization classes.
The derivation was developed before implementation; the v0.2.0 classifier now uses these lists.

## Notation and the meaning of an indicator

Let $M$ be a closed four-manifold, $E$ its background SO(3) bundle, and
$f$ the background plane-group bundle. Write

$$
u_i=w_i(TM),\qquad v_i=w_i(E),\qquad
\epsilon\in H^1(P,\mathbb F_2).
$$

Here $\epsilon(g)=1$ for a reflection or glide and is zero for an
orientation-preserving element. All cohomology products below are cup products;
all polynomial coefficients and exponents of signs are in $\mathbb F_2$.
Pullbacks along $f$ are suppressed. The letter $t$ denotes the physical
time-reversal class, so crystalline equivalence imposes

$$
u_1=\epsilon+t\quad(\Gamma_+),\qquad
u_1=\epsilon\quad(\Gamma_-).                                      \tag{1}
$$

For a chosen ordered basis $Q_1,\ldots,Q_N$ of independent characteristic
numbers, choose the **dual bordism classes** $z_1,\ldots,z_N$, defined by

$$
\langle Q_i,z_j\rangle=\delta_{ij}.
$$

Define the corresponding anomaly indicators by

$$
\boxed{\mathsf J_j=Z_{\mathcal C,\rho,U,\eta}(z_j).}              \tag{2}
$$

The partition function is the one constructed in [YZ22], Secs. III–V.
Representatives of a given bordism class give the same value. On the binary
anomaly sector this is equivalently the unique expansion

$$
Z(M,f,E)=(-1)^{\int_M\sum_j n_jQ_j},\qquad
\mathsf J_j=(-1)^{n_j}.                                         \tag{3}
$$

Equation (2) defines the coordinate convention. The concrete detecting lists
later in this document give representatives for all directions, sometimes in
an equivalent basis. Equation (3) is the response-coordinate interpretation,
not an instruction to substitute UMTC data into a polynomial.

## Common list with independent time reversal

Let $\alpha_1,\ldots,\alpha_{b_1}$,
$\beta_1,\ldots,\beta_{b_2}$, and
$\gamma_1,\ldots,\gamma_{b_4}$ be the ordered bases of
$H^1(P,\mathbb F_2)$, $H^2(P,\mathbb F_2)$, and
$H^4(P,\mathbb F_2)$ specified in each case below.

| Indicator | Characteristic-number coordinate $Q$ | Range |
|---|---|---|
| $\mathsf G$ | $u_2^2$ | one |
| $\mathsf A$ | $u_1^4$ | one |
| $\mathsf B$ | $v_2^2$ | one |
| $\mathsf C$ | $u_1^2v_2$ | one |
| $\mathsf W_i$ | $\alpha_i v_3$ | $1\leq i\leq b_1$ |
| $\mathsf S_j$ | $\beta_j v_2$ | $1\leq j\leq b_2$ |
| $\mathsf K_j$ | $\beta_j u_1^2$ | $1\leq j\leq b_2$ |
| $\mathsf P_r$ | $\gamma_r$ | $1\leq r\leq b_4$ |

The symbols $B,C$ used later for plane-group cohomology generators
are unrelated to the calligraphic/roman indicator names $\mathsf B,\mathsf C$.

### Completeness

The substitution $g\mapsto gT^{\epsilon(g)}$ makes the plane-group copy
unitary and identifies the relevant tangential structure with unoriented
bordism over $X=BP\times BSO(3)$. The unoriented-bordism decomposition gives

$$
\Omega_4^O(X)\cong H_4(X,\mathbb F_2)\oplus
H_2(X,\mathbb F_2)\oplus(\mathbb Z_2)^2.                        \tag{4}
$$

Using $H^*(BSO(3),\mathbb F_2)=\mathbb F_2[v_2,v_3]$, the first summand is
dual to $\gamma_r,\beta_jv_2,\alpha_iv_3,v_2^2$; the second is detected by
$u_1^2\beta_j,u_1^2v_2$. The last two are detected by $u_1^4,u_2^2$.
Independence of the second summand can also be checked on
$N^2\times\mathbb{RP}^2$, with the map to $X$ through $N^2$, subtracting
the same manifold with trivial bundle to remove purely gravitational numbers.
Thus

$$
\boxed{N_+(P)=4+b_1(P)+2b_2(P)+b_4(P).}                         \tag{5}
$$

This is a count of independent anomaly coordinates, not of realizations or
fractionalization classes. See [Thom] for (4) and [YZ22], Appendix D, for the
relation to anomaly indicators.

## Common list without independent time reversal

Set $u_1=\epsilon$. Keep every $\mathsf S_j$, with coordinate
$\beta_jv_2$. For groups containing a reflection or glide, also keep
$\mathsf G$, with coordinate $u_2^2$, and $\mathsf B$, with coordinate
$v_2^2$. For orientation-preserving groups these last two belong to the free
response directions and are omitted from the binary matching test.

Finally keep $\mathsf R_1,\ldots,\mathsf R_d$, whose purely spatial
coordinates $\delta_1,\ldots,\delta_d$ are given in each case. They form a
basis of the sign responses in
$H^4(P,U(1)_\epsilon)$, not a basis of all of
$H^4(P,\mathbb F_2)$.

The reduction must be done on response classes, not by deleting all indicator
expressions that mention $T$. For example the Wu formula gives

$$
\int_M\alpha_i v_3
=\int_M(\alpha_i^2+\epsilon\alpha_i)v_2,                       \tag{6}
$$

so the mixed $\mathsf W_i$ directions are already contained in the
$\mathsf S_j$ directions after restriction. Likewise $\mathsf K_j$
becomes the spatial response $\epsilon^2\beta_j$.

The spatial bases below were obtained using the twisted Bockstein reduction

$$
D_\epsilon=\operatorname{Sq}^1+\epsilon\smile-,\qquad
\delta_r\text{ chosen so }D_\epsilon\delta_r
\text{ are linearly independent}.                              \tag{7}
$$

For these plane groups the degree-four spatial anomaly group is elementary
2-torsion. One way to check this is the cellular spectral sequence for the
action on the plane: high-degree contributions come from cyclic rotation,
reflection, and dihedral stabilizers; in degree four with orientation
coefficients these have respectively $0$, $\mathbb Z_2$, and
$\mathbb Z_2$ (odd dihedral index) or $(\mathbb Z_2)^3$ (even index).
The edge maps take cokernels over $\mathbb F_2$. Hence reduction of the
integer Bockstein is injective in the degree used in (7); it would not be safe
to assume this for arbitrary symmetry groups or arbitrary cohomology degrees.

The degree-four bordism calculation then adds the $b_2(P)$ spin-mixed
directions, the spin-response sign when $\epsilon\ne0$, and the independent
gravitational sign. Thus

$$
\boxed{N_-(P)=b_2(P)+d(P)+2\,\mathbf 1_{\epsilon\ne0}.}        \tag{8}
$$

## Lattice targets and all Wyckoff positions

For each group let $k$ be its lattice-homotopy rank. Our ordered
$\beta$ basis is chosen so the first $k$ elements are LSM generators.
Let $\ell_j\in\{0,1\}$ be the occupation parity of the corresponding
irreducible lattice class and set

$$
\lambda=\sum_{j=1}^{k}\ell_j\beta_j.                            \tag{9}
$$

For a general WP orbit $W$, its contribution is its equivariant mod-2
Poincaré dual in $H^2_P(\mathbb R^2,\mathbb F_2)\cong H^2(P,\mathbb F_2)$.
Equivalently, move and split the occupied orbit according to lattice homotopy
and expand in the first $k$ generators. Add these contributions modulo two.
The geometric descriptions below identify the relevant parity tests. They do
not assume that every non-IWP orbit is trivial: a glide fundamental domain is
an important counterexample. Conventional WP letters must be interpreted in
the same origin, axes, and primitive-cell setting as the group presentation.

The target response is

$$
Z_{\mathrm{LSM},+}=(-1)^{\int\lambda(v_2+t^2)},\qquad
Z_{\mathrm{LSM},-}=(-1)^{\int\lambda v_2}.                       \tag{10}
$$

With time reversal, $t=u_1+\epsilon$, so

$$
\lambda(v_2+t^2)=\lambda v_2+\lambda u_1^2+
\lambda\epsilon^2.                                             \tag{11}
$$

Consequently all $\mathsf G,\mathsf A,\mathsf B,\mathsf C,\mathsf W_i$
have target +1; $\mathsf S_j=\mathsf K_j=(-1)^{\ell_j}$ for $j\le k$
and +1 otherwise. The $\mathsf P_r$ signs are the coefficients of
$\lambda\epsilon^2$ in the listed $\gamma$ basis. Each case below lists
the negative indicators for a single occupied lattice generator. Combine rows
by **symmetric difference** to obtain every one of its $2^k$ lattice classes.

Without time reversal, the only negative target for generator $\ell_j=1$
is $\mathsf S_j$. Every $\mathsf R_r$, $\mathsf G$, and
$\mathsf B$ present in that case has target +1. A trivial lattice has every
listed indicator +1 in either table.

## Index of all 34 cases

Every row retains the $SO(3)$ factor. $N_+$ and $N_-$ count independent
binary indicators with and without independent time reversal. The number of
lattice classes is $2^k$, independent of the UMTC.

| IT | Plane group | $b_1$ | $b_2$ | $b_4$ | $k$ | $N_+$ | $N_-$ |
|---:|---|---:|---:|---:|---:|---:|---:|
| 1 | [p1](#it-1-p1) | 2 | 1 | 0 | 1 | 8 | 1 |
| 2 | [p2](#it-2-p2) | 3 | 4 | 4 | 4 | 19 | 4 |
| 3 | [pm](#it-3-pm) | 3 | 4 | 4 | 2 | 19 | 8 |
| 4 | [pg](#it-4-pg) | 2 | 1 | 0 | 1 | 8 | 3 |
| 5 | [cm](#it-5-cm) | 2 | 2 | 2 | 1 | 12 | 5 |
| 6 | [pmm](#it-6-pmm) | 4 | 8 | 16 | 4 | 40 | 18 |
| 7 | [pmg](#it-7-pmg) | 3 | 4 | 4 | 3 | 19 | 7 |
| 8 | [pgg](#it-8-pgg) | 2 | 2 | 2 | 2 | 12 | 4 |
| 9 | [cmm](#it-9-cmm) | 3 | 5 | 9 | 3 | 26 | 11 |
| 10 | [p4](#it-10-p4) | 2 | 3 | 3 | 3 | 15 | 3 |
| 11 | [p4m](#it-11-p4m) | 3 | 6 | 12 | 3 | 31 | 14 |
| 12 | [p4g](#it-12-p4g) | 2 | 3 | 5 | 2 | 17 | 7 |
| 13 | [p3](#it-13-p3) | 0 | 1 | 0 | 1 | 6 | 1 |
| 14 | [p3m1](#it-14-p3m1) | 1 | 2 | 2 | 1 | 11 | 5 |
| 15 | [p31m](#it-15-p31m) | 1 | 2 | 2 | 1 | 11 | 5 |
| 16 | [p6](#it-16-p6) | 1 | 2 | 2 | 2 | 11 | 2 |
| 17 | [p6m](#it-17-p6m) | 2 | 4 | 8 | 2 | 22 | 10 |

## Group-by-group bases and target tables

In this section $x=A_x$, $y=A_y$, $a=A_{x+y}$, $c=A_c$, $m=A_m$,
and $s=A_s$ are **degree-one cohomology classes**, not translation coordinates.
The symbols $B=B_{xy}$, $D=B_{c^2}$ and $Q=B_{c(x+y)}$ have degree two;
$C=C_{c^2(x+y)}$, used only for $p4g$, has degree three. Their cochain
representatives and the group presentations use [YGHWZ21], Appendix E, with
its primitive-cell and origin conventions. When the same symbol occurs in
different groups it denotes the generator for that group.

In index ranges, $1:n$ means every index from 1 through $n$. Each tuple is ordered. The tuple called $H^2$ is the $\beta$ basis, including
non-LSM directions after index $k$. The $H^4$ tuple is the $\gamma$ basis.
The $\delta$ tuple labels $\mathsf R_r$ in the no-time-reversal case.
For actual evaluation, use the [per-group recipes](#coverage-and-per-group-evaluation-recipes)
for $\mathsf W_i,\mathsf S_j,\mathsf K_j$ and the spatial
$\mathsf E_r$ or $\widehat{\mathsf R}_r$ lists. These replace the
coordinate $\mathsf P_r$ or $\mathsf R_r$ entries by equivalent
independent evaluations; include only one spatial basis.
The displayed ring relations mean that the listed expressions vanish.
All listed monomial bases were obtained by exact linear reduction over
$\mathbb F_2$; no translation quotient was used.

For every row of a target table, all indicators not in the negative column
are +1. Multiple occupied generators combine by symmetric difference.
For `time_reversal=False`, the negative column for generator $j$ is always
just $\mathsf S_j$; this gives the entire target table without repeating it
17 times.

### IT 1: p1

Source: [YGHWZ21], Eqs. (E3–E7) and (F1). Orientation class $\epsilon=0$.

One parity: the number of half-integer spins per translation unit cell.

Ring relations (degree indicated by the notation above):

$$
x^{2}=0,\quad y^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(x,\;y)$ |
| $H^2$ | $(x y)$ |
| $H^4$ | $\varnothing$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:1},\mathsf K_{1:1}$; 8 indicators.

Without $T$: $\mathsf S_{1:1}$; 1 indicator.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |

### IT 2: p2

Source: [YGHWZ21], Eqs. (E8–E12) and (F2). Orientation class $\epsilon=0$.

In order: the rotation centers of $C_2$, $T_1C_2$, $T_2C_2$, and $T_1T_2C_2$.

Ring relations (degree indicated by the notation above):

$$
x^{2}+x c=0,\quad y^{2}+y c=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(x,\;y,\;c)$ |
| $H^2$ | $(x^{2}+x y+y^{2}+c^{2},\;x^{2}+x y,\;x y+y^{2},\;x y)$ |
| $H^4$ | $(x^{4},\;x^{3} y,\;y^{4},\;c^{4})$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:3}$, $\mathsf S_{1:4},\mathsf K_{1:4}$, $\mathsf P_{1:4}$; 19 indicators.

Without $T$: $\mathsf S_{1:4}$; 4 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ | $0$ | $\mathsf S_{2},\;\mathsf K_{2}$ |
| $\ell_3=1$ | $0$ | $\mathsf S_{3},\;\mathsf K_{3}$ |
| $\ell_4=1$ | $0$ | $\mathsf S_{4},\;\mathsf K_{4}$ |

### IT 3: pm

Source: [YGHWZ21], Eqs. (E13–E17) and (F3). Orientation class $\epsilon=m$.

In order: the spin parity per translation period on the mirror axes of $M$ and $T_1M$.

Ring relations (degree indicated by the notation above):

$$
x^{2}+x m=0,\quad y^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(x,\;y,\;m)$ |
| $H^2$ | $(x y+y m,\;x y,\;x^{2}+m^{2},\;x^{2})$ |
| $H^4$ | $(x^{4},\;x^{3} y,\;y m^{3},\;m^{4})$ |
| $\delta$ (without $T$) | $(x^{4},\;m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:3}$, $\mathsf S_{1:4},\mathsf K_{1:4}$, $\mathsf P_{1:4}$; 19 indicators.

Without $T$: $\mathsf S_{1:4}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:2}$; 8 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $x^{3} y+y m^{3}$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{2},\;\mathsf P_{3}$ |
| $\ell_2=1$ | $x^{3} y$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{2}$ |

### IT 4: pg

Source: [YGHWZ21], Eqs. (E18–E22) and (F4). Orientation class $\epsilon=s$.

One parity per fundamental domain of the full glide group. A translation unit cell consists of two such domains; its even total does not remove the glide LSM constraint.

Ring relations (degree indicated by the notation above):

$$
x^{2}+x s=0,\quad s^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(x,\;s)$ |
| $H^2$ | $(x^{2})$ |
| $H^4$ | $\varnothing$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:1},\mathsf K_{1:1}$; 8 indicators.

Without $T$: $\mathsf S_{1:1}$, $\mathsf G,\mathsf B$; 3 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |

### IT 5: cm

Source: [YGHWZ21], Eqs. (E23–E27) and (F5). Orientation class $\epsilon=m$.

One parity per $T_1T_2$ translation period along the mirror axis of $M$, in the primitive centered-lattice basis of [YGHWZ21].

Ring relations (degree indicated by the notation above):

$$
a^{2}=0,\quad a m=0,\quad a B=0,\quad B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(a,\;m)$ |
| $H^2$ | $(B,\;m^{2})$ |
| $H^4$ | $(m^{4},\;m^{2} B)$ |
| $\delta$ (without $T$) | $(m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:2},\mathsf K_{1:2}$, $\mathsf P_{1:2}$; 12 indicators.

Without $T$: $\mathsf S_{1:2}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:1}$; 5 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $m^{2} B$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{2}$ |

### IT 6: pmm

Source: [YGHWZ21], Eqs. (E28–E32) and (F6). Orientation class $\epsilon=m$.

In order: the rotation centers of $C_2$, $T_1T_2C_2$, $T_1C_2$, and $T_2C_2$.

Ring relations (degree indicated by the notation above):

$$
x^{2}+x c+x m=0,\quad y^{2}+y c=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(x,\;y,\;c,\;m)$ |
| $H^2$ | $(x y+x c+y^{2}+y m+c^{2}+c m,\;x y,\;x y+x c,\;x y+y^{2}+y m,\;x^{2}+x c+c m+m^{2},\;y m+c m,\;x^{2}+x c,\;y m)$ |
| $H^4$ | $(x^{4},\;x^{3} y,\;x^{3} c,\;x^{2} y^{2},\;x^{2} c^{2},\;x y^{3},\;x c^{3},\;y^{4},\;y^{3} m,\;y^{2} m^{2},\;y m^{3},\;c^{4},\;c^{3} m,\;c^{2} m^{2},\;c m^{3},\;m^{4})$ |
| $\delta$ (without $T$) | $(x^{4},\;x^{2} y^{2},\;x^{2} c^{2},\;y^{4},\;y^{2} m^{2},\;c^{4},\;c^{2} m^{2},\;m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:4}$, $\mathsf S_{1:8},\mathsf K_{1:8}$, $\mathsf P_{1:16}$; 40 indicators.

Without $T$: $\mathsf S_{1:8}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:8}$; 18 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $x^{3} y+x^{3} c+x y^{3}+x c^{3}+y^{2} m^{2}+y m^{3}+c^{2} m^{2}+c m^{3}$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{2},\;\mathsf P_{3},\;\mathsf P_{6},\;\mathsf P_{7},\;\mathsf P_{10},\;\mathsf P_{11},\;\mathsf P_{14},\;\mathsf P_{15}$ |
| $\ell_2=1$ | $x^{3} y+x y^{3}$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{2},\;\mathsf P_{6}$ |
| $\ell_3=1$ | $x^{3} y+x^{3} c+x y^{3}+x c^{3}$ | $\mathsf S_{3},\;\mathsf K_{3},\;\mathsf P_{2},\;\mathsf P_{3},\;\mathsf P_{6},\;\mathsf P_{7}$ |
| $\ell_4=1$ | $x^{3} y+x y^{3}+y^{2} m^{2}+y m^{3}$ | $\mathsf S_{4},\;\mathsf K_{4},\;\mathsf P_{2},\;\mathsf P_{6},\;\mathsf P_{10},\;\mathsf P_{11}$ |

### IT 7: pmg

Source: [YGHWZ21], Eqs. (E33–E37) and (F7). Orientation class $\epsilon=m$.

In order: the orbit of the $C_2$ center, the orbit of the $T_1T_2C_2$ center, and the parity per $T_2$ period on the mirror axis of $M$. The third LSM generator is required by Eq. (F7).

Ring relations (degree indicated by the notation above):

$$
y^{2}+y c=0,\quad c m=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(y,\;c,\;m)$ |
| $H^2$ | $(y^{2}+c^{2},\;y^{2},\;y m,\;m^{2})$ |
| $H^4$ | $(y^{4},\;y m^{3},\;c^{4},\;m^{4})$ |
| $\delta$ (without $T$) | $(m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:3}$, $\mathsf S_{1:4},\mathsf K_{1:4}$, $\mathsf P_{1:4}$; 19 indicators.

Without $T$: $\mathsf S_{1:4}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:1}$; 7 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ | $0$ | $\mathsf S_{2},\;\mathsf K_{2}$ |
| $\ell_3=1$ | $y m^{3}$ | $\mathsf S_{3},\;\mathsf K_{3},\;\mathsf P_{2}$ |

### IT 8: pgg

Source: [YGHWZ21], Eqs. (E38–E42) and (F8). Orientation class $\epsilon=s$.

In order: the orbit containing the centers of $C_2$ and $T_1T_2C_2$, and the orbit containing the centers of $T_1C_2$ and $T_2C_2$.

Ring relations (degree indicated by the notation above):

$$
s^{2}=0,\quad c s=0,\quad s Q=0,\quad c^{2} Q+Q^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c,\;s)$ |
| $H^2$ | $(c^{2}+Q,\;Q)$ |
| $H^4$ | $(c^{4},\;c^{2} Q)$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:2},\mathsf K_{1:2}$, $\mathsf P_{1:2}$; 12 indicators.

Without $T$: $\mathsf S_{1:2}$, $\mathsf G,\mathsf B$; 4 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ | $0$ | $\mathsf S_{2},\;\mathsf K_{2}$ |

### IT 9: cmm

Source: [YGHWZ21], Eqs. (E43–E48) and (F9). Orientation class $\epsilon=m$.

In order: the center of $C_2$, the center of $T_1T_2C_2$, and the orbit containing the centers of $T_1C_2$ and $T_2C_2$.

Ring relations (degree indicated by the notation above):

$$
a^{2}+a c=0,\quad a m=0,\quad a B=0,\quad c^{2} B+c m B+B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(a,\;c,\;m)$ |
| $H^2$ | $(a^{2}+c^{2}+c m+B,\;B,\;a^{2},\;c m+m^{2},\;c m)$ |
| $H^4$ | $(a^{4},\;c^{4},\;c^{3} m,\;c^{2} m^{2},\;c^{2} B,\;c m^{3},\;c m B,\;m^{4},\;m^{2} B)$ |
| $\delta$ (without $T$) | $(c^{4},\;c^{2} m^{2},\;c m B,\;m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:3}$, $\mathsf S_{1:5},\mathsf K_{1:5}$, $\mathsf P_{1:9}$; 26 indicators.

Without $T$: $\mathsf S_{1:5}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:4}$; 11 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $c^{2} m^{2}+c m^{3}+m^{2} B$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{4},\;\mathsf P_{6},\;\mathsf P_{9}$ |
| $\ell_2=1$ | $m^{2} B$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{9}$ |
| $\ell_3=1$ | $0$ | $\mathsf S_{3},\;\mathsf K_{3}$ |

### IT 10: p4

Source: [YGHWZ21], Eqs. (E49–E54) and (F10). Orientation class $\epsilon=0$.

The standard classes $a,b,c$: respectively the centers of $C_4^2$, $T_1T_2C_4^2$, and the orbit of $T_1C_4^2$ and $T_2C_4^2$. The WP multiplicities are $1a,1b,2c$.

Ring relations (degree indicated by the notation above):

$$
c^{2}=0,\quad c a=0,\quad c B+a B=0,\quad a^{3}+a D+a B=0,\quad D B+B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c,\;a)$ |
| $H^2$ | $(a^{2}+D+B,\;B,\;a^{2})$ |
| $H^4$ | $(a^{4},\;D^{2},\;D B)$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:3},\mathsf K_{1:3}$, $\mathsf P_{1:3}$; 15 indicators.

Without $T$: $\mathsf S_{1:3}$; 3 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ (a) | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ (b) | $0$ | $\mathsf S_{2},\;\mathsf K_{2}$ |
| $\ell_3=1$ (c) | $0$ | $\mathsf S_{3},\;\mathsf K_{3}$ |

### IT 11: p4m

Source: [YGHWZ21], Eqs. (E55–E59) and (F11). Orientation class $\epsilon=m$.

The standard classes $a,b,c$, with the same rotation-center definitions and WP multiplicities $1a,1b,2c$ as in $p4$.

Ring relations (degree indicated by the notation above):

$$
c^{2}+c m=0,\quad c a=0,\quad c B+a B+m B=0,\quad a^{3}+a^{2} m+a D+a B=0,\quad D B+B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c,\;a,\;m)$ |
| $H^2$ | $(a^{2}+a m+D+B,\;B,\;a^{2}+a m,\;c^{2}+a m+m^{2},\;a m,\;c^{2})$ |
| $H^4$ | $(c^{4},\;c^{2} D,\;c^{2} B,\;a^{4},\;a^{3} m,\;a^{2} m^{2},\;a^{2} D,\;a m^{3},\;m^{4},\;m^{2} D,\;D^{2},\;D B)$ |
| $\delta$ (without $T$) | $(c^{4},\;a^{4},\;a^{2} m^{2},\;m^{4},\;D^{2},\;D B)$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:3}$, $\mathsf S_{1:6},\mathsf K_{1:6}$, $\mathsf P_{1:12}$; 31 indicators.

Without $T$: $\mathsf S_{1:6}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:6}$; 14 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ (a) | $c^{2} B+a^{4}+a^{3} m+a^{2} m^{2}+a^{2} D+a m^{3}+m^{2} D$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{3},\;\mathsf P_{4},\;\mathsf P_{5},\;\mathsf P_{6},\;\mathsf P_{7},\;\mathsf P_{8},\;\mathsf P_{10}$ |
| $\ell_2=1$ (b) | $c^{2} B+a^{4}+a^{3} m+a^{2} D$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{3},\;\mathsf P_{4},\;\mathsf P_{5},\;\mathsf P_{7}$ |
| $\ell_3=1$ (c) | $a^{2} m^{2}+a m^{3}$ | $\mathsf S_{3},\;\mathsf K_{3},\;\mathsf P_{6},\;\mathsf P_{8}$ |

### IT 12: p4g

Source: [YGHWZ21], Eqs. (E60–E66) and (F12). Orientation class $\epsilon=s$.

In order: the fourfold-center orbit (centers of $C_4^2$ and $T_1T_2C_4^2$), and the twofold-center orbit on mirrors (centers of $T_1C_4^2$ and $T_2C_4^2$).

Ring relations (degree indicated by the notation above):

$$
c^{2}=0,\quad c s=0,\quad c Q=0,\quad s D+s Q=0,\quad D Q+Q^{2}=0,\quad c C=0,\quad D C+Q C=0,\quad s D C+Q^{3}+C^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c,\;s)$ |
| $H^2$ | $(D+Q,\;Q,\;s^{2})$ |
| $H^4$ | $(s^{4},\;s^{2} D,\;s C,\;D^{2},\;D Q)$ |
| $\delta$ (without $T$) | $(s^{4},\;s C)$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:3},\mathsf K_{1:3}$, $\mathsf P_{1:5}$; 17 indicators.

Without $T$: $\mathsf S_{1:3}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:2}$; 7 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ | $s^{2} D$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{2}$ |

The degree-three generator $C$ is essential: $sC$ occurs in $H^4$ and
also survives in the no-$T$ spatial response. A table built only from
products of degree-one and degree-two generators misses this direction.
The source gives restrictions characterizing $C$, but no explicit cochain.

### IT 13: p3

Source: [YGHWZ21], Eqs. (E67–E71) and (F13). Orientation class $\epsilon=0$.

One parity per translation unit cell. The three inequivalent threefold-center WPs all contribute to the same lattice-homotopy generator; a threefold stabilizer does not by itself imply a trivial LSM class.

Ring relations (degree indicated by the notation above):

$$
B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $\varnothing$ |
| $H^2$ | $(B)$ |
| $H^4$ | $\varnothing$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf S_{1:1},\mathsf K_{1:1}$; 6 indicators.

Without $T$: $\mathsf S_{1:1}$; 1 indicator.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |

### IT 14: p3m1

Source: [YGHWZ21], Eqs. (E72–E77) and (F14). Orientation class $\epsilon=m$.

One parity per translation unit cell, as in Eq. (F14).

Ring relations (degree indicated by the notation above):

$$
B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(m)$ |
| $H^2$ | $(B,\;m^{2})$ |
| $H^4$ | $(m^{4},\;m^{2} B)$ |
| $\delta$ (without $T$) | $(m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:1}$, $\mathsf S_{1:2},\mathsf K_{1:2}$, $\mathsf P_{1:2}$; 11 indicators.

Without $T$: $\mathsf S_{1:2}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:1}$; 5 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $m^{2} B$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{2}$ |

### IT 15: p31m

Source: [YGHWZ21], Eqs. (E78–E83) and (F15). Orientation class $\epsilon=m$.

One parity per $T_1T_2$ translation period on the mirror axis, as in Eq. (F15). Its WP-to-lattice map must use the $p31m$ setting, despite its cohomology ring being isomorphic to that of $p3m1$.

Ring relations (degree indicated by the notation above):

$$
B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(m)$ |
| $H^2$ | $(B,\;m^{2})$ |
| $H^4$ | $(m^{4},\;m^{2} B)$ |
| $\delta$ (without $T$) | $(m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:1}$, $\mathsf S_{1:2},\mathsf K_{1:2}$, $\mathsf P_{1:2}$; 11 indicators.

Without $T$: $\mathsf S_{1:2}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:1}$; 5 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ | $m^{2} B$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{2}$ |

### IT 16: p6

Source: [YGHWZ21], Eqs. (E84–E89) and (F16). Orientation class $\epsilon=0$.

The standard classes $a,c$: the sixfold-center WP $1a$ and the twofold-center WP $3c$. The honeycomb WP $2b$ has zero lattice-homotopy charge.

Ring relations (degree indicated by the notation above):

$$
c^{2} B+B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c)$ |
| $H^2$ | $(c^{2}+B,\;B)$ |
| $H^4$ | $(c^{4},\;c^{2} B)$ |
| $\delta$ (without $T$) | $\varnothing$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:1}$, $\mathsf S_{1:2},\mathsf K_{1:2}$, $\mathsf P_{1:2}$; 11 indicators.

Without $T$: $\mathsf S_{1:2}$; 2 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ (a) | $0$ | $\mathsf S_{1},\;\mathsf K_{1}$ |
| $\ell_2=1$ (c) | $0$ | $\mathsf S_{2},\;\mathsf K_{2}$ |

### IT 17: p6m

Source: [YGHWZ21], Eqs. (E90–E94) and (F17). Orientation class $\epsilon=m$.

The standard classes $a,c$, with WP multiplicities $1a,3c$; $2b$ is trivial as in $p6$.

Ring relations (degree indicated by the notation above):

$$
c^{2} B+c m B+B^{2}=0.
$$

| Basis | Ordered generators |
|---|---|
| $H^1$ | $(c,\;m)$ |
| $H^2$ | $(c^{2}+c m+B,\;B,\;c m+m^{2},\;c m)$ |
| $H^4$ | $(c^{4},\;c^{3} m,\;c^{2} m^{2},\;c^{2} B,\;c m^{3},\;c m B,\;m^{4},\;m^{2} B)$ |
| $\delta$ (without $T$) | $(c^{4},\;c^{2} m^{2},\;c m B,\;m^{4})$ |

With $T$: $\mathsf G,\mathsf A,\mathsf B,\mathsf C$, $\mathsf W_{1:2}$, $\mathsf S_{1:4},\mathsf K_{1:4}$, $\mathsf P_{1:8}$; 22 indicators.

Without $T$: $\mathsf S_{1:4}$, $\mathsf G,\mathsf B$, $\mathsf R_{1:4}$; 10 indicators.

| Occupied lattice generator | $\epsilon^2\beta_j$ | Negative targets with $T$ |
|---|---|---|
| $\ell_1=1$ (a) | $c^{2} m^{2}+c m^{3}+m^{2} B$ | $\mathsf S_{1},\;\mathsf K_{1},\;\mathsf P_{3},\;\mathsf P_{5},\;\mathsf P_{8}$ |
| $\ell_2=1$ (c) | $m^{2} B$ | $\mathsf S_{2},\;\mathsf K_{2},\;\mathsf P_{8}$ |

## Explicit UMTC lists in the four published conventions

The indicators in this section use **the paper's numbering** $\mathsf I_j$.
They are not the $\mathsf S,\mathsf K,\mathsf P,\ldots$ coordinate indicators
above. Equal numbers of indicators do not imply a row-by-row identification:
the two complete lists are related by an invertible change of binary basis.

### Common UMTC functions

Let $\mathcal D=\sqrt{\sum_a d_a^2}$, with $d_a$ and $\theta_a$ the
quantum dimension and topological spin of anyon $a$. Let $q_a=0,1/2$
denote its integer/half-integer SO(3) spin. The required functions are

$$
\begin{aligned}
\mathcal I_0&=\mathcal D^{-1}\sum_a d_a^2\theta_a,\\
\mathcal I_1(A)&=\mathcal D^{-1}
 \sum_{a:\,{}^Aa=a}d_a\theta_a\eta_a(A,A),\\
\mathcal I_4&=\mathcal D^{-1}\sum_a d_a^2\theta_a e^{2\pi i q_a}.
\end{aligned}                                                    \tag{12}
$$

These are Eqs. (209), (210), and (213) of [YZ23]. Their counterparts
in [YZ22] are Eqs. (46), (50), and the spin-weighted sum in (106).
The two further contractions below are Eqs. (55) and (53) of [YZ22],
respectively. In addition:

- $\mathcal I_2(A,B)$ means the **full fusion-multiplicity contraction in
  [Eq. (211)](https://arxiv.org/html/2309.15118v3#A4.E211)**, with $A,B$
  commuting antiunitary involutions.
- $\mathcal I_3(A,B)$ means the **full fusion-multiplicity contraction in
  [Eq. (212)](https://arxiv.org/html/2309.15118v3#A4.E212)**, with $A,B$
  commuting unitary involutions. Its arguments are ordered.

These references specify the entire sums, including $F,R,U,\eta$; no
assumption of trivial anyon permutation or multiplicity-free fusion is made.
Do not replace either function by an $\eta$-commutator for a generic UMTC.

Let $X=T_1$, $Y=T_2$, and $T=\mathcal T$. Let $U,V$ be spin
rotations through $\pi$ about perpendicular axes. They commute and have
order two in SO(3), although their SU(2) lifts anticommute. Set
$R=C_6^3$ for hexagonal groups and $R=C_4^2$ for square groups. These
letters denote group elements in this section, not the cohomology classes
used in the preceding tables.

### Table I: $p6\times SO(3)$

This is Eq. (214) of [YZ23].

| Indicator | UMTC expression | LSM target |
|---|---|---|
| $\mathsf I_1$ | $\mathcal I_3(RU,RV)$ | $(-1)^{\ell_a}$ |
| $\mathsf I_2$ | $\mathcal I_3(XRU,XRV)$ | $(-1)^{\ell_c}$ |

| Lattice class | $\mathsf I_1$ | $\mathsf I_2$ |
|---|---:|---:|
| 0 | +1 | +1 |
| a | −1 | +1 |
| c | +1 | −1 |
| a+c | −1 | −1 |

### Table II: $p4\times SO(3)$

This is Eq. (215) of [YZ23].

| Indicator | UMTC expression | LSM target |
|---|---|---|
| $\mathsf I_1$ | $\mathcal I_3(RU,RV)$ | $(-1)^{\ell_a}$ |
| $\mathsf I_2$ | $\mathcal I_3(XYRU,XYRV)$ | $(-1)^{\ell_b}$ |
| $\mathsf I_3$ | $\mathcal I_3(XRU,XRV)$ | $(-1)^{\ell_c}$ |

| Lattice class | $\mathsf I_1$ | $\mathsf I_2$ | $\mathsf I_3$ |
|---|---:|---:|---:|
| 0 | +1 | +1 | +1 |
| a | −1 | +1 | +1 |
| b | +1 | −1 | +1 |
| c | +1 | +1 | −1 |
| a+b | −1 | −1 | +1 |
| a+c | −1 | +1 | −1 |
| b+c | +1 | −1 | −1 |
| a+b+c | −1 | −1 | −1 |

### Table XVIII: $p6m\times SO(3)\times\mathbb Z_2^T$

This is the complete Eq. (216) list, including the indicators whose lattice
targets are always +1. The two subscript corrections described below are
applied explicitly.

| Index $j$ | $\mathsf I_j$ | LSM target |
|---:|---|---|
| 0 | $\mathcal I_0$ | +1 |
| 1 | $\mathcal I_1(T)$ | +1 |
| 2 | $\mathcal I_1(M)$ | +1 |
| 3 | $\mathcal I_1(RT)$ | $(-1)^{\ell_a}$ |
| 4 | $\mathcal I_1(RM)$ | +1 |
| 5 | $\mathcal I_2(T,RT)$ | $(-1)^{\ell_a}$ |
| 6 | $\mathcal I_2(T,M)$ | +1 |
| 7 | $\mathcal I_2(RT,M)$ | +1 |
| 8 | $\mathcal I_2(RT,RM)$ | +1 |
| 9 | $\mathcal I_2(M,RM)$ | +1 |
| 10 | $\mathcal I_1(XYRT)$ | $(-1)^{\ell_c}$ |
| 11 | $\mathcal I_2(M,XYRT)$ | +1 |
| 12 | $\mathcal I_2(T,XYRT)$ | $(-1)^{\ell_c}$ |
| 13 | $\mathcal I_2(M,XYRM)$ | +1 |
| 14 | $\mathcal I_1(TU)$ | +1 |
| 15 | $\mathcal I_1(MU)$ | +1 |
| 16 | $\mathcal I_1(RTU)$ | +1 |
| 17 | $\mathcal I_1(RMU)$ | +1 |
| 18 | $\mathcal I_1(XYRTU)$ | +1 |
| 19 | $\mathcal I_4$ | +1 |
| 20 | $\mathcal I_3(RU,V)$ | $(-1)^{\ell_a}$ |
| 21 | $\mathcal I_3(MTU,V)$ | +1 |

Equivalently, the full target vectors can be specified by their negative
indices:

| Lattice class | Indices with target −1 |
|---|---|
| 0 | none |
| a | 3, 5, 20 |
| c | 10, 12 |
| a+c | 3, 5, 10, 12, 20 |

### Table XIX: $p4m\times SO(3)\times\mathbb Z_2^T$

This is the complete Eq. (217) list.

| Index $j$ | $\mathsf I_j$ | LSM target |
|---:|---|---|
| 0 | $\mathcal I_0$ | +1 |
| 1 | $\mathcal I_1(T)$ | +1 |
| 2 | $\mathcal I_1(M)$ | +1 |
| 3 | $\mathcal I_1(RT)$ | $(-1)^{\ell_a}$ |
| 4 | $\mathcal I_1(C_4M)$ | +1 |
| 5 | $\mathcal I_2(T,RT)$ | $(-1)^{\ell_a}$ |
| 6 | $\mathcal I_2(T,M)$ | +1 |
| 7 | $\mathcal I_2(T,C_4M)$ | +1 |
| 8 | $\mathcal I_2(RT,M)$ | +1 |
| 9 | $\mathcal I_2(RT,C_4M)$ | +1 |
| 10 | $\mathcal I_1(XM)$ | +1 |
| 11 | $\mathcal I_1(XRT)$ | $(-1)^{\ell_c}$ |
| 12 | $\mathcal I_1(XYRT)$ | $(-1)^{\ell_b}$ |
| 13 | $\mathcal I_2(T,XM)$ | +1 |
| 14 | $\mathcal I_2(T,XRT)$ | $(-1)^{\ell_c}$ |
| 15 | $\mathcal I_2(T,XYRT)$ | $(-1)^{\ell_b}$ |
| 16 | $\mathcal I_2(YRT,M)$ | +1 |
| 17 | $\mathcal I_2(M,YRM)$ | +1 |
| 18 | $\mathcal I_2(XY^{-1}RT,C_4M)$ | +1 |
| 19 | $\mathcal I_2(XYRT,XM)$ | +1 |
| 20 | $\mathcal I_4$ | +1 |
| 21 | $\mathcal I_1(TU)$ | +1 |
| 22 | $\mathcal I_1(MU)$ | +1 |
| 23 | $\mathcal I_1(RTU)$ | +1 |
| 24 | $\mathcal I_1(C_4MU)$ | +1 |
| 25 | $\mathcal I_1(XMU)$ | +1 |
| 26 | $\mathcal I_1(XRTU)$ | +1 |
| 27 | $\mathcal I_1(XYRTU)$ | +1 |
| 28 | $\mathcal I_3(C_4MTU,V)$ | +1 |
| 29 | $\mathcal I_3(MTU,V)$ | +1 |
| 30 | $\mathcal I_3(XMTU,V)$ | +1 |

| Lattice class | Indices with target −1 |
|---|---|
| 0 | none |
| a | 3, 5 |
| b | 12, 15 |
| c | 11, 14 |
| a+b | 3, 5, 12, 15 |
| a+c | 3, 5, 11, 14 |
| b+c | 11, 12, 14, 15 |
| a+b+c | 3, 5, 11, 12, 14, 15 |

### Why these published target signs follow from the lattice response

This also checks the convention relating the two catalogues. An
$\mathcal I_1(A)$ evaluates the response on $\mathbb{RP}^4$; an
$\mathcal I_2(A,B)$ uses $\mathbb{RP}^2\times\mathbb{RP}^2$; an
$\mathcal I_3(A,B)$ uses $\mathbb{RP}^3\times S^1$, with the first
argument assigned to the projective-space cycle. These manifolds and their
bundle assignments are given in [YZ22], Sec. IV.

Let $\lambda_A$ denote the coefficient of the restriction of the lattice
class $\lambda$ to the spatial involution in $A$. Let $t_A=0,1$
record its physical time-reversal factor and $s_A=0,1$ its absent/present
spin $\pi$ rotation. Substitution in (10) gives

$$
\begin{aligned}
\mathcal I_1(A)\big|_{\mathrm{LSM}}
 &=(-1)^{\lambda_A(t_A+s_A)},\\
\mathcal I_2(A,B)\big|_{\mathrm{LSM}}
 &=(-1)^{\lambda_A t_B+\lambda_B t_A}
 \quad\text{for the spin-free pairs above}.                     \tag{13}
\end{aligned}
$$

For $\mathcal I_3(HU,HV)$ or $\mathcal I_3(HU,V)$, where $H$
is a spatial unitary involution without physical time reversal, the SO(3)
bundle has $v_2=x^2+xy$ on $\mathbb{RP}^3\times S^1$. Both evaluations
give $(-1)^{\lambda_H}$. Here $x,y$ are the generators of the
projective-space and circle cohomology and are unrelated to the plane-group
classes named $x,y$ earlier. In particular, $\int x^3y=1$.

The lattice class has nonzero involution restrictions at the occupied
twofold-center orbits, while its mirror-square restrictions vanish. These
rules reproduce every nontrivial entry in the four tables above. For example,
$\mathcal I_1(RT)$ is $(-1)^{\ell_a}$, whereas
$\mathcal I_1(RTU)$ is +1 because the two terms in $v_2+t^2$ cancel.

## Evaluation recipes using published indicators

Let $q$ be the antiunitary character of the full symmetry after crystalline
equivalence. Thus $q(g)=\epsilon(g)$ for a spatial element and $q(T)=1$.
With independent time reversal, $\widehat g=gT^{\epsilon(g)}$ is unitary.
As in the published lists, $X=T_1$, $Y=T_2$, and $U,V$ are spin $\pi$
rotations about orthogonal axes. $L$ is the glide generator denoted $G$ in
[YGHWZ21], Appendix E. A hat over a word applies to the entire word.

### OLD: internal indicators

All four internal coordinates with time reversal use OLD formulas:

$$
\mathsf G=\mathcal I_0,\qquad
\mathsf A=\mathcal I_1(T),\qquad
\mathsf B=\frac{\mathcal I_4}{\mathcal I_0},\qquad
\mathsf C=\frac{\mathcal I_1(TU)}{\mathsf A\mathsf B}.          \tag{14}
$$

Without time reversal, retain only $\mathsf G,\mathsf B$ from (14), and
only for $\epsilon\ne0$. Their formulas do not require a physical $T$.
All these internal indicators have lattice target +1.

### OLD: all evaluations associated with spatial involutions

For a spatial involution $g$, define the following explicit OLD combinations
when independent time reversal is present:

$$
\boxed{
\begin{aligned}
\mathcal S_o(g)&=
\frac{\mathcal I_1(T\widehat gU)\,\mathcal I_1(T)}
     {\mathcal I_1(T\widehat g)\,\mathcal I_1(TU)},\\
\mathcal K_o(g)&=\frac{\mathcal I_2(T\widehat g,T)}{\mathcal I_0},\\
\mathcal W_o(g)&=\frac{\mathcal I_3(\widehat gU,\widehat gV)}
                         {\mathcal S_o(g)}.
\end{aligned}}                                                   \tag{15}
$$

Every argument here satisfies the original published order and antiunitarity
conditions. These replace the corresponding evaluations on
$\mathbb{RP}^2\times S^2$, $\mathbb{RP}^2\times\mathbb{RP}^2$, and
the three-factor manifold associated with the degree-one coordinates.
No new tensor contraction is needed for (15).

For the no-time-reversal case, the OLD spin-mixed involution formula is

$$
\boxed{
\mathcal S_-(g)=
\begin{cases}
\mathcal I_3(gU,gV),&\epsilon(g)=0,\\[2pt]
\displaystyle\frac{\mathcal I_1(gU)}{\mathcal I_1(g)\mathsf B},
 &\epsilon(g)=1.
\end{cases}}                                                     \tag{16}
$$

The $\mathsf B$ in the second row is present for every group in which that
row is used. No artificial time-reversal generator is introduced in (16).

To see exactly what (15) measures, put
$b_j(g)=\langle\beta_j,[\mathbb{RP}^2_g]\rangle$. Then
$\mathcal S_o(g)=\prod_j\mathsf S_j^{b_j(g)}$,
$\mathcal K_o(g)=\prod_j\mathsf K_j^{b_j(g)}$, and
$\mathcal W_o(g)=\prod_i\mathsf W_i^{\alpha_i(g)}$.
For the involutions in the recipes below, $b_j(g)$ selects exactly the stated
$\beta_j$.

The cancellations can be checked on the characteristic numbers. On
$\mathbb{RP}^4$, the spin twist adds $v_2=x^2$, $v_3=0$, so the first
ratio cancels every contribution except $\beta_jv_2$. On
$\mathbb{RP}^2\times\mathbb{RP}^2$, the bundle in the second formula
measures $\beta_j u_1^2$ and $u_2^2$; division by $\mathcal I_0$
removes the latter. On $\mathbb{RP}^3\times S^1$ in the last formula,
$v_2=x^2+xy$, $v_3=x^2y$, and the spatial map is through the involution
on both cycles. Its value is
$\prod_j\mathsf S_j^{b_j(g)}\prod_i\mathsf W_i^{\alpha_i(g)}$.
Division by $\mathcal S_o(g)$ isolates the degree-one contribution.

### EXTENDED: reuse the circle-holonomy contraction

Define

$$
\mathcal J(A,B)=Z(\mathbb{RP}^3\times S^1;A,B),\qquad
A^2=1,\quad [A,B]=1,\quad q(A)=q(B)=0.                          \tag{17}
$$

Its proposed evaluation is the **same full tensor contraction** as [YZ22],
[Eq. (53)](https://arxiv.org/pdf/2210.02444#page=18), equivalently [YZ23],
[Eq. (212)](https://arxiv.org/html/2309.15118v3#A4.E212).
When $B^2=1$, this is simply the OLD function $\mathcal I_3(A,B)$.
Here the EXTENDED label is used only when the second argument is not an
involution.

The extension allows the circle holonomy to be any commuting unitary element,
including a translation. The manifold has fundamental group
$\mathbb Z_2\times\mathbb Z$: its handle relations require $A^2=1$
and $[A,B]=1$, with no condition $B^2=1$. The contraction contains
$\eta_b(A,A)$ and the $A,B$ commutator, and no $B$-square term.
This is the geometric justification for reusing the tensor sum. Extending
its domain is a claim made here; it should still be checked explicitly when
implementing the evaluator. Translations retain their actual infinite order.

For a mirror involution $m$ and a commuting orientation-preserving translation
$h$, define the spin-mixed EXTENDED combination

$$
\boxed{\mathcal S_e(m,h)=
\frac{\mathcal J(\widehat mU,h)}{\mathcal J(\widehat m,h)}.}      \tag{18}
$$

This formula is used **only with independent time reversal**. The spatial
bundle is the same in numerator and denominator. Adding the spin twist gives
$v_2=x^2$, $v_3=0$ on $\mathbb{RP}^3\times S^1$, so the ratio detects
the $xy$ coefficient of $\beta_j$ and no other response coordinate. It
replaces the spin-flux surface evaluation for every mirror-period row below.
Without $T$, the mirror is antiunitary and cannot occupy the first slot of
$\mathcal J$; those rows use NEW $\mathcal N_1$ instead.

### NEW symbols used in the recipes

Only the following four NEW templates occur. Their complete domains, required
instances, derived formulas, and remaining calculations are listed in the
[final section](#new-anomaly-indicators-formulas-and-remaining-calculations):

| Symbol | Geometric evaluation |
|---|---|
| $\mathcal N_1(A;B,C)$ | $Z(\mathbb{RP}^2\times T^2;A,B,C)$ |
| $\mathcal N_2(A;B,L)$ | $Z(\mathbb{RP}^2\times\mathrm{Kl};A,B,L)$, trivial spin bundle |
| $\mathcal N_3(B,C)$ | $Z(T^2_{B,C}\times S^2;\int_{S^2}v_2=1)$ |
| $\mathcal N_4(B,L)$ | $Z(\mathrm{Kl}_{B,L}\times S^2;\int_{S^2}v_2=1)$ |

Here $T^2$ in a manifold name means a two-torus. It is unrelated to the
square of the time-reversal operation. The final section explains which
specializations have explicit formulas; the generic symbols are not aliases
for a single published $\mathcal I_n$ function.

## Coverage and per-group evaluation recipes

Every row below combines with the OLD internal indicators and the spatial
lists that follow. Counts refer to independent scalar indicators in the
selected basis, not the number of calls to an underlying tensor function.
An EXTENDED ratio can use multiple calls to the same contraction. The NEW
counts count instances of four shared templates, not new templates per group.
They retain the provenance labels of the OLD-first lists; the remaining
formula gaps are counted separately at the end.

| IT | Group | With $T$: OLD / EXTENDED / NEW | Without $T$: OLD / NEW |
|---:|---|---:|---:|
| 1 | p1 | 4 / 0 / 4 | 0 / 1 |
| 2 | p2 | 19 / 0 / 0 | 4 / 0 |
| 3 | pm | 12 / 4 / 3 | 6 / 2 |
| 4 | pg | 4 / 0 / 4 | 2 / 1 |
| 5 | cm | 8 / 2 / 2 | 4 / 1 |
| 6 | pmm | 40 / 0 / 0 | 18 / 0 |
| 7 | pmg | 16 / 2 / 1 | 6 / 1 |
| 8 | pgg | 11 / 0 / 1 | 4 / 0 |
| 9 | cmm | 26 / 0 / 0 | 11 / 0 |
| 10 | p4 | 14 / 0 / 1 | 3 / 0 |
| 11 | p4m | 31 / 0 / 0 | 14 / 0 |
| 12 | p4g | 16 / 0 / 1 | 7 / 0 |
| 13 | p3 | 4 / 0 / 2 | 0 / 1 |
| 14 | p3m1 | 8 / 2 / 1 | 4 / 1 |
| 15 | p31m | 8 / 2 / 1 | 4 / 1 |
| 16 | p6 | 11 / 0 / 0 | 2 / 0 |
| 17 | p6m | 22 / 0 / 0 | 10 / 0 |

Complete OLD-only lists suffice for $p2,pmm,cmm,p4m,p6,p6m$ with time
reversal, and for $p2,pmm,pgg,cmm,p4,p4m,p4g,p6,p6m$ without it.
For the remaining settings, the recipes explicitly identify every entry using
an EXTENDED or NEW expression. No NEW indicator is retained where the OLD
replacements with valid argument orders suffice.

### Degree-one coordinates with time reversal

Every expression in this table equals the corresponding $\mathsf W_i$
coordinate in the ordered $H^1$ basis. Every target is **+1**. Products of
$\mathcal W_o(g)$ use ordinary multiplication of their signs.

| IT | Group | Coordinate | Evaluation | Status |
|---:|---|---|---|---|
| 1 | p1 | $\mathsf W_{1}$ ($\alpha=x$) | $\mathcal N_1(TU;\widehat{X},V)$ | NEW |
| 1 | p1 | $\mathsf W_{2}$ ($\alpha=y$) | $\mathcal N_1(TU;\widehat{Y},V)$ | NEW |
| 2 | p2 | $\mathsf W_{1}$ ($\alpha=x$) | $\mathcal W_o(C_2)\,\mathcal W_o(XC_2)$ | OLD |
| 2 | p2 | $\mathsf W_{2}$ ($\alpha=y$) | $\mathcal W_o(C_2)\,\mathcal W_o(YC_2)$ | OLD |
| 2 | p2 | $\mathsf W_{3}$ ($\alpha=c$) | $\mathcal W_o(C_2)$ | OLD |
| 3 | pm | $\mathsf W_{1}$ ($\alpha=x$) | $\mathcal W_o(M)\,\mathcal W_o(XM)$ | OLD |
| 3 | pm | $\mathsf W_{2}$ ($\alpha=y$) | $\mathcal N_1(TU;\widehat{Y},V)$ | NEW |
| 3 | pm | $\mathsf W_{3}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 4 | pg | $\mathsf W_{1}$ ($\alpha=x$) | $\mathcal N_1(TU;\widehat{X},V)$ | NEW |
| 4 | pg | $\mathsf W_{2}$ ($\alpha=s$) | $\mathcal N_1(TU;\widehat{L},V)$ | NEW |
| 5 | cm | $\mathsf W_{1}$ ($\alpha=a$) | $\mathcal N_1(TU;\widehat{X},V)$ | NEW |
| 5 | cm | $\mathsf W_{2}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 6 | pmm | $\mathsf W_{1}$ ($\alpha=x$) | $\mathcal W_o(C_2)\,\mathcal W_o(XC_2)$ | OLD |
| 6 | pmm | $\mathsf W_{2}$ ($\alpha=y$) | $\mathcal W_o(XYC_2)\,\mathcal W_o(XC_2)$ | OLD |
| 6 | pmm | $\mathsf W_{3}$ ($\alpha=c$) | $\mathcal W_o(C_2)$ | OLD |
| 6 | pmm | $\mathsf W_{4}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 7 | pmg | $\mathsf W_{1}$ ($\alpha=y$) | $\mathcal W_o(C_2)\,\mathcal W_o(XYC_2)$ | OLD |
| 7 | pmg | $\mathsf W_{2}$ ($\alpha=c$) | $\mathcal W_o(C_2)$ | OLD |
| 7 | pmg | $\mathsf W_{3}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 8 | pgg | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal W_o(C_2)$ | OLD |
| 8 | pgg | $\mathsf W_{2}$ ($\alpha=s$) | $\mathcal N_1(TU;\widehat{L},V)$ | NEW |
| 9 | cmm | $\mathsf W_{1}$ ($\alpha=a$) | $\mathcal W_o(C_2)\,\mathcal W_o(XC_2)$ | OLD |
| 9 | cmm | $\mathsf W_{2}$ ($\alpha=c$) | $\mathcal W_o(C_2)$ | OLD |
| 9 | cmm | $\mathsf W_{3}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 10 | p4 | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal N_1(TU;\widehat{C_4},V)$ | NEW |
| 10 | p4 | $\mathsf W_{2}$ ($\alpha=a$) | $\mathcal W_o(XR)$ | OLD |
| 11 | p4m | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal W_o(M)\,\mathcal W_o(C_4M)$ | OLD |
| 11 | p4m | $\mathsf W_{2}$ ($\alpha=a$) | $\mathcal W_o(XR)$ | OLD |
| 11 | p4m | $\mathsf W_{3}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 12 | p4g | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal N_1(TU;\widehat{C_4},V)$ | NEW |
| 12 | p4g | $\mathsf W_{2}$ ($\alpha=s$) | $\mathcal W_o(X^{-1}L)$ | OLD |
| 13 | p3 | none | — | — |
| 14 | p3m1 | $\mathsf W_{1}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 15 | p31m | $\mathsf W_{1}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |
| 16 | p6 | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal W_o(R)$ | OLD |
| 17 | p6m | $\mathsf W_{1}$ ($\alpha=c$) | $\mathcal W_o(R)$ | OLD |
| 17 | p6m | $\mathsf W_{2}$ ($\alpha=m$) | $\mathcal W_o(M)$ | OLD |

These OLD products are obtained by solving
$\sum_g n_g\alpha_i(g)=\delta_{i\ell}$ over $\mathbb F_2$ to recover
$\mathsf W_\ell$. The remaining single-loop representatives are chosen
so that $\alpha_i(g)=\delta_{i\ell}$ and use
$\mathcal N_1(TU;\widehat g,V)$.

### Degree-two coordinates with and without time reversal

The surface column fixes the dual of each $\beta_j$: its pairing with
$\beta_i$ is $\delta_{ij}$. $\mathrm{RP}(g)$ denotes
$\mathbb{RP}^2_g$; $\mathrm{Tor}(g,h)$ denotes a torus with the listed
commuting holonomies; $\mathrm{Kl}(X,L)$ denotes the Klein bottle with
$LXL^{-1}=X^{-1}$. The group presentations are those of [YGHWZ21],
Appendix E.

For $p3m1$, the mirror-period surface
$\mathrm{Tor}(XY^{-1},M)$ replaces $\mathrm{Tor}(X,Y)$ for $\beta_1=B$.
It is the same mod-2 degree-two dual: the commutator in Eq. (E77) evaluates
to one, and $m^2$ evaluates to zero. This choice permits the EXTENDED
formula (18).

Every $\mathsf S_j$ and $\mathsf K_j$ below has target
$(-1)^{\ell_j}$ for $j\leq k$, and +1 for $j>k$. The no-$T$ column
has the same $\mathsf S_j$ target. Status codes are **O = OLD**,
**E = EXTENDED**, **N = NEW**.

| IT | Group | $j$ | Dual surface | $\mathsf S_j$ with $T$ | $\mathsf K_j$ with $T$ | $\mathsf S_j$ without $T$ |
|---:|---|---:|---|---|---|---|
| 1 | p1 | 1 | $\mathrm{Tor}(X,Y)$ | $\mathcal N_3(X,\,Y)$ **N** | $\mathcal N_1(T;X,Y)$ **N** | $\mathcal N_3(X,\,Y)$ **N** |
| 2 | p2 | 1 | $\mathrm{RP}(C_2)$ | $\mathcal S_o(C_2)$ **O** | $\mathcal K_o(C_2)$ **O** | $\mathcal S_-(C_2)$ **O** |
| 2 | p2 | 2 | $\mathrm{RP}(XC_2)$ | $\mathcal S_o(XC_2)$ **O** | $\mathcal K_o(XC_2)$ **O** | $\mathcal S_-(XC_2)$ **O** |
| 2 | p2 | 3 | $\mathrm{RP}(YC_2)$ | $\mathcal S_o(YC_2)$ **O** | $\mathcal K_o(YC_2)$ **O** | $\mathcal S_-(YC_2)$ **O** |
| 2 | p2 | 4 | $\mathrm{RP}(XYC_2)$ | $\mathcal S_o(XYC_2)$ **O** | $\mathcal K_o(XYC_2)$ **O** | $\mathcal S_-(XYC_2)$ **O** |
| 3 | pm | 1 | $\mathrm{Tor}(Y,M)$ | $\mathcal S_e(M,\,Y)$ **E** | $\mathcal N_1(T;Y,\widehat{M})$ **N** | $\mathcal N_1(MU;Y,V)$ **N** |
| 3 | pm | 2 | $\mathrm{Tor}(Y,XM)$ | $\mathcal S_e(XM,\,Y)$ **E** | $\mathcal N_1(T;Y,\widehat{XM})$ **N** | $\mathcal N_1(XMU;Y,V)$ **N** |
| 3 | pm | 3 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 3 | pm | 4 | $\mathrm{RP}(XM)$ | $\mathcal S_o(XM)$ **O** | $\mathcal K_o(XM)$ **O** | $\mathcal S_-(XM)$ **O** |
| 4 | pg | 1 | $\mathrm{Kl}(X,L)$ | $\mathcal N_4(X,\,L)$ **N** | $\mathcal N_2(T;X,L)$ **N** | $\mathcal N_4(X,\,L)$ **N** |
| 5 | cm | 1 | $\mathrm{Tor}(XY,M)$ | $\mathcal S_e(M,\,XY)$ **E** | $\mathcal N_1(T;XY,\widehat{M})$ **N** | $\mathcal N_1(MU;XY,V)$ **N** |
| 5 | cm | 2 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 6 | pmm | 1 | $\mathrm{RP}(C_2)$ | $\mathcal S_o(C_2)$ **O** | $\mathcal K_o(C_2)$ **O** | $\mathcal S_-(C_2)$ **O** |
| 6 | pmm | 2 | $\mathrm{RP}(XYC_2)$ | $\mathcal S_o(XYC_2)$ **O** | $\mathcal K_o(XYC_2)$ **O** | $\mathcal S_-(XYC_2)$ **O** |
| 6 | pmm | 3 | $\mathrm{RP}(XC_2)$ | $\mathcal S_o(XC_2)$ **O** | $\mathcal K_o(XC_2)$ **O** | $\mathcal S_-(XC_2)$ **O** |
| 6 | pmm | 4 | $\mathrm{RP}(YC_2)$ | $\mathcal S_o(YC_2)$ **O** | $\mathcal K_o(YC_2)$ **O** | $\mathcal S_-(YC_2)$ **O** |
| 6 | pmm | 5 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 6 | pmm | 6 | $\mathrm{RP}(C_2M)$ | $\mathcal S_o(C_2M)$ **O** | $\mathcal K_o(C_2M)$ **O** | $\mathcal S_-(C_2M)$ **O** |
| 6 | pmm | 7 | $\mathrm{RP}(XM)$ | $\mathcal S_o(XM)$ **O** | $\mathcal K_o(XM)$ **O** | $\mathcal S_-(XM)$ **O** |
| 6 | pmm | 8 | $\mathrm{RP}(YC_2M)$ | $\mathcal S_o(YC_2M)$ **O** | $\mathcal K_o(YC_2M)$ **O** | $\mathcal S_-(YC_2M)$ **O** |
| 7 | pmg | 1 | $\mathrm{RP}(C_2)$ | $\mathcal S_o(C_2)$ **O** | $\mathcal K_o(C_2)$ **O** | $\mathcal S_-(C_2)$ **O** |
| 7 | pmg | 2 | $\mathrm{RP}(XYC_2)$ | $\mathcal S_o(XYC_2)$ **O** | $\mathcal K_o(XYC_2)$ **O** | $\mathcal S_-(XYC_2)$ **O** |
| 7 | pmg | 3 | $\mathrm{Tor}(Y,M)$ | $\mathcal S_e(M,\,Y)$ **E** | $\mathcal N_1(T;Y,\widehat{M})$ **N** | $\mathcal N_1(MU;Y,V)$ **N** |
| 7 | pmg | 4 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 8 | pgg | 1 | $\mathrm{RP}(C_2)$ | $\mathcal S_o(C_2)$ **O** | $\mathcal K_o(C_2)$ **O** | $\mathcal S_-(C_2)$ **O** |
| 8 | pgg | 2 | $\mathrm{RP}(XC_2)$ | $\mathcal S_o(XC_2)$ **O** | $\mathcal K_o(XC_2)$ **O** | $\mathcal S_-(XC_2)$ **O** |
| 9 | cmm | 1 | $\mathrm{RP}(C_2)$ | $\mathcal S_o(C_2)$ **O** | $\mathcal K_o(C_2)$ **O** | $\mathcal S_-(C_2)$ **O** |
| 9 | cmm | 2 | $\mathrm{RP}(XYC_2)$ | $\mathcal S_o(XYC_2)$ **O** | $\mathcal K_o(XYC_2)$ **O** | $\mathcal S_-(XYC_2)$ **O** |
| 9 | cmm | 3 | $\mathrm{RP}(XC_2)$ | $\mathcal S_o(XC_2)$ **O** | $\mathcal K_o(XC_2)$ **O** | $\mathcal S_-(XC_2)$ **O** |
| 9 | cmm | 4 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 9 | cmm | 5 | $\mathrm{RP}(C_2M)$ | $\mathcal S_o(C_2M)$ **O** | $\mathcal K_o(C_2M)$ **O** | $\mathcal S_-(C_2M)$ **O** |
| 10 | p4 | 1 | $\mathrm{RP}(R)$ | $\mathcal S_o(R)$ **O** | $\mathcal K_o(R)$ **O** | $\mathcal S_-(R)$ **O** |
| 10 | p4 | 2 | $\mathrm{RP}(XYR)$ | $\mathcal S_o(XYR)$ **O** | $\mathcal K_o(XYR)$ **O** | $\mathcal S_-(XYR)$ **O** |
| 10 | p4 | 3 | $\mathrm{RP}(XR)$ | $\mathcal S_o(XR)$ **O** | $\mathcal K_o(XR)$ **O** | $\mathcal S_-(XR)$ **O** |
| 11 | p4m | 1 | $\mathrm{RP}(R)$ | $\mathcal S_o(R)$ **O** | $\mathcal K_o(R)$ **O** | $\mathcal S_-(R)$ **O** |
| 11 | p4m | 2 | $\mathrm{RP}(XYR)$ | $\mathcal S_o(XYR)$ **O** | $\mathcal K_o(XYR)$ **O** | $\mathcal S_-(XYR)$ **O** |
| 11 | p4m | 3 | $\mathrm{RP}(XR)$ | $\mathcal S_o(XR)$ **O** | $\mathcal K_o(XR)$ **O** | $\mathcal S_-(XR)$ **O** |
| 11 | p4m | 4 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 11 | p4m | 5 | $\mathrm{RP}(XM)$ | $\mathcal S_o(XM)$ **O** | $\mathcal K_o(XM)$ **O** | $\mathcal S_-(XM)$ **O** |
| 11 | p4m | 6 | $\mathrm{RP}(C_4M)$ | $\mathcal S_o(C_4M)$ **O** | $\mathcal K_o(C_4M)$ **O** | $\mathcal S_-(C_4M)$ **O** |
| 12 | p4g | 1 | $\mathrm{RP}(R)$ | $\mathcal S_o(R)$ **O** | $\mathcal K_o(R)$ **O** | $\mathcal S_-(R)$ **O** |
| 12 | p4g | 2 | $\mathrm{RP}(XR)$ | $\mathcal S_o(XR)$ **O** | $\mathcal K_o(XR)$ **O** | $\mathcal S_-(XR)$ **O** |
| 12 | p4g | 3 | $\mathrm{RP}(X^{-1}L)$ | $\mathcal S_o(X^{-1}L)$ **O** | $\mathcal K_o(X^{-1}L)$ **O** | $\mathcal S_-(X^{-1}L)$ **O** |
| 13 | p3 | 1 | $\mathrm{Tor}(X,Y)$ | $\mathcal N_3(X,\,Y)$ **N** | $\mathcal N_1(T;X,Y)$ **N** | $\mathcal N_3(X,\,Y)$ **N** |
| 14 | p3m1 | 1 | $\mathrm{Tor}(XY^{-1},M)$ | $\mathcal S_e(M,\,XY^{-1})$ **E** | $\mathcal N_1(T;XY^{-1},\widehat{M})$ **N** | $\mathcal N_1(MU;XY^{-1},V)$ **N** |
| 14 | p3m1 | 2 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 15 | p31m | 1 | $\mathrm{Tor}(XY,M)$ | $\mathcal S_e(M,\,XY)$ **E** | $\mathcal N_1(T;XY,\widehat{M})$ **N** | $\mathcal N_1(MU;XY,V)$ **N** |
| 15 | p31m | 2 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 16 | p6 | 1 | $\mathrm{RP}(R)$ | $\mathcal S_o(R)$ **O** | $\mathcal K_o(R)$ **O** | $\mathcal S_-(R)$ **O** |
| 16 | p6 | 2 | $\mathrm{RP}(XR)$ | $\mathcal S_o(XR)$ **O** | $\mathcal K_o(XR)$ **O** | $\mathcal S_-(XR)$ **O** |
| 17 | p6m | 1 | $\mathrm{RP}(R)$ | $\mathcal S_o(R)$ **O** | $\mathcal K_o(R)$ **O** | $\mathcal S_-(R)$ **O** |
| 17 | p6m | 2 | $\mathrm{RP}(XR)$ | $\mathcal S_o(XR)$ **O** | $\mathcal K_o(XR)$ **O** | $\mathcal S_-(XR)$ **O** |
| 17 | p6m | 3 | $\mathrm{RP}(M)$ | $\mathcal S_o(M)$ **O** | $\mathcal K_o(M)$ **O** | $\mathcal S_-(M)$ **O** |
| 17 | p6m | 4 | $\mathrm{RP}(RM)$ | $\mathcal S_o(RM)$ **O** | $\mathcal K_o(RM)$ **O** | $\mathcal S_-(RM)$ **O** |

The NEW product evaluations in this table are already normalized coordinate
indicators; no hidden division by an uncomputed quantity is required. For
$\mathcal N_1(T;g,h)$ the spatial map factors through the torus, which
isolates $\beta_j u_1^2$. For $\mathcal N_3$ and $\mathcal N_4$, spin
flux on $S^2$ isolates $\beta_jv_2$. In the no-$T$ mirror-period row,
$\mathcal N_1(mU;h,V)$ has spin class $v_2=a^2+az$; the spatial torus
class contributes $ay$, yielding $\int a^2yz=1$. Other independent
characteristic numbers vanish in each of these evaluations.

The four NEW templates and the OLD/EXTENDED replacements therefore evaluate
all the ordered coordinates in these two tables. The only change of spatial
basis is the explicitly listed $\mathsf E_r$ or
$\widehat{\mathsf R}_r$ basis. In particular, assemble the final lists as

$$
\begin{aligned}
\Gamma_+:&\quad
(\mathsf G,\mathsf A,\mathsf B,\mathsf C,
 \{\mathsf W_i\},\{\mathsf S_j\},\{\mathsf K_j\},\{\mathsf E_r\}),\\
\Gamma_-:\ \epsilon=0:&\quad (\{\mathsf S_j\}),\\
\Gamma_-:\ \epsilon\ne0:&\quad
(\mathsf G,\mathsf B,\{\mathsf S_j\},\{\widehat{\mathsf R}_r\}).
\end{aligned}                                                   \tag{19}
$$

## Explicit spatial evaluation lists for all 17 groups

Every spatial entry is OLD or EXTENDED. For the case with independent time
reversal, use these abbreviations:

$$
\begin{aligned}
F(g)&=\mathcal I_1(T\widehat g),\\
H(g,h)&=\mathcal I_2(T\widehat g,T\widehat h),\\
J(g,h)&=\begin{cases}
\mathcal I_3(\widehat g,\widehat h),&h^2=1\quad\text{(OLD)},\\
\mathcal J(\widehat g,\widehat h),&h^2\ne1\quad\text{(EXTENDED)}.
\end{cases}
\end{aligned}                                                   \tag{20}
$$

$F$ and $H$ here are scalar indicator functions, unrelated to the UMTC
$F$ symbols. Their spatial arguments are involutions, and arguments of $H$
or $J$ commute. The first argument of $J$ is always an involution.
$R=C_4^2$ in square groups and $R=C_6^3$ in hexagonal groups; other
half turns are written $C_2$.

Append every $\mathsf E_r$ in the applicable table to the internal and mixed
lists above. They replace $\mathsf P_r$, and may mix those pure spatial
coordinates with OLD internal and mixed coordinates. The full pairing matrix
is invertible; their targets below already account for that change of basis.
All entries are OLD except the explicitly marked EXTENDED translation rows.

### Spatial list with time reversal: IT 1, p1

No spatial indicators are required.

### Spatial list with time reversal: IT 2, p2

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(C_2)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{2}$ | $F(XC_2)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{3}$ | $F(YC_2)$ | $(-1)^{\ell_3}$ | OLD |
| $\mathsf E_{4}$ | $F(XYC_2)$ | $(-1)^{\ell_4}$ | OLD |

### Spatial list with time reversal: IT 3, pm

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(XM)$ | $+1$ | OLD |
| $\mathsf E_{3}$ | $J(M,\,Y)$ | $(-1)^{\ell_1}$ | EXTENDED |
| $\mathsf E_{4}$ | $J(XM,\,Y)$ | $(-1)^{\ell_2}$ | EXTENDED |

### Spatial list with time reversal: IT 4, pg

No spatial indicators are required.

### Spatial list with time reversal: IT 5, cm

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $J(M,\,XY)$ | $(-1)^{\ell_1}$ | EXTENDED |

### Spatial list with time reversal: IT 6, pmm

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(C_2M)$ | $+1$ | OLD |
| $\mathsf E_{3}$ | $F(XM)$ | $+1$ | OLD |
| $\mathsf E_{4}$ | $F(YC_2M)$ | $+1$ | OLD |
| $\mathsf E_{5}$ | $F(C_2)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{6}$ | $F(XYC_2)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{7}$ | $F(XC_2)$ | $(-1)^{\ell_3}$ | OLD |
| $\mathsf E_{8}$ | $F(YC_2)$ | $(-1)^{\ell_4}$ | OLD |
| $\mathsf E_{9}$ | $H(M,\,C_2M)$ | $+1$ | OLD |
| $\mathsf E_{10}$ | $H(XM,\,YC_2M)$ | $+1$ | OLD |
| $\mathsf E_{11}$ | $H(XM,\,C_2M)$ | $+1$ | OLD |
| $\mathsf E_{12}$ | $H(M,\,YC_2M)$ | $+1$ | OLD |
| $\mathsf E_{13}$ | $J(M,\,C_2M)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{14}$ | $J(XM,\,YC_2M)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{15}$ | $J(XM,\,C_2M)$ | $(-1)^{\ell_3}$ | OLD |
| $\mathsf E_{16}$ | $J(M,\,YC_2M)$ | $(-1)^{\ell_4}$ | OLD |

### Spatial list with time reversal: IT 7, pmg

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(C_2)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{3}$ | $F(XYC_2)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{4}$ | $J(M,\,Y)$ | $(-1)^{\ell_3}$ | EXTENDED |

### Spatial list with time reversal: IT 8, pgg

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(C_2)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{2}$ | $F(XC_2)$ | $(-1)^{\ell_2}$ | OLD |

### Spatial list with time reversal: IT 9, cmm

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(C_2M)$ | $+1$ | OLD |
| $\mathsf E_{3}$ | $F(C_2)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{4}$ | $F(XYC_2)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{5}$ | $F(XC_2)$ | $(-1)^{\ell_3}$ | OLD |
| $\mathsf E_{6}$ | $H(M,\,C_2M)$ | $+1$ | OLD |
| $\mathsf E_{7}$ | $H(M,\,XYC_2M)$ | $+1$ | OLD |
| $\mathsf E_{8}$ | $J(M,\,C_2M)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{9}$ | $J(M,\,XYC_2M)$ | $(-1)^{\ell_2}$ | OLD |

### Spatial list with time reversal: IT 10, p4

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(R)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{2}$ | $F(XYR)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{3}$ | $F(XR)$ | $(-1)^{\ell_3}$ | OLD |

### Spatial list with time reversal: IT 11, p4m

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(XM)$ | $+1$ | OLD |
| $\mathsf E_{3}$ | $F(C_4M)$ | $+1$ | OLD |
| $\mathsf E_{4}$ | $F(R)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{5}$ | $F(XYR)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{6}$ | $F(XR)$ | $(-1)^{\ell_3}$ | OLD |
| $\mathsf E_{7}$ | $J(M,\,RM)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{8}$ | $J(C_4M,\,C_4^{3}M)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{9}$ | $J(XM,\,YRM)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{10}$ | $J(XYC_4M,\,C_4^{3}M)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{11}$ | $H(XM,\,RM)$ | $+1$ | OLD |
| $\mathsf E_{12}$ | $J(XM,\,RM)$ | $(-1)^{\ell_3}$ | OLD |

### Spatial list with time reversal: IT 12, p4g

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(X^{-1}L)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(R)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{3}$ | $F(XR)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{4}$ | $H(X^{-1}L,\,RL)$ | $+1$ | OLD |
| $\mathsf E_{5}$ | $J(X^{-1}L,\,RL)$ | $(-1)^{\ell_2}$ | OLD |

### Spatial list with time reversal: IT 13, p3

No spatial indicators are required.

### Spatial list with time reversal: IT 14, p3m1

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $J(M,\,XY^{-1})$ | $(-1)^{\ell_1}$ | EXTENDED |

### Spatial list with time reversal: IT 15, p31m

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $J(M,\,XY)$ | $(-1)^{\ell_1}$ | EXTENDED |

### Spatial list with time reversal: IT 16, p6

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(R)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{2}$ | $F(XR)$ | $(-1)^{\ell_2}$ | OLD |

### Spatial list with time reversal: IT 17, p6m

| Indicator | Evaluation | Lattice target | Status |
|---|---|---|---|
| $\mathsf E_{1}$ | $F(M)$ | $+1$ | OLD |
| $\mathsf E_{2}$ | $F(RM)$ | $+1$ | OLD |
| $\mathsf E_{3}$ | $F(R)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{4}$ | $F(XYR)$ | $(-1)^{\ell_2}$ | OLD |
| $\mathsf E_{5}$ | $H(M,\,RM)$ | $+1$ | OLD |
| $\mathsf E_{6}$ | $H(M,\,XYRM)$ | $+1$ | OLD |
| $\mathsf E_{7}$ | $J(M,\,RM)$ | $(-1)^{\ell_1}$ | OLD |
| $\mathsf E_{8}$ | $J(M,\,XYRM)$ | $(-1)^{\ell_2}$ | OLD |


### Why the spatial lists are complete

On the three manifolds in (20), the pure spatial pairing is the coefficient
of $x^4$, $x^2y^2$, and $x^3y$, respectively. Here $x,y$ denote the
cohomology generators of the displayed factors. For commuting involutions
$g,h$, a degree-two class $\beta$ pulls back as

$$
\beta\longmapsto b_gx^2+(b_{gh}+b_g+b_h)xy+b_hy^2,
\qquad b_g=\beta|_{\langle g\rangle}/x^2.
$$

The $b_g$ values are the involution-square invariants encoded by the surface
table above. For the mirror/translation pairs in $J$, the $xy$ coefficient
is the corresponding mirror-period invariant. Multiplication and the ring
relations then determine the degree-four pairing matrix. Its rank is $b_4$
for each of the 17 lists. Together with the internal and mixed recipes, the
full matrix is block triangular with invertible diagonal blocks.

For $p3m1$, the additional mirror-period pairing is
$\langle B,\mathrm{Tor}(M,XY^{-1})\rangle=1$: the commutator of the
cochain in [YGHWZ21], Eq. (E77), gives one on this pair. It detects the same
degree-two generator as $\mathrm{Tor}(X,Y)$; the degree-two recipe table
uses this mirror-period representative to enable (18).

For $p4g$, the commuting mirrors $X^{-1}L$ and $RL$ have product
$X^{-1}R$, conjugate to $XR$. On this mirror subgroup, $Q=xy$ and
$s=x+y$. The degree-three generator restricts to either $x^2y$ or $xy^2$
depending on its choice modulo lower generators; both obey
$\operatorname{Sq}^1C=Q^2$, and the allowed replacement $C\mapsto C+sQ$
exchanges the two restrictions. The five displayed evaluations have rank five
for either choice. In particular they detect the $sC$ direction as well as
the directions generated in degrees one and two.

The target signs follow by evaluating $\lambda t^2$, since the spin bundle
is trivial. On $F(g)$, $t=(1+\epsilon(g))x$; on $H(g,h)$,
$t=(1+\epsilon(g))x+(1+\epsilon(h))y$; on $J(g,h)$,
$t=\epsilon(g)x+\epsilon(h)y$. These rules give every target in the tables,
including the translation-sensitive $J$ entries.

### OLD spatial lists without time reversal

Append these evaluations in the displayed order as
$\widehat{\mathsf R}_r$. Every entry is **OLD**, and every lattice target
is **+1**. They replace the coordinate $\mathsf R_r$ list. All
$\mathcal I_1$ arguments are mirrors; all $\mathcal I_2$ arguments are
commuting mirrors.

| IT | Group | Ordered OLD spatial evaluations |
|---:|---|---|
| 1 | p1 | $\varnothing$ |
| 2 | p2 | $\varnothing$ |
| 3 | pm | $\mathcal I_1(M),\;\mathcal I_1(XM)$ |
| 4 | pg | $\varnothing$ |
| 5 | cm | $\mathcal I_1(M)$ |
| 6 | pmm | $\mathcal I_1(M),\;\mathcal I_1(C_2M)$<br>$\mathcal I_1(XM),\;\mathcal I_1(YC_2M)$<br>$\mathcal I_2(M,\,C_2M),\;\mathcal I_2(XM,\,YC_2M)$<br>$\mathcal I_2(XM,\,C_2M),\;\mathcal I_2(M,\,YC_2M)$ |
| 7 | pmg | $\mathcal I_1(M)$ |
| 8 | pgg | $\varnothing$ |
| 9 | cmm | $\mathcal I_1(M),\;\mathcal I_1(C_2M)$<br>$\mathcal I_2(M,\,C_2M),\;\mathcal I_2(M,\,XYC_2M)$ |
| 10 | p4 | $\varnothing$ |
| 11 | p4m | $\mathcal I_1(M),\;\mathcal I_1(XM)$<br>$\mathcal I_1(C_4M),\;\mathcal I_2(M,\,RM)$<br>$\mathcal I_2(XM,\,YRM),\;\mathcal I_2(XM,\,RM)$ |
| 12 | p4g | $\mathcal I_1(X^{-1}L),\;\mathcal I_2(X^{-1}L,\,RL)$ |
| 13 | p3 | $\varnothing$ |
| 14 | p3m1 | $\mathcal I_1(M)$ |
| 15 | p31m | $\mathcal I_1(M)$ |
| 16 | p6 | $\varnothing$ |
| 17 | p6m | $\mathcal I_1(M),\;\mathcal I_1(RM)$<br>$\mathcal I_2(M,\,RM),\;\mathcal I_2(M,\,XYRM)$ |

These evaluations have rank $d$ on the $\delta$ basis for every group.
$\mathcal I_2$ can additionally measure $u_2^2$, which is independently
fixed by the OLD $\mathsf G$ indicator. Their spin bundles are trivial,
so the no-$T$ LSM response $\lambda v_2$ gives target +1 throughout.

## What remains for a direct evaluator

The OLD entries have explicit tensor formulas already. EXTENDED entries reuse
one existing contraction with a larger domain; they require checking that
extension, including its gauge and framing conventions. The final section
now gives explicit spin-flux reductions for all NEW spin-dependent entries.
The eight spin-free $\mathcal N_1$ entries and the one $\mathcal N_2$
entry use the general contractions in the companion note and their v0.2.0 evaluator.

The finite-subgroup strategy cannot supply a universal replacement for NEW
entries: for $p1$, the response $(-1)^{\int xyv_2}$ vanishes on every
finite spatial subgroup but is detected by $\mathcal N_3(X,Y)$. Products
and ratios of OLD evaluations cannot recover an anomaly on which all of them
are trivial. The spin-flux formulas below keep translations and glides as
elements of their actual groups. The four geometric templates are a
sufficient shared set, without a claim of global minimality.

The v0.2.0 classifier accepts conventional WP letters and reduces them using
[standard plane-group WP tables and settings](wallpaper-groups.md).
The fractionalization calculation still uses $H^2_\rho(\Gamma,\mathcal A)$
with the actual Abelian-anyon module $\mathcal A$; mod-2 anomaly targets do
not justify discarding odd-torsion fractionalization classes.

## Algebra checks, provenance, and source inconsistencies

The group-by-group response bases and counts, including the no-$T$ lists,
are **derived in this document**, not quoted as tables from [YZ23]. The source
inputs are the cohomology rings and lattice generators of [YGHWZ21]. The
verification uses weighted monomials modulo all defining relations over
$\mathbb F_2$, with exact row reduction. It checks that:

- every displayed $\beta$ tuple is a basis of $H^2$, and every
  $\gamma$ tuple is a basis of $H^4$;
- multiplication by $\epsilon^2$ gives exactly the target signs listed;
- the images $D_\epsilon\delta_r$ are independent and span the image of
  $D_\epsilon:H^4\to H^5$;
- the Steenrod derivation preserves all ring relations and squares to zero;
- $D_\epsilon\beta_j=0$ for every LSM generator $j\leq k$, as expected
  for the mod-2 reduction of an orientation-twisted integral lattice class;
- every spatial word in the concrete lists has the required order and
  commutation relations, using exact affine transformations of the plane;
- the concrete spatial evaluation matrices have ranks $b_4$ with $T$
  and $d$ without $T$ for all 17 groups;
- every target sign in the concrete spatial lists follows from (10),
  including the mirror/translation pairs.

For reproducibility, the Steenrod operation used is specified on generators:
$\operatorname{Sq}^1A=A^2$ for every degree-one generator,
$\operatorname{Sq}^1B=\epsilon B$,
$\operatorname{Sq}^1D=\epsilon D$, and
$\operatorname{Sq}^1Q=\epsilon Q$, extended by the Cartan rule. In
$p4g$, $\operatorname{Sq}^1C=Q^2=DQ$. The last value is independently
fixed by requiring the derivation to preserve the ring relations in (E64)
and square to zero: solving for all five possible degree-four coefficients
leaves exactly this value. The relations reduce $\epsilon Q$ to zero
in $pgg$ and to $sD$ in $p4g$.

The purely spatial ranks $d$, in IT order, are

$$
(0,0,2,0,1,8,1,0,4,0,6,2,0,1,1,0,4).                         \tag{21}
$$

For a separate check, these ranks follow from the high-degree stabilizer
calculation described after (7). The familiar counts from [YZ23] are
$N_-(p6)=2$, $N_-(p4)=3$, $N_+(p6m)=22$, and
$N_+(p4m)=31$. These checks verify the response bases, spatial evaluation
ranks, and target signs. The added spin-flux formulas have the separate
consistency checks described at the end. Version 0.2.0 adds a general
$\mathcal N_1$/$\mathcal N_2$ evaluator using the companion state sum.
For the four published cases, all 58 expressions were checked against the
existing specification lists; all involution and commutation requirements
were checked, and 368 target signs across the 24 lattice cases were checked
against (10), (13), and the current implementation.

For the OLD-first rewrite, the involution products recovering every OLD
$\mathsf W_i$ were solved by exact binary linear algebra; their character
pairings equal the required coordinate vectors. The OLD ratios (15)–(16),
the EXTENDED spin ratio (18), and the NEW template assignments were checked
against their characteristic-number evaluations. Replacing a geometric test
by these formulas therefore preserves the response matrix and target signs.
Every coverage-table row sums to $N_+$ or $N_-$. These are algebraic and
geometric checks; numerical implementation checks are recorded in [validation](validation.md).

Source inconsistencies relevant to this catalogue:

- In [YZ23], Eq. (216) prints $\mathcal I_1$ with two arguments for
  $\mathsf I_{12}$ and $\mathsf I_{13}$. The table here uses
  $\mathcal I_2$, the two-argument antiunitary indicator of Eq. (211).
- In [YGHWZ21], the sentence after (E37) calls only $\lambda_1,\lambda_2$
  LSM generators for $pmg$. Equation (F7) and its explanation require
  $\lambda_3=ym$ as well: it detects the spin parity on a mirror period.
  The catalogue uses $k=3$.
- In [YGHWZ21], the sentences associated with (E76) and (E82) print
  $H^1=0$, despite explicitly giving the nonzero mirror class $A_m$.
  The rings (E75), (E81) give $H^1=\mathbb Z_2$, used here.

## References

- **[YZ23]** Weicheng Ye and Liujun Zou, *Classification of symmetry-enriched
  topological quantum spin liquids*, Physical Review X **14**, 021053 (2024).
  [arXiv:2309.15118v3](https://arxiv.org/html/2309.15118v3), especially
  Tables I, II, XVIII, XIX and Appendix D.
- **[YGHWZ21]** Weicheng Ye, Meng Guo, Yin-Chen He, Chong Wang, and Liujun Zou,
  *Topological characterization of Lieb-Schultz-Mattis constraints and
  applications to symmetry-enriched quantum criticality*, SciPost Physics
  **13**, 066 (2022). [arXiv:2111.12097](https://arxiv.org/pdf/2111.12097),
  especially Appendices A, E, and F.
- **[YZ22]** Weicheng Ye and Liujun Zou, *Anomaly of (2+1)-Dimensional
  Symmetry-Enriched Topological Order from (3+1)-Dimensional Topological Quantum
  Field Theory*, SciPost Physics **15**, 004 (2023).
  [arXiv:2210.02444](https://arxiv.org/pdf/2210.02444), especially Secs. III–VI
  and Appendix D.
- **[Thom]** The unoriented-bordism decomposition is given, for example, in
  [Ralph L. Cohen, *Bundles, Manifolds, and Homotopy*, Proposition 11.25](https://math.stanford.edu/~ralph/bookR4.pdf).

## NEW anomaly indicators: formulas and remaining calculations

The four geometric templates are retained below, with explicit formulas where
the calculation can be reduced. The new formulas in this section are
**derived here using [YZ22]**, rather than quoted from that paper. In
particular, its $\mathbb Z_2\times\mathbb Z_2^T$ calculation, written there
using two antiunitary generators, gives the OLD reduction (22a).
Spin-flux reduction gives (22b), (24a), and (25a), which cover all the
spin-dependent NEW entries, including infinite-order holonomies.

The general spin-free evaluations (22) and (23) use the explicit
$F,R,U,\eta$ contraction in
[Section 2A of the companion note](rp2-product-partition-functions.md#2a-explicit-contraction-in-frueta),
Eqs. (S1)–(S8). It specifies the six associators, crossing, symmetry
matrices, fractionalization phase, fusion indices, and product
triangulations. It retains translations and glides as full group elements.

The EXTENDED $\mathcal J$ evaluation in (17) is a separate domain-extension
check of the OLD contraction, not a fifth new contraction. It supplies the
spatial mirror-period evaluations and $\mathcal S_e$ in the five groups
$pm,cm,pmg,p3m1,p31m$ when time reversal is present.

### Shared data: the SO(3) spin-flux anyon

Write $H=P\times\mathbb Z_2^T$ with time reversal, and $H=P$ without it,
with the crystalline antiunitary grading $q$. All elements of $H$ in the
formulas below have trivial SO(3) component. Let $s_a\in\{0,\tfrac12\}$
be the SO(3) spin of anyon $a$ modulo an integer. Define the Abelian anyon
$\mathfrak v$ by

$$
M_{a,\mathfrak v}=e^{2\pi i s_a}\quad\text{for every simple anyon }a.
$$

Here $M$ is monodromy. Fusion compatibility of the spin signs and modularity
give a unique such anyon. It obeys
$\mathfrak v\times\mathfrak v=1$ and
$\rho_g(\mathfrak v)=\mathfrak v$ for every $g\in H$: the spin signs
are real and preserved by the direct-product symmetry. The vacuum is allowed
as $\mathfrak v$. This is the anyon attached to a $2\pi$ SO(3) flux,
not a choice of a generic anyon carrying half-integer spin.

Use the vacuum-normalized conventions of [YZ22], and put

$$
u_g=U_g(\mathfrak v,\mathfrak v;1),\qquad
\sigma(g)=(-1)^{q(g)}.
$$

The symbol $u_g$ here is a complex phase indexed by a **group element**;
it is distinct from the characteristic classes $u_i=w_i(TM)$. The fusion
space $V_{\mathfrak v\mathfrak v}^{1}$ is one-dimensional, even when other
fusion spaces of the UMTC have multiplicities. [YZ22], Eqs. (23)–(24), give

$$
\eta_{\mathfrak v}(g,h)^2
=\frac{u_{gh}}{u_g u_h^{\sigma(g)}}.
$$

Choose phases $r_g$ with $r_g^2=u_g$ and $r_1=1$. The fusion-compatible
sign cocycle of the spin-flux anyon is

$$
\omega_{\mathfrak v}(g,h)
=\eta_{\mathfrak v}(g,h)
  \frac{r_g r_h^{\sigma(g)}}{r_{gh}}
\in\{+1,-1\}.
$$

The preceding identity proves that its square is one; the twisted cocycle
identity for $\eta$ proves the cocycle identity for $\omega_{\mathfrak v}$.
Changing the square roots changes $\omega_{\mathfrak v}$ by a
$\mathbb Z_2$ coboundary. No square roots are needed in the final formulas.

The reduction uses the spin-flux rule in [YZ22], Sec. V, immediately after
[Eq. (65)](https://arxiv.org/pdf/2210.02444#page=24): a two-handle carrying
one unit of $w_2(E)$ contributes $M_{a,\mathfrak v}$. In the linked-anyon
diagram this inserts a $\mathfrak v$ ribbon. Gluing these ribbons across
symmetry defects uses $\eta_{\mathfrak v}$; gluing a pair to the vacuum
also uses $U_g(\mathfrak v,\mathfrak v;1)$. Consequently, the mixed spin
contribution is the pairing of this fusion-compatible sign cocycle with the
spin-flux sheet. Pure spin self-intersection terms are separate. They vanish
on the backgrounds used in (22b), (24a), and (25a).

This reduction keeps arbitrary permutations of all other anyons. It uses the
already-assumed coherent SO(3) and $H$ actions, rather than a restriction of
the entire UMTC to Abelian anyons.

### NEW 1: projective plane times a two-torus

$$
\boxed{\mathcal N_1(A;B,C)=
Z(\mathbb{RP}^2\times S^1\times S^1;A,B,C).}                    \tag{22}
$$

Required conditions: $A^2=1$, $q(A)=1$, $q(B)=q(C)=0$, and all three
holonomies commute. $B$ and $C$ may have infinite order. The arguments
label the projective-space loop, first circle, and second circle, respectively.
Their SO(3) factors specify the spin bundle; omitted spin factors are trivial.
This one contraction serves three roles:

| Use | Substitution | Cases and coordinates | Target |
|---|---|---|---|
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{X},V)$ | IT 1 p1, $\mathsf W_{1}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{Y},V)$ | IT 1 p1, $\mathsf W_{2}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{Y},V)$ | IT 3 pm, $\mathsf W_{2}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{X},V)$ | IT 4 pg, $\mathsf W_{1}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{L},V)$ | IT 4 pg, $\mathsf W_{2}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{X},V)$ | IT 5 cm, $\mathsf W_{1}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{L},V)$ | IT 8 pgg, $\mathsf W_{2}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{C_4},V)$ | IT 10 p4, $\mathsf W_{1}$ | +1 |
| With $T$: degree-one spin term | $\mathcal N_1(TU;\widehat{C_4},V)$ | IT 12 p4g, $\mathsf W_{1}$ | +1 |
| With $T$: time-mixed surface term | $\mathcal N_1(T;X,Y)$ | IT 1 p1, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;Y,\widehat{M})$ | IT 3 pm, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;Y,\widehat{XM})$ | IT 3 pm, $\mathsf K_{2}$ | $(-1)^{\ell_2}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;XY,\widehat{M})$ | IT 5 cm, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;Y,\widehat{M})$ | IT 7 pmg, $\mathsf K_{3}$ | $(-1)^{\ell_3}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;X,Y)$ | IT 13 p3, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;XY^{-1},\widehat{M})$ | IT 14 p3m1, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| With $T$: time-mixed surface term | $\mathcal N_1(T;XY,\widehat{M})$ | IT 15 p31m, $\mathsf K_{1}$ | $(-1)^{\ell_1}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(MU;Y,V)$ | IT 3 pm, $\mathsf S_{1}$ | $(-1)^{\ell_1}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(XMU;Y,V)$ | IT 3 pm, $\mathsf S_{2}$ | $(-1)^{\ell_2}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(MU;XY,V)$ | IT 5 cm, $\mathsf S_{1}$ | $(-1)^{\ell_1}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(MU;Y,V)$ | IT 7 pmg, $\mathsf S_{3}$ | $(-1)^{\ell_3}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(MU;XY^{-1},V)$ | IT 14 p3m1, $\mathsf S_{1}$ | $(-1)^{\ell_1}$ |
| Without $T$: mirror-period spin term | $\mathcal N_1(MU;XY,V)$ | IT 15 p31m, $\mathsf S_{1}$ | $(-1)^{\ell_1}$ |

For the first role, with classes $a,y,z$ on the three factors, the spin
bundle has $v_3=a^2z$ and the spatial map is through the $y$ circle, so
$\int yv_3=1$. For the second role, the spin bundle is trivial and
$u_1^2=a^2$ detects the spatial torus class $yz$. For the last role,
$v_2=a^2+az$ and the spatial mirror-period class is $ay$, so
$\int ay\,v_2=1$. These pairings explain the three uses of the same
geometric template.

#### Reuse of the published two-antiunitary indicator

If **both** $B^2=C^2=1$, (22) has the exact OLD expression

$$
\boxed{
\mathcal N_1(A;B,C)=
\frac{\mathcal I_2(ABC,A)\,\mathcal I_2(A,A)}
     {\mathcal I_2(AB,A)\,\mathcal I_2(AC,A)}
=\frac{\mathcal I_0\,\mathcal I_2(ABC,A)}
      {\mathcal I_2(AB,A)\,\mathcal I_2(AC,A)}.}                \tag{22a}
$$

Every argument of $\mathcal I_2$ is then an antiunitary involution.
Evaluate each $\mathcal I_2$ with the full $F,R,U,\eta$ sum in [YZ22],
[Eq. (55)](https://arxiv.org/pdf/2210.02444#page=20), equivalently
[YZ23], Eq. (211). Thus (22a) reuses precisely the
$\mathbb Z_2\times\mathbb Z_2^T$ calculation, allowing anyon permutations
and fusion multiplicities. It is a derived identity between partition
functions, not a replacement of one manifold by another inside Eq. (55).

To verify it, work first in the abstract group
$\langle A\rangle\times\langle B\rangle\times\langle C\rangle$.
Its orientation character is that of $A$; let $b,c$ be the two unitary
degree-one classes. A complete set of degree-four characteristic numbers is

$$
u_2^2,\ u_1^4,\ b^2u_1^2,\ bcu_1^2,\ c^2u_1^2,
\ b^4,\ b^3c,\ b^2c^2,\ bc^3,\ c^4.
$$

On $\mathbb{RP}^2\times T^2$ with the bundle in (22), only
$\int bcu_1^2=1$ is nonzero. In the four factors on the first right-hand
side of (22a), write $x,y$ for the projective-space classes. They have
$u_1=x+y$, and $(b,c)$ equals $(x,x),(0,0),(x,0),(0,x)$, respectively.
Since $x^3=y^3=0$, the product cancels $u_2^2$, $b^2u_1^2$, and
$c^2u_1^2$, leaves $bcu_1^2$, and has zero pairing with all other
numbers. This proves the bordism identity on the complete ten-dimensional
binary response space. Restricting any UMTC symmetry action along the
abstract-group homomorphism preserves the identity. The diagonal evaluation
$\mathcal I_2(A,A)=\mathcal I_0$ gives the second form.

The order assumptions matter: the translation and glide arguments in the
required table are not involutions. An order-two permutation of the anyons
does not imply an order-two element of the full fractionalized symmetry.
Consequently, (22a) alone does not evaluate those entries.

#### Explicit formula for all required spin-dependent instances

Let $A\in H$ be an antiunitary involution and $B\in H$ a commuting
unitary element of arbitrary order. With the SO(3) twists $U,V$ used in
the table, spin-flux reduction gives

$$
\boxed{
\mathcal N_1(AU;B,V)
=\frac{\eta_{\mathfrak v}(A,B)}
       {\eta_{\mathfrak v}(B,A)\,
        U_B(\mathfrak v,\mathfrak v;1)}.}                      \tag{22b}
$$

In particular, use $A=T$, $B=\widehat g$ for all nine $\mathsf W_i$
rows, and $A=m$, $B=h$ for the six no-$T$ mirror-period rows. The
$A$ in the $\eta$ symbols is the spin-free element; the $U,V$ twists
on the left are accounted for by $\mathfrak v$.

Here is the reduction in terms of the sign cocycle above. On this manifold,
$v_2=a^2+az$ and $\omega_{\mathfrak v}$ is pulled back along the
$A,B$ cycles. Its $ay$ coefficient is the sign
$\omega_{\mathfrak v}(A,B)/\omega_{\mathfrak v}(B,A)$, and
$ay(a^2+az)=a^2yz$. The possible $a^2$ coefficient contributes zero.
The spin-free background factors through $\mathbb{RP}^2\times S^1$
and has zero degree-four characteristic numbers on this product. Pure spin
terms also vanish. The surviving ratio is therefore the full evaluation.
Using $AB=BA$, $q(A)=1$, $q(B)=0$ gives

$$
\frac{\omega_{\mathfrak v}(A,B)}
     {\omega_{\mathfrak v}(B,A)}
=\frac{\eta_{\mathfrak v}(A,B)}
       {\eta_{\mathfrak v}(B,A)}\frac{r_B^*}{r_B}
=\frac{\eta_{\mathfrak v}(A,B)}
       {\eta_{\mathfrak v}(B,A)u_B},
$$

which proves (22b). No step uses $B^2=1$.

The $U_B$ factor is essential. Under the symmetry-action gauge change
of [YZ22], Eq. (26), with phase $\gamma_{\mathfrak v}(B)$, the bare
$\eta$ ratio acquires $\gamma_{\mathfrak v}(B)^2$ and $U_B$ acquires
the same factor. Their quotient is gauge invariant. The coherence identity
above also gives
$(\eta_{\mathfrak v}(A,B)/\eta_{\mathfrak v}(B,A))^2=u_B^2$,
so (22b) is a sign. In a gauge with $U_B=1$, it simplifies to the bare
commutator ratio; that gauge choice must not be silently assumed.

This establishes a formula for the 15 spin-dependent instances, not a general
formula for $\mathcal N_1(A;B,C)$. The eight spin-free $\mathsf K_j$
instances in the table instead use the full triangulated formula
(S1)–(S8) in the companion note, with two independent unitary circle
holonomies.

### NEW 2: projective plane times a Klein bottle

$$
\boxed{\mathcal N_2(A;B,L)=
Z(\mathbb{RP}^2\times\mathrm{Kl};A,B,L;E_{\rm trivial}).}       \tag{23}
$$

Required conditions: $A^2=1$, $q(A)=q(L)=1$, $q(B)=0$,
$LBL^{-1}=B^{-1}$, and $[A,B]=[A,L]=1$. The spin bundle is trivial.
The $A$ holonomy belongs to $\mathbb{RP}^2$; $B,L$ are the two
Klein-bottle generators. The required instance is

| Symmetry | Evaluation | Coordinate | Target |
|---|---|---|---|
| $pg\times SO(3)\times\mathbb Z_2^T$ | $\mathcal N_2(T;X,L)$ | $\mathsf K_1$ | $(-1)^{\ell_1}$ |

Here $L$ is the actual glide, with infinite order. If $a$ is the
projective-space class and $s$ the Klein-bottle orientation class, then
$u_1=a+s$, $s^2=0$, so $u_1^2=a^2$. The spatial degree-two class pairs
once with the Klein bottle. The gravitational number $\int u_2^2$ is zero,
so no additional normalization is needed.

An explicit general UMTC contraction for this case is now given by
(S1)–(S8) in the companion note, using its Klein-bottle edge assignment.
Equation (55) of [YZ22] cannot be used with $T_2=L$: its second
projective-space holonomy must square to the identity, whereas the glide
squares to a nontrivial translation. The state sum retains
$LBL^{-1}B=1$ as the Klein-bottle relation.

### NEW 3: translation torus times a spin-flux sphere

$$
\boxed{\mathcal N_3(B,C)=
Z(T^2_{B,C}\times S^2;\int_{S^2}v_2=1).}                       \tag{24}
$$

Required conditions: $[B,C]=1$ and $q(B)=q(C)=0$. The spatial bundle
factors through the torus, and the SO(3) bundle is pulled back from the
nontrivial bundle on $S^2$. There are no additional spin holonomies on the
torus. Both required groups use actual translations $B=X,C=Y$.

| Group | Time reversal | Evaluation | Coordinate | Target |
|---|---|---|---|---|
| $p1\times SO(3)$ | absent or present | $\mathcal N_3(X,Y)$ | $\mathsf S_1$ | $(-1)^{\ell_1}$ |
| $p3\times SO(3)$ | absent or present | $\mathcal N_3(X,Y)$ | $\mathsf S_1$ | $(-1)^{\ell_1}$ |

When time reversal is included, its bundle is trivial in these evaluations.
The nonzero characteristic number is the product of the spatial torus class
and $v_2$ on the sphere. In the mirror groups the corresponding spin terms
already use EXTENDED $\mathcal S_e$ or NEW $\mathcal N_1$, so no further
instances of $\mathcal N_3$ are needed there.

The spin-flux sphere projects the linked handle label onto $\mathfrak v$.
The remaining torus measures its projective commutator. Thus

$$
\boxed{
\mathcal N_3(B,C)
=\frac{\eta_{\mathfrak v}(B,C)}
       {\eta_{\mathfrak v}(C,B)}.}                            \tag{24a}
$$

Equivalently, evaluate $\omega_{\mathfrak v}$ on the torus two-cycle
$[B|C]-[C|B]$. The factors $r_Br_C/r_{BC}$ cancel because both
elements are unitary and commute. Symmetry-action gauge phases cancel for
the same reason; the coherence identity makes the square of (24a) equal
to one. No sum over all anyons or assumption of trivial anyon permutation
is needed after identifying $\mathfrak v$. There is no restriction on the
orders of $B,C$.

### NEW 4: Klein bottle times a spin-flux sphere

$$
\boxed{\mathcal N_4(B,L)=
Z(\mathrm{Kl}_{B,L}\times S^2;\int_{S^2}v_2=1).}               \tag{25}
$$

Required conditions: $LBL^{-1}=B^{-1}$, $q(B)=0$, and $q(L)=1$.
The spatial bundle factors through the Klein bottle; the SO(3) bundle is
pulled back from the spin-flux sphere. No spin holonomies are assigned to
$B,L$. The required instance is

| Group | Time reversal | Evaluation | Coordinate | Target |
|---|---|---|---|---|
| $pg\times SO(3)$ | absent or present | $\mathcal N_4(X,L)$ | $\mathsf S_1$ | $(-1)^{\ell_1}$ |

The independent $T$ bundle, when available, is trivial here: the glide already
accounts for the orientation character of the Klein bottle. Its
$w_1^2$ vanishes, and the evaluation isolates the spatial degree-two class
times the sphere's $v_2$.

Reducing on the spin-flux sphere again leaves the projective symmetry of
$\mathfrak v$. The Klein-bottle relation gives

$$
\boxed{
\mathcal N_4(B,L)
=\frac{\eta_{\mathfrak v}(L,B)\,
        \eta_{\mathfrak v}(B^{-1},B)}
       {\eta_{\mathfrak v}(B^{-1},L)}.}                        \tag{25a}
$$

To derive the expression, introduce formal projective operators $P_g$ with
$P_gP_h=\eta_{\mathfrak v}(g,h)P_{gh}$, antilinear when $q(g)=1$.
The actual relation $LB=B^{-1}L$ implies

$$
\begin{aligned}
P_LP_B
 &=\frac{\eta_{\mathfrak v}(L,B)}
          {\eta_{\mathfrak v}(B^{-1},L)}P_{B^{-1}}P_L,\\
P_LP_BP_L^{-1}P_B
 &=\frac{\eta_{\mathfrak v}(L,B)\,
          \eta_{\mathfrak v}(B^{-1},B)}
         {\eta_{\mathfrak v}(B^{-1},L)}\,1.
\end{aligned}
$$

Here $P_L^{-1}$ is the inverse operator; it is not identified with
$P_{L^{-1}}$ without its projective phase. This is also the evaluation of
$\omega_{\mathfrak v}$ on the Klein-bottle cycle: substituting its
definition cancels all $r$ factors because $q(L)=1$ and $LB=B^{-1}L$.
Applying [YZ22], Eq. (26), directly cancels all symmetry-action gauge
phases in (25a). The squared expression reduces to
$u_{LB}/u_{B^{-1}L}=1$, which verifies sign quantization. In particular,
the formula uses the actual inverse translation and allows the glide to
have infinite order.

### Checks of the added formulas

The following checks support the reductions and make their scope explicit:

- The OLD identity (22a) was checked by exact characteristic-number
  evaluation on all ten generators of the response space for
  $\mathbb Z_2^T\times\mathbb Z_2\times\mathbb Z_2$.
- The spin-flux expressions were compared with the existing published
  contractions in 3,744 scalar comparisons, using 16 sampled
  fractionalization classes per selected symmetry homomorphism. Categories
  were toric code, double semion, $\mathbb Z_4$ gauge theory,
  $U(1)_4\times U(1)_{-4}$, and Ising times conjugate Ising. The checks
  included anyon permutations and the non-Abelian doubled-Ising category.
  In the involution domain, (22b) agreed both with (22a), evaluated using
  the full published $\mathcal I_2$ contraction, and with the OLD
  $\mathcal W_o$ ratio. Related spin-flux square identities checked were
  $\mathcal I_1(AU)/(\mathcal I_1(A)\mathsf B)
  =\eta_{\mathfrak v}(A,A)$ for antiunitary involutions and
  $\mathcal I_3(gU,gV)=\eta_{\mathfrak v}(g,g)u_g$ for unitary
  involutions.
- There were 600 sign and symmetry-action gauge checks of (22b), (24a),
  and (25a), using explicit sign cocycles and arbitrary phase gauges on
  $\mathbb Z_2^T\times\mathbb Z$, $\mathbb Z^2$, and the Klein-bottle
  group, including large translation powers. These check the phase
  cancellations and group relations; they are not evaluations of an
  independently implemented four-dimensional state sum.

These are consistency checks of the stated reductions. They do not test
every UMTC or every fusion multiplicity. The new spin-free state sum has
separate local and global checks recorded in the companion note. The general argument for arbitrary other fusion
multiplicities is the reduction to the one-dimensional fusion space of
the invariant Abelian spin-flux anyon. These formulas are now implemented in version 0.2.0.

### NEW formula coverage and implementation

| Template and use | Entries in the 34-case lists | Formula status |
|---|---:|---|
| $\mathcal N_1$: degree-one spin terms | 9 | (22b) |
| $\mathcal N_1$: no-$T$ mirror-period spin terms | 6 | (22b) |
| $\mathcal N_1$: spin-free time-mixed surface terms | 8 | Companion note, (S1)–(S8), torus product |
| $\mathcal N_2$: spin-free $pg$ time-mixed term | 1 | Companion note, (S1)–(S8), Klein product |
| $\mathcal N_3$: translation torus with spin flux | 4 | (24a) |
| $\mathcal N_4$: Klein bottle with spin flux | 2 | (25a) |

Thus 21 of the 30 entries labelled NEW now have explicit spin-flux
expressions. The other nine entries—the eight $\mathsf K_j$ rows in the
$\mathcal N_1$ table and $\mathsf K_1$ of $pg$ with time reversal—now
have explicit triangulated $F,R,U,\eta$ expressions. All nine have trivial
spin bundle, so they use the full state sum instead of the spin-flux
reduction. Version 0.2.0 evaluates them by reference/relative splitting
and a 24-simplex product state sum. A compact handle simplification remains
a possible performance improvement. The separate EXTENDED circle-holonomy check for (17)
is also retained.

For a future compact simplification, the relevant product handle decompositions
have handle counts $(N_0,N_1,N_2,N_3,N_4)=(1,3,4,3,1)$ for
$\mathbb{RP}^2\times T^2$ and $\mathbb{RP}^2\times\mathrm{Kl}$.
Both have Euler characteristic zero. The global prefactor in [YZ22],
Eq. (44), is therefore $\mathcal D^{-4}$, before the handle-label
dimension factors. Their two-handle relation words are respectively

$$
\begin{array}{ll}
\mathbb{RP}^2\times T^2:
 &A^2,\ ABA^{-1}B^{-1},\ ACA^{-1}C^{-1},\ BCB^{-1}C^{-1},\\
\mathbb{RP}^2\times\mathrm{Kl}:
 &A^2,\ ABA^{-1}B^{-1},\ ALA^{-1}L^{-1},\ LBL^{-1}B.
\end{array}
$$

These data identify the extra handles and relations relative to the
two-antiunitary calculation. They are a starting point for evaluating the
framed Kirby diagrams and every $F,R,U,\eta$ factor; the presentation
and prefactor alone are not a complete tensor formula.

The continuation
[Twisted partition functions on RP² × T² and RP² × Kl](rp2-product-partition-functions.md)
now derives all four two-handle $\eta$ factors and the handle-label
dimension weight. It also gives explicit 12-factor and 18-factor
evaluations in terms of a supplied anomaly four-cocycle, and fully
evaluates both partition functions for a nonpermuting pointed
specialization including toric code. The Klein-bottle formula in that
specialization contains an additional topological-spin factor.
Its Section 2A now gives the explicit general triangulated contraction,
including every fusion index and antiunitary conjugation. It also specifies
finite triangulations and flat connections for both manifolds, preserving
infinite-order holonomies. Thus the nine entries have mathematical tensor
recipes, now evaluated by the v0.2.0 backend. The general non-Abelian
fallback remains computationally expensive. The note records its
isometric-vertex normalization and independent checks, and distinguishes
that derivation from the scalar prefactors printed in the state-sum papers.
These formulas are now implemented in version 0.2.0.
