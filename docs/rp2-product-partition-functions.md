# Twisted partition functions on RP² × T² and RP² × Kl

This note continues the [wallpaper-group indicator catalogue](anomaly-indicators-all-wallpaper-groups.md).
It uses the construction of Weicheng Ye and Liujun Zou,
[*Anomaly of (2+1)-Dimensional Symmetry-Enriched Topological Order from
(3+1)-Dimensional Topological Quantum Field Theory*,
arXiv:2210.02444](https://arxiv.org/pdf/2210.02444), abbreviated YZ22.

**Status.** [Section 2A](#2a-explicit-contraction-in-frueta) now gives an
explicit triangulated $F,R,U,\eta$ contraction for both manifolds, including
anyon permutations, fusion multiplicities, antiunitary conjugations,
normalization, and the full translation or glide twists. It needs no
anomaly four-cocycle as extra input. The compact four-handle kernels
below remain unsimplified. Version 0.2.0 implements the state sum on a
24-simplex product Delta-complex. The later four-cocycle and pointed formulas provide
smaller expressions when their additional assumptions hold.

All SO(3) bundles in this note are trivial. The symbols $A,B,C,L$ denote
actual symmetry-group elements, with their full categorical action and
fractionalization data. Finite-order permutations alone do not impose
finite order on these elements.

## 1. Admissible twists

Write $q(g)=0,1$ for unitary/antiunitary grading and
$\sigma(g)=(-1)^{q(g)}$.

| Manifold | Twists | Relations and grading |
|---|---|---|
| $\mathbb{RP}^2\times T^2$ | $A$ on the projective loop; $B,C$ on the torus | $A^2=1$, $[A,B]=[A,C]=[B,C]=1$; $q(A)=1$, $q(B)=q(C)=0$ |
| $\mathbb{RP}^2\times\mathrm{Kl}$ | $A$ on the projective loop; $B,L$ on the Klein bottle | $A^2=1$, $[A,B]=[A,L]=1$, $LBL^{-1}=B^{-1}$; $q(A)=q(L)=1$, $q(B)=0$ |

There is no condition $B^2=C^2=1$ in the first row or $L^2=1$ in the
second. A twist failing these relations or the orientation grading is not
a compatible flat background on the indicated manifold; its partition
function is not an extra value to be included.

The wallpaper substitutions are those in the main catalogue:
$A=T$ for the eight spin-free torus-product indicators, and
$(A;B,L)=(T;X,L)$ for the $pg$ Klein-bottle indicator.

## 2. Applying the handle prescription

Use the product of the surface handle decompositions, as in YZ22,
Appendix E. Both products have

$$
(N_0,N_1,N_2,N_3,N_4)=(1,3,4,3,1),\qquad \chi=0.
$$

Thus the overall factor in YZ22,
[Eq. (44)](https://arxiv.org/pdf/2210.02444#page=13), is
$\mathcal D^{-4}$, where $\mathcal D^2=\sum_a d_a^2$.
Assign anyons $a,b,c,d$ to the following two-handles. These anyon labels
are independent of the cohomology generators used later.

| Label | Torus-product attaching word | Klein-product attaching word |
|---|---|---|
| $a$ | $A^2$ | $A^2$ |
| $b$ | $BCB^{-1}C^{-1}$ | $LBL^{-1}B$ |
| $c$ | $ABA^{-1}B^{-1}$ | $ABA^{-1}B^{-1}$ |
| $d$ | $ACA^{-1}C^{-1}$ | $ALA^{-1}L^{-1}$ |

Choose the segment carrying each label so that the displayed functor word
acts with that label as its final output. In particular, an inverse letter
means the inverse functor, as in YZ22, Appendix B; it must not be silently
identified with the chosen functor of the inverse group element.

The dimension denominator in Eq. (44) counts repeated passages through a
one-handle. Its three factors are

$$
\begin{array}{c|ccc}
 & A & B & C\text{ or }L\\ \hline
\text{factor} & d_a d_c d_d & d_b d_c & d_b d_d .
\end{array}
$$

Symmetry preserves quantum dimensions. Dividing the two-handle numerator
$d_a d_b d_c d_d$ by these factors leaves

$$
\frac{1}{d_b d_c d_d}.                                      \tag{H1}
$$

### The four explicit $\eta$ factors

For commuting $g,h$, define

$$
C_x(g,h)=\frac{\eta_x(g,h)}{\eta_x(h,g)}.
$$

This notation describes a two-handle factor. By itself it is generally
neither gauge invariant nor an anomaly indicator, and $x$ need not be
fixed by $g$ or $h$.

For the torus product, the combined two-handle contribution is

$$
\boxed{
\Theta_T(a,b,c,d)=
\eta_a(A,A)\,
C_b(B,C)\,C_c(A,B)\,C_d(A,C).
}                                                           \tag{H2}
$$

For the Klein product, define

$$
K_x(L,B)=
\frac{\eta_x(L,B)\eta_x(B^{-1},B)}
     {\eta_x(B^{-1},L)}.
$$

Then

$$
\boxed{
\Theta_K(a,b,c,d)=
\eta_a(A,A)\,
K_b(L,B)\,C_c(A,B)\,C_d(A,L).
}                                                           \tag{H3}
$$

The commutator factors follow by comparing
$\rho_g\rho_h\Rightarrow\rho_{gh}$ with
$\rho_h\rho_g\Rightarrow\rho_{hg}$, exactly as in YZ22, Sec. III D,
Remark g. To obtain the Klein factor, first compare
$\rho_L\rho_B$ and $\rho_{B^{-1}}\rho_L$, using $LB=B^{-1}L$.
This contributes $\eta_x(L,B)/\eta_x(B^{-1},L)$. After canceling
$\rho_L\rho_L^{-1}$, the remaining composition
$\rho_{B^{-1}}\rho_B\Rightarrow 1$ contributes
$\eta_x(B^{-1},B)$. This derivation uses no condition $L^2=1$.

Consequently, the partially evaluated handle formulas have the form

$$
Z_T=\frac{1}{\mathcal D^4}
\sum_{a,b,c,d,\boldsymbol\mu}
\frac{\Theta_T(a,b,c,d)}{d_b d_c d_d}\,
\mathscr K_T^{\rho,U,F,R}(a,b,c,d;\boldsymbol\mu),              \tag{H4}
$$

$$
Z_K=\frac{1}{\mathcal D^4}
\sum_{a,b,c,d,\boldsymbol\mu}
\frac{\Theta_K(a,b,c,d)}{d_b d_c d_d}\,
\mathscr K_K^{\rho,U,F,R}(a,b,c,d;\boldsymbol\mu).              \tag{H5}
$$

Here $\boldsymbol\mu$ runs over the admissible fusion-space bases at the
one-handles. The symbols $\mathscr K_T,\mathscr K_K$ stand for the
**unevaluated** framed ribbon diagrams, including the three one-handle
$U$ factors of YZ22, Eq. (43). They are not new supplied UMTC data.
Writing them does not complete the tensor calculation. In particular,
their crossing order, framing twists, conjugations at antiunitary
one-handles, and multiplicity contractions are not specified by (H4)–(H5).
The $\eta$ factors in (H2)–(H3) alone cannot be used in their place.
The following triangulated contraction supplies a fully specified
alternative without needing those two minimal-handle kernels.

## 2A. Explicit contraction in $F,R,U,\eta$

A triangulation gives a larger but explicit alternative to the two minimal
handle kernels. This section specifies its local tensors, every contracted
fusion index, its normalization, and triangulations and edge twists for
both products. No anomaly four-cocycle is required as additional input.

The ribbon contraction follows Bulmash–Barkeshli,
[*Absolute anomalies in (2+1)D symmetry-enriched topological states and
exact (3+1)D constructions*, arXiv:2003.11553](https://arxiv.org/pdf/2003.11553),
Sec. III B and Fig. 5, abbreviated BB20. YZ22 identifies its handle
construction with this approach in Sec. I and Sec. III. For an explicit
fixed-background prescription and the antiunitary factors, use
Kobayashi–Barkeshli,
[*(3+1)D path integral state sums on curved U(1) bundles and U(1) anomalies
of (2+1)D topological phases*, arXiv:2111.14827](https://arxiv.org/pdf/2111.14827),
Sec. V, Eqs. (58)–(62), abbreviated KB21, with its U(1) background set to
zero. The fusion-index expansion and the isometric normalization below
are written out here; they are not claimed to be a new equation quoted
verbatim from either paper.

### Background and labels

Let $K$ be an ordered triangulation of the four-manifold. A flat edge
connection $h_{ij}$ transports from vertex $j$ to vertex $i$, so

$$
h_{ji}=h_{ij}^{-1},\qquad h_{ij}h_{jk}=h_{ik}.
$$

Its holonomies are the twists in Section 1, and $q(h)$ represents
$w_1(M)$. Write ${}^{ij}a=\rho_{h_{ij}}(a)$. A triangle $ijk$, $i<j<k$,
carries an anyon $a_{ijk}$ in the local frame at $k$. A tetrahedron
$ijkl$ carries an anyon $b_{ijkl}$ and **two** basis indices:

$$
\begin{split}
\mu_{ijkl}&=1,\ldots,N^{b_{ijkl}}_{a_{ikl},{}^{lk}a_{ijk}},\\
\nu_{ijkl}&=1,\ldots,N^{b_{ijkl}}_{a_{ijl},a_{jkl}}.
\end{split}                                                   \tag{S1}
$$

A labeling violating either fusion rule contributes zero. The associated
map, in orthonormal splitting bases, is

$$
E_{ijkl}=
|a_{ikl},{}^{lk}a_{ijk};b_{ijkl},\mu_{ijkl}\rangle
\langle a_{ijl},a_{jkl};b_{ijkl},\nu_{ijkl}|.
$$

Use isometric trivalent vertices: a splitting vertex followed by its
adjoint is the identity on its simple source. Consequently
$\operatorname{tr}(E_{ijkl}^{\dagger}E_{ijkl})=d_{b_{ijkl}}$.
This specifies the vertex normalization, including when a fusion space
has dimension greater than one.

### The local six-$F$ contraction

For a simplex $01234$, abbreviate the five tetrahedron labels as

| Index $r$ | Tetrahedron | Anyon and basis indices |
|---|---|---|
| 0 | 0123 | $b_0,\mu_0,\nu_0$ |
| 1 | 0124 | $b_1,\mu_1,\nu_1$ |
| 2 | 0134 | $b_2,\mu_2,\nu_2$ |
| 3 | 0234 | $b_3,\mu_3,\nu_3$ |
| 4 | 1234 | $b_4,\mu_4,\nu_4$ |

Set $z={}^{42}a_{012}$ and $\bar b_0={}^{43}b_0$. The bar here denotes
transport, **not** antiparticle conjugation. The internal simple labels
$t,x$ are summed over the UMTC. Define the six associator matrices

$$
\begin{array}{lll}
F_1=F^{a_{024},a_{234},z}_{t},
&F_2=F^{a_{024},z,a_{234}}_{t},
&F_3=F^{a_{014},a_{124},a_{234}}_{t},\\[2pt]
F_4=F^{a_{014},a_{134},{}^{43}a_{123}}_{t},
&F_5=F^{a_{034},{}^{43}a_{013},{}^{43}a_{123}}_{t},
&F_6=F^{a_{034},{}^{43}a_{023},z}_{t}.
\end{array}                                                   \tag{S2}
$$

Our convention, also used by `umtc.F`, is

$$
[F^{abc}_{t}]_{(e,\alpha,\beta),(f,\gamma,\delta)}:
\quad ((ab)_e c)_t\longrightarrow(a(bc)_f)_t.
$$

Here the left tree is the row index and the right tree is the column
index. $F^{-1}=F^{\dagger}$ reverses the two composite indices; it does
not mean taking the reciprocal of each entry. The matrix
$R^{ab}_{x}$ has a $ba\to x$ row and an $ab\to x$ column, as does
`umtc.R_matrix`.

For any scalar or matrix, let $\mathsf c_g$ mean entrywise complex
conjugation when $q(g)=1$, and the identity otherwise. Set

$$
\begin{split}
\widehat U_-&=\mathsf c_{h_{34}}\!\left[
 U_{h_{34}}(a_{023},{}^{32}a_{012};b_0)\right],\\
\widehat U_+&=\mathsf c_{h_{34}}\!\left[
 U_{h_{34}}(a_{013},a_{123};b_0)\right],\\
\widehat\eta&=\mathsf c_{h_{24}}\!\left[
 \eta_{a_{012}}(h_{23},h_{34})\right].
\end{split}                                                   \tag{S3}
$$

The arguments of $U$ specify the **output** anyons, as in YZ22. Its
row basis is on the $h_{34}^{-1}$-transported input and its column basis
is on that output. In particular, the transported indices below run over

$$
\bar\mu_0=1,\ldots,N^{{}^{43}b_0}_{{}^{43}a_{023},z},\qquad
\bar\nu_0=1,\ldots,N^{{}^{43}b_0}_{{}^{43}a_{013},{}^{43}a_{123}}.
$$

The complete positive-simplex weight in this normalization is

$$
\boxed{\begin{aligned}
\mathcal W_{01234}^{+}
={}&\widehat\eta^{-1}
\sum_{t,x}\ d_t
\sum_{p,q,r,s,u,v,\alpha,\beta,\bar\mu_0,\bar\nu_0}
 [F_1]_{(b_3,\nu_3,p),(x,\alpha,r)}
 [R^{z,a_{234}}_{x}]_{\alpha\beta}\\
&\times[F_2^{-1}]_{(x,\beta,r),(b_1,\mu_1,q)}
 [F_3]_{(b_1,\nu_1,q),(b_4,\nu_4,s)}\\
&\times[F_4^{-1}]_{(b_4,\mu_4,s),(b_2,\nu_2,u)}
 [F_5]_{(b_2,\mu_2,u),(\bar b_0,\bar\nu_0,v)}\\
&\times[F_6^{-1}]_{(\bar b_0,\bar\mu_0,v),(b_3,\mu_3,p)}
 [\widehat U_-^{-1}]_{\mu_0\bar\mu_0}
 [\widehat U_+]_{\bar\nu_0\nu_0}.
\end{aligned}}                                               \tag{S4}
$$

Every internal index occurs exactly twice; its range is the dimension of
the indicated trivalent fusion space. The ten indices $\mu_j,\nu_j$
are external to this simplex and are summed when tetrahedra are glued.
Thus (S4) includes fusion multiplicities and anyon permutations explicitly.
For the opposite orientation, with the same external label names,

$$
\mathcal W_{01234}^{-}=\overline{\mathcal W_{01234}^{+}}.       \tag{S5}
$$

To obtain (S4), glue the five maps $E$ along their common triangle
lines. Move the $0123$ map to the frame at vertex 4; this supplies the
two $\widehat U$ matrices. Straightening the two consecutive transports
of $a_{012}$ supplies $\widehat\eta^{-1}$. Resolving the resulting
closed ribbon graph in total charge $t$ gives, in order,
$F_1,R,F_2^{-1},F_3,F_4^{-1},F_5,F_6^{-1}$. Closing its remaining
$t$ line gives $\operatorname{tr}(\mathrm{id}_t)=d_t$.
This explains both the order of the contraction and the internal
quantum-dimension factor.

When all fusion multiplicities are at most one, (S4) reduces to

$$
\mathcal W^+=
\frac{\mathsf c_{h_{34}}\!\left[
 U_{h_{34}}(a_{013},a_{123};b_0)/
 U_{h_{34}}(a_{023},{}^{32}a_{012};b_0)\right]}
 {\mathsf c_{h_{24}}[\eta_{a_{012}}(h_{23},h_{34})]}
\sum_{t,x}d_t\,
(F_1)_{b_3x}R^{z,a_{234}}_x
(F_2^{-1})_{xb_1}(F_3)_{b_1b_4}
(F_4^{-1})_{b_4b_2}(F_5)_{b_2\bar b_0}
(F_6^{-1})_{\bar b_0b_3}.                                    \tag{S6}
$$

The two antiunitary conjugations in (S3) are different:
$h_{34}$ for $U$ and $h_{24}$ for $\eta$. They follow from the local
frames of the vertices involved, and agree with KB21, Eq. (58).

### Gluing and normalization

Let $n_j$ count the $j$-simplices of $K$; these are **simplex counts**,
distinct from the earlier handle counts. Choose simplex signs
$\epsilon_\sigma=\pm1$ representing the orientation-twisted fundamental
cycle, with the coefficient of each ordered simplex based at its last
vertex. There is a directly usable rule for the signs. In the boundary
of $[01234]$, faces omitting vertex $i<4$ receive $(-1)^i$, while the
face omitting 4 receives $\sigma(h_{34})$. At each shared tetrahedron,
its two incident coefficients, multiplied by their $\epsilon$ signs,
must sum to zero. Start with one sign and propagate these equations
through the dual graph. Consistency is precisely the condition
$q(h)=w_1(M)$.

The two desired partition functions are the following sum, evaluated
with their respective triangulations and twists:

$$
\boxed{
Z(M;h)=\mathcal D^{\,2(n_0-n_1)-\chi(M)}
\sum_{\{a_f,b_\tau,\mu_\tau,\nu_\tau\}}
\frac{\prod_{f\in K_2}d_{a_f}}
     {\prod_{\tau\in K_3}d_{b_\tau}}
\prod_{\sigma\in K_4}\mathcal W_\sigma^{\epsilon_\sigma}.
}                                                            \tag{S7}
$$

All tetrahedron labels, including both multiplicity indices, are shared
between their two incident four-simplices. The factor $1/d_{b_\tau}$
is the inverse norm of $E_\tau$ in the quantum-trace pairing. The factor
$\mathcal D^{-\chi}$ chooses the invertible-theory normalization
$Z(S^4)=1$, as in KB21, Eq. (51); both products here have $\chi=0$.
The braiding, symmetry and fractionalization factors are already in
$\mathcal W$. The earlier $\Theta_T,\Theta_K$ and handle prefactor
must not be multiplied into (S7) a second time.

**Normalization check and source convention.** Formula (S4) uses a
quantum trace of isometric vertices. In particular, it has $d_t$ inside
the sum and no additional simplex factor
$\sqrt{\prod_\tau d_{b_\tau}/\prod_f d_{a_f}}$.
A literal transcription of the scalar normalization printed in BB20,
Eqs. (42)–(45), or KB21, Eqs. (61)–(62), into this orthonormal convention
does not pass the Ising $S^4$ check below. The normalization here is
therefore specified by the trace derivation and checked independently;
a term-by-term reconciliation with those printed scalar normalizations
is not being asserted. This distinguishes a verified convention from an
unexplained change of prefactors.

### Concrete triangulations and all allowed twists

One explicit, deliberately nonminimal choice for $\mathbb{RP}^2$ has
vertices $1,\ldots,6$ and triangles

```text
123  124  135  146  156  236  245  256  345  346
```

Let $\alpha$ be the mod-two edge cocycle that is one on
$25,26,34,36,45$ and zero on all other edges. The flat connection on
an edge of this factor is $A^{\alpha}$; it has projective-loop holonomy
$A$.

For the second factor, use the $3\times3$ grid in the plane, split each
unit square along its lower-left to upper-right diagonal, and make one
of the identifications

$$
\begin{array}{ll}
T^2:&(x+3,y)\sim(x,y),\quad(x,y+3)\sim(x,y),\\
\mathrm{Kl}:&(x+3,y)\sim(x,y),\quad(x,y+3)\sim(-x,y).
\end{array}                                                   \tag{S8}
$$

Each surface has 9 vertices, 27 edges and 18 triangles. Its vertices
are the canonical representatives $(i,j)$ with $0\leq i,j<3$, ordered
lexicographically. The horizontal loop has holonomy $B$, and the
vertical loop has holonomy $C$ or $L$.

Here is an explicit edge assignment that retains the full group words.
For every lifted triangle and each of its lifted vertices $(x,y)$,
write $y=j+3n$ and

- on the torus, $x=i+3m$ and $\gamma_{(x,y)}=B^{-m}C^{-n}$;
- on the Klein bottle, $x=(-1)^n i+3m$ and
  $\gamma_{(x,y)}=B^{-m}L^{-n}$.

On its edge from canonical vertex $u$ to $v$, set
$h^{\Sigma}_{uv}=\gamma_u^{-1}\gamma_v$; remember that $h_{uv}$
transports from $v$ to $u$. The prescribed loop holonomies follow with
this convention. Changing the lift left-multiplies all the $\gamma$
values on a triangle by the same element, so the edge assignment is
well defined. For the Klein bottle this uses $LBL^{-1}=B^{-1}$.

For every ordered triangle $[u_0u_1u_2]$ of $\mathbb{RP}^2$ and
$[v_0v_1v_2]$ of the second surface, triangulate their product by the
six monotone paths from $(0,0)$ to $(2,2)$ with two horizontal and two
vertical steps. The five visited vertex pairs form a four-simplex.
For any edge between vertex pairs put

$$
h_{(u,v),(u',v')}=A^{\alpha(u,u')}h^{\Sigma}_{vv'},
$$

where a repeated projection vertex contributes the identity. This is
flat because $A$ commutes with the surface twists. The construction gives

$$
(n_0,n_1,n_2,n_3,n_4)=(54,702,2268,2700,1080),\qquad\chi=0.
$$

Every tetrahedron has two incident four-simplices. The orientation-sign
rule above is consistent for both connections. Substituting this finite
complex into (S4)–(S7) is an explicit $F,R,U,\eta$ formula for
$Z_T(A;B,C)$ or $Z_K(A;B,L)$.

This uses the fixed-background formulation of KB21, Sec. V. There is no
sum over symmetry-group elements and no $|G|$ normalization. Only the
finitely many words supplied by this triangulation are evaluated, so
$B,C,L$ can have infinite order. A finite permutation image must still
not be substituted for the full categorical action and its $\eta$
values. For the wallpaper catalogue, insert $A=T$ and the surface twists
listed in the relevant row. All SO(3) backgrounds remain trivial here.

### What this completes

Equations (S1)–(S8) give an explicit triangulated tensor contraction for
both general-UMTC partition functions. They replace the need to know
$\mathcal O$ in advance or to treat $\mathscr K_T,\mathscr K_K$ as
unknown inputs. They do **not** simplify the answer to the four
anyon-label sums in the minimal handle decomposition. The latter would
be useful for numerical efficiency, but is a separate simplification.
Version 0.2.0 implements this local tensor on a smaller branched product
Delta-complex with counts (2,18,52,60,24). Its face identifiers retain
incidence information, so loop edges and multiple faces are distinguished.
Reference anomalies use this state sum after OLD-indicator reductions;
fractionalization changes use the relative obstruction and cycles (C2)–(C3).

## 3. Explicit formulas when the anomaly four-cocycle is known

Let

$$
\mathcal O\in Z^4(G,U(1)_q)
$$

be a normalized representative of the group-cohomology part of the
anomaly. Normalization means that $\mathcal O=1$ if any argument is the
identity; $U(1)_q$ means that an antiunitary element conjugates a phase.
This $\mathcal O$ is an anomaly four-cocycle, not the fractionalization
two-cocycle or an $\eta$ symbol.

Under the anomaly convention of the main catalogue, the separate
gravitational factor is $\mathcal I_0^{\int w_2(TM)^2}$. It equals one
on both products. Indeed, with $a$ the projective-space class and $s$ the
Klein-bottle orientation class,

$$
\begin{array}{c|cc}
M & w_2(TM) & \int w_2(TM)^2\\ \hline
\mathbb{RP}^2\times T^2 & a^2 & 0\\
\mathbb{RP}^2\times\mathrm{Kl} & a^2+as & 0
\end{array}
$$

because $a^3=0$ and $s^2=0$. Thus evaluating $\mathcal O$ suffices for
these backgrounds.

For $g,h$ commuting with $A$, define the six-factor expression

$$
\boxed{
\Xi_A(g,h)=
\frac{
\mathcal O(A,A,g,h)\,
\mathcal O(A,g,h,A)\,
\mathcal O(g,A,A,h)\,
\mathcal O(g,h,A,A)}
{\mathcal O(A,g,A,h)\,
 \mathcal O(g,A,h,A)}.
}                                                           \tag{C1}
$$

The partition functions are

$$
\boxed{
Z(\mathbb{RP}^2\times T^2;A,B,C)
=\frac{\Xi_A(B,C)}{\Xi_A(C,B)}.
}                                                           \tag{C2}
$$

$$
\boxed{
Z(\mathbb{RP}^2\times\mathrm{Kl};A,B,L)
=\frac{\Xi_A(L,B)\,\Xi_A(B^{-1},B)}
       {\Xi_A(B^{-1},L)}.
}                                                           \tag{C3}
$$

These contain 12 and 18 four-cocycle factors, respectively, before
cancellations. They retain the actual group elements and apply to all
admissible twists in Section 1, irrespective of anyon permutations.
Their use requires the full anomaly $\mathcal O$ of that symmetry
enrichment. In particular, (C1) is not a recipe for recovering
$\mathcal O$ from $\eta$ alone.

### Derivation from twisted fundamental cycles

Use normalized inhomogeneous bar chains, with orientation-twisted boundary

$$
\partial[g_1|\cdots|g_n]
=\sigma(g_1)[g_2|\cdots|g_n]
+\sum_{i=1}^{n-1}(-1)^i
 [g_1|\cdots|g_ig_{i+1}|\cdots|g_n]
+(-1)^n[g_1|\cdots|g_{n-1}].                                 \tag{C4}
$$

Chains containing the identity are zero. The three surface cycles are

$$
\begin{aligned}
z_{\rm RP}&=[A|A],\\
z_T&=[B|C]-[C|B],\\
z_K&=[L|B]+[B^{-1}|B]-[B^{-1}|L].
\end{aligned}                                                \tag{C5}
$$

For example,
$\partial[A|A]=-[A]+[A]=0$. For the Klein bottle, the three boundaries
cancel using $LB=B^{-1}L$ and $\sigma(L)=-1$. The extra
$[B^{-1}|B]$ term is required for this cancellation.

More explicitly, triangulating the Klein-bottle polygon $LBL^{-1}B$
and accounting for its inverse edge gives the cycle
$[L|B]+[LB|L^{-1}]+[B^{-1}|B]-[L|L^{-1}]$.
The boundary of $[B^{-1}|L|L^{-1}]$ reduces this to $z_K$.
Thus (C5) is the image of the fundamental surface class, not just an
arbitrary closed chain.

Since $A$ commutes with the other twists, the product map of the two
fundamental groups is a homomorphism. Take the signed shuffle product of
$z_{\rm RP}$ and $z_T$ or $z_K$. For one term $[g|h]$, its six shuffles
are

$$
\begin{aligned}
[A|A]\times[g|h]={}&[A|A|g|h]-[A|g|A|h]
+[A|g|h|A]\\
&+[g|A|A|h]-[g|A|h|A]+[g|h|A|A].
\end{aligned}                                                \tag{C6}
$$

Evaluating $\mathcal O$ on (C6) gives (C1); evaluating it on the two
product cycles gives (C2)–(C3). This is a cohomological evaluation of the
same anomaly partition function defined by YZ22. It is a derived
alternative representation, rather than an expansion of its Kirby diagram.

### Gauge invariance and sign quantization

The function $\Xi_A$ is a $q$-twisted two-cocycle on the centralizer of
$A$. In particular, if
$\mathcal O\mapsto\mathcal O\,\delta_q\lambda$ for a normalized
three-cochain $\lambda$, put

$$
\xi_A(g)=\frac{\lambda(A,A,g)\lambda(g,A,A)}{\lambda(A,g,A)}.
$$

The shuffle identity gives

$$
\Xi_A(g,h)\mapsto
\Xi_A(g,h)\frac{\xi_A(g)\xi_A(h)^{\sigma(g)}}{\xi_A(gh)}.
$$

These factors cancel in (C2) and (C3). The latter cancellation uses
antiunitarity of $L$ as well as the Klein-bottle relation.

Moreover,
$\partial[A|A|A]=-2[A|A]$. Both four-cycles are therefore of order
dividing two in orientation-twisted homology. Their partition functions
are signs, even though individual $\mathcal O$ and $\Xi_A$ values can
be arbitrary phases. There is no additional complex conjugation to insert
by hand into (C1): the twisting is already included in (C4) and
$\delta_q\mathcal O=1$.

### Exact reductions to the published indicator for special twists

Use the notation of the main catalogue:
$\mathcal I_2(g,h)=Z(\mathbb{RP}^2\times\mathbb{RP}^2;g,h)$,
evaluated by the full tensor formula in YZ22,
[Eq. (55)](https://arxiv.org/pdf/2210.02444#page=20).
Its arguments must be commuting antiunitary involutions.

If $B^2=C^2=1$, the torus-product result is the OLD formula already
derived in the catalogue:

$$
\boxed{
Z_T=\frac{\mathcal I_0\,\mathcal I_2(ABC,A)}
           {\mathcal I_2(AB,A)\mathcal I_2(AC,A)}.
}                                                           \tag{C7}
$$

There is a second exact reduction. If **$L^2=1$**, while $B$ can still
have arbitrary order, then $(BL)^2=1$ by the Klein-bottle relation.
Both $L$ and $BL$ are therefore admissible antiunitary arguments, and

$$
\boxed{
Z_K=\mathcal I_2(A,L)\,\mathcal I_2(A,BL).
}                                                           \tag{C8}
$$

To check this, compactification on the projective plane gives the twisted
two-cocycle $\Xi_A$. Its Klein-bottle evaluation equals
$\Xi_A(BL,BL)/\Xi_A(L,L)$ when $L^2=1$.
For example, projective operators with multiplication factor $\Xi_A$ obey
$(P_BP_L)^2=Z_K P_L^2$; because $P_BP_L$ is antiunitary, the phase
relating it to $P_{BL}$ cancels in its square. Each antiunitary-involution
square is a sign. Moreover,
$\mathcal I_2(A,D)=\mathcal I_0\,\Xi_A(D,D)$ for such a $D$:
the additional $\mathcal I_0$ is the gravitational contribution on
$\mathbb{RP}^2\times\mathbb{RP}^2$. It cancels in the ratio, which is
also the product in (C8).

Geometrically, this is the decomposition of the Klein bottle into two
crosscaps with holonomies $L$ and $BL$, whose boundary holonomies are
trivial in this special case. These OLD reductions are valid for general
UMTCs, including permutations and fusion multiplicities. Formula (C8)
allows an infinite-order translation $B$, but it does not apply to the
actual glide in $pg$, since that glide has $L^2\ne1$.

## 4. Fully evaluated pointed specialization

The following formulas do not require an unknown four-cocycle. Assume:

- the UMTC is pointed, with anyon group $E$ of exponent two;
- $F=1$ and the braiding $R^{x,y}\in\{+1,-1\}$ is a bicharacter;
- the symmetries in the background fix all anyons and have $U=1$;
- fractionalization is specified by a normalized
  $w\in Z^2(G,E)$, with $\eta_x(g,h)=M_{x,w(g,h)}$.

Here
$M_{x,y}=R^{x,y}R^{y,x}$ and $\theta_x=R^{x,x}$.
Toric code satisfies these assumptions. They do not hold for a general
UMTC or a general anyon-permuting symmetry action.

In this gauge the symmetry-fractionalization obstruction has representative

$$
\mathcal O(g,h,k,l)=R^{w(g,h),w(k,l)}.                         \tag{P1}
$$

The interchange of two fractionalization junctions crosses their attached
anyon lines $w(g,h)$ and $w(k,l)$ once. It supplies the displayed $R$
factor; the associator and symmetry-vertex factors are one under the
stated assumptions. This simplification is why (P1) cannot be used for a
general permutation action or nontrivial $F,U$ data.

Define the following anyons, using additive notation in $E$:

$$
\begin{aligned}
\mathfrak k&=w(A,A),\\
\mathfrak p&=w(A,B)-w(B,A),\\
\mathfrak q_T&=w(A,C)-w(C,A),\\
\mathfrak q_K&=w(A,L)-w(L,A),\\
\mathfrak b_T&=w(B,C)-w(C,B),\\
\mathfrak b_K&=w(L,B)+w(B^{-1},B)-w(B^{-1},L).
\end{aligned}                                                \tag{P2}
$$

All signs in this additive notation are equivalent modulo two. They
are written as above to retain the surface-relation conventions.

Substitution into (C2)–(C3) gives

$$
\boxed{
Z_T=M_{\mathfrak k,\mathfrak b_T}\,
    M_{\mathfrak p,\mathfrak q_T}.
}                                                           \tag{P3}
$$

$$
\boxed{
Z_K=M_{\mathfrak k,\mathfrak b_K}\,
    M_{\mathfrak p,\mathfrak q_K}\,
    \theta_{\mathfrak p}.
}                                                           \tag{P4}
$$

The extra $\theta_{\mathfrak p}$ in (P4) is necessary.

To see its origin, on $\mathbb{RP}^2\times T^2$ use classes $a,y,z$
with $a^3=y^2=z^2=0$ and top class $a^2yz$. The pullback of $w$ is

$$
w=\mathfrak k\,a^2+\mathfrak p\,ay
  +\mathfrak q_T\,az+\mathfrak b_T\,yz.
$$

In the quadratic expression (P1), only the pairings of the first and last
terms and of the middle two survive. Each pair produces a monodromy,
giving (P3).

For the Klein bottle let $x$ evaluate on $B$ and $s$ on $L$. Its ring
has $s^2=0$, $x^2=xs$, with $\int_{\rm Kl}xs=1$. Now

$$
w=\mathfrak k\,a^2+\mathfrak p\,ax
  +\mathfrak q_K\,as+\mathfrak b_K\,xs.
$$

The same two mutual pairings survive. In addition,
$(ax)^2=a^2xs$, so the self-pairing of $\mathfrak p$ contributes
$R^{\mathfrak p,\mathfrak p}=\theta_{\mathfrak p}$, proving (P4).

### Toric-code values for representative choices

Write $0,e,m,\psi=e+m$ for its anyons. Then $M_{e,m}=-1$ and
$\theta_\psi=-1$, while $\theta_e=\theta_m=1$. In this table
$\mathfrak b,\mathfrak q$ mean the appropriate torus or Klein quantities
from (P2).

| $\mathfrak k$ | $\mathfrak b$ | $\mathfrak p$ | $\mathfrak q$ | $Z_T$ | $Z_K$ |
|---|---|---|---|---:|---:|
| $0$ | $0$ | $0$ | $0$ | +1 | +1 |
| $e$ | $m$ | $0$ | $0$ | −1 | −1 |
| $0$ | $0$ | $e$ | $m$ | −1 | −1 |
| $e$ | $m$ | $e$ | $m$ | +1 | +1 |
| $0$ | $0$ | $\psi$ | $0$ | +1 | −1 |

These choices describe fractionalization evaluated at the selected twists.
Changing the twists changes the evaluations in (P2). The table is not a
claim that every wallpaper group independently permits all these choices.

## 5. Derivation checks and implementation validation

The derivation was checked with normalized bar chains and explicit phase
cochains:

- The projective-plane, torus, and Klein-bottle two-chains have zero
  orientation-twisted boundary. Their 12-term and 18-term product chains
  also have zero boundary.
- On each abstract group
  $\mathbb Z_2^A\times\mathbb Z^2$ and
  $\mathbb Z_2^A\times\pi_1(\mathrm{Kl})$, all 256 choices of the
  eight binary toric-code fractionalization parameters were evaluated.
  The four-cocycle formulas and (P3)–(P4) agreed in every case.
- Eighty arbitrary phase three-cochains were used to construct
  four-coboundaries. Both closed-manifold formulas evaluated to one.
  Eight hundred twisted two-cocycle identities for $\Xi_A$ and fifty
  instances of the explicit $\xi_A$ gauge formula also passed.
- The special-twist reductions were checked directly against the
  published $\mathcal I_2$ tensor contraction. For toric code and the
  all-fermion four-anyon UMTC, all 4,096 fractionalization choices on
  the three-involution group were tested for each manifold. All 16,384
  scalar comparisons with (P3)–(P4) passed, including the
  $\theta_{\mathfrak p}$ factor in the Klein-bottle formula.

These earlier checks establish the cycle algebra and the pointed
specialization. The added triangulated contraction has the following
independent checks:

- Gluing two oppositely oriented four-simplices along their entire boundary
  gives $S^4$. Using the Ising UMTC, all 2,080 admissible labelings give
  $Z(S^4)=1$ with (S4) and (S7). Omitting the $d_t$ trace weight instead
  gives $3/4$. This tests non-Abelian quantum dimensions and normalization.
- For the Fibonacci UMTC, 896 admissible choices of boundary labels were
  tested under the three-to-three Pachner move, of which 650 had nonzero
  amplitudes. The largest discrepancy between the two contractions was
  $7.5\times10^{-16}$. This tests the six-$F$ order and the crossing.
- Sixteen independent changes of fusion bases were checked with
  multiplicity-two tensors, for both values of $q(h_{34})$. Every internal
  basis transformation cancels and the ten external indices transform
  with the required orientation and conjugations; the largest discrepancy
  was $9.5\times10^{-16}$. These synthetic tensors test the index identity,
  not the existence of a UMTC with arbitrary chosen tensors.
- Both explicit product triangulations have the simplex counts stated
  above. The full group-word edge assignments have the stated generator
  holonomies and satisfy flatness on every triangle. All 2,700
  tetrahedron gluings satisfy the orientation-twisted sign rule.
- Twenty global symmetry-action gauge checks used arbitrary complex
  $\gamma_a(g)$ phases on toric-code labelings of the two products.
  With the full infinite-group edge words, the $U$ and $\eta$ changes
  cancel after gluing, with maximum error $1.8\times10^{-14}$.
  This checks both distinct conjugations in (S3) together with the
  orientation signs, rather than setting $U=1$ throughout the check.
- In the toric-code specialization, the state sum on each product reduces
  to a finite Gauss sum over its four-dimensional mod-two $H^2$. For all
  256 pairs of fractionalization classes on each manifold, it agrees with
  (P3)–(P4). In the basis $(a^2,ax,as,xs)$, the two intersection matrices are

  $$
  Q_T=\begin{pmatrix}0&0&0&1\\0&0&1&0\\0&1&0&0\\1&0&0&0\end{pmatrix},
  \qquad
  Q_K=\begin{pmatrix}0&0&0&1\\0&1&1&0\\0&1&0&0\\1&0&0&0\end{pmatrix}.
  $$

  The extra diagonal entry in $Q_K$ reproduces the
  $\theta_{\mathfrak p}$ term. Here $x,s$ are the two surface
  degree-one classes, with $s$ the orientation class for the Klein bottle.

Together these check the local non-Abelian ribbon contraction, the
multiplicity indices, and the global pointed reductions. A full numerical
contraction of the 1,080-simplex products with a permuting non-Abelian
UMTC has not been performed. Version 0.2.0 implements the smaller product
complex, a gauge-reduced pointed sum, and a general non-Abelian contraction.
The latter is tested on the four-sphere with Fibonacci data; full product
checks cover pointed inputs, including permutations, nontrivial F symbols,
complex symmetry gauges, and a reference with order-four circle holonomies.
The general non-Abelian product fallback has no practical runtime guarantee.
See [release validation](validation.md) for reproducible tests. The nine
spin-free NEW entries now have explicit mathematical tensor recipes via
(S1)–(S8); they remain unimplemented in the classifier.
