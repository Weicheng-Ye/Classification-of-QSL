# Algorithm and conventions

Let C be a finite UMTC, A its group of invertible anyons, and G₀ the coherent
finite intrinsic symmetry supplied by the input. The reference U₀ and η₀
must describe an action of the whole supplied G₀. The implementation does
not infer G₀ from fusion and spins. Missing intrinsic automorphisms would
make the classification incomplete, even when all supplied data are coherent.

All 17 microscopic plane groups have wallpaper factor P and connected SO(3).
Each independently permits an optional commuting time reversal T. The
crystalline-equivalence grading is s(g)=m(g)+t(g) modulo two. Homomorphisms
φ:G→G₀ are enumerated by their generator images, checking every conjugation
and power relation. SO(3) has identity image by continuity.

The input's A is computed from dₐ=1 and its actual fusion table. A direct
product basis A=⊕ᵢ Z/mᵢ is found without relying on anyon label arithmetic.
The induced action of φ on this basis supplies an arbitrary finite Abelian
module, including mixed cyclic orders and non-diagonal actions.

## Infinite-group cohomology

Write wallpaper elements as XˣYʸRᶜMᵐTᵗ, omitting absent factors and using L
for a glide generator. Here x,y are arbitrary integers; R,M,T have relative
orders n,2,2. A glide has relative order two over the translation subgroup.
For every
conjugation relation and finite power relation introduce an A-valued tail:

```
g_i g_j g_i^-1 = a_ij * word_ij(g_0,...,g_(i-1))
g_i^n_i = p_i * power_word_i(g_0,...,g_(i-1))
```

Starting from A, add X and Y as infinite cyclic extensions and R,M/L,T as
finite cyclic extensions. At each stage the new conjugation automorphism α
must preserve all previous defining relations. For finite order n, also
require αⁿ=Inn(P) on the lower generators and α(P)=P, where P includes
both the anyon tail and the lower-generator power word. This keeps L²=Y
in pg/pgg and L²=XY in p4g. Its action on A
already satisfies the required relations because φ is a homomorphism.
These conditions are necessary and sufficient for consistency of the
iterated extension presentation. They are linear congruences in the tails.

Changing lifts gᵢ→bᵢgᵢ gives a second linear map B, the coboundary subgroup.
Thus the discrete fractionalization group is ker(C)/im(B). Integer lattice
arithmetic, Hermite normal form, and Smith decomposition compute this quotient,
representative lifts, and projection onto quotient coordinates exactly.
No torus truncation of translations is used to compute it.

For the connected spin factor, append an invariant element s∈A with 2s=0.
This implements H²(SO(3),A)=A[2]; mixed H¹ terms with SO(3) vanish. This
adds the cocycle s·w₂. An element's `spin` field is a unit quaternion
representing an SO(3) rotation. Choose its lift with the first nonzero
component positive. The sign of the product of two chosen lifts determines
w₂. This numerical quaternion section has the usual discontinuity at its
branch cut; it uses tolerance 10⁻¹² for zero components.

The ordered-generator section defines t(g,h) by collecting its two lifted
words. The collector supports signed, unbounded integer translations, using
binary powers. Every realization's callable is

```
eta_a(g,h) = eta0_a(phi(g),phi(h)) * M(a,t(g,h)),
M(a,b) = theta(a*b)/(theta(a)*theta(b)).
```

The `qsl_eta_v1` descriptor stores φ and the finite list of relation tails,
including `spin_lift_squared`. It is sufficient to reconstruct η on the full
group; it is not a finite table of group-element pairs. Reconstruction uses
the same UMTC JSON and checks the relation congruences.

## Anomaly matching

The contractions in `indicators.py` implement Eqs. (209)–(213) of
[Ye and Zou](https://arxiv.org/html/2309.15118v3#A4), retaining the fusion
multiplicity indices in I₂ and I₃. Their restrictions to the wallpaper/spin
subgroups follow Eqs. (214)–(217). The LSM target signs follow Tables I, II,
XVIII, and XIX. Two apparent subscript typos in Eq. (216) are interpreted as
I₂: its two-argument entries I₁₂ and I₁₃ involve two antiunitary generators.

For the other settings, `wallpaper_indicators.py` assembles the independent
bases in [the all-group catalogue](anomaly-indicators-all-wallpaper-groups.md).
Old indicators are reused, and the S² factors reduce to the invariant
order-two spin-flux anyon. Wyckoff orbits supply lattice-class coordinates
using [the Bilbao catalogue](wallpaper-groups.md).

The remaining RP² × T² and RP² × Kl evaluations split into a pulled-back
reference anomaly and a relative obstruction. The latter retains all six F,
one R, two U, and reference eta factors of Eq. (50) of
[arXiv:1906.10691](https://arxiv.org/abs/1906.10691), evaluated on the 12-term
and 18-term twisted bar cycles. Reference holonomies may first be reduced
by odd-degree covers. Old formulas apply when their **reference images**
meet the order conditions; the full infinite-group fractionalization is
never reduced by this shortcut.

If those reductions do not apply, `product_state_sum.py` contracts a
24-simplex product Delta-complex. Pointed categories use an exact quotient
of twisted two-cocycles by one-cochain gauge changes. The general fallback
retains all anyon and fusion-multiplicity sums with admissibility pruning.
Its isometric-basis normalization and quantum trace are specified in
[the partition-function derivation](rp2-product-partition-functions.md).

The expensive F/R/U contractions are independent of t and are cached.
The remaining η dependence is a finite Fourier polynomial in H² coordinates.
The relative obstruction is quadratic in fractionalization. Its polarization
therefore determines each sign indicator from the origin, each generator,
and generator pairs. Diagonal polarization multiplies binomial(nᵢ,2), so
order-four classes are not accidentally reduced to order two. Additional
direct Fourier evaluations check this identity. An indicator outside ±1 or
a failed polarization check raises `IndicatorError`; it is never silently
rounded to an allowed class.

Small sectors are enumerated in bounded batches. Large cyclic 2-power
sectors use exact Boolean quadratic solving with linear elimination.
For a Z4 or higher factor, binomial(n,2) is the second binary digit of n;
it is retained as an independent linear term in the expanded system.
The solver reconstructs every solution in the original H² coordinates.
The unitary centralizer of φ acts
on their H² coordinates; one representative per orbit is retained. Under the
coherent reference G₀ action, intrinsic conjugation carries the pulled-back
reference to an equivalent reference, so this action is linear on t.
Literal homomorphisms in the same intrinsic conjugacy orbit are all included
in the output but contribute to `total_realizations` only once.

## Scope

The implementation is category-independent and retains multiplicity indices.
Validation covers the supplied Abelian, Ising, Fibonacci, and SU(2) examples,
plus a constructed doubled-Ising category with an antiunitary layer exchange.
Multiplicity-two tensor contractions are checked against explicit index sums.
The physical example categories do not include Nᶜₐᵦ>1, so nontrivial
fusion-multiplicity categories do not yet have a published regression fixture.
The runtime is not bounded uniformly over all finite UMTCs: tensor sums and
H² enumeration can be expensive. Counts exceeding a signed 64-bit class index
raise an explicit error. There is no family-specific formula or published
count table in the classifier itself.

The classification excludes additional SPT stacking, following both papers.
Full UMTC and intrinsic-action coherence checks are provided separately by
the companion `umtc-data` package. The classifier assumes those input
equations hold; loading validates structural completeness, not all coherence.
