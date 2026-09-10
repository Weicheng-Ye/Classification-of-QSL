# Validation

## Version 0.2.0

The release was checked against a frozen v0.1.0 checkout at commit
`0753feb766c767b03f98098401efd3a6ebb43e3f`. All **276 complete JSON results**
are identical, including homomorphism images, cohomology orders, counts,
and the five known paper discrepancies. Four additional verbose result
hashes verify preservation of the original eta descriptors.
The baseline is committed in
[tests/fixtures/v0_1_0.json](../tests/fixtures/v0_1_0.json).

All **26 example UMTCs × 34 symmetry settings = 884 classifications**
were completed with the empty WP list. Their homomorphism and realization
counts are recorded in
[the v0.2.0 regression fixture](../tests/fixtures/v0_2_0_wallpaper.json).
These new-group counts are implementation regressions; the papers do not
provide independent printed counts for all of them.

The tests additionally check:

- all 34 exact presentations, antiunitary gradings, and mod-two cohomology
  dimensions against the independent wallpaper cohomology ranks;
- every Bilbao WP multiplicity, the b/c ordering in p2, centered-cell
  conventions, and general-position lattice charges;
- twisted cocycle identities and eta reconstruction for glides with
  translation exponents far larger than any finite quotient;
- the relative F/R/U/eta obstruction against the old absolute indicators;
- both 24-simplex product sums with negative anomaly signs, complex
  symmetry gauges, permutations, and nontrivial F symbols;
- higher-order reference holonomies, including a noncommuting Klein-bottle
  background whose glide image has order four;
- the full non-Abelian Fibonacci four-sphere partition function;
- Boolean and cyclic 2-power constraint solving against exhaustive enumeration.

The general non-Abelian product fallback retains every fusion index, but a
full non-Abelian product contraction has not been benchmarked. Its runtime
can be exponential. Physical regression inputs have no fusion multiplicity
greater than one; separate synthetic tensor tests check multiplicity indices.

Reproduce the release checks with:

```sh
python -m pytest -q
python scripts/validate_wallpaper_groups.py
python scripts/validate_papers.py
```

The paper runner still exits with status 1 for the five known discrepancies;
the frozen v0.1.0 regression requires those results to remain unchanged.
A wheel was also built, installed outside the source checkout, and exercised
with an IT-number classification and a reconstructed glide eta function.

## Published examples and earlier checks

The public `classify` function was run against **276 category/group/lattice
cases** from the two papers, covering all 25 paper-derived input JSON files.
The remaining supplied file, Fibonacci, was checked for all four original
groups. The report is [validation/papers.json](../validation/papers.json).

**271 of 276 published comparisons match.** The five differences are confined
to an extra order-three sector in U(1)₆ with p6 × SO(3) and Z₃ gauge theory
with p6m × O(3). They remain marked `passed: false` in the report. See the
[explicit extension witness and count breakdown](order-three-discrepancy.md).
The classifier was not modified to discard those classes to match a table.

The comparisons include the permutation-pattern breakdown of Table V, all
eight Ising chiralities from Sec. VII, the mirror-group counts in Table X,
and every supplied SU(2) level in the second paper. All SU(2) results match.
For example, SU(2)₆ has four homomorphisms, each with 16 realizations, in the
trivial p4 lattice class. For Z₄ gauge theory, the p4m trivial-class total is
886,740 and the p6m total is 16,453, both matching Table X.

Reproduce the comparisons from the project root:

```sh
.venv/bin/python run_examples.py
.venv/bin/python scripts/validate_papers.py
.venv/bin/python scripts/check_order_three.py
.venv/bin/python scripts/compare_paper_subsector.py
.venv/bin/python scripts/compare_legacy.py
.venv/bin/pytest -q
```

`validate_papers.py` exits with status 1 because the five literal table
comparisons disagree. The independent witness checks all 157,464 cocycle
identities of its finite quotient and proves nontriviality under all generator
lift changes in the infinite group. `compare_paper_subsector.py` demonstrates
that removing precisely the additional sector recovers the printed counts;
this restriction is confined to the diagnostic script.

All runners use the repository's local `examples` folder by default.
The short `run_examples.py` demonstration prints realization counts grouped
by UMTC and saves just those counts to `validation/example-results.json`,
nested by UMTC, symmetry group, and lattice class. It does not compare against
the papers. The strict `validate_papers.py` runner retains its nonzero mismatch
exit status. The alternate toric-code input is `examples/toric_code.json`.

All 24 permutation patterns in the supplied original Z₂ implementation also
agree, covering 160 pattern/lattice comparisons; see
[validation/legacy-z2.json](../validation/legacy-z2.json).

The original 18 unit tests cover group associativity, exact mixed-modulus quotients,
twisted cocycle identities with signed translations, translations as large
as 10⁵⁰, antiunitary grading, anyon-relabeling counts, JSON reconstruction,
SO(3) quaternion lifts, invalid inputs, catalog coverage, and a category with
a deliberately unfamiliar name. A new doubled-Ising test exercises a
non-Abelian antiunitary layer exchange. Multiplicity-two contractions of
Eqs. (211) and (212) are also checked against explicit index sums.

Example outputs:

- [The requested p4 / 1a+1b call, with eta descriptor](../validation/example-output.json)
- [SU(2)₆ with its four homomorphisms](../validation/su2-k6-output.json)

The numerical tensor checks use a tolerance of 2×10⁻⁷ for sign indicators.
The module, group, cocycle constraints, and coboundary quotients use exact
integer arithmetic. No published expected count is imported by the package.
