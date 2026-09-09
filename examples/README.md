# UMTC examples

These 26 JSON files contain the data from the companion `umtc-data`
example catalogue. The alternate toric-code example is named `toric_code.json`
here; `z2_gauge.json` is a separate gauge of the same topological order.
The classifier and validation scripts use these local files by default.

The catalogue includes U(1)₂N for N=1,…,5; all eight Ising chiralities;
SU(2)ₖ for k=1,2,3,4,6,−3; Z₂, Z₃, and Z₄ gauge theories; double semion;
U(1)₄×U(1)₋₄; Fibonacci; and an alternate toric-code gauge.

From the project root, run:

```sh
.venv/bin/python run_examples.py
```

This prints realization counts for 276 category/group/lattice cases, grouped
by UMTC and symmetry group. Fibonacci is an additional example covered by the
unit tests. The counts are saved to `validation/example-results.json`, nested
by UMTC, symmetry group, and lattice class. Use `scripts/validate_papers.py`
for comparisons with the papers; see [validation](../docs/validation.md).

The files retain the companion catalogue's normalization corrections:
doubled-U(1) symbols use the tensor product of a chiral category and its
conjugate, and the Zₙ reference eta uses the main-text Eq. (59).

Sources: [Ye and Zou](https://arxiv.org/html/2309.15118v3) and
[Hao et al.](https://arxiv.org/html/2608.14180v1).
