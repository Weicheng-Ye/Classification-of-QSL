# QSL classification

[![arXiv](https://img.shields.io/badge/arXiv-2309.05118-b31b1b.svg)](https://arxiv.org/abs/2309.05118)

A Python package for symmetry enrichment of finite UMTCs supplied in the
`umtc-data` JSON format. The computation uses the category's fusion, F/R,
intrinsic symmetry, U, and reference eta data, without category-name dispatch.

## Quick start from downloaded folders

Use one Python environment for both packages. You need **Python 3.10 or newer**
and **GAP 4**, with the `gap` command available in the same terminal as Python.
GAP is needed for examples with an intrinsic GAP group, including the toric code;
the U(1)₂ and Fibonacci examples can run without it. No Mathematica or SageMath
installation is required.

Install the prerequisites once:

- **macOS:** install [Python](https://www.python.org/downloads/) if needed.
  The [GAP macOS guide](https://gap-system.github.io/GapWWW/install/mac/)
  offers the **Gap.app + GAP** download. After installing it, use its
  **Gap → Install GAP Command For Shell** menu option so Python can launch GAP.
  An existing installation providing the `gap` command also works.
- **Ubuntu 22.04+ / Debian 12+:** run `sudo apt update`, then
  `sudo apt install python3 python3-venv python3-pip gap`.
- **Windows:** use [WSL with Ubuntu](https://learn.microsoft.com/en-us/windows/wsl/install),
  then follow the Ubuntu instructions and run the commands below inside WSL.
  Keep both downloaded folders inside that Linux environment.

Unzip the two downloads alongside each other, for example:

```text
Downloads/
├── QSLClassification/
│   ├── pyproject.toml
│   ├── run_examples.py
│   └── examples/
└── umtc/
    ├── pyproject.toml
    └── src/
```

In a terminal, enter `QSLClassification` and install both packages:

```sh
cd /path/to/QSLClassification
python3 -m venv .venv
source .venv/bin/activate
python -m pip install ../umtc .
```

Replace `/path/to/QSLClassification` with the location of your download. If the
other folder is called `umtc-main`, use `../umtc-main`; it can also be an absolute
path in quotes. Both paths must point to folders containing `pyproject.toml`.
The last command installs the downloaded UMTC package and this package together,
and downloads their Python dependencies. You do not need a second environment
or a separate installation from inside `umtc`.

Check the installation with a small toric-code classification that also exercises
the GAP connection:

```sh
python -m pip check
qsl-classify 'p6m*O(3)' examples/toric_code.json --iwp '1 a' --output result.json
python -c 'import json; print(json.load(open("result.json"))["total_realizations"])'
```

The first command should report no broken requirements; the last should print
**8**. `result.json` contains the full answer. Run commands using relative
`examples/` paths from the `QSLClassification` folder.

When you open a new terminal, return to this folder and run
`source .venv/bin/activate` again. Alternatively, use
`.venv/bin/python -m qsl_classification ...` without activation. In an editor,
select this folder's `.venv/bin/python` as the Python interpreter.

This uses Python's standard [venv and pip workflow](https://packaging.python.org/en/latest/guides/installing-using-pip-and-virtual-environments/).
For common setup errors, see [troubleshooting](#troubleshooting).

## Python API

```python
import json
from qsl_classification import classify, eta_from_json

result = classify('p4*SO(3)', ['1 a', '1 b'],
                  'examples/u1_2.json', verbose=True)
print(json.dumps(result, indent=2))
descriptor = result['homomorphisms'][0]['realizations'][0]['eta_symbol']
eta = eta_from_json(descriptor, 'examples/u1_2.json')
value = eta((1,), {'translation': [100, -27], 'rotation': 2},
                    {'spin': [0, 1, 0, 0]})
```

Supported groups are `p4*SO(3)`, `p6*SO(3)`, `p4m*O(3)`, and `p6m*O(3)`.
Here O(3) means SO(3) × Z₂ᵀ; under crystalline equivalence both M and T
are antiunitary. The connected SO(3) factor maps trivially to the finite
intrinsic symmetry group.

IWPs are occupied half-odd-integer-spin orbits: p4/p4m use `1 a`, `1 b`,
`2 c`; p6/p6m use `1 a`, `2 b`, `3 c`. The empty list is trivial lattice
homotopy. Repeated orbits add modulo two, and p6's `2 b` orbit is homotopically
trivial. Integer-spin orbits need not be listed.

The return value is a JSON-compatible dictionary. Every literal graded
homomorphism appears with its generator images, realization count, and
`equivalent_to` representative under unitary intrinsic conjugation. Counts
within a homomorphism quotient coboundaries and its unitary centralizer.
`total_realizations` counts each homomorphism orbit once. These are the papers'
anyon-enrichment counts; stacking additional SPT phases is excluded.

With `verbose=True`, each realization contains a declarative, serializable
eta-function descriptor. `eta_from_json` reconstructs the callable on the
infinite group. JSON itself cannot contain Python functions. Elements are
wallpaper tuples `(x,y,c)` / `(x,y,c,m,t)` or dictionaries with `translation`,
`rotation`, `mirror`, `time_reversal`, and `spin`. Spin rotations use unit
quaternions `[w,x,y,z]`; q and -q describe the same SO(3) element. A canonical
SU(2) section supplies w₂. Translations are arbitrary integers.

## Command line and paper examples

```sh
qsl-classify 'p4*SO(3)' examples/su2_k6.json --output result.json
qsl-classify 'p6m*O(3)' examples/toric_code.json --iwp '1 a' --verbose
```

The [examples folder](examples/README.md) contains all 26 UMTC JSON files.
Run the short [example script](run_examples.py) to cover all 276
catalogued cases for the four supported groups:

```sh
python run_examples.py
```

It prints each UMTC once, with aligned realization counts for each symmetry
group and lattice class. For example:

```text
UMTC: u1_2
  p4*SO(3)
    Lattice       0  a  b  c  a+b  a+c  b+c  a+b+c
    Realizations  9  1  1  1    1    1    1      1
  p6*SO(3)
    Lattice       0  a  c  a+c
    Realizations  5  1  1    1
```

The JSON in `validation/example-results.json` contains only the realization
counts, nested by UMTC, symmetry group, and lattice class. Neither output
includes absolute local paths or paper comparisons. Use
`python scripts/validate_papers.py` for the separate comparison with published
counts; its five known disagreements are documented below.

The input must contain valid UMTC data and a coherent reference action of its
full intrinsic symmetry group. The classifier uses that supplied group; it
does not discover omitted automorphisms. `symmetry: null` declares a trivial
intrinsic group. Use `umtc-check` to check input coherence. Enumeration is
finite but grows with the size of H²; verbose output can be very large.

See [the algorithm](docs/algorithm.md) and [validation](docs/validation.md).

Validation matches 271 of 276 printed comparisons. Five cases expose an
additional order-three cohomology sector in the first paper; the general
classifier retains it. See the [independent witness](docs/order-three-discrepancy.md).

## Development and tests

For editing either package, use an
[editable install](https://pip.pypa.io/en/stable/topics/local-project-installs/#editable-installs)
in the activated environment:

```sh
python -m pip install -e ../umtc -e '.[test]'
python -m pytest -q
```

Source edits then take effect without reinstalling. Keep both source folders in
place. With the regular quick-start install, rerun `python -m pip install ../umtc .`
after changing the package source. The test extra is optional for running
classifications and `run_examples.py`.

## Troubleshooting

- **Cannot launch GAP / `gap` not found:** install GAP and make its command
  available on `PATH`; check with `command -v gap` in the terminal you use for
  Python. On macOS, installing the graphical app alone does not enable its shell
  command; use the menu option described above.
- **`qsl-classify` not found / `No module named qsl_classification`:** activate
  `.venv`, or run `.venv/bin/python -m qsl_classification` with the same arguments.
  If using an editor or notebook, check its selected Python environment.
- **`ensurepip` or `venv` is unavailable:** on Ubuntu/Debian install
  `python3-venv`, then repeat environment creation.
- **`../umtc` is not installable:** use the actual extracted folder name and
  check it contains `pyproject.toml`.
- **An example JSON cannot be found:** return to `QSLClassification` or pass an
  absolute JSON path. The JSON inputs are already included in `examples/`.

## References

If this repository is useful for your research, please consider citing the
following papers.

The [PRX article](https://journals.aps.org/prx/abstract/10.1103/PhysRevX.14.021053):

```bibtex
@article{PhysRevX.14.021053,
  title = {Classification of Symmetry-Enriched Topological Quantum Spin Liquids},
  author = {Ye, Weicheng and Zou, Liujun},
  journal = {Phys. Rev. X},
  volume = {14},
  issue = {2},
  pages = {021053},
  numpages = {45},
  year = {2024},
  month = {Jun},
  publisher = {American Physical Society},
  doi = {10.1103/PhysRevX.14.021053},
  url = {https://link.aps.org/doi/10.1103/PhysRevX.14.021053}
}
```

There is another followup [arXiv preprint](https://arxiv.org/abs/2608.14180):

```bibtex
@misc{Hao2026TopologicalPhases,
  title = {Topological phases and quantum criticality from {$SU(2)$} Chern--Simons--matter theories},
  author = {Hao, Yunchao and Li, Yingcheng and Li, Kangle and Zou, Liujun},
  year = {2026},
  month = {Aug},
  eprint = {2608.14180},
  archivePrefix = {arXiv},
  primaryClass = {cond-mat.str-el},
  doi = {10.48550/arXiv.2608.14180},
  url = {https://arxiv.org/abs/2608.14180}
}
```
