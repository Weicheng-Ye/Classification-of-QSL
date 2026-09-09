"""Print realization counts for the bundled UMTC examples, grouped by category."""
import json
from itertools import combinations
from pathlib import Path

from qsl_classification import classify

ROOT = Path(__file__).resolve().parent
OUTPUT = Path("validation/example-results.json")


def example_groups():
    chiral = ("p4*SO(3)", "p6*SO(3)")
    mirror = ("p4m*O(3)", "p6m*O(3)")
    for n in range(2, 11, 2):
        yield f"u1_{n}", chiral
    for nu in range(1, 16, 2):
        yield f"ising_nu{nu}", chiral
    for level in ("1", "2", "3", "4", "6", "_minus3"):
        yield f"su2_k{level}", chiral[:1]
    for name in ("z2_gauge", "z3_gauge", "z4_gauge", "double_semion",
                 "u1_4_x_u1_minus4", "toric_code"):
        yield name, mirror


def lattice_cases(group):
    multiplicities = {"a": 1, "b": 1, "c": 2} if group.startswith("p4") else {"a": 1, "c": 3}
    for size in range(len(multiplicities) + 1):
        for sites in combinations(multiplicities, size):
            yield "+".join(sites) or "0", [f"{multiplicities[s]} {s}" for s in sites]


def main():
    report = {}
    for category, groups in example_groups():
        print(f"\nUMTC: {category}", flush=True)
        report[category] = {}
        for group in groups:
            counts = {
                lattice: classify(group, iwps, ROOT / "examples" / f"{category}.json")["total_realizations"]
                for lattice, iwps in lattice_cases(group)
            }
            report[category][group] = counts
            widths = [max(len(lattice), len(f"{count:,}")) for lattice, count in counts.items()]
            print(f"  {group}")
            print("    Lattice       " + "  ".join(f"{label:>{width}}" for label, width in zip(counts, widths)))
            print("    Realizations  " + "  ".join(f"{count:>{width},}" for count, width in zip(counts.values(), widths)), flush=True)

    output = ROOT / OUTPUT
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(f"\nSaved realization counts to {OUTPUT.as_posix()}")


if __name__ == "__main__":
    main()
