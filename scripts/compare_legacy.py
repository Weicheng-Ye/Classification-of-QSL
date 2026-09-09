"""Compare the provided original Z2 implementation, by permutation pattern."""
import argparse
import importlib.util
import json
from pathlib import Path
from qsl_classification import classify
from validate_papers import lattice_cases


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--original',type=Path,default=Path.home()/'Downloads/Classification-of-QSL-Main/python/Z2TO.py')
    p.add_argument('--examples',type=Path,default=Path(__file__).resolve().parents[1]/'examples')
    args=p.parse_args()
    spec=importlib.util.spec_from_file_location('legacy_z2',args.original)
    old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
    rows=[]
    for n in (6,4):
        lattice=list(lattice_cases(n))
        results=[classify(f'p{n}m*O(3)',iwps,args.examples/'z2_gauge.json') for _,iwps in lattice]
        get_action=old.get_p6mO3_ActionList if n==6 else old.get_p4m_ActionList
        generate=old.p6mO3Generate if n==6 else old.p4mO3Generate
        for i in range(1,9 if n==6 else 17):
            action=get_action(i)
            # In the supplied z2_gauge gauge, S and T swap e,m; S*T fixes them.
            names=['C6','M','T'] if n==6 else ['T1','C4','M','T']
            match=lambda h: [int(h['generator_images'][name] in ('S','T')) for name in names]==action
            observed=[next(h['number_of_realizations'] for h in r['homomorphisms'] if match(h)) for r in results]
            expected=list(map(len,generate(i,[h for h,_ in lattice])))
            row=dict(group=f'p{n}m*O(3)',legacy_action=i,permutation=action,lattice_order=[h for h,_ in lattice],
                     expected=expected,observed=observed,passed=observed==expected)
            rows.append(row)
            print(('PASS' if row['passed'] else 'FAIL'),row['group'],i,observed,flush=True)
    report=dict(passed=all(r['passed'] for r in rows),patterns=len(rows),cases=sum(len(r['expected']) for r in rows),comparisons=rows)
    output=Path('validation/legacy-z2.json')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+'\n')
    if not report['passed']:raise SystemExit(1)


if __name__=='__main__':main()
