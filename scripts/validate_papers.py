"""Independent reference counts from the two papers; no expected data enter classify."""
import argparse
import json
from itertools import combinations
from math import gcd
from pathlib import Path
import time
from qsl_classification import classify


def lattice_cases(n):
    letters = 'abc' if n == 4 else 'ac'
    for k in range(len(letters)+1):
        for subset in combinations(letters,k):
            yield '+'.join(subset) or '0', [f"{({'a':1,'b':1,'c':2} if n == 4 else {'a':1,'c':3})[s]} {s}" for s in subset]


def references():
    # Ye-Zou Table V, including the breakdown by permutation pattern.
    for N in range(1,6):
        for n in (4,6):
            for homotopy,iwps in lattice_cases(n):
                if N == 1:
                    expected = [9 if n == 4 else 5] if homotopy == '0' else [1]
                elif n == 6:
                    q = N*gcd(N,3)
                    if N % 2:
                        expected = [5*(q+1)//2,5] if homotopy == '0' else [(q+1)//2,1]
                    else:
                        expected = [5*q//2+3,8] if homotopy == '0' else [q//2+int(homotopy=='a+c'),0]
                elif N % 2:
                    expected = [9*(N+1)//2,9,9,9] if homotopy == '0' else [(N+1)//2,1,1,1]
                else:
                    expected = {'0':[9*N+6,12,20,20], 'a':[N,0,4,0], 'b':[N,0,0,4],
                                'c':[N+2,4,0,0]}.get(homotopy,[N,0,0,0])
                yield f'u1_{2*N}', f'p{n}*SO(3)', homotopy, iwps, sum(expected), expected, '2309.15118 Table V'
    # Ye-Zou Sec. VII: all eight Ising chiralities.
    for nu in range(1,16,2):
        for n in (4,6):
            for homotopy,iwps in lattice_cases(n):
                expected = 2**(4 if n == 4 else 3) if homotopy == '0' else 0
                yield f'ising_nu{nu}',f'p{n}*SO(3)',homotopy,iwps,expected,[expected],'2309.15118 Sec. VII'
    # Hao et al. Sec. II B 4 / Eq. (26).
    for k in (1,2,3,4,6,-3):
        for homotopy,iwps in lattice_cases(4):
            per = (9 if homotopy == '0' else 1) if k % 2 else (16 if homotopy == '0' else 0)
            expected = [per]*(4 if k == 6 else 1)
            yield f"su2_k{'_minus'+str(-k) if k < 0 else k}",'p4*SO(3)',homotopy,iwps,sum(expected),expected,'2608.14180 Sec. II B 4'
    # Ye-Zou Table X, columns Z2, Z3, Z4, doubled U1_2, doubled U1_4.
    names = ['z2_gauge','z3_gauge','z4_gauge','double_semion','u1_4_x_u1_minus4']
    tables = {
        6: {'0':[336,8,16453,32,144], 'a':[8,0,70,0,0], 'c':[8,0,70,0,0], 'a+c':[4,0,82,0,0]},
        4: {'0':[3653,9,886740,128,1344], 'a':[64,0,5008,0,0], 'b':[64,0,5008,0,0],
            'c':[64,0,8872,0,0], 'a+b':[16,0,636,0,0], 'a+c':[16,0,656,0,0],
            'b+c':[16,0,656,0,0], 'a+b+c':[8,0,318,0,0]}}
    for name_index,name in enumerate(names):
        for n in (4,6):
            for homotopy,iwps in lattice_cases(n):
                yield name,f'p{n}m*O(3)',homotopy,iwps,tables[n][homotopy][name_index],None,'2309.15118 Table X'
    for n in (4,6):
        for homotopy,iwps in lattice_cases(n):
            yield 'toric_code',f'p{n}m*O(3)',homotopy,iwps,tables[n][homotopy][0],None,'2309.15118 Table X (alternate gauge)'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--examples',type=Path,default=Path(__file__).resolve().parents[1]/'examples')
    parser.add_argument('--output',type=Path,default=Path('validation/papers.json'))
    parser.add_argument('--category',action='append')
    args = parser.parse_args()
    rows = []
    start = time.monotonic()
    for name,group,lattice,iwps,expected,patterns,source in references():
        if args.category and name not in args.category:
            continue
        t = time.monotonic()
        result = classify(group,iwps,args.examples/(name+'.json'))
        observed = result['total_realizations']
        counts = [h['number_of_realizations'] for h in result['homomorphisms'] if h['id']==h['equivalent_to']]
        ok = observed==expected and (patterns is None or counts==patterns)
        rows.append(dict(category=name,group=group,lattice=lattice,source=source,expected=expected,
                         observed=observed,expected_per_homomorphism=patterns,
                         observed_per_homomorphism=counts,passed=ok,seconds=round(time.monotonic()-t,3)))
        print(f"{'PASS' if ok else 'FAIL'} {name} {group} [{lattice}] {observed} expected {expected}",flush=True)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps({'complete':False,'cases':rows},indent=2)+'\n')
    report = {'complete':True,'passed':all(r['passed'] for r in rows),'case_count':len(rows),
              'seconds':round(time.monotonic()-start,3),'cases':rows}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    if not report['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
