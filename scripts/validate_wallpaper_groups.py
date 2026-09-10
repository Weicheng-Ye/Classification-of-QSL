"""Reproduce the v0.2.0 all-wallpaper example regression (884 cases)."""
import argparse
import json
from pathlib import Path
from qsl_classification import classify, wallpaper_groups


def main():
    root=Path(__file__).resolve().parents[1]
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--category',action='append')
    args=parser.parse_args()
    baseline=json.loads((root/'tests/fixtures/v0_2_0_wallpaper.json').read_text())
    if args.category and set(args.category)-baseline.keys():
        parser.error('Unknown category: '+', '.join(sorted(set(args.category)-baseline.keys())))
    checked=0
    errors=[]
    for category,settings in baseline.items():
        if args.category and category not in args.category:
            continue
        for time_reversal in (False,True):
            expected=settings['with_time_reversal' if time_reversal else 'without_time_reversal']
            for info,reference in zip(wallpaper_groups(),expected):
                result=classify(info['it_number'],[],root/'examples'/(category+'.json'),
                                time_reversal=time_reversal)
                observed={'homomorphisms':result['number_of_homomorphisms'],
                          'realizations':result['total_realizations']}
                if observed != reference:
                    errors.append((category,info['name'],time_reversal,reference,observed))
                checked+=1
        print(f'{category}: checked all 34 settings',flush=True)
    for error in errors:
        print('FAIL',error)
    print(f'{checked-len(errors)}/{checked} cases match the v0.2.0 regression.')
    raise SystemExit(bool(errors))


if __name__=='__main__':
    main()
