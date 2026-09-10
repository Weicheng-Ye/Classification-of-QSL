"""Print realization counts for all 17 wallpaper groups, with and without T."""
import argparse
from pathlib import Path
from qsl_classification import classify, wallpaper_groups


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('umtc',nargs='?',type=Path,
                        default=Path(__file__).resolve().parent/'examples/toric_code.json')
    args=parser.parse_args()
    print(f'UMTC: {args.umtc.stem}')
    print(f"{'IT':>3}  {'Group':<6} {'SO(3)':>14} {'SO(3) x T':>14}")
    for group in wallpaper_groups():
        number=group['it_number']
        counts=[classify(number,[],args.umtc,time_reversal=tr)['total_realizations']
                for tr in (False,True)]
        print(f"{number:>3}  {group['name']:<6} {counts[0]:>14,d} {counts[1]:>14,d}")


if __name__=='__main__':
    main()
