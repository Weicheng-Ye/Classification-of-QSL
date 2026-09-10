import argparse
import json
from . import classify


def main():
    p = argparse.ArgumentParser(description="Classify UMTC symmetry enrichment")
    p.add_argument("symmetry_group",help="plane-group IT number 1–17 or wallpaper-group name")
    p.add_argument("umtc_json_file")
    p.add_argument("--wp","--iwp", dest="wps", action="append", default=[])
    p.add_argument("--time-reversal",action=argparse.BooleanOptionalAction,default=None)
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--output")
    args = p.parse_args()
    result = classify(args.symmetry_group,args.wps,args.umtc_json_file,
                      verbose=args.verbose,time_reversal=args.time_reversal)
    text = json.dumps(result,indent=2,allow_nan=False)+"\n"
    if args.output:
        with open(args.output,"w",encoding="utf-8") as f:
            f.write(text)
    else:
        print(text,end="")


if __name__ == "__main__":
    main()
