import argparse
import json
from . import classify


def main():
    p = argparse.ArgumentParser(description="Classify UMTC symmetry enrichment")
    p.add_argument("symmetry_group")
    p.add_argument("umtc_json_file")
    p.add_argument("--iwp", action="append", default=[])
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--output")
    args = p.parse_args()
    result = classify(args.symmetry_group,args.iwp,args.umtc_json_file,args.verbose)
    text = json.dumps(result,indent=2,allow_nan=False)+"\n"
    if args.output:
        with open(args.output,"w",encoding="utf-8") as f:
            f.write(text)
    else:
        print(text,end="")


if __name__ == "__main__":
    main()
