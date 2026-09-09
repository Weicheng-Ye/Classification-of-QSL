"""Show that omitting the additional Z3 sectors recovers the printed counts.

This is a diagnostic of the discrepancy, not an alternative classify mode.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
from qsl_classification.classifier import _engine
from qsl_classification.groups import SpaceGroup
from validate_papers import lattice_cases


def main():
    rows=[]
    for filename,space in [('u1_6.json',SpaceGroup(6)),('z3_gauge.json',SpaceGroup(6,True))]:
        p=Path(__file__).resolve().parents[1]/'examples'/filename
        engine=_engine(str(p.resolve()),hashlib.sha256(p.read_bytes()).hexdigest())
        intr=engine.intrinsic;homs=list(intr.homomorphisms(space))
        reps=[]
        for h in homs:
            if any(intr.conjugated(h,k) in reps for k in intr.unitary):continue
            reps.append(h)
        for lattice,iwps in lattice_cases(6):
            target=tuple(space.lattice(iwps)[x] for x in 'abc')
            full=restricted=0
            for h in reps:
                analysis=engine.analysis(space,h)
                ids,_=analysis.sectors[target]
                full+=len(ids)
                # Table XI's C6 charge-conjugating sector includes only
                # elements killed by two. Table XIV's omitted Z3 sector is
                # the pattern with C6 charge conjugation and M=T.
                omit=(h[2]!=intr.identity and (not space.mirror or h[3]==h[4]))
                if omit:
                    coords=analysis.coordinates(ids)
                    restricted+=int(np.all((2*coords)%analysis.orders==0,axis=1).sum())
                else:
                    restricted+=len(ids)
            printed=(30 if lattice=='0' else 6) if not space.mirror else (8 if lattice=='0' else 0)
            assert restricted==printed
            rows.append(dict(category=filename,group=space.name,lattice=lattice,
                             full_count=full,without_extra_order_three_sector=restricted,printed_count=printed))
    output=Path('validation/paper-subsector.json')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps({'all_restricted_counts_match':True,'cases':rows},indent=2)+'\n')
    print(json.dumps(rows,indent=2))


if __name__=='__main__':main()
