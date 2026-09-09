"""Public classifier and anyon-relabeling quotient."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import numpy as np
from umtc import load_json
from .groups import SpaceGroup, Intrinsic
from .algebra import AnyonModule
from .extensions import ExtensionCollector
from .indicators import TopologicalWeights, AnomalySystem
from .symbols import EtaSymbol


class Analysis:
    def __init__(self, engine, space, images):
        self.collector = ExtensionCollector(space,engine.module,engine.intrinsic,images)
        self.quotient = self.collector.cohomology()
        self.anomalies = AnomalySystem(self.collector,self.quotient,engine.weights)
        self.quadratic = self.anomalies.quadratic()
        self.orders = np.array(self.quotient.orders,dtype=np.int64)
        strides, stride = [], 1
        for m in self.orders:
            strides.append(stride)
            stride *= int(m)
        if stride > np.iinfo(np.int64).max:
            raise OverflowError("H² enumeration exceeds the 64-bit class index; use a smaller category")
        self.strides = np.array(strides,dtype=np.int64)
        self.relabelings = []
        for k in engine.intrinsic.unitary:
            if engine.intrinsic.conjugated(images,k) != images:
                continue
            transform = np.kron(np.eye(len(self.collector.names),dtype=np.int64),engine.module.actions[k])
            matrix = self.quotient.induced(transform)
            if np.array_equal(matrix % self.orders[:,None],np.eye(len(self.orders),dtype=np.int64) % self.orders[:,None]):
                continue
            if not any(np.array_equal(matrix,v) for v in self.relabelings):
                self.relabelings.append(matrix)
        letters = 'abc' if space.n == 4 else 'ac'
        self.parities = [dict(zip(letters,bits)) for bits in product((0,1),repeat=len(letters))]
        self.parities = [dict(a=p.get('a',0),b=p.get('b',0),c=p.get('c',0)) for p in self.parities]
        self.sectors = {}

    def coordinates(self, ids):
        return (np.asarray(ids,dtype=np.int64)[:,None] // self.strides) % self.orders

    def enumerate(self):
        if self.sectors:
            return
        targets = [np.array(self.anomalies.target(p),dtype=np.uint8) for p in self.parities]
        results = [[] for _ in targets]
        raw_counts = [0]*len(targets)
        for start in range(0,self.quotient.size,65536):
            ids = np.arange(start,min(start+65536,self.quotient.size),dtype=np.int64)
            coords = self.coordinates(ids)
            indicators = self.quadratic.evaluate(coords)
            canonical = np.ones(len(ids),dtype=bool)
            for transform in self.relabelings:
                moved = np.empty_like(coords)
                for j,row in enumerate(transform):
                    terms = np.flatnonzero(row)
                    moved[:,j] = sum((int(row[k])*coords[:,k] for k in terms),start=np.zeros(len(ids),dtype=np.int64)) % self.orders[j]
                canonical &= ids <= moved @ self.strides
            for i,target in enumerate(targets):
                matching = np.all(indicators == target,axis=1)
                raw_counts[i] += int(matching.sum())
                results[i].append(ids[matching & canonical])
        for p,parts,raw in zip(self.parities,results,raw_counts):
            self.sectors[tuple(p[x] for x in 'abc')] = (np.concatenate(parts),raw)


class Engine:
    def __init__(self, path):
        self.category = load_json(path)
        self.intrinsic = Intrinsic(self.category)
        self.module = AnyonModule(self.category,self.intrinsic)
        self.weights = TopologicalWeights(self.category,self.intrinsic)
        self.analyses = {}

    def analysis(self, space, images):
        key = (space,images)
        if key not in self.analyses:
            self.analyses[key] = Analysis(self,space,images)
        result = self.analyses[key]
        result.enumerate()
        return result


@lru_cache(maxsize=8)
def _engine(path, digest):
    return Engine(path)


def classify(symmetry_group: str, iwps: list[str], umtc_json_file: str | Path,
             verbose: bool = False) -> dict:
    """Return a JSON-compatible dictionary of anomaly-matched SET realizations.

    IWPs list occupied half-odd-integer-spin orbits. An empty list describes
    trivial lattice homotopy. O(3) means SO(3) × Z₂ᵀ. All literal graded
    homomorphisms are returned; the total counts one representative of each
    unitary intrinsic-conjugacy orbit. SPT stacking is not counted.
    """
    if type(verbose) is not bool:
        raise TypeError("verbose must be a boolean")
    space = SpaceGroup.parse(symmetry_group)
    parity = space.lattice(iwps)
    path = Path(umtc_json_file).expanduser().resolve()
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    engine = _engine(str(path),digest)
    intr = engine.intrinsic
    homs = list(intr.homomorphisms(space))
    indices = {h:i for i,h in enumerate(homs)}
    records = []
    total = 0
    for index,images in enumerate(homs):
        conjugates = [(indices[intr.conjugated(images,k)],k) for k in intr.unitary]
        representative = min(i for i,k in conjugates)
        rep_images = homs[representative]
        analysis = engine.analysis(space,rep_images)
        ids, raw = analysis.sectors[tuple(parity[x] for x in 'abc')]
        if index == representative:
            total += len(ids)
        record = {"id": f"h{index}", "generator_images": dict(zip(space.names,images)),
                  "SO3_image": intr.identity, "equivalent_to": f"h{representative}",
                  "fractionalization_group": {"cyclic_orders": list(analysis.quotient.orders),
                                               "order": analysis.quotient.size},
                  "number_of_fractionalization_classes": raw,
                  "number_of_realizations": len(ids)}
        if verbose:
            if index == representative:
                collector = analysis.collector
                transform = np.eye(collector.width,dtype=np.int64)
            else:
                k = next(k for k in intr.unitary if intr.conjugated(rep_images,k) == images)
                collector = ExtensionCollector(space,engine.module,intr,images)
                transform = np.kron(np.eye(len(collector.names),dtype=np.int64),engine.module.actions[k])
            record["realizations"] = []
            for class_id in ids:
                coordinates = analysis.coordinates([class_id])[0]
                parameters = transform @ analysis.quotient.lifts @ coordinates
                record["realizations"].append({"id": f"h{index}:r{int(class_id)}",
                                               "eta_symbol": EtaSymbol(collector,parameters).to_json()})
        records.append(record)
    return {"schema_version": 1, "symmetry_group": space.name, "iwps": list(iwps),
            "lattice_homotopy_class": "+".join(k for k in 'abc' if parity[k]) or "0",
            "umtc": {"name": engine.category.name, "sha256": digest},
            "conventions": {"crystalline_antiunitary_parity": "mirror + time_reversal (mod 2)",
                            "counting": "modulo coboundaries and unitary intrinsic anyon relabeling; SPT stacking excluded",
                            "intrinsic_symmetry": "the full coherent intrinsic group supplied in the input JSON",
                            "spin_rotations": "continuous SO(3); identity image in the finite intrinsic group"},
            "number_of_homomorphisms": len(homs),
            "number_of_inequivalent_homomorphisms": len({r['equivalent_to'] for r in records}),
            "total_realizations": total, "homomorphisms": records}
