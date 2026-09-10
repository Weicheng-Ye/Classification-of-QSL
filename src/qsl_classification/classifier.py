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
from .wallpaper_indicators import WallpaperAnomalySystem
from .symbols import EtaSymbol


class Analysis:
    def __init__(self, engine, space, images):
        self.collector = ExtensionCollector(space,engine.module,engine.intrinsic,images)
        self.quotient = self.collector.cohomology()
        anomaly_class = AnomalySystem if space.legacy_indicators else WallpaperAnomalySystem
        self.anomalies = anomaly_class(self.collector,self.quotient,engine.weights)
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
        letters = space.lattice_keys
        self.parities = [dict(zip(letters,bits)) for bits in product((0,1),repeat=len(letters))]
        self.lattice_keys = letters
        self.sectors = {}

    def coordinates(self, ids):
        return (np.asarray(ids,dtype=np.int64)[:,None] // self.strides) % self.orders

    def enumerate(self):
        if self.sectors:
            return
        if self.quotient.size > 2**20 and all(not (int(m) & (int(m)-1)) for m in self.orders):
            return self.enumerate_binary()
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
            self.sectors[tuple(p[x] for x in self.lattice_keys)] = (np.concatenate(parts),raw)

    def enumerate_binary(self):
        from .quadratic_solver import binary_solutions, binary_encoding
        model = binary_encoding(self.quadratic,self.orders)
        for parity in self.parities:
            target = self.anomalies.target(parity)
            ids = np.fromiter(binary_solutions(model,target),dtype=np.int64)
            ids.sort()
            raw = len(ids)
            kept=[]
            for start in range(0,len(ids),65536):
                batch=ids[start:start+65536]
                coords=self.coordinates(batch)
                canonical=np.ones(len(batch),dtype=bool)
                for transform in self.relabelings:
                    moved=(coords @ transform.T) % self.orders
                    canonical &= batch <= moved @ self.strides
                kept.append(batch[canonical])
            self.sectors[tuple(parity[x] for x in self.lattice_keys)] = (
                np.concatenate(kept) if kept else np.array([],dtype=np.int64),raw)


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


def classify(symmetry_group: str | int, iwps: list[str], umtc_json_file: str | Path,
             *positional, time_reversal: bool | None = None, verbose: bool | None = None) -> dict:
    """Return a JSON-compatible dictionary of anomaly-matched SET realizations.

    WPs use Bilbao's conventional-cell letters and multiplicities. Each entry
    occupies one half-odd-integer-spin orbit. IT numbers 1–17 default to an
    independent T; use time_reversal=False to omit it. A group suffix SO(3)
    or O(3) explicitly selects SO(3) or SO(3) × Z₂ᵀ. All literal graded
    homomorphisms are returned; the total counts one representative of each
    unitary intrinsic-conjugacy orbit. SPT stacking is not counted.
    """
    if len(positional) > 2:
        raise TypeError('Expected time_reversal and verbose after the three required arguments')
    if positional:
        legacy = (isinstance(symmetry_group,str) and 'O(3)' in symmetry_group
                  and SpaceGroup.parse(symmetry_group).legacy_indicators)
        if len(positional) == 1 and legacy:
            if verbose is not None:
                raise TypeError('verbose was provided twice')
            verbose = positional[0]
        else:
            if time_reversal is not None:
                raise TypeError('time_reversal was provided twice')
            time_reversal = positional[0]
            if len(positional) == 2:
                if verbose is not None:
                    raise TypeError('verbose was provided twice')
                verbose = positional[1]
    if verbose is None:
        verbose = False
    if type(verbose) is not bool:
        raise TypeError("verbose must be a boolean")
    space = SpaceGroup.parse(symmetry_group,time_reversal)
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
        ids, raw = analysis.sectors[tuple(parity[x] for x in space.lattice_keys)]
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
    result = {"schema_version": 1, "symmetry_group": space.name, "iwps": list(iwps),
            "lattice_homotopy_class": "+".join(k for k in space.lattice_keys if parity[k]) or "0",
            "umtc": {"name": engine.category.name, "sha256": digest},
            "conventions": {"crystalline_antiunitary_parity": "mirror + time_reversal (mod 2)",
                            "counting": "modulo coboundaries and unitary intrinsic anyon relabeling; SPT stacking excluded",
                            "intrinsic_symmetry": "the full coherent intrinsic group supplied in the input JSON",
                            "spin_rotations": "continuous SO(3); identity image in the finite intrinsic group"},
            "number_of_homomorphisms": len(homs),
            "number_of_inequivalent_homomorphisms": len({r['equivalent_to'] for r in records}),
            "total_realizations": total, "homomorphisms": records}
    if not space.legacy_indicators:
        result.update(it_number=space.number,time_reversal=space.time_reversal,
                      wyckoff_convention="Bilbao standard conventional-cell setting",
                      lattice_coordinates=parity)
    return result
