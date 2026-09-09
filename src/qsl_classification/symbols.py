"""JSON-reconstructible eta functions, including a section of SU(2) -> SO(3)."""
import math
import numpy as np
from umtc import load_json
from .groups import SpaceGroup, Intrinsic
from .algebra import AnyonModule
from .extensions import ExtensionCollector


def quaternion(q):
    if len(q) != 4 or any(not math.isfinite(float(x)) for x in q):
        raise ValueError("SO(3) spin rotation is a finite unit quaternion [w,x,y,z]")
    norm = math.sqrt(sum(float(x)**2 for x in q))
    if not norm:
        raise ValueError("A zero quaternion is not a rotation")
    q = tuple(float(x)/norm for x in q)
    sign = next((1 if x > 0 else -1 for x in q if abs(x) > 1e-12), 1)
    return tuple(sign*x for x in q)


def spin_cocycle(q, r):
    a, b, c, d = quaternion(q)
    e, f, g, h = quaternion(r)
    p = (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
         a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)
    return int(next(x for x in p if abs(x) > 1e-12) < 0)


def parse_element(space, g):
    if isinstance(g, dict):
        unknown = set(g)-{"translation", "rotation", "mirror", "time_reversal", "spin"}
        if unknown:
            raise ValueError(f"Unknown group-element fields: {sorted(unknown)}")
        xy = g.get("translation", [0, 0])
        if len(xy) != 2:
            raise ValueError("translation must have two integer coordinates")
        e = space.element(*xy, g.get("rotation", 0), g.get("mirror", 0), g.get("time_reversal", 0))
        return e, quaternion(g.get("spin", [1, 0, 0, 0]))
    if len(g) != len(space.names):
        raise ValueError(f"Use {len(space.names)} wallpaper coordinates or an element dictionary")
    return space.element(*g), (1., 0., 0., 0.)


class EtaSymbol:
    def __init__(self, collector, parameters):
        self.collector = collector
        self.parameters = np.asarray(parameters, dtype=np.int64)
        self.space = collector.space
        self.module = collector.module
        self.intrinsic = collector.intrinsic

    def __call__(self, a, g, h):
        if isinstance(a, list):
            a = tuple(a)
        if a not in self.module.category.anyons:
            raise ValueError(f"Unknown anyon {a!r}")
        g, q = parse_element(self.space, g)
        h, r = parse_element(self.space, h)
        c = self.collector.cocycle_matrix(g, h) @ self.parameters
        c += spin_cocycle(q, r) * (self.collector.spin @ self.parameters)
        b = self.module.label(c)
        s = self.intrinsic.sym
        ref = s.eta(a, self.intrinsic.word(self.collector.images, g),
                    self.intrinsic.word(self.collector.images, h)) if s else 1
        return complex(ref * self.module.braiding[a, b])

    def to_json(self):
        c = self.collector
        d = self.module.rank
        return {"type": "qsl_eta_v1", "symmetry_group": self.space.name,
                "generator_images": dict(zip(self.space.names, c.images)),
                "relation_values": [{"relation": name, "anyon": self.module.label(self.parameters[i*d:(i+1)*d])}
                                    for i, name in enumerate(c.names)],
                "formula": "eta_ref(a,phi(g),phi(h))*M(a,t(g,h)); t from lifted relations plus spin_anyon*w2"}


def eta_from_json(descriptor, umtc_json_file):
    """Reconstruct eta(a,g,h) from its JSON descriptor. No code is evaluated."""
    if descriptor.get("type") != "qsl_eta_v1":
        raise ValueError("Unknown eta descriptor type")
    category = load_json(umtc_json_file) if not hasattr(umtc_json_file, "anyons") else umtc_json_file
    space = SpaceGroup.parse(descriptor["symmetry_group"])
    intrinsic = Intrinsic(category)
    module = AnyonModule(category, intrinsic)
    images = tuple(descriptor["generator_images"][g] for g in space.names)
    if images not in set(intrinsic.homomorphisms(space)):
        raise ValueError("The descriptor has an invalid graded homomorphism")
    c = ExtensionCollector(space, module, intrinsic, images)
    records = descriptor["relation_values"]
    if [r["relation"] for r in records] != c.names:
        raise ValueError("The descriptor has incomplete or reordered relations")
    values = [module.coords[tuple(r["anyon"]) if isinstance(r["anyon"], list) else r["anyon"]] for r in records]
    parameters = np.array(values, dtype=np.int64).reshape(-1)
    if module.rank:
        C, mods = c.equations()
        if np.any((C @ parameters) % np.array(mods)):
            raise ValueError("The descriptor does not define a consistent cocycle")
    return EtaSymbol(c, parameters)
