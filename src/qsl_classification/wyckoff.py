"""Standard Bilbao/International Tables plane-group Wyckoff positions.

Multiplicities refer to the conventional cell, including centring for cm
and cmm. The last field is the occupied orbit's Z2 lattice-homotopy vector
in the degree-two surface basis documented in docs/. Generic positions
are included: in particular pg's general 2a orbit is nontrivial.

Tables cross-checked against Hicks et al., AFLOW Library of Crystallographic
Prototypes, Part 2, section 4, doi:10.1016/j.commatsci.2018.10.043.
"""
import re

# (multiplicities in alphabetical order, nonzero surface coordinate per WP).
TABLES = {
    1: ((1,), (1,)),
    2: ((1,1,1,1,2), (1,3,2,4,0)),
    3: ((1,1,2), (1,2,0)),
    4: ((2,), (1,)),
    5: ((2,4), (1,0)),
    6: ((1,1,1,1,2,2,2,2,4), (1,4,3,2,0,0,0,0,0)),
    7: ((2,2,2,4), (1,2,3,0)),
    8: ((2,2,4), (1,2,0)),
    9: ((2,2,4,4,4,8), (1,2,3,0,0,0)),
    10: ((1,1,2,4), (1,2,3,0)),
    11: ((1,1,2,4,4,4,8), (1,2,3,0,0,0,0)),
    12: ((2,2,4,8), (1,2,0,0)),
    13: ((1,1,1,3), (1,1,1,1)),
    14: ((1,1,1,3,6), (1,1,1,1,0)),
    15: ((1,2,3,6), (1,0,1,0)),
    16: ((1,2,3,6), (1,0,2,0)),
    17: ((1,2,3,6,6,12), (1,0,2,0,0,0)),
}


def positions(number):
    multiplicities, coordinates = TABLES[number]
    return {chr(97+i): {'multiplicity': m, 'lsm_coordinate': j}
            for i,(m,j) in enumerate(zip(multiplicities,coordinates))}


def lattice_class(space, wps):
    if not isinstance(wps,(list,tuple)):
        raise ValueError("WPs must be a list, e.g. ['1 a', '1 b']")
    table = positions(space.number)
    parity = dict.fromkeys(space.lattice_keys,0)
    for item in wps:
        match = re.fullmatch(r'\s*(\d+)?\s*([a-z])\s*',item) if isinstance(item,str) else None
        if not match or match[2] not in table or (match[1] and int(match[1]) != table[match[2]]['multiplicity']):
            expected = ', '.join(f"{p['multiplicity']}{a}" for a,p in table.items())
            raise ValueError(f'Invalid WP {item!r} for {space.name}; Bilbao positions: {expected}')
        coordinate = table[match[2]]['lsm_coordinate']
        if coordinate:
            parity[space.lattice_keys[coordinate-1]] ^= 1
    return parity
