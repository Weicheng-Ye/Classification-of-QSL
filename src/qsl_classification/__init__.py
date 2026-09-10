"""Category-independent classification of lattice symmetry enrichment."""
from .classifier import classify
from .symbols import EtaSymbol, eta_from_json
from .indicators import IndicatorError
from .groups import WALLPAPER_NAMES, BILBAO_NAMES, SpaceGroup
from .wyckoff import positions

__version__ = "0.2.0"


def wallpaper_groups():
    """Return the 17 IT numbers, aliases, generator orders, and Bilbao WPs."""
    return [{"it_number":i,"name":name,"bilbao_name":bilbao,
             "wyckoff_positions":positions(i),
             "generators":list(SpaceGroup(number=i,time_reversal=False).names)}
            for i,(name,bilbao) in enumerate(zip(WALLPAPER_NAMES,BILBAO_NAMES),1)]

__all__ = ["classify", "EtaSymbol", "eta_from_json", "IndicatorError", "wallpaper_groups"]
