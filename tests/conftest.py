import os
from pathlib import Path
import pytest


@pytest.fixture(scope='session')
def examples():
    path = Path(os.environ.get('UMTC_EXAMPLES',Path(__file__).resolve().parents[1]/'examples'))
    if not path.is_dir():
        pytest.skip('Local examples are missing; set UMTC_EXAMPLES to an example directory')
    return path
