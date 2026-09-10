"""Frozen v0.1.0 outputs, including the five documented paper discrepancies."""
import hashlib
import json
from pathlib import Path
from qsl_classification import classify


def digest(result):
    return hashlib.sha256(json.dumps(result,sort_keys=True).encode()).hexdigest()


def test_all_276_v010_results_are_identical(examples):
    fixture=json.loads((Path(__file__).parent/'fixtures/v0_1_0.json').read_text())
    for case in fixture['cases']:
        result=classify(case['group'],case['wps'],examples/(case['category']+'.json'))
        assert digest(result)==case['result_sha256'], (case['category'],case['group'],case['wps'])


def test_v010_verbose_eta_descriptors_are_identical(examples):
    fixture=json.loads((Path(__file__).parent/'fixtures/v0_1_0.json').read_text())
    for case in fixture['verbose']:
        result=classify(case['group'],[],examples/(case['category']+'.json'),verbose=True)
        assert digest(result)==case['sha256'],case
