#!/usr/bin/env python3
"""Independent rerun of frozen source, preserving the original output files.

Run with the sibling hs_cert_venv/bin/python interpreter. The audited source
is executed from the exact text whose SHA256 is recorded, and unchanged
source hashes are checked again after execution.
"""
from pathlib import Path
import hashlib
import json
import sys
import types

base = Path(__file__).resolve().parent
sys.path.insert(0, str(base))
source_names = ['certify_facet_moment_hs.py', 'arb_facet_diagonal.py']
before = {name: (base/name).read_bytes() for name in source_names}
hashes = {name: hashlib.sha256(data).hexdigest() for name, data in before.items()}
mod = types.ModuleType('covariance_frozen_certificate')
mod.__file__ = str(base/source_names[0])
exec(compile(before[source_names[0]], mod.__file__, 'exec'), mod.__dict__)
mod.ROOT = base/'covariance_frozen_certificate_rerun'
mod.ROOT.mkdir(exist_ok=True)
mod.run()
assert all((base/name).read_bytes() == data for name, data in before.items())
output = json.loads((mod.ROOT/'facet_moment_certificate.json').read_text())
assert all(output['claims_verified_by_interval_comparison'].values())
notes = ['INDEPENDENT_CURVATURE_QUADRATURE_AND_FLOATING_AUDIT_20261101.txt',
         'covariance_audit_rational_quadrature_bounds.py', Path(__file__).name]
receipt = {
    'verdict': 'Accepted for the stated facet operator bounds under the audited binary64 arithmetic model; no global endpoint claim.',
    'source_sha256': hashes,
    'audit_sha256': {name: hashlib.sha256((base/name).read_bytes()).hexdigest() for name in notes},
    'source_unchanged_during_run': True,
    'numpy_version': mod.np.__version__,
    'float_rounds': sys.float_info.rounds,
    'float_epsilon': sys.float_info.epsilon,
    'independent_output': str(mod.ROOT.relative_to(base)/'facet_moment_certificate.json'),
    'total_HS_upper': output['total_HS_upper'],
    'delta_upper': output['delta_upper'],
    'mass_constrained_Rayleigh_upper': output['mass_constrained_Rayleigh_upper'],
    'claims_verified_by_interval_comparison': output['claims_verified_by_interval_comparison'],
}
(base/'covariance_frozen_certificate_audit_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
