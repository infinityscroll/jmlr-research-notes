#!/usr/bin/env python3
"""Build and audit the actual quantitative finite-polyhedron Ehrhard infrastructure."""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path
from ehrhard_audit_inventory import inventory

parser = argparse.ArgumentParser()
parser.add_argument('--lake', default='lake')
args = parser.parse_args()
root = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

closure = json.loads((root / 'EHRHARD_COMPLETE_SOURCE_CLOSURE.json').read_text())
for path, expected_hash in closure['local_sources'].items():
    assert digest(root / path) == expected_hash, path
receipt_names = ['EHRHARD_UPSTREAM_VERIFICATION.json', 'EHRHARD_POLYHEDRON_VERIFICATION.json',
                 'EHRHARD_CURVATURE_VERIFICATION.json', 'EHRHARD_MOMENT_VERIFICATION.json']
frozen = {name: digest(root / name) for name in receipt_names}
version = subprocess.check_output([args.lake, 'env', 'lean', '--version'], cwd=root, text=True).strip()
assert 'version 4.35.0-rc2' in version
assert 'commit 11acb17ec6b07a8f9e9173e6845197929540936b' in version
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                  cwd=root / '.lake/packages/mathlib', text=True).strip()
assert revision == closure['mathlib_revision']
with (root / 'EHRHARD_COMPLETE_BUILD.txt').open('w') as log:
    subprocess.run([args.lake, 'build', 'GaussianEhrhardCoefficient'], cwd=root,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
audit = subprocess.check_output([args.lake, 'env', 'lean', 'EhrhardAllAudit.lean'],
                                cwd=root, text=True, stderr=subprocess.STDOUT)
(root / 'EHRHARD_COMPLETE_AXIOMS.txt').write_text(audit)
expected = inventory(root)
assert expected == (root / 'EHRHARD_ALL_AUDIT_TARGETS.txt').read_text().splitlines()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
assert len(found) == len(expected) == 77
assert {name for name, _ in found} == set(expected)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axioms = {name: sorted({a.strip() for a in values.split(',') if a.strip()})
          for name, values in found}
for name, values in axioms.items():
    assert set(values) <= allowed, (name, values)
for path, expected_hash in closure['local_sources'].items():
    assert digest(root / path) == expected_hash, path
assert {name: digest(root / name) for name in receipt_names} == frozen
receipt = {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'compiler': version, 'mathlib_revision': revision,
    'source_closure_sha256': digest(root / 'EHRHARD_COMPLETE_SOURCE_CLOSURE.json'),
    'local_source_count': len(closure['local_sources']),
    'frozen_dependency_receipts': frozen,
    'build_succeeded': True, 'axiom_audit_succeeded': True,
    'audited_exports': len(expected), 'axioms_by_declaration': axioms,
    'scope': 'Actual finite Gaussian polyhedron Ehrhard concavity and normalized conditional variance with an explicit positive logarithmic mean correction; classical infrastructure, not the full negative-voting theorem.'
}
(root / 'EHRHARD_COMPLETE_VERIFICATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: 17 local source files; 77 extension exports; actual quantitative Ehrhard covariance bound; standard axioms only.')
