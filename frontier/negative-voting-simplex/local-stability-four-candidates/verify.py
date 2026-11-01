"""Recompute the accepted local operator certificate without altering evidence."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def main():
    manifest = json.loads((ROOT/'PACKAGE_MANIFEST.json').read_text())
    for name, digest in manifest['files'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    provenance = json.loads((ROOT/'SOURCE_PROVENANCE.json').read_text())
    for record in provenance['unchanged_research_sources'].values():
        assert hashlib.sha256((ROOT/record['public_path']).read_bytes()).hexdigest() == record['sha256']
    original = (ROOT/'frozen_source/certify_facet_moment_hs.py').read_text()
    removed = "WORKSPACE=Path('/Users/sanjana/Documents/Codex/2026-08-15/cr')\nsys.path.insert(0,str(WORKSPACE/'tmp/astro_3i_audit_venv/lib/python3.9/site-packages'))\n"
    assert original.count(removed) == 1
    assert original.replace(removed, '') == (ROOT/'certify_facet_moment_hs.py').read_text()
    receipt = json.loads((ROOT/'covariance_frozen_certificate_audit_receipt.json').read_text())
    assert hashlib.sha256(original.encode()).hexdigest() == receipt['source_sha256']['certify_facet_moment_hs.py']
    assert hashlib.sha256((ROOT/'arb_facet_diagonal.py').read_bytes()).hexdigest() == receipt['source_sha256']['arb_facet_diagonal.py']
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='tetrahedral-exact-checks-') as temp:
        for name in ('certify_common_mass_box_rational_20261101.py',
                     'certify_operator_tail_rational_20261101.py',
                     'certify_tensor_moment_tail_rational_20261101.py',
                     'covariance_audit_rational_quadrature_bounds.py'):
            target = Path(temp)/name
            shutil.copy2(ROOT/name, target)
            subprocess.run([sys.executable, str(target)], check=True, capture_output=True, text=True, env=env)
    sys.path.insert(0, str(ROOT))
    spec = importlib.util.spec_from_file_location('tetrahedral_certificate', ROOT/'certify_facet_moment_hs.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    with tempfile.TemporaryDirectory(prefix='tetrahedral-certificate-') as temp:
        module.ROOT = Path(temp)
        with contextlib.redirect_stdout(io.StringIO()):
            module.run()
        result = json.loads((Path(temp)/'facet_moment_certificate.json').read_text())
        checks = result['claims_verified_by_interval_comparison']
        assert all(checks.values()), checks
        from flint import arb
        assert arb(result['total_HS_upper']) < arb(243)/8
        assert arb(result['delta_upper']) < arb(11)/400
        assert arb(result['mass_constrained_Rayleigh_upper']) < arb(17)/25
    print('PASS: source integrity, exact tails, arithmetic budget, mass box, and full operator certificate.')
    print('PASS: H < 243/8, delta < 11/400, constrained Rayleigh bound < 17/25.')
    print('The analytic theorem is a second-variation result; global optimality is not certified.')

if __name__ == '__main__':
    main()
