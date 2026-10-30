#!/usr/bin/env python3
"""Verify this release and run its independent exact-algebra checkers."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    for entry in manifest['files']:
        path = (root / entry['path']).resolve()
        if root not in path.parents:
            raise RuntimeError('Manifest path escapes release directory')
        if sha256(path) != entry['sha256']:
            raise RuntimeError('SHA256 mismatch: ' + entry['path'])

    with tempfile.TemporaryDirectory(prefix='gaussian_covariance_review_') as td:
        work = Path(td)
        scripts = ['check_simplex_chain_exact.py', 'check_chain_geometry.py']
        results = []
        for name in scripts:
            path = work / name
            shutil.copyfile(root / 'checks' / name, path)
            run = subprocess.run([sys.executable, str(path)], cwd=work,
                                 capture_output=True, text=True, timeout=600)
            if run.returncode:
                raise RuntimeError(name + ' failed:\n' + run.stdout + run.stderr)
            results.append(json.loads(run.stdout))
        symbolic, fractions = results
        if symbolic['status'] != 'PASS' or fractions['status'] != 'PASS':
            raise RuntimeError('Checker did not report PASS')
        local = sum(case['local_entry_checks'] for case in symbolic['cases'])
        global_entries = sum(case['identity_entries'] for case in symbolic['cases'])
        if (local, global_entries, fractions['check_count']) != (882, 1742, 96):
            raise RuntimeError('Unexpected checker coverage')
        fraction_full = json.loads((work / 'CHAIN_GEOMETRY_CHECKS.json').read_text())
        if len(fraction_full['fixtures']) != 12:
            raise RuntimeError('Unexpected fixture count')

    report = {
        'status': 'PASS',
        'python': platform.python_version(),
        'manifest_sha256': sha256(root / 'MANIFEST.json'),
        'verified_files': len(manifest['files']),
        'sympy': {'local_entries': local, 'global_entries': global_entries,
                  'dimensions': [case['d'] for case in symbolic['cases']]},
        'fractions': {'checks': 96, 'fixtures': 12, 'dimensions': list(range(2, 8))},
        'limits': 'Finite exact algebra corroboration; not formal verification of the analytic theorem.',
    }
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output:
        destination = args.output.resolve()
        if destination == root or root in destination.parents:
            raise RuntimeError('Choose an output path outside the release directory')
        destination.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
