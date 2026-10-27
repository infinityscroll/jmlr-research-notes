#!/usr/bin/env python3
"""Run finite research checks in an isolated temporary copy; no third-party packages.

Certificate equality checks reproducibility of saved finite calculations. It is
not a formal verification of the analytical theorems or a novelty assessment.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--only', action='append', default=[], metavar='NAME')
    parser.add_argument('--timeout', type=float, default=120.0,
                        help='seconds allowed for each individual checker (default 120)')
    args = parser.parse_args()
    cases = json.loads((HERE / 'REPRODUCTION_CASES.json').read_text())
    if args.list:
        for case in cases:
            print(case['name'] + ': ' + case['checker'])
        return 0
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    unknown = set(args.only) - {case['name'] for case in cases}
    if unknown:
        parser.error('unknown check names: ' + ', '.join(sorted(unknown)))
    manifest = json.loads((HERE / 'PROVENANCE.json').read_text())
    for record in manifest['files']:
        if digest(HERE / record['path']) != record['staged_sha256']:
            raise RuntimeError('Publication source hash mismatch: ' + record['path'])
    selected = [c for c in cases if not args.only or c['name'] in args.only]
    results = []
    with tempfile.TemporaryDirectory(prefix='research-check-') as temp:
        checkout = Path(temp) / HERE.name
        shutil.copytree(HERE, checkout, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        for case in selected:
            relative = Path(case['checker'])
            certificate = relative.parent / case['certificate']
            original = json.loads((HERE / certificate).read_text())
            # Remove the copied certificate first: a checker must regenerate it.
            (checkout / certificate).unlink()
            started = time.monotonic()
            run = subprocess.run([sys.executable, '-B', str(checkout / relative)],
                                 cwd=checkout, capture_output=True, text=True,
                                 timeout=args.timeout, check=False)
            if run.returncode:
                raise RuntimeError(case['name'] + ' failed: ' + run.stderr[-4000:]
                                   + run.stdout[-1000:])
            generated = json.loads((checkout / certificate).read_text())
            if generated != original:
                keys = sorted(set(original) | set(generated))
                changed = [key for key in keys if original.get(key) != generated.get(key)]
                raise RuntimeError(case['name'] + ': regenerated certificate differs in '
                                   + ', '.join(changed))
            elapsed = time.monotonic() - started
            print('PASS ' + case['name'], file=sys.stderr, flush=True)
            results.append({'name': case['name'], 'checker': case['checker'],
                            'certificate': str(certificate),
                            'certificate_sha256': digest(HERE / certificate),
                            'exact_saved_certificate_match': True,
                            'seconds': round(elapsed, 3)})
    print(json.dumps({'status': 'PASS', 'python': sys.version.split()[0],
                      'scope': 'Finite checks and unchanged source hashes; not formal theorem verification.',
                      'sources_verified': len(manifest['files']), 'checks': results}, indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
