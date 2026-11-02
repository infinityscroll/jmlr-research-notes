#!/usr/bin/env python3
"""Verify the attributed Mulgund comparator and its explicit statement bridge."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGETS = ['WeakSimplex.lowerOrthant_ge_iid',
           'NegativeVotingDependencies.equalThreshold_gaussian_comparison']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument("--write-evidence", action="store_true", help="Update saved receipts and transcripts; default verification is read-only")
    args = parser.parse_args()
    if Path(args.lake).is_absolute():
        os.environ['PATH'] = str(Path(args.lake).parent) + os.pathsep + os.environ.get('PATH', '')
    provenance = json.loads((ROOT / 'MULGUND_PROVENANCE.json').read_text())
    transcript = []

    def run(command):
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        transcript.append(result.stdout)
        print(result.stdout, end='', flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
        return result.stdout

    observed_lean = run([args.lake, 'env', 'lean', '--version']).strip()
    version = provenance['lean'].split(':v', 1)[1]
    if 'version ' + version + ',' not in observed_lean:
        raise SystemExit('Actual Lean version differs from provenance')
    if (ROOT / 'lean-toolchain').read_text().strip() != provenance['lean']:
        raise SystemExit('Toolchain pin differs from provenance')
    observed_mathlib = run(['git', '-C', str(ROOT / '.lake/packages/mathlib'),
                           'rev-parse', 'HEAD']).strip()
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    revisions = [p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib']
    if observed_mathlib != provenance['mathlib'] or revisions != [provenance['mathlib']]:
        raise SystemExit('Actual mathlib checkout or manifest differs from provenance')

    def check_sources():
        for item in provenance['sources']:
            if digest(ROOT / item['path']) != item['sha256']:
                raise SystemExit('Changed active dependency source: ' + item['path'])
            if digest(ROOT / item['original_path']) != item['upstream_sha256']:
                raise SystemExit('Changed preserved upstream source: ' + item['original_path'])
        if digest(ROOT / 'MulgundGaussianComparison.lean') != provenance['bridge_sha256']:
            raise SystemExit('Changed independent statement bridge')
    check_sources()
    expected = 'import MulgundGaussianComparison\n\n' + ''.join(
        '#print axioms ' + name + '\n' for name in TARGETS)
    if (ROOT / 'AuditMulgund.lean').read_text() != expected:
        raise SystemExit('Audit source does not match the exact required endpoints')
    run([args.lake, 'build', 'MulgundGaussianComparison'])
    audit = run([args.lake, 'env', 'lean', 'AuditMulgund.lean'])
    found = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit):
        axioms = sorted(x.strip() for x in body.split(',') if x.strip())
        if name in found or not set(axioms) <= ALLOWED:
            raise SystemExit('Unexpected or duplicate axiom report: ' + name)
        found[name] = axioms
    if set(found) != set(TARGETS):
        raise SystemExit('Missing required endpoint axiom audit')
    check_sources()
    receipt = {'status': 'passed', 'upstream_repository': provenance['repository'],
               'upstream_commit': provenance['commit'], 'observed_lean': observed_lean,
               'observed_mathlib': observed_mathlib, 'audit': found,
               'sources': provenance['sources'], 'bridge_sha256': provenance['bridge_sha256'],
               'scope': 'External equal-threshold Gaussian comparison, not the negative-voting theorem'}
    if args.write_evidence:
        (ROOT / 'MULGUND_BUILD_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (ROOT / 'MULGUND_BUILD_TRANSCRIPT.txt').write_text(''.join(transcript))
    print('Mulgund comparator and exact statement bridge verified.')


if __name__ == '__main__':
    main()
