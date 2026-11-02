#!/usr/bin/env python3
"""Verify the pinned polyhedral, Ehrhard and singular-Schur dependencies.

Read-only by default. --write-evidence records fresh build/audit evidence.
The main first-party verifier separately audits all project theorem constants.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_COMMIT = '11acb17ec6b07a8f9e9173e6845197929540936b'
MATHLIB_COMMIT = '065356127b1dc0016f66b7283ce0ce2c4055aa55'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, expected: str) -> None:
    if sha(path) != expected:
        raise RuntimeError(f'Source hash mismatch: {path.relative_to(ROOT)}')


def run(args: list[str]) -> str:
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f'{args!r} failed:\n{p.stdout}')
    return p.stdout


def audit_print_output(output: str, expected: set[str]) -> None:
    seen: set[str] = set()
    for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        axioms = {a.strip() for a in values.split(',') if a.strip()}
        if not axioms <= ALLOWED:
            raise RuntimeError(f'Unexpected axioms for {name}: {sorted(axioms - ALLOWED)}')
        seen.add(name)
    seen.update(re.findall(r"'([^']+)' does not depend on any axioms", output))
    if seen != expected:
        raise RuntimeError(f'Audit inventory mismatch: {sorted(seen ^ expected)}')


def verify(lake: str, write_evidence: bool) -> dict:
    poly = ROOT / 'third_party/polyhedral-support'
    ehrhard = ROOT / 'third_party/openai-ehrhard'
    tau = ROOT / 'third_party/tauceti'
    pm = json.loads((poly / 'SOURCE_MANIFEST.json').read_text())
    for row in pm['modules']:
        check(poly / 'originals' / row['path'], row['sha256'])
        check(ROOT / row['path'], row['modern_final_sha256'])
    ep = json.loads((ehrhard / 'OPENAI-EHRHARD-PROVENANCE.json').read_text())
    for path, digest in ep['source_sha256'].items():
        check(ROOT / path, digest)
    tm = json.loads((tau / 'SOURCE_MANIFEST_DEDUPLICATED.json').read_text())
    tp = json.loads((tau / 'PORT_MANIFEST.json').read_text())
    for row in tm['files'] + tm['metadata']:
        check(tau / 'upstream_original' / row['path'], row['sha256'])
    for row in tp['files']:
        check(ROOT / row['path'], row['sha256'])
    for row in tp['backport_sources']:
        check(tau / row['path'], row['sha256'])

    version = run([lake, 'env', 'lean', '--version']).strip()
    if 'version 4.35.0-rc2' not in version or LEAN_COMMIT not in version:
        raise RuntimeError(f'Unexpected compiler: {version}')
    revision = run(['git', '-C', str(ROOT / '.lake/packages/mathlib'),
                    'rev-parse', 'HEAD']).strip()
    if revision != MATHLIB_COMMIT:
        raise RuntimeError(f'Unexpected mathlib revision: {revision}')
    build = run([lake, 'build', 'PolyhedralSupportBoundary',
                 'OAI.Probability.GaussianPropeller.SmoothedConcavity',
                 'TauCeti.Analysis.Matrix.SchurComplement'])
    pa = run([lake, 'env', 'lean', 'PolyhedralSupportAudit.lean'])
    expected_poly = set(json.loads((poly / 'POLYHEDRAL_SUPPORT_VERIFICATION.json')
                                  .read_text())['audited_endpoints'])
    audit_print_output(pa, expected_poly)
    ea = run([lake, 'env', 'lean', str(ehrhard / 'EhrhardUpstreamAudit.lean')])
    expected_ehrhard = set(json.loads((ehrhard / 'EHRHARD_UPSTREAM_VERIFICATION.json')
                                     .read_text())['audited_exports'])
    audit_print_output(ea, expected_ehrhard)
    ti = run([lake, 'env', 'lean', str(tau / 'isolated_Inventory.lean')])
    tc = set(re.findall(r'TC_CONSTANT (\S+)', ti))
    modules = set(re.findall(r'TC_MODULE (\S+)', ti))
    expected_modules = {r['path'][:-5].replace('/', '.') for r in tp['files']}
    if not tc or modules != expected_modules:
        raise RuntimeError('Tau Ceti compiled-module inventory mismatch')
    ta = run([lake, 'env', 'lean', str(tau / 'isolated_AxiomAudit.lean')])
    seen: set[str] = set()
    for line in ta.splitlines():
        if line.startswith('TC_AXIOM_JSON '):
            row = json.loads(line.removeprefix('TC_AXIOM_JSON '))
            if not set(row['axioms']) <= ALLOWED:
                raise RuntimeError(f'Unexpected Tau Ceti axioms: {row}')
            seen.add(row['constant'])
    if seen != tc:
        raise RuntimeError('Tau Ceti compiled-constant audit mismatch')
    receipt = {
        'status': 'passed', 'compiler': version, 'mathlib_revision': revision,
        'polyhedral_pinned_sources': len(pm['modules']),
        'polyhedral_audited_endpoints': len(expected_poly),
        'ehrhard_pinned_sources': len(ep['source_sha256']),
        'ehrhard_audited_exports': len(expected_ehrhard),
        'tauceti_pinned_source_modules': len(modules),
        'tauceti_compiled_constants_audited': len(tc),
        'allowed_axioms': sorted(ALLOWED),
        'scope': 'Attributed prerequisite proofs only; full negative-voting theorem remains unproved.',
    }
    if write_evidence:
        (ROOT / 'EXTENDED_DEPENDENCY_BUILD.txt').write_text(build)
        (ROOT / 'EXTENDED_DEPENDENCY_AXIOMS.txt').write_text(pa + ea + ti + ta)
        (ROOT / 'EXTENDED_DEPENDENCY_VERIFICATION.json').write_text(
            json.dumps(receipt, indent=2) + '\n')
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--write-evidence', action='store_true')
    args = parser.parse_args()
    print(json.dumps(verify(args.lake, args.write_evidence), indent=2))
