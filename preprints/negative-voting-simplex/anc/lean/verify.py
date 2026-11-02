#!/usr/bin/env python3
"""Build the partial formalization and enforce its explicit axiom boundary."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def verify(lake: str) -> dict:
    sources = sorted((ROOT / 'NegativeVoting').rglob('*.lean')) + [ROOT / 'NegativeVoting.lean', ROOT / 'GaussianSpectralBridge.lean', ROOT / 'GaussianSecondChaos.lean', ROOT / 'GaussianAffineComparison.lean', ROOT / 'MulgundGaussianComparison.lean', ROOT / 'GaussianHypercontractivityBridge.lean', ROOT / 'GaussianSmallCap.lean', ROOT / 'GaussianCapTailAndStrip.lean', ROOT / 'GaussianNormalTrace.lean', ROOT / 'GaussianNormalDerivatives.lean', ROOT / 'GaussianFanCover.lean', ROOT / 'GaussianFacetDisintegration.lean', ROOT / 'GaussianChaosDecay.lean', ROOT / 'PolyhedralSupportBoundary.lean', ROOT / 'GaussianCapCovariance.lean', ROOT / 'GaussianCapFirstMoment.lean', ROOT / 'GaussianSmoothingComposition.lean', ROOT / 'GaussianLowModeProjection.lean', ROOT / 'GaussianWeightedFacetEnergy.lean', ROOT / 'GaussianMassCentroid.lean', ROOT / 'GaussianFacetDegree.lean', ROOT / 'GaussianCapMixedMGF.lean', ROOT / 'GaussianCapSecondMoment.lean', ROOT / 'GaussianCapCovarianceGap.lean', ROOT / 'GaussianFanMassBase.lean', ROOT / 'GaussianFanMassMinimizer.lean', ROOT / 'GaussianFanMassGradient.lean', ROOT / 'GaussianFanMassExistence.lean', ROOT / 'GaussianSoftPolyhedron.lean', ROOT / 'GaussianPolyhedronEhrhard.lean', ROOT / 'GaussianEhrhardCurvature.lean', ROOT / 'GaussianEhrhardMomentBridge.lean', ROOT / 'GaussianEhrhardCoefficient.lean', ROOT / 'GaussianFanMassJacobian.lean']
    authored_count = 0
    for path in sources:
        text = path.read_text()
        # Proof source only: comments are removed before scanning escape hatches.
        clean = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        clean = re.sub(r'--[^\n]*', '', clean)
        authored_count += len(re.findall(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+[\w.]+', clean))
        forbidden = re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', clean)
        if forbidden:
            raise RuntimeError(f'Forbidden proof escape in {path.name}: {forbidden.group()}')
    audit_source = (ROOT / 'AxiomAudit.lean').read_text()
    audited = re.findall(r'^#print axioms (\S+)', audit_source, re.M)
    build = subprocess.run([lake, 'build'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if build.returncode:
        print(build.stdout)
        raise RuntimeError('lake build failed')
    inventory = subprocess.run([lake, 'env', 'lean', 'Inventory.lean'], cwd=ROOT,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if inventory.returncode:
        print(inventory.stdout)
        raise RuntimeError('Compiled-environment inventory failed')
    theorem_names = re.findall(r'NV_THEOREM ([^\r\n]+)', inventory.stdout)
    if sorted(audited) != sorted(theorem_names):
        raise RuntimeError('The axiom audit must cover every compiled project theorem exactly once')
    imported_modules = set(re.findall(r'NV_MODULE (\S+)', inventory.stdout))
    expected_modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in sources}
    if not expected_modules <= imported_modules:
        raise RuntimeError(f'Unimported project sources: {sorted(expected_modules - imported_modules)}')
    audit = subprocess.run([lake, 'env', 'lean', 'AxiomAudit.lean'], cwd=ROOT,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if audit.returncode:
        print(audit.stdout)
        raise RuntimeError('Lean axiom audit failed')
    seen = set()
    for name, axiom_list in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit.stdout):
        axioms = {x.strip() for x in axiom_list.split(',') if x.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f'Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}')
        seen.add(name)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit.stdout):
        seen.add(name)
    if seen != set(audited):
        raise RuntimeError(f'Audit output does not account for all theorems: {sorted(set(audited) - seen)}')
    print(build.stdout, end='')
    print(inventory.stdout, end='')
    print(audit.stdout, end='')
    return {'status': 'passed', 'theorem_count': len(theorem_names),
            'named_theorem_count': authored_count,
            'allowed_logical_axioms': sorted(ALLOWED_AXIOMS),
            'scope': 'actual Gaussian spectral, moment, reference, affine comparison, trace and local cap components; the full Gaussian theorem remains unproved'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake', help='Lake executable, normally supplied by elan')
    args = parser.parse_args()
    print(json.dumps(verify(args.lake), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        raise SystemExit(1)
