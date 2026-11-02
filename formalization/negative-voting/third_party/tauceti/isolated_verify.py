#!/usr/bin/env python3
"""Rebuild the isolated, pinned Tau Ceti port and audit every compiled source constant."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess

ROOT = Path(__file__).resolve().parent
DEFAULT_LAKE = '/tmp/negative-voting-lean-tooling/lean-4.35.0-rc2-darwin_aarch64/bin/lake'
LAKE = os.environ.get('TAUCETI_AUDIT_LAKE', DEFAULT_LAKE if Path(DEFAULT_LAKE).exists() else 'lake')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGET = 'TauCeti.Analysis.Matrix.SchurComplement'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def uncomment(s):
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s[i:i+2] == '/-': depth += 1; i += 2
            elif s[i:i+2] == '-/': depth -= 1; i += 2
            else: i += 1
        elif not string and s[i:i+2] == '/-': depth = 1; i += 2
        elif not string and s[i:i+2] == '--':
            j = s.find('\n', i); i = len(s) if j < 0 else j
        else:
            if s[i] == '"' and (i == 0 or s[i-1] != '\\'): string = not string
            out.append(s[i]); i += 1
    assert not depth
    return ''.join(out)

def run(args, output):
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / output).write_text(p.stdout)
    if p.returncode:
        raise RuntimeError(f'{args!r} exited {p.returncode}; see {output}')
    return p.stdout

original = json.loads((ROOT / 'SOURCE_MANIFEST_DEDUPLICATED.json').read_text())
port = json.loads((ROOT / 'PORT_MANIFEST.json').read_text())
for row in original['files']:
    assert sha(ROOT / 'upstream_original' / row['path']) == row['sha256'], row['path']
for row in original['metadata']:
    assert sha(ROOT / 'upstream_original' / row['path']) == row['sha256'], row['path']
for row in port['files'] + port['backport_sources']:
    assert sha(ROOT / row['path']) == row['sha256'], row['path']
for row in port['files']:
    text = uncomment((ROOT / row['path']).read_text())
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|implemented_by|unsafe|run_elab|run_cmd|IO|System)\b|#(?:eval|external)', text), row['path']

assert (ROOT / 'lean-toolchain').read_text().strip() == port['toolchain']
version = run([LAKE, 'env', 'lean', '--version'], 'LEAN_VERSION.txt').strip()
assert '4.35.0-rc2' in version, version
mathlib_rev = subprocess.check_output(['git','-C',str(ROOT / '.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
assert mathlib_rev == port['mathlib'], mathlib_rev
run([LAKE, 'build', TARGET], 'BUILD_TRANSCRIPT.txt')
inventory = run([LAKE, 'env', 'lean', 'Inventory.lean'], 'INVENTORY.txt')
constants = sorted(set(re.findall(r'TC_CONSTANT (\S+)', inventory)))
theorems = sorted(set(re.findall(r'TC_THEOREM (\S+)', inventory)))
modules = set(re.findall(r'TC_MODULE (\S+)', inventory))
expected_modules = {row['path'][:-5].replace('/', '.') for row in port['files']}
assert modules == expected_modules, (modules - expected_modules, expected_modules - modules)
assert constants and set(theorems) <= set(constants)
audit = run([LAKE, 'env', 'lean', 'AxiomAudit.lean'], 'AXIOM_AUDIT.txt')
assert 'error:' not in audit
seen = {}
for line in audit.splitlines():
    if line.startswith('TC_AXIOM_JSON '):
        record = json.loads(line.removeprefix('TC_AXIOM_JSON '))
        assert set(record['axioms']) <= ALLOWED, record
        seen[record['constant']] = sorted(record['axioms'])
assert set(constants) == set(seen), set(constants) - set(seen)
endpoints = [
 'Matrix.PosSemidef.schur_complement₂₂',
 'Matrix.PosSemidef.schur_complement₁₁',
 'Matrix.PosSemidef.toBlocks₁₂_mul_covariancePseudoInverse_mul',
 'Matrix.PosSemidef.schur_complement₂₂_covariancePseudoInverse',
 'Matrix.PosSemidef.schur_complement₁₁_covariancePseudoInverse',
 'Matrix.isMoorePenroseInverse_covariancePseudoInverse',
 'Matrix.eq_covariancePseudoInverse_of_penrose',
 'Matrix.toEuclideanLin_mul_covariancePseudoInverse',
 'Matrix.tendsto_inv_sq_add_smul_mul',
 'Matrix.measurable_covariancePseudoInverse',
]
assert set(endpoints) <= set(seen)
receipt = {
 'utc_completed': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'upstream_repository': original['repository'], 'upstream_commit': original['commit'],
 'upstream_lean_file_count': len(original['files']),
 'original_manifest_rows': original['original_row_count'],
 'duplicate_manifest_rows_removed': len(original['duplicate_rows_removed']),
 'toolchain': port['toolchain'], 'lean_version_output': version,
 'mathlib_commit': mathlib_rev,
 'build_target': TARGET, 'build_exit_code': 0, 'audit_exit_code': 0,
 'compiled_source_modules': sorted(modules),
 'compiled_source_constant_count': len(constants),
 'compiled_source_theorem_constant_count': len(theorems),
 'all_compiled_source_constants_transitively_audited': True,
 'allowed_logical_axioms': sorted(ALLOWED),
 'named_endpoint_axioms': {n:seen[n] for n in endpoints},
 'source_manifest_sha256': sha(ROOT / 'SOURCE_MANIFEST_DEDUPLICATED.json'),
 'port_manifest_sha256': sha(ROOT / 'PORT_MANIFEST.json'),
 'exact_patch_sha256': sha(ROOT / 'PORT_PATCHES.diff'),
 'scope': 'Finite-dimensional singular Schur complement and canonical pseudoinverse algebra; not Gaussian Hessian identification or the full negative-voting theorem.',
}
(ROOT / 'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'verified','source_modules':len(modules),'compiled_constants':len(constants),'compiled_theorem_constants':len(theorems),'named_endpoints':len(endpoints),'receipt':'BUILD_RECEIPT.json'},indent=2))
