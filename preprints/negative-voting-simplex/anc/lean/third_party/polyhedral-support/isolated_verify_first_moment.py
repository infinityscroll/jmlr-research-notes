#!/usr/bin/env python3
"""Verify first-moment identities without regenerating frozen base receipts."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--lake", default="lake")
args = parser.parse_args()
root = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

base_path = root / "POLYHEDRAL_SUPPORT_VERIFICATION.json"
cov_path = root / "GAUSSIAN_CAP_COVARIANCE_VERIFICATION.json"
base_hash, cov_hash = digest(base_path), digest(cov_path)
base, cov = json.loads(base_path.read_text()), json.loads(cov_path.read_text())
assert digest(root / "PolyhedralSupportBoundary.lean") == base["boundary_sha256"]
assert digest(root / "SOURCE_MANIFEST.json") == base["source_manifest_sha256"]
assert digest(root / "GaussianCapCovariance.lean") == cov["source_sha256"]
assert cov["base_verification_sha256"] == base_hash
version = subprocess.check_output(
    [args.lake, "env", "lean", "--version"], cwd=root, text=True).strip()
assert version == base["compiler"]
mathlib = subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/mathlib", text=True).strip()
assert mathlib == base["mathlib_revision"]

with (root / "GAUSSIAN_CAP_FIRST_MOMENT_BUILD.txt").open("w") as log:
    subprocess.run([args.lake, "build", "GaussianCapFirstMoment"], cwd=root,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
audit = subprocess.check_output(
    [args.lake, "env", "lean", "GaussianCapFirstMomentAudit.lean"],
    cwd=root, text=True, stderr=subprocess.STDOUT)
(root / "GAUSSIAN_CAP_FIRST_MOMENT_AXIOMS.txt").write_text(audit)
expected = (root / "GAUSSIAN_CAP_FIRST_MOMENT_AUDIT_TARGETS.txt").read_text().splitlines()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
assert len(found) == len(expected) == 6
assert {name for name, _ in found} == set(expected)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, (name, axioms)
assert digest(base_path) == base_hash
assert digest(cov_path) == cov_hash
receipt = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": digest(root / "GaussianCapFirstMoment.lean"),
    "audit_sha256": digest(root / "GaussianCapFirstMomentAudit.lean"),
    "base_verification_sha256": base_hash,
    "covariance_verification_sha256": cov_hash,
    "build_succeeded": True,
    "axiom_audit_succeeded": True,
    "audited_declarations": expected,
    "allowed_axioms": sorted(allowed),
    "scope": "Actual scalar, vector and coordinate Gaussian cap first-moment boundary identities.",
}
(root / "GAUSSIAN_CAP_FIRST_MOMENT_VERIFICATION.json").write_text(
    json.dumps(receipt, indent=2) + "\n")
print("PASS: Gaussian first-moment identities; all six declaration audits; frozen receipts preserved.")
