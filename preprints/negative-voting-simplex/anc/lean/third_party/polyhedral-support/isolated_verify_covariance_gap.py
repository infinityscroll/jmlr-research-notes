#!/usr/bin/env python3
"""Verify actual normalized conditional covariance boundary gap, preserving all frozen dependency receipts."""
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

receipt_paths = [root / name for name in [
    "POLYHEDRAL_SUPPORT_VERIFICATION.json",
    "GAUSSIAN_CAP_COVARIANCE_VERIFICATION.json",
    "GAUSSIAN_CAP_FIRST_MOMENT_VERIFICATION.json",
    "GAUSSIAN_CAP_SECOND_MOMENT_VERIFICATION.json"]]
receipt_hashes = {p.name: digest(p) for p in receipt_paths}
base, cov, first, second = [json.loads(p.read_text()) for p in receipt_paths]
expected_sources = {
    "PolyhedralSupportBoundary.lean": base["boundary_sha256"],
    "GaussianCapCovariance.lean": cov["source_sha256"],
    "GaussianCapFirstMoment.lean": first["source_sha256"],
    "GaussianCapMixedMGF.lean": "5338a4112fd389e14c2d7a4bf11c4a1142f07445e19953ce2afd30ccc3671ace",
    "GaussianCapSecondMoment.lean": second["source_sha256"],
}
for name, expected in expected_sources.items():
    assert digest(root / name) == expected, name
assert digest(root / "SOURCE_MANIFEST.json") == base["source_manifest_sha256"]
version = subprocess.check_output(
    [args.lake, "env", "lean", "--version"], cwd=root, text=True).strip()
assert "version 4.35.0-rc2" in version
expected_commit = re.search(r"commit ([0-9a-f]+)", base["compiler"]).group(1)
assert f"commit {expected_commit}" in version
mathlib = subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/mathlib", text=True).strip()
assert mathlib == base["mathlib_revision"]

with (root / "GAUSSIAN_CAP_COVARIANCE_GAP_BUILD.txt").open("w") as log:
    subprocess.run([args.lake, "build", "GaussianCapCovarianceGap"], cwd=root,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
audit = subprocess.check_output(
    [args.lake, "env", "lean", "GaussianCapCovarianceGapAudit.lean"],
    cwd=root, text=True, stderr=subprocess.STDOUT)
(root / "GAUSSIAN_CAP_COVARIANCE_GAP_AXIOMS.txt").write_text(audit)
expected = (root / "GAUSSIAN_CAP_COVARIANCE_GAP_AUDIT_TARGETS.txt").read_text().splitlines()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
assert len(found) == len(expected) == 3
assert {name for name, _ in found} == set(expected)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, (name, axioms)
assert {p.name: digest(p) for p in receipt_paths} == receipt_hashes
receipt = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": digest(root / "GaussianCapCovarianceGap.lean"),
    "audit_sha256": digest(root / "GaussianCapCovarianceGapAudit.lean"),
    "frozen_dependency_sources": expected_sources,
    "frozen_dependency_receipts": receipt_hashes,
    "build_succeeded": True,
    "axiom_audit_succeeded": True,
    "audited_declarations": expected,
    "allowed_axioms": sorted(allowed),
    "scope": "Actual normalized conditional covariance, boundary-gap identity and positive semidefiniteness.",
}
(root / "GAUSSIAN_CAP_COVARIANCE_GAP_VERIFICATION.json").write_text(
    json.dumps(receipt, indent=2) + "\n")
print("PASS: actual Gaussian covariance boundary gap; all 3 theorem audits; frozen dependencies preserved.")
