#!/usr/bin/env python3
"""Verify the actual conditional covariance extension and its pinned base."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--lake", default="lake")
args = parser.parse_args()
root = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(root / "verify.py"), "--lake", args.lake],
               cwd=root, check=True)
with (root / "GAUSSIAN_CAP_COVARIANCE_BUILD.txt").open("w") as log:
    subprocess.run([args.lake, "build", "GaussianCapCovariance"], cwd=root,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
audit = subprocess.check_output(
    [args.lake, "env", "lean", "GaussianCapCovarianceAudit.lean"],
    cwd=root, text=True, stderr=subprocess.STDOUT)
(root / "GAUSSIAN_CAP_COVARIANCE_AXIOMS.txt").write_text(audit)
expected = (root / "GAUSSIAN_CAP_COVARIANCE_AUDIT_TARGETS.txt").read_text().splitlines()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
assert len(found) == len(expected) == 17
assert {name for name, _ in found} == set(expected)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, (name, axioms)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

receipt = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_sha256": digest(root / "GaussianCapCovariance.lean"),
    "audit_sha256": digest(root / "GaussianCapCovarianceAudit.lean"),
    "base_verification_sha256": digest(root / "POLYHEDRAL_SUPPORT_VERIFICATION.json"),
    "build_succeeded": True,
    "axiom_audit_succeeded": True,
    "audited_declarations": expected,
    "allowed_axioms": sorted(allowed),
    "scope": "Actual conditional variance bound for a positive-mass finite Gaussian polyhedron.",
}
(root / "GAUSSIAN_CAP_COVARIANCE_VERIFICATION.json").write_text(
    json.dumps(receipt, indent=2) + "\n")
print("PASS: actual conditional Gaussian covariance; all 17 declaration axiom audits.")
