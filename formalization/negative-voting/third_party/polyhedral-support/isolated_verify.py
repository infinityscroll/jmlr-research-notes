#!/usr/bin/env python3
"""Rebuild the pinned concrete interface and check its selected axiom closure."""
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
manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for entry in manifest["modules"]:
    assert digest(root / "originals" / entry["path"]) == entry["sha256"], entry["path"]
    assert digest(root / entry["path"]) == entry["modern_final_sha256"], entry["path"]

version = subprocess.check_output(
    [args.lake, "env", "lean", "--version"], cwd=root, text=True
).strip()
assert "version 4.35.0-rc2" in version, version
mathlib_revision = subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/mathlib", text=True
).strip()
assert mathlib_revision == manifest["modern_mathlib"], mathlib_revision

with (root / "POLYHEDRAL_SUPPORT_BUILD.txt").open("w") as log:
    subprocess.run([args.lake, "build", "PolyhedralSupportBoundary"],
                   cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
audit = subprocess.check_output(
    [args.lake, "env", "lean", "PolyhedralSupportAudit.lean"],
    cwd=root, text=True, stderr=subprocess.STDOUT
)
(root / "POLYHEDRAL_SUPPORT_AXIOMS.txt").write_text(audit)
expected = (root / "POLYHEDRAL_SUPPORT_AUDIT_TARGETS.txt").read_text().splitlines()
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
assert len(found) == len(expected) == 19, (len(found), len(expected), audit)
assert {name for name, _ in found} == set(expected)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, (name, axioms)

receipt = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "compiler": version,
    "mathlib_revision": mathlib_revision,
    "boundary_sha256": digest(root / "PolyhedralSupportBoundary.lean"),
    "source_manifest_sha256": digest(root / "SOURCE_MANIFEST.json"),
    "audit_sha256": digest(root / "PolyhedralSupportAudit.lean"),
    "build_succeeded": True,
    "axiom_audit_succeeded": True,
    "audited_endpoints": expected,
    "allowed_axioms": sorted(allowed),
    "scope": "Actual fixed-normal Gaussian support calculus; no main-optimality claim.",
}
(root / "POLYHEDRAL_SUPPORT_VERIFICATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("PASS: pinned compiler/source hashes; build; all 19 endpoint axiom audits.")
