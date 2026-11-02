#!/usr/bin/env python3
"""Build the pinned upstream Gaussian dependency and reject unexpected axioms."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "OAI.MinUncut.GaussianHermite.hermiteBasis",
    "OAI.MinUncut.GaussianHermite.productHermiteBasis",
    "OAI.MinUncut.GaussianHermite.ae_zero_of_integral_mvpoly_eq_zero",
    "OAI.MinUncut.GaussianHermite.rotation_preserves",
    "OAI.MinUncut.GaussianHermite.psi_noise",
    "OAI.MinUncut.GaussianHermite.noise_coefficient",
    "SlowEquilibration.GaussianMaximalCorrelation.coupled_memLp",
    "SlowEquilibration.GaussianMaximalCorrelation.memLp_noise_L2",
    "SlowEquilibration.GaussianMaximalCorrelation.noise_coefficient_L2",
]


def run(args):
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--write-evidence", action="store_true", help="Update saved receipts and transcripts; default verification is read-only")
    options = parser.parse_args()
    if Path(options.lake).is_absolute():
        os.environ["PATH"] = str(Path(options.lake).parent) + os.pathsep + os.environ.get("PATH", "")
    provenance = json.loads((ROOT / "UPSTREAM_PROVENANCE.json").read_text())
    if (ROOT / "lean-toolchain").read_text().strip() != provenance["lean"]:
        raise SystemExit("Toolchain file differs from pinned provenance")
    observed_lean = run([options.lake, "env", "lean", "--version"]).strip()
    expected_version = provenance["lean"].split(":v", 1)[1]
    if "version " + expected_version + "," not in observed_lean:
        raise SystemExit("Unexpected actual Lean version: " + observed_lean)
    observed_mathlib = run(["git", "-C", str(ROOT / ".lake/packages/mathlib"),
                           "rev-parse", "HEAD"]).strip()
    if observed_mathlib != provenance["mathlib"]:
        raise SystemExit("Unexpected actual mathlib checkout: " + observed_mathlib)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if [p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"] != [provenance["mathlib"]]:
        raise SystemExit("Manifest mathlib revision differs from pinned provenance")
    for source in provenance["files"]:
        actual = hashlib.sha256((ROOT / source["path"]).read_bytes()).hexdigest()
        if actual != source["sha256"]:
            raise SystemExit("Upstream source changed: " + source["path"])
    build = run([options.lake, "build", "SlowEquilibration.GaussianNoiseL2"])
    audit_file = ROOT / "AuditGaussianDependency.lean"
    expected_source = "import SlowEquilibration.GaussianNoiseL2\n\n" + "".join(
        "#print axioms " + name + "\n" for name in TARGETS)
    if audit_file.read_text() != expected_source:
        raise SystemExit("Audit source differs from exact required inventory")
    audit = run([options.lake, "env", "lean", str(audit_file)])
    found = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
        if name in found:
            raise SystemExit("Duplicate axiom result: " + name)
        axioms = [x.strip() for x in body.split(",") if x.strip()]
        unexpected = set(axioms) - ALLOWED
        if unexpected:
            raise SystemExit("Unexpected axioms: " + repr(unexpected))
        found[name] = axioms
    if set(found) != set(TARGETS):
        raise SystemExit("Axiom audit inventory mismatch: " + repr(set(found)))
    receipt = {"lean": provenance["lean"], "mathlib": provenance["mathlib"],
               "observed_lean": observed_lean, "observed_mathlib": observed_mathlib,
               "upstream_commit": provenance["commit"], "sources": provenance["files"],
               "build_succeeded": True, "audit": found, "allowed_axioms": sorted(ALLOWED)}
    if options.write_evidence:
        (ROOT / "GAUSSIAN_DEPENDENCY_BUILD_RECEIPT.json").write_text(
            json.dumps(receipt, indent=2) + "\n")
        (ROOT / "GAUSSIAN_DEPENDENCY_BUILD_TRANSCRIPT.txt").write_text(build + audit)
    print("Verified pinned Gaussian basis and noise dependency; all 9 audits passed.")


if __name__ == "__main__":
    main()
