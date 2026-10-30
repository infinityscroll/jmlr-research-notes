#!/usr/bin/env python3
"""Run the preserved exact cactus fixtures without changing their sources."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for item in pins["files"]:
        path = ROOT / item["path"]
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != item["sha256"]:
            raise RuntimeError("Source integrity mismatch: " + item["path"])

    # The original checker writes next to __file__. Isolate it and its outputs.
    with tempfile.TemporaryDirectory(prefix=".cactus-check-", dir=ROOT) as tmp:
        scratch = Path(tmp)
        engine = scratch / "exact_coupling_checks.py"
        shutil.copyfile(ROOT / "checks" / engine.name, engine)
        run = subprocess.run(
            [sys.executable, "-I", "-B", str(engine)],
            cwd=scratch, capture_output=True, text=True, timeout=180,
        )
        if run.returncode:
            raise RuntimeError(
                "Existing checker failed:\n" + run.stdout + "\n" + run.stderr
            )
        reports = {}
        for name in ("EXACT_COUPLING_CHECKS.json",
                     "TWO_CYCLE_LENGTH_BOUNDARY.json"):
            actual = json.loads((scratch / name).read_text())
            expected = json.loads((ROOT / "evidence" / name).read_text())
            if actual != expected:
                raise RuntimeError("Fresh evidence differs: " + name)
            reports[name] = actual

    report = reports["EXACT_COUPLING_CHECKS.json"]
    print(json.dumps({
        "status": "PASS",
        "copied_source_hashes_verified": len(pins["files"]),
        "cross_support_patterns": report["cross_support_patterns"],
        "cross_support_flip_comparisons":
            report["cross_support_flip_comparisons"],
        "cycle_density_lengths": len(report["branch_change_density"]),
        "whole_covariance_fixtures": len(report["whole_covariance_fixtures"]),
        "cactus_reconstructions": len(report["cactus_reconstructions"]),
        "length_two_boundary":
            reports["TWO_CYCLE_LENGTH_BOUNDARY.json"]["status"],
        "fresh_records_match_preserved_evidence": True,
        "scope": "Bounded exact fixtures and source integrity, not formal "
                 "verification of the uniform theorem.",
    }, indent=2))


if __name__ == "__main__":
    main()

