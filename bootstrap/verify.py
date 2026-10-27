#!/usr/bin/env python3
"""Bounded portable checks. No Monte Carlo; retained evidence is read-only."""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, timeout):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", OMP_NUM_THREADS="1",
               OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout, check=True)
    return result.stdout


def certificate_bindings():
    folder = HERE / "moderate_curvature_gate_20261028"
    source = folder / "moderate_curvature_bias_proposition.md"
    rows = []
    for filename, checker, key in [
        ("moderate_bias_certificate.json", "certify_moderate_bias.py",
         "recursion_average_lower"),
        ("root_bias_certificate.json", "root_check_bias.py",
         "certified_negative_mean_lower"),
    ]:
        cert = json.loads((folder / filename).read_text())
        assert cert["status"] == "PASS" and cert["n"] == 1_000_000
        assert cert["source_sha256"] == sha(source)
        assert cert["checker_sha256"] == sha(folder / checker)
        assert Fraction(cert[key]) > Fraction(131, 25000)
        rows.append({"certificate": filename, "negative_mean_lower": cert[key],
                     "million_steps_recomputed_by_default": False})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-bias", action="store_true",
                        help="also recompute both deterministic million-step bounds")
    args = parser.parse_args()
    start = time.monotonic()
    provenance = json.loads((HERE / "copy_provenance.json").read_text())
    for row in provenance["files"]:
        assert sha(HERE / row["path"]) == row["release_sha256"] == row["source_sha256"]
    release = json.loads((HERE / "release_manifest.json").read_text())
    for row in release["files"]:
        assert sha(HERE / row["path"]) == row["sha256"], row["path"]

    checks = {"unchanged_curated_files": len(provenance["files"]),
              "release_hashes_checked": len(release["files"]),
              "retained_bias_certificates": certificate_bindings()}
    with tempfile.TemporaryDirectory(prefix="bootstrap-check-") as temporary:
        scratch = Path(temporary)
        folders = {Path(row["path"]).parts[0] for row in provenance["files"]}
        for folder in folders:
            shutil.copytree(HERE / folder, scratch / folder)
        endpoint = scratch / "author_correction_v2"
        stdout = run([sys.executable, "bootstrap_exact_cleanroom.py"], endpoint, 120)
        checks["endpoint_exact"] = json.loads(stdout)
        run([sys.executable, "-c", "import check_endpoint as c; c.verify_weights()"],
            endpoint, 30)
        checks["endpoint_floating_weights"] = "PASS"

        moderate = scratch / "moderate_curvature_gate_20261028"
        (moderate / "retained_probe_validation.json").unlink()
        stdout = run([sys.executable, "check_retained_probe.py"], moderate, 60)
        checks["retained_probe"] = json.loads(stdout)

        boundary = scratch / "moderate_distribution_gate_20261028"
        (boundary / "noncentral_limit_bound_certificate.json").unlink()
        stdout = run([sys.executable, "check_noncentral_limit_bound.py"], boundary, 30)
        checks["limiting_bound"] = json.loads(stdout)

        critical = scratch / "critical_endpoint_20261027"
        stdout = run([sys.executable, "check_critical_weights.py"], critical, 90)
        checks["critical_weight_identities"] = json.loads(stdout)

        if args.full_bias:
            for checker, output, key in [
                ("certify_moderate_bias.py", "moderate_bias_certificate.json",
                 "recursion_average_lower"),
                ("root_check_bias.py", "root_bias_certificate.json",
                 "certified_negative_mean_lower"),
            ]:
                (moderate / output).unlink()
                run([sys.executable, checker], moderate, 180)
                recomputed = json.loads((moderate / output).read_text())
                retained = json.loads((HERE / "moderate_curvature_gate_20261028" / output).read_text())
                assert recomputed[key] == retained[key]
                checks[checker] = {"status": "PASS", "exact_lower": recomputed[key],
                                   "million_steps_recomputed": True}

    # Recheck after all subprocesses: no retained file was changed.
    for row in release["files"]:
        assert sha(HERE / row["path"]) == row["sha256"]
    result = {"status": "PASS", "checks": checks,
              "full_bias_recomputed": args.full_bias,
              "new_random_draws": 0, "retained_files_unchanged": True,
              "elapsed_seconds": time.monotonic() - start,
              "scope": "Finite identities, saved evidence and arithmetic only; no CLT proof, expert review or novelty clearance."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
