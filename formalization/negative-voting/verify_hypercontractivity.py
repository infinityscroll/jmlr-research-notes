#!/usr/bin/env python3
"""Build the actual Gaussian endpoint and enforce a transitive axiom allowlist."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BASE_TARGETS = [
    "GaussianFin.stdGaussianFin_isHypercontractive",
    "GaussianFin.ouSemigroupFinLp_coeFn_ae",
    "GaussianFin.stdGaussianFin_satisfiesLogSobolev",
]


def stripped_lean(source):
    result = []
    i = 0
    depth = 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise SystemExit("Unterminated Lean block comment")
    return "".join(result)


def run(args):
    process = subprocess.run(args, cwd=ROOT, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(process.stdout, end="", flush=True)
    if process.returncode:
        raise SystemExit(process.returncode)
    return process.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--write-evidence", action="store_true", help="Update saved receipts and transcripts; default verification is read-only")
    parser.add_argument("--legacy-present", action="store_true")
    parser.add_argument("--dependency-only", action="store_true")
    options = parser.parse_args()
    if Path(options.lake).is_absolute():
        os.environ["PATH"] = str(Path(options.lake).parent) + os.pathsep + os.environ.get("PATH", "")
    provenance = json.loads((ROOT / "HYPERCONTRACTIVITY_PROVENANCE.json").read_text())
    observed_lean = run([options.lake, "env", "lean", "--version"]).strip()
    version = provenance["pilot_lean"].split(":v", 1)[1]
    if "version " + version + "," not in observed_lean or provenance["pilot_lean_commit"] not in observed_lean:
        raise SystemExit("Unexpected Lean compiler")
    if (ROOT / "lean-toolchain").read_text().strip() != provenance["pilot_lean"]:
        raise SystemExit("Unexpected toolchain file")
    mathlib = run(["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"]).strip()
    if mathlib != provenance["pilot_mathlib"]:
        raise SystemExit("Unexpected mathlib checkout")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    manifest_pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if manifest_pin != provenance["pilot_mathlib"]:
        raise SystemExit("Unexpected mathlib manifest pin")
    sources = []
    changes = []
    legacy = []
    for original in provenance["files"]:
        path = original["path"]
        before = (ROOT / "third_party/markov-semigroups/originals" / path).read_bytes()
        after = (ROOT / path).read_bytes()
        if hashlib.sha256(before).hexdigest() != original["original_sha256"]:
            raise SystemExit("Changed preserved original: " + path)
        code = stripped_lean(after.decode())
        forbidden = re.findall(r"\b(sorry|admit|unsafe|native_decide|implemented_by|extern)\b", code)
        if forbidden:
            raise SystemExit("Forbidden proof mechanism in " + path + ": " + repr(forbidden))
        declared = re.findall(r"\baxiom\s+([A-Za-z0-9_'.]+)", code)
        legacy.extend(declared)
        sources.append({"path": path, "original_sha256": original["original_sha256"],
                        "compiled_sha256": hashlib.sha256(after).hexdigest(), "modified": before != after})
        if before != after:
            changes.extend(difflib.unified_diff(before.decode().splitlines(True), after.decode().splitlines(True),
                                               fromfile="originals/" + path, tofile=path))
    expected_legacy = provenance["legacy_axioms_to_reject"] if options.legacy_present else []
    if sorted(legacy) != sorted(expected_legacy):
        raise SystemExit("Unexpected source axiom inventory: " + repr(legacy))
    build_target = "MarkovSemigroups.Instances.WorkInProgress.EuclideanHypercontractive"
    build = run([options.lake, "build", build_target])
    targets = list(BASE_TARGETS)
    imports = ["import " + build_target]
    if not options.dependency_only:
        bridge = ROOT / "GaussianHypercontractivityBridge.lean"
        code = stripped_lean(bridge.read_text())
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b", code):
            raise SystemExit("Forbidden proof mechanism in bridge")
        namespaces = re.findall(r"^namespace\s+(\S+)", code, re.M)
        if namespaces != ["NegativeVotingHypercontractivity"]:
            raise SystemExit("Bridge namespace changed; update inventory deliberately")
        names = re.findall(r"^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def)\s+([^\s({:]+)", code, re.M)
        if not names:
            raise SystemExit("No bridge theorems found")
        targets += ["NegativeVotingHypercontractivity." + n for n in names]
        imports.append("import GaussianHypercontractivityBridge")
        build += run([options.lake, "build", "GaussianHypercontractivityBridge"])
        sources.append({"path": bridge.name, "compiled_sha256": hashlib.sha256(bridge.read_bytes()).hexdigest()})
    audit_path = ROOT / "GeneratedHypercontractivityAudit.lean"
    expected_audit = "\n".join(imports) + "\n" + "".join("#print axioms " + n + "\n" for n in targets)
    if options.write_evidence:
        audit_path.write_text(expected_audit)
    elif audit_path.read_text() != expected_audit:
        raise SystemExit("Saved audit source differs from the exact required endpoints")
    audit = run([options.lake, "env", "lean", str(audit_path)])
    found = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
        axioms = [x.strip() for x in body.split(",") if x.strip()]
        if name in found or set(axioms) - ALLOWED_AXIOMS:
            raise SystemExit("Duplicate or unsafe axiom result: " + name + " " + repr(axioms))
        found[name] = axioms
    if set(found) != set(targets):
        raise SystemExit("Axiom audit inventory mismatch")
    stage = "LEGACY_PRESENT" if options.legacy_present else "CLEAN"
    receipt = {"upstream_commit": provenance["commit"], "observed_lean": observed_lean,
               "mathlib": mathlib, "stage": stage, "sources": sources,
               "manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
               "provenance_sha256": hashlib.sha256((ROOT / "HYPERCONTRACTIVITY_PROVENANCE.json").read_bytes()).hexdigest(),
               "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "source_axioms_present": legacy, "audit": found,
               "no_unexpected_transitive_axioms": True,
               "endpoint_scope": "Actual Gaussian OU integral; raw L2-to-L^(1+tau^-2) and L^(1+tau^2)-to-L2 bounds; not the negative-voting theorem"}
    if options.write_evidence:
        (ROOT / ("HYPERCONTRACTIVITY_" + stage + "_RECEIPT.json")).write_text(json.dumps(receipt, indent=2) + "\n")
        (ROOT / ("HYPERCONTRACTIVITY_" + stage + "_TRANSCRIPT.txt")).write_text(build + audit)
        (ROOT / "HYPERCONTRACTIVITY_PORT.patch").write_text("".join(changes))
    print("Gaussian endpoint and requested bridge audits passed:", stage)


if __name__ == "__main__":
    main()
