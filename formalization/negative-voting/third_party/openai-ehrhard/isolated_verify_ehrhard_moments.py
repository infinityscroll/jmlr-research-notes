#!/usr/bin/env python3
"""Verify actual Gaussian Ehrhard moment and conditional-variance consequences."""
import argparse,datetime,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument("--lake",default="lake")
args=parser.parse_args()
root=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source=root/"GaussianEhrhardMomentBridge.lean"
assert digest(source)=="409b550c7d6af48e66f5130e45747d945b8114aa451fa70c24b5f69f51a8fae3"
receipts=[root/n for n in ["EHRHARD_UPSTREAM_VERIFICATION.json","EHRHARD_POLYHEDRON_VERIFICATION.json","EHRHARD_CURVATURE_VERIFICATION.json"]]
frozen={p.name:digest(p) for p in receipts}
closure=json.loads((root/"EHRHARD_MOMENT_SOURCE_CLOSURE.json").read_text())
for f,h in closure["local_sources"].items():assert digest(root/f)==h,f
version=subprocess.check_output([args.lake,"env","lean","--version"],cwd=root,text=True).strip()
assert "version 4.35.0-rc2" in version and "commit 11acb17ec6b07a8f9e9173e6845197929540936b" in version
revision=subprocess.check_output(["git","rev-parse","HEAD"],cwd=root/".lake/packages/mathlib",text=True).strip()
assert revision==closure["mathlib_revision"]
with (root/"EHRHARD_MOMENT_BUILD.txt").open("w") as log:
 subprocess.run([args.lake,"build","GaussianEhrhardMomentBridge"],cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,"env","lean","GaussianEhrhardMomentAudit.lean"],cwd=root,text=True,stderr=subprocess.STDOUT)
(root/"EHRHARD_MOMENT_AXIOMS.txt").write_text(audit)
expected=(root/"EHRHARD_MOMENT_AUDIT_TARGETS.txt").read_text().splitlines()
found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
assert len(found)==len(expected)==16,(len(found),len(expected))
assert {n for n,_ in found}==set(expected)
allowed={"propext","Classical.choice","Quot.sound"}
for n,axs in found:assert {a.strip() for a in axs.split(",") if a.strip()}<=allowed,(n,axs)
assert {p.name:digest(p) for p in receipts}==frozen
for f,h in closure["local_sources"].items():assert digest(root/f)==h,f
receipt={"checked_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "compiler":version,"mathlib_revision":revision,"source_sha256":digest(source),
 "source_closure_sha256":digest(root/"EHRHARD_MOMENT_SOURCE_CLOSURE.json"),
 "local_source_count":len(closure["local_sources"]),"frozen_dependency_receipts":frozen,
 "build_succeeded":True,"axiom_audit_succeeded":True,"audited_exports":expected,
 "allowed_axioms":sorted(allowed),
 "scope":"Actual first/second Gaussian moments and normalized conditional-variance Ehrhard correction for finite polyhedra of mass strictly between0 and1. No positive/lower-bound assertion for the correction coefficient is included."}
(root/"EHRHARD_MOMENT_VERIFICATION.json").write_text(json.dumps(receipt,indent=2)+"\n")
print("PASS: actual Ehrhard Gaussian moments and variance correction; all16 exports audited; frozen dependencies preserved.")
