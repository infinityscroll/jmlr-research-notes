#!/usr/bin/env python3
"""Check concrete prescribed-mass Gaussian fan existence and all 26 new theorems."""
import argparse, datetime, hashlib, json, re, subprocess
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument("--lake",default="lake")
args=parser.parse_args()
root=Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected_sources={'GaussianFanMassBase.lean': '4fe7277fac6a0bd825635b1c91317315f512bcee17eb99f85f15bd91b9c8835b', 'GaussianFanMassMinimizer.lean': '0c1494d3b1760de63f9eb9932d97a0b71165de339a7994b7c748e9ab32c03310', 'GaussianFanMassGradient.lean': '69da0b21c2a748ea2a977666d887529ae6acd9e77b2cea98a15ab9453623f231', 'GaussianFanMassExistence.lean': '2c4a6cb9e6c18e479fe5298b4d7702ad53a5bcd3253f0db04045f3f545c8c95a'}
for f,h in expected_sources.items(): assert digest(root/f)==h,f
frozen=root/"GAUSSIAN_FAN_MASS_MINIMIZER_VERIFICATION.json"
frozen_hash=digest(frozen)
closure=json.loads((root/"GAUSSIAN_FAN_MASS_SOURCE_CLOSURE.json").read_text())
for f,h in closure["local_sources"].items(): assert digest(root/f)==h,f
version=subprocess.check_output([args.lake,"env","lean","--version"],cwd=root,text=True).strip()
assert "version 4.35.0-rc2" in version
assert "commit 11acb17ec6b07a8f9e9173e6845197929540936b" in version
revision=subprocess.check_output(["git","rev-parse","HEAD"],cwd=root/".lake/packages/mathlib",text=True).strip()
assert revision==closure["mathlib_revision"]
with (root/"GAUSSIAN_FAN_MASS_BUILD.txt").open("w") as log:
 subprocess.run([args.lake,"build","GaussianFanMassExistence"],cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,"env","lean","GaussianFanMassAudit.lean"],cwd=root,text=True,stderr=subprocess.STDOUT)
(root/"GAUSSIAN_FAN_MASS_AXIOMS.txt").write_text(audit)
expected=(root/"GAUSSIAN_FAN_MASS_AUDIT_TARGETS.txt").read_text().splitlines()
found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
assert len(found)==len(expected)==26,(len(found),len(expected))
assert {n for n,_ in found}==set(expected)
allowed={"propext","Classical.choice","Quot.sound"}
for n,axs in found:
 assert {a.strip() for a in axs.split(",") if a.strip()}<=allowed,(n,axs)
assert digest(frozen)==frozen_hash
for f,h in closure["local_sources"].items(): assert digest(root/f)==h,f
receipt={"checked_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "compiler":version,"mathlib_revision":revision,"sources":expected_sources,
 "source_closure_sha256":digest(root/"GAUSSIAN_FAN_MASS_SOURCE_CLOSURE.json"),
 "local_source_count":len(closure["local_sources"]),
 "audit_sha256":digest(root/"GaussianFanMassAudit.lean"),
 "frozen_minimizer_receipt_sha256":frozen_hash,
 "build_succeeded":True,"axiom_audit_succeeded":True,
 "audited_declarations":expected,"allowed_axioms":sorted(allowed),
 "scope":"Actual arbitrary strictly positive Gaussian winning-cell masses for fixed finite distinct sites; centered offsets exist. No uniqueness or C2/Hessian theorem is asserted."}
(root/"GAUSSIAN_FAN_MASS_VERIFICATION.json").write_text(json.dumps(receipt,indent=2)+"\n")
print("PASS: Gaussian prescribed-mass fan existence; all26 theorem audits; source closure and frozen minimizer receipt preserved.")
