#!/usr/bin/env python3
import argparse,datetime,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser();parser.add_argument("--lake",default="lake");args=parser.parse_args()
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=r/"GaussianFanCycleComplex.lean"
assert sha(source)=="034b7690005971fd7ff623e75b23dfecdbfd2436fbe408e5e38e2d2a0e614bfd"
compiler=subprocess.check_output([args.lake,"env","lean","--version"],cwd=r,text=True).strip()
assert "version 4.35.0-rc2" in compiler and "commit 11acb17ec6b07a8f9e9173e6845197929540936b" in compiler
revision=subprocess.check_output(["git","rev-parse","HEAD"],cwd=r/".lake/packages/mathlib",text=True).strip()
assert revision=="065356127b1dc0016f66b7283ce0ce2c4055aa55"
with (r/"GAUSSIAN_FAN_CYCLE_COMPLEX_BUILD.txt").open("w") as log:
 subprocess.run([args.lake,"build","GaussianFanCycleComplex"],cwd=r,stdout=log,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,"env","lean","GaussianFanCycleComplexAudit.lean"],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/"GAUSSIAN_FAN_CYCLE_COMPLEX_AXIOMS.txt").write_text(audit)
names=(r/"GAUSSIAN_FAN_CYCLE_COMPLEX_AUDIT_TARGETS.txt").read_text().splitlines()
found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
assert len(found)==len(names)==24
assert {n for n,_ in found}==set(names)
allowed={"propext","Classical.choice","Quot.sound"}
for n,axs in found:assert {a.strip() for a in axs.split(",") if a.strip()}<=allowed,(n,axs)
receipt={"checked_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"compiler":compiler,
 "mathlib_revision":revision,"source_sha256":sha(source),"audit_sha256":sha(r/"GaussianFanCycleComplexAudit.lean"),
 "build_succeeded":True,"axiom_audit_succeeded":True,"audited_exports":names,"allowed_axioms":sorted(allowed),
 "scope":"Concrete alternating simplex chains, cone exactness, boundary-of-boundary zero and actual global triangle-mean cancellation. No Gaussian stratum factorization or covariance Hessian assumed or proved."}
(r/"GAUSSIAN_FAN_CYCLE_COMPLEX_VERIFICATION.json").write_text(json.dumps(receipt,indent=2)+"\n")
print("PASS: concrete finite simplex cycle complex and cross-term cancellation; all24 exports audited.")
