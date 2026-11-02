#!/usr/bin/env python3
import argparse,datetime,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser();parser.add_argument("--lake",default="lake");args=parser.parse_args()
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=r/"GaussianFanCycleNested.lean"
assert sha(source)=="1ac42db25084fcf11a3383d14aae01e24eff40efb11d02abb315e3b2d198687f"
closure=json.loads((r/"GAUSSIAN_FAN_CYCLE_NESTED_SOURCE_CLOSURE.json").read_text())
for f,h in closure.items():assert sha(r/f)==h,f
frozen=r/"GAUSSIAN_FAN_CYCLE_COMPLEX_VERIFICATION.json"
frozen_hash=sha(frozen)
compiler=subprocess.check_output([args.lake,"env","lean","--version"],cwd=r,text=True).strip()
assert "version 4.35.0-rc2" in compiler and "commit 11acb17ec6b07a8f9e9173e6845197929540936b" in compiler
revision=subprocess.check_output(["git","rev-parse","HEAD"],cwd=r/".lake/packages/mathlib",text=True).strip()
assert revision=="065356127b1dc0016f66b7283ce0ce2c4055aa55"
with (r/"GAUSSIAN_FAN_CYCLE_NESTED_BUILD.txt").open("w") as log:
 subprocess.run([args.lake,"build","GaussianFanCycleNested"],cwd=r,stdout=log,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,"env","lean","GaussianFanCycleNestedAudit.lean"],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/"GAUSSIAN_FAN_CYCLE_NESTED_AXIOMS.txt").write_text(audit)
names=(r/"GAUSSIAN_FAN_CYCLE_NESTED_AUDIT_TARGETS.txt").read_text().splitlines()
found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
found += [(n,"") for n in re.findall(r"'([^']+)' does not depend on any axioms",audit)]
assert len(found)==len(names)==10,(len(found),len(names))
assert {n for n,_ in found}==set(names)
allowed={"propext","Classical.choice","Quot.sound"}
for n,axs in found:assert {a.strip() for a in axs.split(",") if a.strip()}<=allowed,(n,axs)
assert sha(frozen)==frozen_hash
for f,h in closure.items():assert sha(r/f)==h,f
receipt={"checked_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"compiler":compiler,
 "mathlib_revision":revision,"source_sha256":sha(source),"audit_sha256":sha(r/"GaussianFanCycleNestedAudit.lean"),
 "source_closure":closure,"frozen_complex_receipt_sha256":frozen_hash,
 "build_succeeded":True,"axiom_audit_succeeded":True,"audited_exports":names,"allowed_axioms":sorted(allowed),
 "scope":"Actual child tangent, orthogonal direction-space splitting, rank increment, affine-origin shift and exact Gaussian density ratio. Child slice Gaussian law and A-B factorization remain separate."}
(r/"GAUSSIAN_FAN_CYCLE_NESTED_VERIFICATION.json").write_text(json.dumps(receipt,indent=2)+"\n")
print("PASS: actual nested stratum geometry and Gaussian density ratio; all10 exports audited; normalization factors and frozen complex preserved.")
