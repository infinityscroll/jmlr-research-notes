#!/usr/bin/env python3
import argparse,datetime,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--lake',default='lake');args=p.parse_args()
r=Path(__file__).resolve().parent;prefix='GAUSSIAN_REGULAR_COEFFICIENT_MAJORANT'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
closure=json.loads((r/(prefix+'_SOURCE_CLOSURE.json')).read_text())
for f,h in closure.items():assert sha(r/f)==h,f
compiler=subprocess.check_output([args.lake,'env','lean','--version'],cwd=r,text=True).strip()
assert 'version 4.35.0-rc2' in compiler and 'commit 11acb17ec6b07a8f9e9173e6845197929540936b' in compiler
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages/mathlib',text=True).strip()
assert rev=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
with (r/(prefix+'_BUILD.txt')).open('w') as f:
 subprocess.run([args.lake,'build','GaussianRegularCoefficientMajorant'],cwd=r,stdout=f,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,'env','lean','GaussianRegularCoefficientMajorantAudit.lean'],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/(prefix+'_AXIOMS.txt')).write_text(audit)
rows=[json.loads(x.split(' ',1)[1]) for x in audit.splitlines() if x.startswith(prefix+'_AXIOMS ')]
assert len(rows)>=8,len(rows)
allowed={'propext','Classical.choice','Quot.sound'}
for row in rows:assert set(row['axioms'])<=allowed,row
assert len(set(x['constant'] for x in rows))==len(rows)
for f,h in closure.items():assert sha(r/f)==h,f
receipt={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':compiler,'mathlib_revision':rev,'build_succeeded':True,'all_owned_constant_audit_succeeded':True,'owned_modules':['GaussianRegularCoefficientMajorant'],'owned_constants':len(rows),'owned_theorem_constants':sum(x['theorem'] for x in rows),'allowed_axioms':sorted(allowed),'constants':rows,'source_closure':closure,'scope':'A literal C-infinity log-sum-exp score-range majorant is defined and proved to dominate |1-k_ij| simultaneously for every actual divided regular-noise pair coefficient, including ties, for 0<r<=1/2. The majorant is (2r^2+Q)exp Q with Q=C(tau W sqrt L+tau^2 W^2), W=log sum exp scores+log sum exp negative scores. Smoothness is proved both in utility coordinates and actual arbitrary-dimensional Gaussian score coordinates. Its size is bounded by finite max-absolute-score expressions. Gaussian Lq moments remain subsequent work; no such estimate is asserted here.'}
(r/(prefix+'_VERIFICATION.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS:',len(rows),'compiled owned constants; actual smooth common divided-noise error majorant; full local source closure pinned.')
