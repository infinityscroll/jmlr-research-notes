#!/usr/bin/env python3
import argparse,datetime,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--lake',default='lake');args=p.parse_args()
r=Path(__file__).resolve().parent;prefix='GAUSSIAN_COVARIANCE_UNIFORM_MIXED'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
closure=json.loads((r/(prefix+'_SOURCE_CLOSURE.json')).read_text())
for f,h in closure.items():assert sha(r/f)==h,f
compiler=subprocess.check_output([args.lake,'env','lean','--version'],cwd=r,text=True).strip()
assert 'version 4.35.0-rc2' in compiler and 'commit 11acb17ec6b07a8f9e9173e6845197929540936b' in compiler
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages/mathlib',text=True).strip()
assert rev=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
with (r/(prefix+'_BUILD.txt')).open('w') as f:
 subprocess.run([args.lake,'build','GaussianCovarianceOptimizerConstants','GaussianCovarianceUniformMixed'],cwd=r,stdout=f,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,'env','lean','GaussianCovarianceUniformMixedAudit.lean'],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/(prefix+'_AXIOMS.txt')).write_text(audit)
rows=[json.loads(x.split(' ',1)[1]) for x in audit.splitlines() if x.startswith(prefix+'_AXIOMS ')]
assert len(rows)>=15,len(rows)
allowed={'propext','Classical.choice','Quot.sound'}
for row in rows:assert set(row['axioms'])<=allowed,row
assert len(set(x['constant'] for x in rows))==len(rows)
for f,h in closure.items():assert sha(r/f)==h,f
receipt={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':compiler,'mathlib_revision':rev,'build_succeeded':True,'all_owned_constant_audit_succeeded':True,'owned_modules':['GaussianCovarianceOptimizerConstants', 'GaussianCovarianceUniformMixed'],'owned_constants':len(rows),'owned_theorem_constants':sum(x['theorem'] for x in rows),'allowed_axioms':sorted(allowed),'constants':rows,'source_closure':closure,'scope':'Explicit eventual retention and coefficient/gap bounds with relaxed mass floor 1/(200m), degree cap 2, and retention m^-4. The actual offset derivative is bounded by an absolute logarithmic-square constant times the actual covariance curvature deficit, both on displayed relaxed geometry and at every actual small-positive-floor optimizer uniformly over the full mass box [1/(100m),2/m]. No factor, edge, degree or optimizer-differentiability premise remains in the optimizer endpoint.'}
(r/(prefix+'_VERIFICATION.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS:',len(rows),'compiled owned constants; actual uniform logarithmic-square covariance mixed estimate; full local source closure pinned.')
