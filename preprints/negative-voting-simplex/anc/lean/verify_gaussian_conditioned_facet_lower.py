#!/usr/bin/env python3
import argparse,datetime,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--lake',default='lake');args=p.parse_args()
r=Path(__file__).resolve().parent;prefix='GAUSSIAN_CONDITIONED_FACET_LOWER'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
closure=json.loads((r/(prefix+'_SOURCE_CLOSURE.json')).read_text())
for f,h in closure.items():assert sha(r/f)==h,f
compiler=subprocess.check_output([args.lake,'env','lean','--version'],cwd=r,text=True).strip()
assert 'version 4.35.0-rc2' in compiler and 'commit 11acb17ec6b07a8f9e9173e6845197929540936b' in compiler
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages/mathlib',text=True).strip()
assert rev=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
with (r/(prefix+'_BUILD.txt')).open('w') as f:
 subprocess.run([args.lake,'build','GaussianConditionedFacetCap','GaussianConditionedFacetWitness','GaussianFanOffsetRange','GaussianConditionedFacetLower'],cwd=r,stdout=f,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,'env','lean','GaussianConditionedFacetLowerAudit.lean'],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/(prefix+'_AXIOMS.txt')).write_text(audit)
rows=[json.loads(x.split(' ',1)[1]) for x in audit.splitlines() if x.startswith(prefix+'_AXIOMS ')]
assert len(rows)>=8,len(rows)
allowed={'propext','Classical.choice','Quot.sound'}
for row in rows:assert set(row['axioms'])<=allowed,row
assert len(set(x['constant'] for x in rows))==len(rows)
for f,h in closure.items():assert sha(r/f)==h,f
receipt={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':compiler,'mathlib_revision':rev,'build_succeeded':True,'all_owned_constant_audit_succeeded':True,'owned_modules':['GaussianConditionedFacetCap', 'GaussianConditionedFacetWitness', 'GaussianFanOffsetRange', 'GaussianConditionedFacetLower'],'owned_constants':len(rows),'owned_theorem_constants':sum(x['theorem'] for x in rows),'allowed_axioms':sorted(allowed),'constants':rows,'source_closure':closure,'scope':'For a centered affine-basis Gaussian fan with m>=3, centered offsets, actual winning-cell masses>=1/(2m), row-pair norms<=D and centered singular lower bound sigma>0, the literal intrinsic facet probability is at least (1/4)exp(-[6(2H+U)^2+2H^2]/sigma^2), H=D sqrt(2log(2m)), U=D sqrt(2log(2(m+1))). All offset bounds, score witnesses, tangent-cap laws, Gaussian shift and union estimates are derived. If D/sigma<=4, the actual intrinsic probability, including the cycle/Hessian convention, is at least m^(-4096). No supplied facet probability, independence, offset-size, point existence or moment premise is used in the final endpoint.'}
(r/(prefix+'_VERIFICATION.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS:',len(rows),'compiled owned constants; actual conditioned-facet exponential and polynomial lower bounds; full local source closure pinned.')
