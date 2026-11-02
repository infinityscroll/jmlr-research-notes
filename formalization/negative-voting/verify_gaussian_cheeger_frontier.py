#!/usr/bin/env python3
import argparse,datetime,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--lake',default='lake');args=p.parse_args()
r=Path(__file__).resolve().parent;prefix='GAUSSIAN_CHEEGER_FRONTIER'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
closure=json.loads((r/(prefix+'_SOURCE_CLOSURE.json')).read_text())
for f,h in closure.items():assert sha(r/f)==h,f
pin=json.loads((r/'upstream/kls500/SOURCE_PIN.json').read_text())
assert pin['revision']=='c1a50992a81456849996deef2971d4a0b3190bdd'
for f,row in pin['files'].items():
 assert sha(r/f)==row['ported_sha256'],f
 assert sha(r/'upstream/kls500/originals'/f)==row['upstream_sha256'],f
compiler=subprocess.check_output([args.lake,'env','lean','--version'],cwd=r,text=True).strip()
assert 'version 4.35.0-rc2' in compiler and 'commit 11acb17ec6b07a8f9e9173e6845197929540936b' in compiler
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages/mathlib',text=True).strip()
assert rev=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
with (r/(prefix+'_BUILD.txt')).open('w') as f:
 subprocess.run([args.lake,'build','GaussianFanCheeger'],cwd=r,stdout=f,stderr=subprocess.STDOUT,check=True)
audit=subprocess.check_output([args.lake,'env','lean','GaussianCheegerFrontierAudit.lean'],cwd=r,text=True,stderr=subprocess.STDOUT)
(r/(prefix+'_AXIOMS.txt')).write_text(audit)
rows=[json.loads(x.split(' ',1)[1]) for x in audit.splitlines() if x.startswith(prefix+'_AXIOMS ')]
assert len(rows)>=100,len(rows)
allowed={'propext','Classical.choice','Quot.sound'}
for row in rows:assert set(row['axioms'])<=allowed,row
assert len(set(x['constant'] for x in rows))==len(rows)
for f,h in closure.items():assert sha(r/f)==h,f
receipt={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':compiler,'mathlib_revision':rev,'build_succeeded':True,'all_owned_constant_audit_succeeded':True,'owned_modules':json.loads((r/(prefix+'_OWNED_MODULES.json')).read_text()),'owned_constants':len(rows),'owned_theorem_constants':sum(x['theorem'] for x in rows),'allowed_axioms':sorted(allowed),'constants':rows,'source_closure':closure,'upstream_kls500_pin':pin,'scope':'Actual Gaussian Cheeger constant at least 1/pi; actual affine-fan cut conductance min(p(I),1-p(I)) <= 2*pi*sum_cross ||B_i-B_j||*facetWeight_ij. Distinct sites and finite Euclidean dimension; actual tube/frontier, tie-null cut mass, and Gaussian functional premise all derived.'}
(r/(prefix+'_VERIFICATION.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS:',len(rows),'compiled owned constants; actual Gaussian Cheeger and fan-cut conductance; full local source closure pinned.')
