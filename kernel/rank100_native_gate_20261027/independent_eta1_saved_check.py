"""Independent reader of the retained eta=1 certificate.

No proposal, Vandermonde solve, interpolation, or producer checker is imported.
Saved Bernstein coefficients are evaluated by de Casteljau at five NEW
unisolvent rational nodes and both endpoints against the previously audited
six-coordinate native covariance map. Only Python's standard library is used.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'rank100_default_gate_20261027'
THEOREM_PIN='e72f428b57cd871d6bd594b9faa640fe961e7a5e3d51feb3419df4c0e8010013'
OPERATOR_PIN='eecb2c18bb1ec6fc5d443d41bbd937190e1ecdd3cf54e1b3f4adf3dc8aa2777e'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def minors(v):
 a,b,c,d,e,f=v
 return [a,e,a*e-c*c,b,f,b*f-d*d]

def casteljau(control,t):
 work=[v.copy() for v in control]
 while len(work)>1:
  work=[[(1-t)*x+t*y for x,y in zip(left,right)] for left,right in zip(work,work[1:])]
 return work[0]

def main():
 assert sha(HERE/'eta1_repair_theorem.md')==THEOREM_PIN
 assert sha(OLD/'general_block_operator.py')==OPERATOR_PIN
 cert=json.loads((HERE/'eta1_repair_certificate.json').read_text())
 assert cert['n']==10000 and cert['b']==100 and cert['rank']==100 and F(cert['eta'])==1
 assert cert['status']=='PASS' and F(cert['energy_prefactor'])==4
 rho=F(cert['rate']); assert rho==F(999999,1000000)
 left,right=map(F,cert['delta_interval']); assert [left,right]==[F(1,20000000000),F(1,5000000000)]
 for rel,pin in cert['source_hashes'].items():assert sha(HERE/rel)==pin
 spec=importlib.util.spec_from_file_location('bound_eta1_general_map',OLD/'general_block_operator.py')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 image=module.image
 n,b,s=10000,100,F(1,100000);lam=F(1,10**8)
 assert F(n,b)*s*s==lam and 1/(F(n,b)*s)==1000
 initial=[F(1),F(0),F(1),F(0),F(1),F(0)]
 # These five interior nodes differ from ALL producer interpolation nodes
 # (0,1/4,1/2,3/4,1) and its extra evaluations (2/7,5/13).
 fresh=[F(1,13),F(2,11),F(3,7),F(7,11),F(12,13)]
 assert len(set(fresh))==5
 producer_nodes={F(k,4) for k in range(5)}|{F(2,7),F(5,13)}
 assert not (set(fresh)&producer_nodes)
 nodes=[F(0),*fresh,F(1)];seen=set();matrix_count=0;node_count=0;energies=[]
 minimum_determinants=[]
 assert len(cert['records'])==64
 for rec in cert['records']:
  stale=rec['stale'];box=rec['box'];assert type(stale) is bool and type(box) is int and 0<=box<32
  assert (stale,box) not in seen;seen.add((stale,box))
  lo,hi=F(rec['lo']),F(rec['hi'])
  assert lo==left+(right-left)*F(box,32) and hi==left+(right-left)*F(box+1,32)
  U=list(map(F,rec['U']));assert len(U)==6 and U[0]==1
  um=minors(U);assert all(x>0 for x in um);assert um==list(map(F,rec['witness_psd']))
  reach=minors([3*u-v for u,v in zip(U,initial)]);assert all(x>=0 for x in reach)
  assert reach==list(map(F,rec['initial_domination']))
  controls=[list(map(F,v)) for v in rec['bernstein']]
  assert len(controls)==5 and all(len(v)==6 for v in controls)
  assert len(rec['minors'])==5
  for v,recorded in zip(controls,rec['minors']):
   mm=minors(v);assert all(x>=0 for x in mm);assert mm==list(map(F,recorded))
   minimum_determinants.extend([mm[2],mm[5]]);matrix_count+=1
  for t in nodes:
   delta=lo+(hi-lo)*t
   D=(lam+2*delta)*(b+lam-(b-2)*delta);assert D>0
   mapped=image(n,b,s,delta,F(1),stale,U)
   exact=[D*D*(rho*u-v) for u,v in zip(U,mapped)]
   assert casteljau(controls,t)==exact,(stale,box,str(t))
   node_count+=1
  # Eigenvalues of A on contrast and constant subspaces.
  a_left=lam+lo; b_left=n+lam-(n-1)*lo
  w_left=b_left/((n-1)*a_left)
  energy=3*(U[0]+w_left*U[1]);assert energy<4
  assert energy==F(rec['relative_initial_energy_upper'])
  # Exact derivative numerator of the mean/contrast weight is negative.
  derivative_numerator=-(n-1)*((n-1)*lam+n+lam)
  assert derivative_numerator<0 and U[1]>=0
  right_energy=3*(U[0]+(n+lam-(n-1)*hi)/((n-1)*(lam+hi))*U[1])
  assert right_energy<=energy;energies.append(energy)
 assert seen=={(stale,box) for stale in [True,False] for box in range(32)}
 assert matrix_count==320 and node_count==448
 out={'status':'PASS exact saved-certificate verification','witnesses':len(seen),
  'witnesses_strictly_positive_definite':64,'initial_domination_checks':64,
  'Bernstein_PSD_matrices':matrix_count,'fresh_unisolvent_nodes_per_box':list(map(str,fresh)),
  'direct_map_polynomial_evaluations':node_count,'coordinate_equalities':6*node_count,
  'maximum_energy_prefactor_exact':str(max(energies)),'maximum_energy_prefactor_display':float(max(energies)),
  'both_gradients':True,'all_closed_subintervals_cover_entire_interval':True,
  'source_pins':{p:sha(HERE/p) for p in ['eta1_repair_theorem.md','certify_eta1_repair.py','eta1_repair_certificate.json','independent_eta1_saved_check.py']},
  'operator_sha256':OPERATOR_PIN,'uses_producer_interpolation':False,
  'degree_and_source_reduction':'Analytically audited in separate source-bound review; not inferred from finitely many checks',
  'paid_jobs':0}
 target=HERE/'independent_eta1_saved_certificate.json'
 with target.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
