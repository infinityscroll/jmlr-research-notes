"""Run the actual released rank-2 damped-Nyström and 10-step random-power update.

CPU float64, no source changes. Only block choice is controlled to cover all
blocks. The observed random stepsize is used in the analytical comparison.
"""
from pathlib import Path
from fractions import Fraction as F
import os
import sys
import math
import json
import hashlib
import importlib

HERE=Path(__file__).resolve().parent
deps=[HERE.parent/'pilot/deps',HERE.parent.parent/'attention/deps']
os.environ['PYTHONPATH']=os.pathsep.join(map(str,deps))+os.pathsep+os.environ.get('PYTHONPATH','')
os.environ['KEOPS_CACHE_FOLDER']=str(HERE/'keops-cache')
sys.path.insert(0,str(HERE.parent/'pilot'))
from common import verify_source,dense_kernel
import numpy as np
import torch
from fast_krr.models import FullKRR
from fast_krr.opts import ASkotchV2
released=importlib.import_module('fast_krr.opts.askotchv2')
from check_uniform_stepsizes import native_matrix,BLOCKS,LO,HI,LAM,DELTA,RHO

class CorrectedFullKRR(FullKRR):
    def _get_block_grad(self,w,block):
        return super()._get_block_grad(w,block)+self.lambd*(w[block]-self.w[block])

def main():
    torch.set_default_dtype(torch.float64);torch.set_num_threads(1)
    source=verify_source()
    distance=math.sqrt(-2*math.log1p(-float(DELTA)))
    x=torch.tensor([[0.,0.],[distance,0.],[distance/2,math.sqrt(3)*distance/2]])
    kernel={'type':'rbf','sigma':1.};K=dense_kernel(x,x,kernel)
    H=K+float(LAM)*torch.eye(3);target=torch.tensor([1.,-1.,0.]);rhs=H@target
    old_block=released._get_block;old_properties=released._get_block_properties
    captured={};paired_steps={};checks=[]
    def record_properties(*args,**kwargs):
        result=old_properties(*args,**kwargs)
        pre,eta,L=result
        captured.update(eta=float(eta[0]),L=float(L[0]),rho=float(pre[0].rho),
                        min_nystrom_eigenvalue=float(pre[0].S[-1]))
        return result
    try:
        released._get_block_properties=record_properties
        for stale,cls in [(True,FullKRR),(False,CorrectedFullKRR)]:
            maximum=0.;records=[]
            for bi,indices in enumerate(BLOCKS):
                selected=torch.tensor(indices)
                released._get_block=lambda *args,selected=selected,**kwargs:selected
                probes=[np.zeros(6),*np.eye(6),np.array([-1.,1.,0.,-1.,1.,0.])]
                for j,state in enumerate(probes):
                    model=cls(x,rhs,x,rhs,kernel,True,float(LAM),'regression',torch.zeros(3),'cpu')
                    opt=ASkotchV2(model,block_sz=2,precond_params={'type':'nystrom','r':2,'rho':'damped'},accelerated=True)
                    model.w=target+torch.from_numpy(state[:3].copy())
                    opt.v=target+torch.from_numpy(state[3:].copy())
                    opt.y=opt.alpha*opt.v+(1-opt.alpha)*model.w
                    torch.manual_seed(1000+17*bi+j)
                    opt.step()
                    eta=captured['eta']
                    assert float(LO)-1e-11<=eta<=float(HI)+1e-11
                    assert abs(captured['rho']-float(RHO))<1e-12
                    assert abs(captured['min_nystrom_eigenvalue']-float(DELTA))<1e-12
                    if stale: paired_steps[(bi,j)]=captured.copy()
                    else: assert captured==paired_steps[(bi,j)], 'Correction changed randomized preconditioner/stepsize'
                    M=np.array([[float(v) for v in row] for row in native_matrix(indices,F.from_float(eta),stale)])
                    observed=torch.cat([model.w-target,opt.v-target]).detach().numpy()
                    error=float(np.max(abs(observed-M@state)))
                    assert error<2e-7,(stale,indices,j,error)
                    maximum=max(maximum,error)
                    records.append({'block':list(indices),'state_index':j,**captured,'max_absolute_error':error})
            checks.append({'stale':stale,'checks':records,'max_absolute_error':maximum})
    finally:
        released._get_block=old_block;released._get_block_properties=old_properties
    all_eta=[r['eta'] for r in checks[0]['checks']]
    assert max(all_eta)>min(all_eta), 'Must exercise genuinely varying random power estimates'
    bound=['check_uniform_stepsizes.py','check_released_damped_interface.py','theorem.md']
    result={'status':'PASS','source':source,'device':'cpu','dtype':'float64','input':x.tolist(),'kernel':K.tolist(),
            'rhs':rhs.tolist(),'configuration':{'block_size':2,'rank':2,'rho':'damped','mu':float(LAM),'nu':1.5},
            'permitted_eta_interval':[str(LO),str(HI)],'observed_eta_min':min(all_eta),'observed_eta_max':max(all_eta),
            'matched_randomized_stepsizes':True,'results':checks,
            'source_bindings':{p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in bound if (HERE/p).exists()},
            'scope':'Numerical source-interface validation only; uniform instability and correction use the separate exact certificate.'}
    (HERE/'released_damped_interface_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'checks':48,'observed_eta_min':min(all_eta),'observed_eta_max':max(all_eta),
                      'max_absolute_error':max(c['max_absolute_error'] for c in checks),'matched_randomized_stepsizes':True}))

if __name__=='__main__':main()
