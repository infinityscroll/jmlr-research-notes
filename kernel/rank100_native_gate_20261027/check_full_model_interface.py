"""Native FullKRR versus structured model at rank100 on bounded n=120.

Different reduction orders are measured, not assumed bit-identical. This
does not run the full n=10000 high-dimensional KeOps experiment.
"""
from pathlib import Path
import os,sys,json,math,hashlib,importlib
HERE=Path(__file__).resolve().parent
deps=[HERE.parent/'pilot/deps',HERE.parent.parent/'attention/deps']
os.environ['PYTHONPATH']=os.pathsep.join(map(str,deps))+os.pathsep+os.environ.get('PYTHONPATH','')
os.environ['KEOPS_CACHE_FOLDER']=str(HERE/'keops-cache')
from run_structured_release import StructuredRBF,verify_source
import torch
from fast_krr.models import FullKRR
from fast_krr.opts import ASkotchV2
release=importlib.import_module('fast_krr.opts.askotchv2')

class Repaired(FullKRR):
    def _get_block_grad(self,w,block):
        return super()._get_block_grad(w,block)+self.lambd*(w[block]-self.w[block])

def main():
    out=HERE/'full_model_interface_results.json'
    if out.exists():raise RuntimeError('Preserve existing observations')
    source=verify_source();torch.set_default_dtype(torch.float64);torch.set_num_threads(1)
    n,b=120,100;delta=1e-10;lam=1e-8
    radius=math.sqrt(-math.log1p(-delta));x=radius*torch.eye(n)
    d=float(1-torch.exp(-((x[0]-x[1])**2).sum()/2))
    u=torch.where(torch.arange(n)%2==0,1.,-1.);rhs=(lam+d)*u
    block=torch.arange(b)
    old_block,old_props=release._get_block,release._get_block_properties
    release._get_block=lambda *a,**kw:block
    properties={}
    def capture(*a,**kw):
        ans=old_props(*a,**kw)
        properties.update(eta=float(ans[1][0]),rho=float(ans[0][0].rho),small_eigenvalue=float(ans[0][0].S[-1]))
        return ans
    release._get_block_properties=capture
    records=[];columns=[]
    try:
      for repaired in [False,True]:
       for state in [0,1]:
        native=(Repaired if repaired else FullKRR)(x,rhs,x,rhs,{'type':'rbf','sigma':1.},True,lam,'regression',torch.zeros(n),'cpu')
        adapter=StructuredRBF(n,b,d,lam,repaired)
        on=ASkotchV2(native,b,precond_params={'type':'nystrom','r':100,'rho':'damped'})
        oa=ASkotchV2(adapter,b,precond_params={'type':'nystrom','r':100,'rho':'damped'})
        w=torch.zeros(n) if state==0 else .1*torch.cos(torch.arange(n))
        v=torch.zeros(n) if state==0 else .1*torch.sin(torch.arange(n))
        w-=w.mean();v-=v.mean()
        for model,opt in [(native,on),(adapter,oa)]:
            model.w=w.clone();opt.v=v.clone();opt.y=opt.alpha*opt.v+(1-opt.alpha)*model.w
        if not columns:
            basis=torch.zeros(n);basis[0]=1
            col=native.K@basis
            columns.append(dict(diagonal=float(col[0]),off_diagonal=float(col[1]),
                                max_off_diagonal_deviation=float((col[1:]-col[1]).abs().max()),
                                delta_from_native=float(1-col[1]),delta_from_torch=d))
        grad_native=native._get_block_grad(on.y,block)
        grad_adapter=adapter._get_block_grad(oa.y,block)
        torch.manual_seed(2026102703+state);on.step();pn=properties.copy()
        torch.manual_seed(2026102703+state);oa.step();pa=properties.copy()
        a=torch.cat([native.w,on.v,on.y]);z=torch.cat([adapter.w,oa.v,oa.y])
        maximum=float((a-z).abs().max());relative=maximum/(1+float(a.abs().max()))
        records.append(dict(repaired=repaired,state=state,gradient_max_abs_difference=float((grad_native-grad_adapter).abs().max()),
                            state_max_abs_difference=maximum,state_scaled_difference=relative,
                            native_properties=pn,adapter_properties=pa))
    finally:
      release._get_block=old_block;release._get_block_properties=old_props
    result=dict(source=source,n=n,block_size=b,rank=b,dtype='float64',native_kernel_columns=columns,
                comparisons=records,scope='One-step actual FullKRR comparison; no full n10000 untouched pipeline run',
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
