"""Optional CPU reproduction of both prespecified 50,000-step p=2 diagnostics.

This is a training run, unlike verify.py. It never overwrites prior output.
The released optimizer must first be fetched explicitly with fetch_optimizer.py.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json
import time
from fetch_optimizer import checked_path, EXPECTED

ROOT=Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,required=True,
                        help='A new directory for both complete trajectories; must not exist')
    args=parser.parse_args()
    OPT=checked_path()
    out=args.output_dir.resolve()
    if out.exists():
        parser.error('Output directory exists; prior runs are never overwritten.')
    out.mkdir(parents=True,exist_ok=False)
    protocol={'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'deltas':[0.,.5],'p':2.,'eta':.1,'steps':50000,'initial_l':[4.,-4.],
      'initial_k':[4.,0.],'paired_labels':[1,-1],'seed':None,
      'optimizer_sha256':EXPECTED,'producer_sha256':sha(Path(__file__)),
      'original_protocol_sha256':sha(ROOT/'data/diagnostic_protocol.json'),
      'working_derivation_sha256':sha(ROOT/'provenance/WORKING_DERIVATION.md'),
      'outcome_adaptive_choices':False,'scope':'Fixed diagnostic, not proof',
      'portable_reproduction':True}
    (out/'diagnostic_protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    import numpy as np
    import torch
    torch.set_num_threads(1)
    spec=importlib.util.spec_from_file_location('released_smd',OPT)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    xs=[];w1s=[];w2s=[]
    for delta in protocol['deltas']:
     x=np.array([[1.,0.],[delta,1.]])
     d=x[0]-x[1];s=d@d
     w1=np.outer(np.linalg.solve(x,np.array([4.,-4.])),d)/s
     w2=np.outer(np.array([4.,0.]),d)/s
     xs.append(x);w1s.append(w1);w2s.append(w2)
    Xbase=np.stack(xs)
    X=torch.tensor(np.stack([Xbase,-Xbase],axis=1),dtype=torch.float64)
    labels=torch.tensor([1.,-1.],dtype=torch.float64)
    W1=torch.tensor(np.stack(w1s),dtype=torch.float64,requires_grad=True)
    W2=torch.tensor(np.stack(w2s),dtype=torch.float64,requires_grad=True)
    opt=mod.SMD([W1,W2],p=2.,normalize=False)
    opt.param_groups[0]['lr']=protocol['eta']
    checkpoints=set([0,1,2,3,5,10,20,50,100,200,500,1000,2000,5000,10000,20000,50000])
    checkpoints.update(int(v) for v in np.geomspace(1,50000,201))
    records=[];states1=[];states2=[];maxerr=0.
    start=time.monotonic()
    for step in range(protocol['steps']+1):
     opt.zero_grad()
     H=torch.softmax(X@W1[:,None]@X.transpose(-1,-2),dim=-1)@X
     O=torch.softmax(H@W2[:,None]@H.transpose(-1,-2),dim=-1)@H
     signed=O[:,:,0,0]*labels[None,:]
     loss=torch.nn.functional.softplus(-signed).mean(dim=1).sum()
     loss.backward()
     if step in checkpoints:
      r=[];s1=W1.detach().numpy().copy();s2=W2.detach().numpy().copy()
      for i,delta in enumerate(protocol['deltas']):
       x=Xbase[i];d=x[0]-x[1];D=1-delta
       l=x@s1[i]@d;a,b=1/(1+np.exp(-l));h1=x[1]+a*d;h2=x[1]+b*d
       k=s2[i]@d;m=(a-b)*(h1@k);pi=1/(1+np.exp(-m))
       f=delta+D*(b+pi*(a-b));Q=1/(1+np.exp(f))
       ca=pi+pi*(1-pi)*(m+(a-b)**2*(d@k))
       cb=(1-pi)*(1-pi*m)
       A=a*(1-a)*ca;B=b*(1-b)*cb
       g1=-Q*D*np.outer(A*x[0]+B*x[1],d)
       g2=-Q*D*(a-b)**2*pi*(1-pi)*np.outer(h1,d)
       err=max(np.abs(g1-W1.grad.detach().numpy()[i]).max(),
               np.abs(g2-W2.grad.detach().numpy()[i]).max(),
               abs(f-float(signed[i,0].detach())))
       maxerr=max(maxerr,float(err))
       C1=np.outer(x[0],d);C2=np.outer(h1,h1-h2)
       ratio1=float(np.sum(C1*s1[i])/(np.linalg.norm(C1)*np.linalg.norm(s1[i])))
       ratio2=float(np.sum(C2*s2[i])/(np.linalg.norm(C2)*np.linalg.norm(s2[i])))
       r.append({'delta':delta,'l':l.tolist(),'a':float(a),'b':float(b),
         'm':float(m),'k':k.tolist(),'prediction':float(f),'loss':float(np.logaddexp(0,-f)),
         'A':float(A),'B':float(B),'lower_margin_fraction':ratio1,
         'upper_margin_fraction':ratio2,'upper_optimal_margin':float(np.linalg.norm(C2)),
         'memory_distance':float(np.linalg.norm(h1-h2)),'gradient_interface_error':float(err)})
      records.append({'step':step,'cases':r});states1.append(s1);states2.append(s2)
     if step==protocol['steps']:break
     opt.step()
    np.savez_compressed(out/'diagnostic_states.npz',steps=np.array([r['step'] for r in records]),
     W1=np.stack(states1),W2=np.stack(states2),X=Xbase)
    result={'protocol_sha256':sha(out/'diagnostic_protocol.json'),
     'runtime_seconds':time.monotonic()-start,'max_interface_error':maxerr,
     'records':records,'all_outcomes_retained':True,
     'states_sha256':sha(out/'diagnostic_states.npz')}
    (out/'diagnostic_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'runtime_seconds':result['runtime_seconds'],'max_interface_error':maxerr,
     'final':records[-1]},indent=2))


if __name__=='__main__':
    main()
