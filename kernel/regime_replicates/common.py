"""Shared utilities; the pinned official checkout is never modified."""
from pathlib import Path
import importlib.util
import os
import subprocess
import sys

HERE=Path(__file__).resolve().parent
COMMIT='61cdb69cb11adea48ecb13c823ad654d46dc15df'
OFFICIAL=Path(os.environ.get('ASKOTCH_OFFICIAL',str(HERE.parent/'official')))
if (HERE/'deps').exists():sys.path.insert(0,str(HERE/'deps'))
attention_deps=HERE.parent.parent/'attention/deps'
if importlib.util.find_spec('torch') is None and attention_deps.exists():
    sys.path.insert(0,str(attention_deps))
if OFFICIAL.exists():sys.path.insert(0,str(OFFICIAL))


def verify_source():
    if (OFFICIAL/'.git').exists():
        commit=subprocess.check_output(['git','-C',str(OFFICIAL),'rev-parse','HEAD'],text=True).strip()
        dirty=subprocess.check_output(['git','-C',str(OFFICIAL),'diff','--name-only','HEAD','--','fast_krr'],text=True).strip()
        if commit!=COMMIT or dirty:raise RuntimeError(f'Official source mismatch: {commit}, dirty={dirty}')
        return {'commit':commit,'source':str(OFFICIAL),'unmodified':True}
    import importlib.metadata,json
    dist=importlib.metadata.distribution('fast_krr')
    direct=json.loads(dist.read_text('direct_url.json') or '{}')
    commit=direct.get('vcs_info',{}).get('commit_id')
    if commit!=COMMIT:raise RuntimeError(f'Pinned fast_krr install required; got {direct}')
    return {'commit':commit,'source':str(dist.locate_file('')),'unmodified':'installed VCS package'}


def sync(device):
    import torch
    if str(device).startswith('cuda'):torch.cuda.synchronize(device)


def dense_kernel(x,z,params):
    import torch
    d2=(x[:,None,:]-z[None,:,:]).square().sum(-1)
    sigma=params['sigma']
    if params['type']=='rbf':return (-d2/(2*sigma*sigma)).exp()
    d=d2.sqrt();nu=params['nu']
    if nu==.5:return (-d/sigma).exp()
    a=(3 if nu==1.5 else 5)**.5*d/sigma
    if nu==1.5:return (1+a)*(-a).exp()
    return (1+a+5*d2/(3*sigma*sigma))*(-a).exp()


def prediction(x,basis,w,params):
    from pykeops.torch import LazyTensor
    from fast_krr.kernels.kernel_inits import _get_kernel
    return _get_kernel(LazyTensor(x[:,None,:]),LazyTensor(basis[None,:,:]),params)@w
