"""Unchanged released ASkotchV2/Nystrom/power with a structured RBF model.

This replaces the expensive KeOps model operator by its equicorrelation
algebra; it is NOT an untouched full-pipeline floating-point reproduction.
Protocol is saved before random draws; failures and timeouts are retained.
"""
from pathlib import Path
import os, sys, json, hashlib, time, math, traceback, importlib

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'pilot'))
from common import verify_source
import numpy as np
import torch
from fast_krr.opts import ASkotchV2

release = importlib.import_module('fast_krr.opts.askotchv2')


class StructuredRBF:
    """Same exact kernel and gradient; different floating summation order."""
    def __init__(self, n, bsize, delta, lambd, repaired):
        self.n = n
        self.lambd = lambd
        self.device = 'cpu'
        self.delta = delta
        self.repaired = repaired
        self.w = torch.zeros(n)
        self.u = torch.where(torch.arange(n) % 2 == 0, 1., -1.)
        self.b = (lambd + delta) * self.u
        self.block_kernel = delta * torch.eye(bsize) + (1-delta) * torch.ones(bsize, bsize)

    def _get_block_lin_ops(self, block):
        K = self.block_kernel
        return (lambda v: K @ v,
                lambda v: K @ v + self.lambd * v,
                len(block))

    def _get_block_grad(self, w, block):
        ridge = w if self.repaired else self.w
        return self.delta*w[block] + (1-self.delta)*w.sum() + self.lambd*ridge[block] - self.b[block]


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def main():
    outpath = HERE/'structured_release_results.json'
    if outpath.exists() or (HERE/'structured_release_protocol.json').exists():
        raise RuntimeError('Do not overwrite a retained experiment')
    source = verify_source()
    cases = []
    for seed in [2026102701, 2026102702]:
        for variant in ['released', 'repaired', 'repaired_eta1']:
            cases.append({'dtype':'float64','seed':seed,'variant':variant})
    for seed in [2026102701, 2026102702]:
        cases.append({'dtype':'float32','seed':seed,'variant':'released'})
    protocol = dict(n=10000, block_size=100, rank=100, delta=1e-10,
                    lambd=1e-8, steps=20000, case_wall_seconds=120,
                    checkpoints=[0,1,10,100,500,1000,2500,5000,10000,20000],
                    cases=cases, source=source, additional_paid_jobs=0,
                    scope='Unchanged released optimizer, preconditioner, power; structured kernel model adapter. No untouched FullKRR pipeline claim.',
                    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    dump(HERE/'structured_release_protocol.json', protocol)
    torch.set_num_threads(1)
    results = dict(protocol_sha256=hashlib.sha256((HERE/'structured_release_protocol.json').read_bytes()).hexdigest(),
                   torch=torch.__version__, numpy=np.__version__, source=source, cases=[])
    original_props = release._get_block_properties
    original_block = release._get_block
    retained = {}
    try:
        for idx, case in enumerate(cases):
            torch.set_default_dtype(getattr(torch, case['dtype']))
            torch.manual_seed(case['seed']); np.random.seed(case['seed'])
            # Off-diagonal RBF value of two distinct orthogonal input points.
            radius = torch.tensor(math.sqrt(-math.log1p(-protocol['delta'])))
            delta_used = float(1-torch.exp(-(radius*radius)))
            model = StructuredRBF(protocol['n'],protocol['block_size'],delta_used,
                                  protocol['lambd'],case['variant']!='released')
            opt = ASkotchV2(model, protocol['block_size'],
                           precond_params={'type':'nystrom','r':100,'rho':'damped'})
            rec = {**case, 'actual_rounded_delta':delta_used, 'status':'running',
                   'checkpoints':[], 'eta_min':math.inf,'eta_max':-math.inf,
                   'rho_min':math.inf,'rho_max':-math.inf,
                   'S_min':math.inf,'S_max':-math.inf,
                   'preconditioner_calls':0}
            rng_digest = hashlib.sha256()
            def block(*args, **kwargs):
                answer = original_block(*args, **kwargs)
                rng_digest.update(answer.numpy().tobytes())
                return answer
            def props(*args, **kwargs):
                ans = original_props(*args, **kwargs)
                pre, eta, L = ans
                ee, rr, ss = float(eta[0]),float(pre[0].rho),float(pre[0].S[-1])
                for field, value in [('eta',ee),('rho',rr),('S',ss)]:
                    rec[field+'_min']=min(rec[field+'_min'],value)
                    rec[field+'_max']=max(rec[field+'_max'],value)
                rec['preconditioner_calls'] += 1
                rng_digest.update(np.asarray([ee,rr,ss],dtype=np.float64).tobytes())
                if case['variant']=='repaired_eta1':
                    return pre, [torch.ones_like(eta[0])], L
                return ans
            release._get_block=block; release._get_block_properties=props
            initial=(protocol['lambd']+delta_used)*protocol['n']
            def checkpoint(t):
                e=model.w.to(torch.float64)-model.u.to(torch.float64)
                ee=float(e@e); total=float(e.sum())
                energy=(protocol['lambd']+delta_used)*ee+(1-delta_used)*total*total
                rec['checkpoints'].append(dict(step=t,relative_A_error=energy/initial,
                                               relative_contrast_error=ee/protocol['n'],sum_error=total))
                retained[f'case_{idx}_step_{t}']=model.w.numpy().copy()
                print(idx,case,t,energy/initial,flush=True)
            started=time.monotonic(); done=0
            try:
                checkpoint(0)
                for t in range(1,protocol['steps']+1):
                    opt.step(); done=t
                    if not torch.isfinite(model.w).all():
                        raise ArithmeticError('nonfinite iterate')
                    if t in protocol['checkpoints']:
                        checkpoint(t)
                    if time.monotonic()-started>protocol['case_wall_seconds']:
                        raise TimeoutError('fixed per-case wall budget exhausted')
                rec['status']='complete'
            except Exception as exc:
                rec['status']='failed'
                rec['exception_type']=type(exc).__name__
                rec['exception']=str(exc)
                rec['traceback']=traceback.format_exc()
                if torch.isfinite(model.w).all() and done not in protocol['checkpoints']:
                    checkpoint(done)
            rec['steps_completed']=done
            rec['wall_seconds']=time.monotonic()-started
            rec['random_draw_digest']=rng_digest.hexdigest()
            for key,value in list(rec.items()):
                if isinstance(value,float) and not math.isfinite(value): rec[key]=None
            results['cases'].append(rec)
            dump(outpath, results)
            np.savez_compressed(HERE/'structured_release_checkpoints.npz',**retained)
    finally:
        release._get_block_properties=original_props; release._get_block=original_block
    results['paired_float64_draws_equal']=[len({c['random_draw_digest'] for c in results['cases'] if c['dtype']=='float64' and c['seed']==s})==1 for s in [2026102701,2026102702]]
    dump(outpath,results)


if __name__=='__main__':
    main()
