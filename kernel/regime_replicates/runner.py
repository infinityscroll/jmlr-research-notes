"""Bounded fair-budget pilot. Launching is the caller's responsibility.

python runner.py check --config pilot_config.json
python runner.py suite --config pilot_config.json --device cuda --output output/gpu

One suite runs sequential child processes inside one container. Each method has
its own persistent JIT cache. Neither W&B nor network services are used.
"""
import argparse,itertools,json,math,os,subprocess,sys,time,traceback,hashlib
from pathlib import Path
from common import HERE,COMMIT,verify_source,sync,prediction


def cases(cfg):
    result=[dict(n=n,kernel=k,noise_sd=noise,seed=seed) for n,k,noise,seed in
            itertools.product(cfg['n_train'],cfg['kernels'],cfg['noise_sd'],cfg['seeds'])]
    if 'shard' in cfg:
        result=[c for c in result if c['n']==cfg['shard']['n'] and c['seed']==cfg['shard']['seed']]
    return result


def candidates(cfg):
    return [dict(lambda_unscaled=l,capacity=c) for l,c in
            itertools.product(cfg['lambda_unscaled'],cfg['capacity'])]


def validate(cfg):
    assert cfg['source_commit']==COMMIT
    assert set(cfg['methods'])<= {'official_askotchv2','inducing_pcg_falkon','corrected_askotchv2'}
    assert len(cfg['methods'])>=2 and len(set(cfg['methods']))==len(cfg['methods'])
    assert all(32<=n<=16384 for n in cfg['n_train'])
    assert 4<=cfg['dimension']<=64
    assert 0<cfg['trial_seconds']<=30 and cfg['max_iterations']<=100000
    assert cfg['timing'] in ['warm','cold'] and cfg['dtype'] in ['float32','float64']
    assert 2<=cfg['validation_intervals']<=10
    assert cfg['warmup_steps'] in [1,2,3]
    assert cfg['suite_timeout_seconds']<=1400 and cfg['worker_timeout_seconds']<=180
    assert all(k in ['rbf','matern_0.5','matern_1.5','matern_2.5'] for k in cfg['kernels'])
    assert all(c in ['small','large'] for c in cfg['capacity'])
    assert all(l>0 for l in cfg['lambda_unscaled'])
    expected=len(cases(cfg))*len(cfg['methods'])*len(candidates(cfg))*cfg['trial_seconds']
    assert expected<cfg['suite_timeout_seconds'], 'Measured budgets alone exceed suite limit'
    return dict(cases=len(cases(cfg)),candidates_per_method_per_case=len(candidates(cfg)),
                nominal_measured_budget_seconds=expected,maximum_suite_seconds=cfg['suite_timeout_seconds'])


def kernel_params(case,cfg):
    if case['kernel']=='rbf':return dict(type='rbf',sigma=cfg['sigma'])
    return dict(type='matern',nu=float(case['kernel'].split('_')[1]),sigma=cfg['sigma'])


def target(x):
    import torch
    return torch.sin(1.5*x[:,0])+.5*x[:,1]*x[:,2]+.3*torch.cos(2*x[:,3])


def data(case,cfg,test=False):
    """Disjoint deterministic RNG streams; test stream is called only post-selection."""
    import torch
    seed=case['seed'];d=cfg['dimension']
    if test:
        g=torch.Generator().manual_seed(1000003+seed)
        x=torch.randn(cfg['n_test'],d,generator=g,dtype=torch.float64)
        latent=target(x);y=latent+case['noise_sd']*torch.randn(len(x),generator=g,dtype=torch.float64)
        return x,y,latent
    g=torch.Generator().manual_seed(1009+seed)
    # Generate maximum training pool first so n regimes use nested training rows.
    x=torch.randn(max(cfg['n_train']),d,generator=g,dtype=torch.float64)
    y=target(x)+case['noise_sd']*torch.randn(len(x),generator=g,dtype=torch.float64)
    gv=torch.Generator().manual_seed(100003+seed)
    xv=torch.randn(cfg['n_validation'],d,generator=gv,dtype=torch.float64)
    yv=target(xv)+case['noise_sd']*torch.randn(len(xv),generator=gv,dtype=torch.float64)
    return x[:case['n']],y[:case['n']],xv,yv


def build(method,case,cfg,candidate,cpu_data,device):
    import torch,numpy as np
    from fast_krr.models import FullKRR,InducingKRR
    from fast_krr.opts import ASkotchV2,PCG
    dtype=getattr(torch,cfg['dtype']);torch.set_default_dtype(dtype)
    torch.manual_seed(200003+case['seed']);np.random.seed(200003+case['seed'])
    x,y,xv,yv=[v.to(device=device,dtype=dtype) for v in cpu_data]
    n=len(x);params=kernel_params(case,cfg);lambd=n*candidate['lambda_unscaled']
    if method in ['official_askotchv2','corrected_askotchv2']:
        cls=FullKRR
        if method=='corrected_askotchv2':
            class CorrectedFullKRR(FullKRR):
                def _get_block_grad(self,w,block):
                    return super()._get_block_grad(w,block)+self.lambd*(w[block]-self.w[block])
            cls=CorrectedFullKRR
        model=cls(x,y,xv,yv,params,True,lambd,'regression',torch.zeros(n,device=device),device)
        block=min(n,max(16,n//100) if candidate['capacity']=='small' else max(32,n//20))
        rank=min(16,block)
        nu=n/block
        mu=min(lambd,0.9/nu)
        assert 0<mu<nu and mu*nu<=0.9+1e-12
        opt=ASkotchV2(model,block_sz=block,sampling_method='uniform',mu=mu,nu=nu,
                      precond_params={'type':'nystrom','r':rank,'rho':'damped'},accelerated=True)
        idx=None;details=dict(block_size=block,preconditioner_rank=rank,accelerated=True,
                             mu=mu,nu=nu,mu_times_nu=mu*nu,
                             acceleration_policy='mu=min(lambda,0.9/nu), nu=n/block',
                             theoretical_projection_bounds_certified=False)
    else:
        m=min(n,max(16,math.ceil(n*(.125 if candidate['capacity']=='small' else .5))))
        idx=torch.randperm(n,device=device)[:m]
        model=InducingKRR(x,y,xv,yv,params,True,idx,lambd,'regression',torch.zeros(m,device=device),device)
        opt=PCG(model,{'type':'falkon'})
        details=dict(inducing_points=m,inducing_selection='uniform without replacement',preconditioner='falkon')
    return model,opt,idx,details


def pcg_finished(opt):
    import torch
    if not hasattr(opt,'r'):return False
    denom=float(opt.rhs.norm())
    tolerance=1e-6 if opt.r.dtype==torch.float32 else 1e-10
    return float(opt.r.norm())<=tolerance*max(denom,1e-30)


def run_trial(method,case,cfg,candidate,cpu_data,device):
    import torch,gc
    warm_seconds=0.
    if cfg['timing']=='warm':
        warm_start=time.perf_counter()
        wm,wo,_,_=build(method,case,cfg,candidate,cpu_data,device)
        for _ in range(cfg['warmup_steps']):
            if pcg_finished(wo):break
            wo.step()
        # Compile prediction reduction; the result is not scored or selected.
        _=wm.K_tst@wm.w;sync(device)
        del wm,wo;gc.collect()
        if str(device).startswith('cuda'):torch.cuda.empty_cache()
        sync(device);warm_seconds=time.perf_counter()-warm_start
    # Fresh model, inducing selection, data transfer and preconditioner are timed.
    # No state from warmup is retained. RNG resets inside build.
    sync(device);start=time.perf_counter();deadline=start+cfg['trial_seconds']
    model,opt,idx,details=build(method,case,cfg,candidate,cpu_data,device)
    sync(device);setup_seconds=time.perf_counter()-start
    records=[];best=None;iterations=0;late_evaluations=0;stop='budget'
    def evaluate():
        nonlocal best,late_evaluations
        pred=model.K_tst@model.w
        mse=float((pred-model.b_tst).square().mean()) # conventional MSE, no 1/2
        weights=model.w.detach().cpu().clone()
        indices=None if idx is None else idx.detach().cpu().clone()
        sync(device);elapsed=time.perf_counter()-start
        eligible=elapsed<=cfg['trial_seconds'] and math.isfinite(mse) and bool(torch.isfinite(weights).all())
        records.append(dict(seconds=elapsed,iterations=iterations,validation_mse=mse if math.isfinite(mse) else None,eligible=eligible))
        if not eligible:late_evaluations+=1
        if eligible and (best is None or mse<best['validation_mse']):
            best=dict(validation_mse=mse,seconds=elapsed,iterations=iterations,weights=weights,indices=indices)
    if time.perf_counter()<deadline:evaluate()
    # Common wall-clock validation schedule. Last slot is at 95% to leave room
    # for synchronized evaluation. Late snapshots are never eligible.
    slots=[cfg['trial_seconds']*i/cfg['validation_intervals'] for i in range(1,cfg['validation_intervals'])]
    slots.append(.95*cfg['trial_seconds']);slot=0
    while time.perf_counter()<deadline and iterations<cfg['max_iterations']:
        if pcg_finished(opt):
            stop='residual_tolerance';evaluate();break
        opt.step();iterations+=1;sync(device)
        elapsed=time.perf_counter()-start
        if slot<len(slots) and elapsed>=slots[slot]:
            evaluate()
            while slot<len(slots) and time.perf_counter()-start>=slots[slot]:slot+=1
        if not bool(torch.isfinite(model.w).all()):stop='nonfinite';break
    if iterations>=cfg['max_iterations'] and time.perf_counter()<deadline:
        stop='iteration_limit'
    if time.perf_counter()<deadline and stop!='nonfinite' and (not records or records[-1]['iterations']!=iterations):
        evaluate()
    sync(device);total=time.perf_counter()-start
    report=dict(candidate=candidate,method_details=details,timing=cfg['timing'],warmup_seconds=warm_seconds,
                setup_seconds=setup_seconds,total_measured_seconds=total,budget_seconds=cfg['trial_seconds'],
                overrun_seconds=max(0.,total-cfg['trial_seconds']),iterations=iterations,
                stop=stop,late_or_invalid_evaluations=late_evaluations,checkpoints=records,
                selected_validation_mse=None if best is None else best['validation_mse'],
                selected_state_seconds=None if best is None else best['seconds'])
    return report,best


def worker(request_path,output_path,device):
    import torch,platform
    torch.set_num_threads(1)
    req=json.loads(Path(request_path).read_text());cfg=req['config'];case=req['case'];method=req['method']
    validate(cfg);source=verify_source();wall_start=time.perf_counter()
    prep_start=time.perf_counter();cpu_data=data(case,cfg);prep_seconds=time.perf_counter()-prep_start
    out=Path(output_path);out.parent.mkdir(parents=True,exist_ok=True)
    result=dict(status='running',method=method,case=case,source=source,torch=torch.__version__,
                device=device,dtype=cfg['dtype'],common_data_preparation_seconds=prep_seconds,
                timing=cfg['timing'],trials=[],test_accessed=False,platform=platform.platform())
    best=None;chosen=None
    for candidate in candidates(cfg):
        try:
            report,state=run_trial(method,case,cfg,candidate,cpu_data,device)
        except Exception as exc:
            report=dict(candidate=candidate,error=f'{type(exc).__name__}: {exc}',traceback=traceback.format_exc());state=None
        result['trials'].append(report)
        if state is not None and (best is None or state['validation_mse']<best['validation_mse']):
            best=state;chosen=candidate
        out.write_text(json.dumps(result,indent=2))
    if best is None:
        result.update(status='no_eligible_configuration',wall_seconds=time.perf_counter()-wall_start)
        out.write_text(json.dumps(result,indent=2));return result
    # Commit selection BEFORE constructing the test RNG stream or test tensors.
    state_path=out.with_suffix('.selected.pt')
    torch.save({'weights':best['weights'],'indices':best['indices']},state_path)
    selection=dict(candidate=chosen,validation_mse=best['validation_mse'],state_seconds=best['seconds'],
                   iterations=best['iterations'],all_validation_candidates_finished=True,
                   selected_state_sha256=hashlib.sha256(state_path.read_bytes()).hexdigest(),
                   selected_state_file=state_path.name,selection_unix_ns=time.time_ns())
    selection_path=out.with_suffix('.selection.json');selection_path.write_text(json.dumps(selection,indent=2))
    result['selection']=selection
    test_start=time.perf_counter();test_access_unix_ns=time.time_ns();xt,yt,latent=data(case,cfg,test=True)
    dtype=getattr(torch,cfg['dtype']);x=cpu_data[0].to(device=device,dtype=dtype)
    basis=x if best['indices'] is None else x[best['indices'].to(device)]
    w=best['weights'].to(device=device,dtype=dtype)
    xt,yt,latent=[v.to(device=device,dtype=dtype) for v in [xt,yt,latent]]
    pred=prediction(xt,basis,w,kernel_params(case,cfg));sync(device)
    result.update(status='complete',test_accessed=True,test_access_unix_ns=test_access_unix_ns,
                  test_mse=float((pred-yt).square().mean()),
                  test_latent_mse=float((pred-latent).square().mean()),test_evaluation_seconds=time.perf_counter()-test_start,
                  wall_seconds=time.perf_counter()-wall_start)
    result['search_measured_seconds']=sum(t.get('total_measured_seconds',0) for t in result['trials'])
    result['compile_warmup_seconds']=sum(t.get('warmup_seconds',0) for t in result['trials'])
    out.write_text(json.dumps(result,indent=2));return result


def suite(config_path,device,output_path):
    cfg=json.loads(Path(config_path).read_text());plan=validate(cfg);out=Path(output_path).resolve();out.mkdir(parents=True,exist_ok=True)
    (out/'config.json').write_text(json.dumps(cfg,indent=2));start=time.perf_counter();deadline=start+cfg['suite_timeout_seconds']
    reports=[]
    for ci,case in enumerate(cases(cfg)):
        # Rotate and reverse: each method occupies every position across cases.
        shift=(ci+case['seed'])%len(cfg['methods'])
        methods=cfg['methods'][shift:]+cfg['methods'][:shift]
        if (ci//len(cfg['methods']))%2:methods=list(reversed(methods))
        for method in methods:
            if time.perf_counter()>=deadline:break
            tag=f'case{ci:02d}_{method}';request=out/f'{tag}.request.json';result_path=out/f'{tag}.json'
            request.write_text(json.dumps(dict(config=cfg,case=case,method=method)))
            env=os.environ.copy();env['KEOPS_CACHE_FOLDER']=str(out/'keops-cache'/method)
            timeout=min(cfg['worker_timeout_seconds'],max(1,deadline-time.perf_counter()))
            worker_start=time.perf_counter()
            try:
                with (out/f'{tag}.log').open('w') as log:
                    proc=subprocess.run([sys.executable,str(Path(__file__).resolve()),'worker','--request',str(request),
                                         '--output',str(result_path),'--device',device],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
                status='finished' if proc.returncode==0 else 'worker_error'
            except subprocess.TimeoutExpired:status='worker_timeout'
            result=json.loads(result_path.read_text()) if result_path.exists() else {}
            reports.append(dict(tag=tag,process_status=status,process_wall_seconds=time.perf_counter()-worker_start,result=result))
            (out/'summary.json').write_text(json.dumps(dict(plan=plan,reports=reports,elapsed_seconds=time.perf_counter()-start),indent=2))
        if time.perf_counter()>=deadline:break
    summary=dict(plan=plan,reports=reports,elapsed_seconds=time.perf_counter()-start,
                 all_workers_completed=len(reports)==len(cases(cfg))*len(cfg['methods']))
    (out/'summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary))


def main():
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='command',required=True)
    for name in ['check','suite']:
        p=sub.add_parser(name);p.add_argument('--config',default=str(HERE/'pilot_config.json'))
        if name=='suite':p.add_argument('--device',default='cuda');p.add_argument('--output',default=str(HERE/'output/pilot'))
    p=sub.add_parser('worker');p.add_argument('--request',required=True);p.add_argument('--output',required=True);p.add_argument('--device',default='cuda')
    args=ap.parse_args()
    if args.command=='check':print(json.dumps(validate(json.loads(Path(args.config).read_text())),indent=2))
    elif args.command=='suite':suite(args.config,args.device,args.output)
    else:print(json.dumps(worker(args.request,args.output,args.device)))


if __name__=='__main__':main()
