"""Independent comparison to literal resampled-array legacy metrics; synthetic only."""
import importlib.util
import json
from pathlib import Path
import tempfile
import time
import numpy as np
from cached_metrics import kernel, cached_kvd, evaluate, count_draws, SEED
from analyze_complete import require_complete_paths

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('original', HERE.parent/'heldout_metrics.py')
old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old)


def main():
    rng = np.random.default_rng(34091)
    errors = []
    explicit_cases = 0
    for n,m,d in [(3,5,2),(9,7,5),(4,4,1)]:
        x,y = rng.normal(size=(n,d)), rng.normal(size=(m,d))
        # Repeated observations and all-equal resampling are deliberate.
        indices = [(np.zeros(n,dtype=int),np.zeros(m,dtype=int)),
                   (np.arange(n)%2,np.arange(m)%2), (np.arange(n),np.arange(m))]
        indices += [(rng.integers(n,size=n),rng.integers(m,size=m)) for _ in range(30)]
        for i,j in indices:
            c = np.bincount(i,minlength=n).astype(float)[None,:]
            r = np.bincount(j,minlength=m).astype(float)[None,:]
            expected = old.kvd(x[i],y[j])
            actual = cached_kvd(kernel(x,x),kernel(y,y),kernel(x,y),c,r)[0]
            np.testing.assert_allclose(actual,expected,rtol=2e-12,atol=2e-12)
            errors.append(abs(actual-expected));explicit_cases += 1
    ref,gen = rng.normal(size=(7,5)),rng.normal(size=(4,9,6,5))
    b = 79
    points,boot = evaluate(ref,gen,b)
    legacy_points = np.array([[old.kvd(ref,g[:,h]) for h in range(6)] for g in gen])
    legacy_boot = [];draw_rng=np.random.default_rng(SEED)
    gc,rc = count_draws(9,7,b)
    for j in range(b):
        inds=draw_rng.integers(9,size=9);rinds=draw_rng.integers(7,size=7)
        np.testing.assert_array_equal(gc[j],np.bincount(inds,minlength=9))
        np.testing.assert_array_equal(rc[j],np.bincount(rinds,minlength=7))
        legacy_boot.append([old.kvd(ref[rinds],g[inds,-1])-old.kvd(ref[rinds],g[inds,0]) for g in gen])
    legacy_boot=np.asarray(legacy_boot)
    np.testing.assert_allclose(points,legacy_points,rtol=2e-12,atol=2e-12)
    np.testing.assert_allclose(boot,legacy_boot,rtol=2e-12,atol=2e-12)
    interval_error=0.
    for i in range(4):
        for j in range(i+1,4):
            a=np.quantile(boot[:,i]-boot[:,j],[.025,.975])
            e=np.quantile(legacy_boot[:,i]-legacy_boot[:,j],[.025,.975])
            np.testing.assert_allclose(a,e,rtol=2e-12,atol=2e-12)
            interval_error=max(interval_error,float(np.max(abs(a-e))))
    # All paths must exist before a single shard is read. Existing placeholders
    # are intentionally invalid JSON; the missing-file gate must fire first.
    with tempfile.TemporaryDirectory() as folder:
        root=Path(folder)
        for kind,count in [('calibration',4),('rollout',31)]:
            for i in range(count):(root/f'{kind}_{i:02d}.json').write_text('invalid JSON')
        try:require_complete_paths(root)
        except ValueError as e:
            assert 'rollout_31.json' in str(e) and 'No analysis of partial results' in str(e)
        else:raise AssertionError('Accepted incomplete study')
        (root/'rollout_31.json').write_text('invalid JSON')
        assert len(require_complete_paths(root))==36
    # Full-size timing is random synthetic data, with all 2000 frozen draws.
    ref=rng.normal(size=(128,400));gen=rng.normal(size=(4,128,6,400))
    start=time.monotonic();k,bt=evaluate(ref,gen)
    assert k.shape==(4,6) and bt.shape==(2000,4) and np.isfinite(bt).all()
    result={'status':'passed','data':'synthetic only; no study features read',
            'explicit_duplicate_index_cases':explicit_cases,
            'max_explicit_kvd_abs_error':max(errors),
            'max_bootstrap_abs_error':float(np.max(abs(boot-legacy_boot))),
            'max_pairwise_percentile_abs_error':interval_error,
            'rng_count_arrays_exact':True,'missing_final_shard_rejected_before_reads':True,
            'full_size_2000_bootstrap_seconds':time.monotonic()-start,'numpy_version':np.__version__}
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
