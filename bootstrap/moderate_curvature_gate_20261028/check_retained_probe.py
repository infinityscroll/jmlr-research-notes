"""Independent saved-output and exact binomial endpoint checks; no new draws."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import math
import numpy as np

HERE=Path(__file__).resolve().parent


def cdf_numerator(n,k,a,b):
    return sum(math.comb(n,j)*a**j*(b-a)**(n-j) for j in range(k+1))


def main():
    out=HERE/'retained_probe_validation.json'
    assert not out.exists()
    report=json.loads((HERE/'probe_results.json').read_text())
    assert report['complete'] and report['completed_steps']==1_000_000
    data=np.load(HERE/'probe_outputs.npz')
    assert hashlib.sha256((HERE/'probe_outputs.npz').read_bytes()).hexdigest()==report['outputs_sha256']
    assert data['averaged_iterates'].shape==(2,512,4)
    assert data['sample_means'].shape==(512,4)
    assert np.array_equal(data['sample_means'][:,0],4*(2*data['original_plus_counts']-1_000_000)/1_000_000)
    assert np.array_equal(data['checkpoint_steps'],[100,1000,10000,100000,1000000])
    assert np.array_equal(data['checkpoint_averages'][-1],data['averaged_iterates'])
    assert np.all(np.isfinite(data['checkpoint_averages']))
    # Independent formula, avoiding the producer's sinh implementation.
    x=data['saa'][0]
    residual=x+.25*(np.logaddexp(2*x,-2*x)-math.log(2))-data['sample_means']
    assert np.max(np.abs(residual))<1e-13
    names=['logcosh_ASGD','quadratic_ASGD','logcosh_SAA_control','quadratic_SAA_control']
    stats=[data['averaged_iterates'][0],data['averaged_iterates'][1],data['saa'][0],data['saa'][1]]
    checked=[]
    for j,(name,stat) in enumerate(zip(names,stats)):
        differences=stat[:,1:]-stat[:,0,None]
        radius=3.182446305284263*np.linalg.norm(differences,axis=1)/math.sqrt(3)
        mask=np.abs(stat[:,0])<=radius
        k=int(mask.sum());n=len(mask)
        assert k==report['results'][name]['covered']
        assert np.array_equal(mask,data['coverage_masks'][j])
        lo,hi=report['results'][name]['monte_carlo_95_CP']
        scale=10**8
        a_lo=math.floor(lo*scale);a_hi=math.ceil(hi*scale)
        # Exact inequalities certify outward endpoints, independently of floats.
        assert 40*cdf_numerator(n,k-1,a_lo,scale)>=39*scale**n
        assert 40*cdf_numerator(n,k,a_hi,scale)<=scale**n
        checked.append({'case':name,'covered':k,'replications':n,
                        'exact_outward_CP_lower':str(F(a_lo,scale)),
                        'exact_outward_CP_upper':str(F(a_hi,scale))})
    # Exact small experiment: count-first uniform ordering equals iid data, and
    # subsequent empirical Bernoulli draws equal ordinary empirical resampling.
    checks=0
    for original in product((0,1),repeat=3):
        k=sum(original);remaining=k
        sequential=F(math.comb(3,k),8)
        for t,z in enumerate(original):
            sequential*=F(remaining if z else 3-t-remaining,3-t)
            remaining-=z
        assert sequential==F(1,8)
        for bootstrap in product((0,1),repeat=3):
            count_first=sequential
            direct=F(1,8)
            for z in bootstrap:
                count_first*=F(k if z else 3-k,3)
                direct*=F(sum(int(v==z) for v in original),3)
            assert count_first==direct
            checks+=1
    result={'status':'PASS','no_new_random_draws':True,'terminal_cases':checked,
            'exact_small_joint_law_checks':checks,
            'maximum_SAA_residual':float(np.max(np.abs(residual))),
            'outputs_sha256':report['outputs_sha256'],
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Saved numerical statistics, confidence endpoints and algorithm-law mapping; not independent terminal-trajectory replication.'}
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
