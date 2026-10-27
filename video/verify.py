"""Recompute the frozen feature-level KVD result without a model or cloud."""
from pathlib import Path
import hashlib,json,sys
import numpy as np

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'final_analysis'))
from cached_metrics import evaluate

def main():
    root=HERE/'final_analysis/completed_study';ev=root/'evidence'
    read=lambda p:json.loads(p.read_text())
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    prov=read(root/'provenance.json');m=read(root/'metrics.json');sel=read(ev/'selection.json')
    for name,key in [('features.npz','feature_sha256'),('metrics.json','metrics_sha256')]:assert sha(root/name)==prov[key]
    for name,key in [('protocol.json','protocol_sha256'),('selection.json','selection_sha256'),('analysis_freeze.json','analysis_freeze_sha256')]:assert sha(ev/name)==prov[key]
    with np.load(root/'features.npz',allow_pickle=False) as z:
        ref=z['reference'].astype(np.float64);gen=z['generated'].astype(np.float64)
        names=z['schedule_names'].tolist()
        assert ref.shape==(128,400) and gen.shape==(4,128,6,400)
        assert names==sel['schedules']==m['schedules']
    points,boot=evaluate(ref,gen)
    assert np.max(abs(points-np.array(m['kvd_by_horizon'])))<1e-8
    delta=points[:,-1]-points[:,0]
    checks=[m['primary'],*m['exploratory_other_pairwise_comparisons']]
    for row in checks:
        a=names.index(row['a']);b=names.index(row['b'])
        assert abs(delta[a]-delta[b]-row['kvd_degradation_difference_a_minus_b'])<1e-8
        ci=np.quantile(boot[:,a]-boot[:,b],[.025,.975],method='linear')
        assert np.max(abs(ci-np.array(row['paired_bootstrap_95_percentile_interval'])))<1e-7
    assert m['primary']['a']==sel['primary_best'] and m['primary']['b']==sel['primary_worst']
    lo,hi=m['primary']['paired_bootstrap_95_percentile_interval'];assert lo<0<hi
    print('PASS: complete feature shapes, bound inputs, 24 KVD points and all six paired intervals; primary remains inconclusive.')

if __name__=='__main__':main()
