"""Recompute all retained error summaries without replaying trajectories."""
from pathlib import Path
import json,hashlib
import numpy as np
HERE=Path(__file__).resolve().parent

def main():
    out=HERE/'saved_result_check.json'
    if out.exists():raise RuntimeError('Preserve saved verification')
    cfg=json.loads((HERE/'structured_release_protocol.json').read_text())
    result=json.loads((HERE/'structured_release_results.json').read_text())
    assert result['protocol_sha256']==hashlib.sha256((HERE/'structured_release_protocol.json').read_bytes()).hexdigest()
    assert cfg['script_sha256']==hashlib.sha256((HERE/'run_structured_release.py').read_bytes()).hexdigest()
    assert len(result['cases'])==8
    assert result['paired_float64_draws_equal']==[True,True]
    arrays=np.load(HERE/'structured_release_checkpoints.npz')
    target=np.where(np.arange(cfg['n'])%2==0,1.,-1.)
    rows=[];worst=0.
    for j,case in enumerate(result['cases']):
        assert all(case[k]==v for k,v in cfg['cases'][j].items())
        assert case['steps_completed']<=cfg['steps']
        if case['dtype']=='float64':
            assert case['status']=='complete' and case['steps_completed']==20000
        else:
            assert case['status']=='failed' and case['exception_type']=='_LinAlgError'
            assert case['actual_rounded_delta']==0
        d=case['actual_rounded_delta'];initial=(cfg['lambd']+d)*cfg['n']
        for checkpoint in case['checkpoints']:
            e=arrays[f'case_{j}_step_{checkpoint["step"]}'].astype(np.float64)-target
            sq=e*e
            energy=((cfg['lambd']+d)*sum(sq)+(1-d)*sum(e)**2)/initial
            error=abs(energy-checkpoint['relative_A_error'])/(1+abs(energy))
            worst=max(worst,error);assert error<1e-11
            rows.append(dict(case=j,step=checkpoint['step'],relative_A_error=float(energy),
                             maximum_coordinate_error=float(abs(e).max()),
                             largest_coordinate_energy_fraction=float(sq.max()/sq.sum()),
                             largest_ten_energy_fraction=float(np.sort(sq)[-10:].sum()/sq.sum())))
    paths=['structured_release_protocol.json','structured_release_results.json',
           'structured_release_checkpoints.npz','full_model_interface_results.json',
           'run_structured_release.py','check_full_model_interface.py','check_saved_results.py']
    report=dict(status='PASS',checks=len(rows),maximum_scaled_energy_discrepancy=worst,
                scope='Independent saved-state arithmetic and source binding, not a full independent trajectory replay',
                records=rows,files={x:hashlib.sha256((HERE/x).read_bytes()).hexdigest() for x in paths})
    out.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS',len(rows),'checkpoints; maximum discrepancy',worst)

if __name__=='__main__':main()
