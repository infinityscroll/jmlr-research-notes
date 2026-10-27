"""Bounded release checks; never run a solver or modify retained artifacts."""
from pathlib import Path
import json, math, shutil, statistics, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent

def main():
    aggregate=json.loads((HERE/'replicated_analysis/aggregate.json').read_text())
    assert aggregate['cells']==90 and aggregate['models']==270
    rows=aggregate['paired_comparisons'];assert len(rows)==54
    primary=[]
    for row in rows:
        data=row['raw_seeds'];assert len(data)==5
        ds=[r['left_test_mse']-r['right_test_mse'] for r in data]
        assert all(abs(d-r['difference'])<1e-14 for d,r in zip(ds,data))
        m=statistics.mean(ds);se=statistics.stdev(ds)/math.sqrt(5)
        assert abs(m-row['mean_paired_difference'])<1e-14
        assert abs(se-row['paired_seed_standard_error'])<1e-14
        assert max(abs(a-b) for a,b in zip([m-2.7764451051977987*se,m+2.7764451051977987*se],row['student_t4_95_interval']))<1e-14
        assert sum(d<0 for d in ds)==row['left_wins_out_of_5']
        if row['left']=='official_askotchv2' and row['right']=='inducing_pcg_falkon':primary.append(m)
    assert len(primary)==18 and sum(x<0 for x in primary)==13
    grid=json.loads((HERE/'moderate_conditioning_gate_20261028/exploration.json').read_text())
    cert=json.loads((HERE/'moderate_conditioning_gate_20261028/rationalized_operator_check.json').read_text())
    assert len(grid['cases'])==len(cert['cases'])==140 and cert['selected_count']==0
    assert not any(r['condition_number']<1e9 and r['spectral_radius_256']>1.0001 for r in grid['cases'])
    with tempfile.TemporaryDirectory(prefix='kernel-release-') as tmp:
        dest=Path(tmp).resolve()
        for folder in ['rank100_default_gate_20261027','rank100_native_gate_20261027']:
            shutil.copytree(HERE/folder,dest/folder,ignore=shutil.ignore_patterns('__pycache__'))
        # Original readers create new receipts; remove only disposable copies.
        for folder,name in [('rank100_native_gate_20261027','independent_eta1_saved_certificate.json'),('rank100_native_gate_20261027','saved_result_check.json')]:
            (dest/folder/name).unlink(missing_ok=True)
        for rel in ['rank100_default_gate_20261027/independent_dense_and_certificate_check.py','rank100_native_gate_20261027/independent_eta1_saved_check.py','rank100_native_gate_20261027/check_saved_results.py']:
            r=subprocess.run([sys.executable,str(dest/rel)],text=True,capture_output=True,timeout=120)
            if r.returncode:raise RuntimeError(rel+'\n'+r.stdout+'\n'+r.stderr)
            print('PASS',rel)
    print('PASS: 54 paired comparisons; 18 regimes; 140 retained grid cases; exact certificates and all saved states.')

if __name__=='__main__':main()
