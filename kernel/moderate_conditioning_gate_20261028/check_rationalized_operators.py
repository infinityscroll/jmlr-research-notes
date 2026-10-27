"""Exact covariance algebra at rationalized nearby parameter grid points.

Quadrature and eigenvalues remain floating point; no stability proof is claimed.
This check removes cancellation in constructing the six-coordinate matrix.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,math,sys,time
import numpy as np

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'rank100_default_gate_20261027'))
from general_block_operator import image
from explore_operator import moments


def op(s,delta,stale,eta):
    gamma=1/(100*s)
    scale=[F(1),F(1),gamma,gamma,gamma**2,gamma**2]
    columns=[]
    for i in range(6):
        c=[F(0)]*6;c[i]=scale[i]
        result=image(10000,100,s,delta,F(eta),stale,c)
        columns.append([x/y for x,y in zip(result,scale)])
    return [[columns[j][i] for j in range(6)] for i in range(6)]


def main():
    out=HERE/'rationalized_operator_check.json'
    assert not out.exists()
    old=json.loads((HERE/'exploration.json').read_text())['cases']
    checked=[];start=time.monotonic()
    for row in old:
        s=F(str(math.sqrt(row['lam']/100)))
        lam=100*s*s;delta=F(str(row['ratio']))*lam
        m1,m2=moments(float(lam),float(delta),512)
        e1,e2=F(str(m1)),F(str(m2))
        a,b,c=[op(s,delta,row['stale'],eta) for eta in [0,1,2]]
        matrix=[]
        for i in range(6):
            line=[]
            for j in range(6):
                quadratic=(c[i][j]-2*b[i][j]+a[i][j])/2
                linear=b[i][j]-a[i][j]-quadratic
                line.append(float(a[i][j]+e1*linear+e2*quadratic))
            matrix.append(line)
        radius=float(max(abs(np.linalg.eigvals(np.asarray(matrix)))))
        checked.append({'nominal_lambda':row['lam'],'ratio':row['ratio'],'stale':row['stale'],
            'exact_lambda':str(lam),'exact_delta':str(delta),
            'lambda_relative_displacement':abs(float(lam)/row['lam']-1),
            'spectral_radius_512_exact_matrix_algebra':radius,
            'radius_difference':abs(radius-row['spectral_radius_256']),
            'condition_number':float((10000+lam-9999*delta)/(lam+delta))})
    selected=[r for r in checked if r['condition_number']<1e9 and r['spectral_radius_512_exact_matrix_algebra']>1.0001]
    result={'scope':'Exact rational operator algebra on nearby rationalized grid; numerical quadrature and eigenvalues, not a proof.',
        'cases':checked,'selected_count':len(selected),
        'maximum_radius_discrepancy':max(r['radius_difference'] for r in checked),
        'maximum_relative_lambda_displacement':max(r['lambda_relative_displacement'] for r in checked),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'elapsed_seconds':time.monotonic()-start}
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))


if __name__=='__main__':main()
