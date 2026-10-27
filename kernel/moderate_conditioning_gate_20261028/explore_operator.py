from pathlib import Path
import hashlib,json,math,sys
import numpy as np

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'rank100_default_gate_20261027'))
from general_block_operator import image


def moments(lam,delta,nodes):
    x,w=np.polynomial.legendre.leggauss(nodes)
    u=(x+1)/2
    weights=w*np.exp(math.lgamma(50)-math.lgamma(.5)-math.lgamma(49.5))*np.power(1-u*u,48.5)
    assert abs(weights.sum()-1)<1e-10
    a=(lam+delta)/(lam+2*delta)
    h=(100+lam-99*delta)/(100+lam-98*delta)
    R=(h/a)**18
    Z=u*u
    top=R*Z/(1+(R-1)*Z)
    eta=1/(a+(h-a)*top)
    return float(weights@eta),float(weights@(eta*eta))


def operator(lam,delta,stale,eta):
    s=math.sqrt(lam/100)
    gamma=1/math.sqrt(lam*100)
    scales=np.array([1,1,gamma,gamma,gamma*gamma,gamma*gamma])
    matrix=[]
    for i in range(6):
        C=np.zeros(6);C[i]=scales[i]
        matrix.append(np.array(image(10000,100,s,delta,eta,stale,C),dtype=float)/scales)
    return np.column_stack(matrix)


def main():
    out=HERE/'exploration.json'
    assert not out.exists()
    results=[]
    for exponent in range(3,10):
        lam=10.**(-exponent)
        for ratio in [.0001,.001,.003,.01,.03,.1,.3,1.,3.,10.]:
            delta=lam*ratio
            mm=[moments(lam,delta,nodes) for nodes in [128,256]]
            for stale in [True,False]:
                m0,m1,m2=[operator(lam,delta,stale,eta) for eta in [0.,1.,2.]]
                quadratic=(m2-2*m1+m0)/2
                linear=m1-m0-quadratic
                radii=[]
                for first,second in mm:
                    mat=m0+first*linear+second*quadratic
                    radii.append(float(max(abs(np.linalg.eigvals(mat)))))
                results.append(dict(lam=lam,delta=delta,ratio=ratio,stale=stale,
                    condition_number=(10000+lam-9999*delta)/(lam+delta),
                    eta_moments_128=mm[0],eta_moments_256=mm[1],
                    spectral_radius_128=radii[0],spectral_radius_256=radii[1],
                    quadrature_radius_difference=abs(radii[1]-radii[0])))
    record=dict(scope='exploratory floating covariance spectra; not a proof or native trajectory',
        protocol_sha256=hashlib.sha256((HERE/'PROTOCOL.md').read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        operator_sha256=hashlib.sha256((HERE.parent/'rank100_default_gate_20261027/general_block_operator.py').read_bytes()).hexdigest(),
        cases=results)
    out.write_text(json.dumps(record,indent=2)+'\n')
    selected=[r for r in results if r['condition_number']<1e9 and r['spectral_radius_256']>1.0001]
    print(json.dumps({'cases':len(results),'selected_count':len(selected),
                     'selected':sorted(selected,key=lambda r:-r['spectral_radius_256'])[:10],
                     'max_quadrature_radius_difference':max(r['quadrature_radius_difference'] for r in results)},indent=2))


if __name__=='__main__':main()
