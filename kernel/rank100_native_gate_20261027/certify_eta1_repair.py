"""Exact, piecewise-uniform mean-square certificate for eta=1.

All 32 predetermined delta intervals are checked; no empirical search.
The old producer covariance map is separately bound and independently audited.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'rank100_default_gate_20261027'
sys.path.insert(0,str(OLD))
from general_block_operator import image
from check_rank100_mean_step import solve

N,B,S=10000,100,F(1,100000)
LEFT,RIGHT=F(1,20000000000),F(1,5000000000)
RATE=F(999999,1000000)
INITIAL=[F(1),F(0),F(1),F(0),F(1),F(0)]

def psd(v):
    a,b,c,d,e,f=v
    minors=[a,e,a*e-c*c,b,f,b*f-d*d]
    assert all(x>=0 for x in minors),list(map(str,minors))
    return list(map(str,minors))

def den(d):
    return (F(1,10**8)+2*d)*(B+F(1,10**8)-(B-2)*d)

def witness(d,stale):
    cols=[image(N,B,S,d,F(1),stale,[F(i==j) for i in range(6)]) for j in range(6)]
    A=[[F(i==j)-cols[j][i] for j in range(6)] for i in range(6)]
    Q=[F(1),F(1,10**20),F(0),F(0),F(10**6),F(1,10**14)]
    U=[r[0] for r in solve(A,[[x] for x in Q])]
    U=[x/U[0] for x in U]
    # Float is ONLY a coefficient proposal. Every resulting rational is
    # independently checked exactly below, including the whole interval.
    return [F(format(float(x),'.10g')) for x in U]

def main():
    path=HERE/'eta1_repair_certificate.json'
    if path.exists():raise RuntimeError('Preserve retained certificate')
    records=[]
    for stale in [True,False]:
      for box in range(32):
        lo=LEFT+(RIGHT-LEFT)*F(box,32)
        hi=LEFT+(RIGHT-LEFT)*F(box+1,32)
        U=witness((lo+hi)/2,stale)
        up=psd(U)
        reach=psd([3*u-x for u,x in zip(U,INITIAL)])
        values=[]
        for k in range(5):
            d=lo+(hi-lo)*F(k,4)
            values.append([den(d)**2*(RATE*u-v) for u,v in zip(U,image(N,B,S,d,F(1),stale,U))])
        powers=solve([[F(k,4)**j for j in range(5)] for k in range(5)],values)
        bern=[[sum(powers[j][i]*F(comb(k,j),comb(4,j)) for j in range(k+1)) for i in range(6)] for k in range(5)]
        checks=[psd(v) for v in bern]
        for t in [F(2,7),F(5,13)]:
            d=lo+(hi-lo)*t
            expected=[den(d)**2*(RATE*u-v) for u,v in zip(U,image(N,B,S,d,F(1),stale,U))]
            assert expected==[sum(bern[k][i]*comb(4,k)*t**k*(1-t)**(4-k) for k in range(5)) for i in range(6)]
        # Relative A-energy of 3U is <4 uniformly over the interval.
        max_mean_weight=(N+F(1,10**8)-(N-1)*lo)/((N-1)*(F(1,10**8)+lo))
        energy_upper=3*(U[0]+max_mean_weight*U[1])
        assert energy_upper<4
        records.append(dict(stale=stale,box=box,lo=str(lo),hi=str(hi),U=list(map(str,U)),
                            witness_psd=up,initial_domination=reach,
                            bernstein=[list(map(str,v)) for v in bern],minors=checks,
                            relative_initial_energy_upper=str(energy_upper)))
    result=dict(status='PASS',arithmetic='exact Fraction verification; floating proposal only',
                n=N,b=B,rank=B,eta='1',rate=str(RATE),energy_prefactor='4',
                delta_interval=[str(LEFT),str(RIGHT)],records=records,
                source_hashes={'certify_eta1_repair.py':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                               '../rank100_default_gate_20261027/general_block_operator.py':hashlib.sha256((OLD/'general_block_operator.py').read_bytes()).hexdigest()})
    with path.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS',len(records),'boxes;',len(records)*5,'PSD coefficient matrices')

if __name__=='__main__':main()
