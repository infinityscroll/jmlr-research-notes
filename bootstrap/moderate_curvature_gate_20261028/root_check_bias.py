"""Independent one-sided integer recomputation of all million bias steps.

Uses a different fixed-point scale and fused rational polynomials, without
importing the producer's interval operations. No random trajectories.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import time

HERE=Path(__file__).resolve().parent
Q=2**42
N=1_000_000
NUM=(47*Q)**100
DEN0=50**100


def up(num,den):
    return (num+den-1)//den


def eta(t):
    k=int(Q*.94*t**(-.51))
    den=DEN0*t**51
    while den*k**100>NUM:
        k-=1
    while den*(k+1)**100<=NUM:
        k+=1
    assert den*k**100<=NUM<den*(k+1)**100
    return k,k+1


def main():
    output=HERE/'root_bias_certificate.json'
    if output.exists():
        raise FileExistsError(output)
    start=time.monotonic()
    lo,hi=eta(1)
    v=16*lo*lo//Q
    u=up(16*hi*hi,Q)
    w=up(256*hi**4,Q**3)
    mean=total=0
    for t in range(2,N+1):
        lo,hi=eta(t)
        d=Q-hi
        c=2*Q-lo
        assert 0<d<Q and Q<c<2*Q
        h=max(0,(3*v-2*w)//6)
        mean=(d*mean+lo*h)//Q
        total+=mean
        nextv=(d*d*v+16*lo*lo*Q)//(Q*Q)
        nextu=up(c*c*u+64*hi*hi*Q,4*Q*Q)
        nextw=up(c**4*w+384*hi*hi*c*c*u+4096*hi**4*Q,16*Q**4)
        v,u,w=nextv,nextu,nextw
        assert 0<=v<=u and w>=0 and mean>=0
    lower=Fraction(total,Q*N)
    assert lower>Fraction(131,25000)
    result={'status':'PASS','n':N,'scale':Q,'independent_gain_enclosures':N,
            'certified_negative_mean_lower':str(lower),'readable_lower':float(lower),
            'threshold':'131/25000','new_random_draws':0,
            'scope':'Bias bound only; no finite-coverage theorem or trajectory replication.',
            'source_sha256':hashlib.sha256((HERE/'moderate_curvature_bias_proposition.md').read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'elapsed_seconds':time.monotonic()-start}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
