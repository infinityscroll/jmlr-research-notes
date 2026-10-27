"""Outward integer certificate for M5–M8; no simulation."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import time

HERE=Path(__file__).resolve().parent
N=1_000_000
Q=2**44
NUM=(47*Q)**100
DEN0=50**100


def ceildiv(x,y): return -((-x)//y)
def add(x,y): return x[0]+y[0],x[1]+y[1]
def mul(x,y):
    assert min(*x,*y)>=0
    return x[0]*y[0]//Q,ceildiv(x[1]*y[1],Q)
def scale(x,a,b=1): return x[0]*a//b,ceildiv(x[1]*a,b)
def contraction(e,a,b=1):
    v=scale(e,a,b)
    assert v[1]<Q
    return Q-v[1],Q-v[0]
def gain(t):
    den=DEN0*t**51
    k=int(Q*.94*t**(-.51))
    while den*k**100>NUM: k-=1
    while den*(k+1)**100<=NUM: k+=1
    assert den*k**100<=NUM<den*(k+1)**100
    return k,k+1


def main():
    out=HERE/'moderate_bias_certificate.json'
    assert not out.exists(), 'Do not overwrite a certificate.'
    start=time.monotonic()
    e=gain(1);ee=mul(e,e)
    v=u=scale(ee,16);w=scale(mul(ee,ee),256)
    b=(0,0);total=(0,0)
    for t in range(2,N+1):
        e=gain(t);e2=mul(e,e)
        vhalf=scale(v,1,2);wthird=scale(w,1,3)
        hlo=max(0,vhalf[0]-wthird[1])
        hhi=max(0,vhalf[1]-wthird[0])
        d=contraction(e,1);c=contraction(e,1,2);c2=mul(c,c)
        b=add(mul(d,b),mul(e,(hlo,hhi)))
        total=add(total,b)
        v=add(mul(mul(d,d),v),scale(e2,16))
        w=add(add(mul(mul(c2,c2),w),scale(mul(mul(e2,c2),u),96)),scale(mul(e2,e2),256))
        u=add(mul(c2,u),scale(e2,16))
        if t%250000==0:
            print(json.dumps({'stage':'certifying_mean','t':t,'elapsed_seconds':time.monotonic()-start}),flush=True)
    lower=Fraction(total[0],Q*N)
    upper=Fraction(total[1],Q*N)
    assert lower>Fraction(131,25000)
    source=HERE/'moderate_curvature_bias_proposition.md'
    result={'status':'PASS','n':N,'fixed_point_scale':Q,'gain_intervals_verified':N,
            'recursion_average_lower':str(lower),'recursion_average_upper':str(upper),
            'lower_display_only':float(lower),'proves_negative_mean_strictly_exceeds':'131/25000',
            'normalized_lower_display_only':float(lower)*250,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'new_random_draws':0,'elapsed_seconds':time.monotonic()-start,
            'scope':'Negative-mean bound only, not a finite-bootstrap-coverage certificate.'}
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__': main()
