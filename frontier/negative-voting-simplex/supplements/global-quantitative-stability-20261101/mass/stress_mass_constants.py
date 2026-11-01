#!/usr/bin/env python3
"""Independent stdlib-only numeric stress test. Not interval certification.
Integrates survival functions of max of m iid standard Gaussians; no
finite-dimensional score optimization or Monte Carlo enters this check.
"""
import json, math
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def adaptive_simpson(f, a, b, tolerance=2e-12, depth=28):
    c=(a+b)/2; fa=f(a); fc=f(c); fb=f(b)
    whole=(b-a)*(fa+4*fc+fb)/6
    def rec(a,b,fa,fc,fb,whole,tol,d):
        c=(a+b)/2; l=(a+c)/2; r=(c+b)/2
        fl=f(l); fr=f(r)
        left=(c-a)*(fa+4*fl+fc)/6
        right=(b-c)*(fc+4*fr+fb)/6
        defect=left+right-whole
        if d==0 or abs(defect)<=15*tol:
            return left+right+defect/15
        return rec(a,c,fa,fl,fc,left,tol/2,d-1)+rec(c,b,fc,fr,fb,right,tol/2,d-1)
    return rec(a,b,fa,fc,fb,whole,tolerance,depth)

def normal_tail(x): return math.erfc(x/math.sqrt(2))/2

def stats(m):
    hi=math.sqrt(2*math.log(m))+10
    def plus(t):
        q=normal_tail(t)
        return -math.expm1(m*math.log1p(-q))
    def minus(t):
        q=normal_tail(t)
        return math.exp(m*math.log(q)) if q else 0.0
    mean=adaptive_simpson(lambda t: plus(t)-minus(t),0,hi)
    second=adaptive_simpson(lambda t: 2*t*(plus(t)+minus(t)),0,hi)
    lo=0.0; upper=hi
    for _ in range(90):
        mid=(lo+upper)/2
        if normal_tail(mid)>1/m: lo=mid
        else: upper=mid
    b=(lo+upper)/2
    density=math.exp(-b*b/2)/math.sqrt(2*math.pi)
    w=mean*mean/(m-1)
    individual=m*density*density
    a2=m*(second-1)**2/(2*(m-1)*(m-2))
    tangent=(m*w-1)**2/(2*m)
    B=max(2*math.log(m)+1,6)
    Lcert=(m*m/(1-B/(m-1)))*((individual-w)/(m-1)+a2/(m-1)**2+1/(m-1)**3+1/(m-1)**4)
    return dict(m=m,mean=mean,second=second,variance=second-mean*mean,m_individual_minus_w=m*(individual-w),mass_certificate=Lcert,m_reference_degree2_defect=m*(a2-tangent))

K=128*4*math.pi*(56*math.exp(1.5)+2)/(0.01**2)
rows=[stats(m) for m in (100,1000,10000,1000000,10**9,10**12)]
# A sufficient asymptotic gate for the explicit K in the source, evaluated
# monotonically in this large-m region. This is not a full theorem threshold.
lo,hi=10**6,10**15
while lo+1<hi:
    mid=(lo+hi)//2
    gate=K*(1+math.log(mid/.01))**2/(mid-1)
    if gate<=.5: hi=mid
    else: lo=mid
out=dict(disclaimer='Floating-point numerical stress test only; not a proof or full theorem m0.',euler_gamma_limit=2-2*0.5772156649015329,explicit_K_c001_C2=K,first_integer_for_displayed_half_coefficient_gate=hi,rows=rows)
(ROOT/'stress_mass_constants.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
