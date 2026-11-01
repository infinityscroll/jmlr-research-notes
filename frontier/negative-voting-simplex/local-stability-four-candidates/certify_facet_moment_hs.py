#!/usr/bin/env python3
"""Arb + positive floating cubature certificate for tetrahedral facet HS.

The floating stage has an explicit 1e-6 relative forward-error envelope.
No floating transcendental is used in that stage: exponential weights are
Taylor18 polynomials, and cell constants/gradients and GL rules use Arb.
See the companion proof note for all analytic and arithmetic error budgets.
"""
import os,sys,json,time,math
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','VECLIB_MAXIMUM_THREADS']:
    os.environ[k]='1'
ROOT=Path(__file__).resolve().parent
import numpy as np
from flint import arb,ctx
from fractions import Fraction
from arb_facet_diagonal import diagonal
ctx.prec=128

N=60;J=18;h=1/8;cells=112;H=arb(1)/8
FP=arb(1)/10**6
UNDERFLOW=arb(2)**-600
EPS=3*H*H/64
ETA=arb(6).exp()*arb(3)**19/arb(math.factorial(19))
PREF=2*arb(2).sqrt()/(2*arb.pi())**arb('1.5')
EXPS=np.arange(N+1);EVENS=np.arange(0,N+1,2)
TWOS=np.array([float(1<<j) for j in range(31)])
COEFF=np.array([1/math.factorial(i) for i in range(J+1)])
MAX_ABS_T=0.0
assert np.finfo(np.float64).eps==2**-52 and sys.float_info.rounds==1
for j,c in enumerate(COEFF):
    assert abs(arb(float(c))*math.factorial(j)-1).upper()<arb(2)**-48

def gaussian_tail_certificate():
    def bracket(a):
        return Fraction(15**2,1)/(2*a)+1/(2*a*a)+1/(28*a*a)
    hs=Fraction(193536)*bracket(Fraction(3,16))*Fraction(3,8)**36
    ut=Fraction(1,8)*Fraction(3,8)**98
    vt=9*bracket(Fraction(7,16))*Fraction(3,8)**85
    assert hs<Fraction(1,10**7) and ut<Fraction(1,10**40) and vt<Fraction(1,10**30)
    return {'HS_rational_bound':str(hs),'U_rational_bound':str(ut),'V_rational_bound':str(vt)}

def arithmetic_budget_certificate():
    unit=Fraction(1,2**53)
    gamma_n=2000000*unit/(1-2000000*unit)
    # Independent audit: positive-operation depth, Horner condition,
    # node/gradient argument perturbations, and coefficient conversion.
    bound=404*gamma_n+Fraction(1000,10**11)+Fraction(1,10**10)
    assert bound<Fraction(1,10**6)
    return {'audited_relative_bound':str(bound),'envelope':'1/1000000'}

def txt(x):return x.str(40)
def check_mid(x,relative=True):
    f=float(x.mid())
    err=abs(x/arb(f)-1) if relative else abs(x-arb(f))
    assert err.upper()<arb('1e-12'),(x,err)
    return f

def gauss(n):
    nodes=[];weights=[]
    for k in range(n):
        r,w=arb.legendre_p_root(n,k,weight=True)
        r=(1+r)/2;w=w/2
        rf=float(r.mid());wf=float(w.mid())
        assert abs(r/arb(rf)-1).upper()<arb(2)**-48
        assert abs(w/arb(wf)-1).upper()<arb(2)**-48
        nodes.append(rf);weights.append(wf)
    return np.array(nodes),np.array(weights)

U49,W49=gauss(49);U67,W67=gauss(67)

def poly_exp(t):
    global MAX_ABS_T
    value=float(np.max(np.abs(t)))
    MAX_ABS_T=max(MAX_ABS_T,value)
    assert value<2.9
    p=np.full_like(t,COEFF[J])
    for j in range(J-1,-1,-1):p=p*t+COEFF[j]
    assert np.all(p>0)
    return p

def powers(x,degree=60):
    out=np.ones(x.shape+(degree+1,))
    for k in range(1,degree+1):out[...,k]=out[...,k-1]*x
    return out

def arbcells(i,j):
    q=(arb(2*i+1))/16;w=(arb(2*j+1))/16
    d,grad=diagonal(q,w)
    assert d>0
    rr=q*q+2*w*w
    cm=PREF*(-5*rr/8).exp()/d
    cv=PREF*(-rr/2).exp()/d
    cu=PREF*(-rr/2).exp()*d
    vals=[check_mid(c) for c in (cm,cv,cu)]
    grads=[check_mid(g,relative=False) for g in grad]
    return vals,grads,[txt(d),txt(grad[0]),txt(grad[1])]

def run():
    started=time.time()
    tail_certificate=gaussian_tail_certificate()
    arithmetic_certificate=arithmetic_budget_certificate()
    moments=np.zeros((61,31));U=0.;V=0.;cache=[]
    for i in range(cells):
        for j in range(i+1):
            (cm,cv,cu),(gq,gw),evidence=arbcells(i,j)
            qc=(i+.5)*h;wc=(j+.5)*h
            if i!=j:
                q=i*h+h*U49;w=j*h+h*U49
                dq=h*(U49-.5);dw=dq
                pq=powers(q);pw=powers(w)[:,::2]
                fq=-(1.25*qc+gq)*dq-.625*dq*dq
                fw=-(2.5*wc+gw)*dw-1.25*dw*dw
                iq=(h*W49*poly_exp(fq))@pq
                iw=(h*W49*poly_exp(fw))@pw
                moments+=cm*np.outer(iq,iw)*TWOS[None,:]
                fqv=-(qc+gq)*dq-.5*dq*dq
                fwv=-(2*wc+gw)*dw-dw*dw
                V+=cv*h*h*np.sum(W49*poly_exp(fqv))*np.sum(W49*poly_exp(fwv))
                fqu=-(qc-gq)*dq-.5*dq*dq
                fwu=-(2*wc-gw)*dw-dw*dw
                U+=cu*h*h*np.sum(W49*poly_exp(fqu))*np.sum(W49*poly_exp(fwu))
            else:
                qu=i*h+h*U67
                ww=i*h+h*U67[:,None]*U49[None,:]
                dq=h*(U67-.5);dw=h*(U67[:,None]*U49[None,:]-.5)
                pq=powers(qu);pw=powers(ww)[:,:,::2]
                fq=-(1.25*qc+gq)*dq-.625*dq*dq
                fw=-(2.5*wc+gw)*dw-1.25*dw*dw
                inner=np.einsum('uvn,uv,v->un',pw,poly_exp(fw),W49)
                outerweights=h*h*W67*U67*poly_exp(fq)
                moments+=cm*(pq.T@(outerweights[:,None]*inner))*TWOS[None,:]
                fqv=-(qc+gq)*dq-.5*dq*dq
                fwv=-(2*wc+gw)*dw-dw*dw
                V+=cv*h*h*np.sum(W67*U67*poly_exp(fqv)*(poly_exp(fwv)@W49))
                fqu=-(qc-gq)*dq-.5*dq*dq
                fwu=-(2*wc-gw)*dw-dw*dw
                U+=cu*h*h*np.sum(W67*U67*poly_exp(fqu)*(poly_exp(fwu)@W49))
            cache.append({'i':i,'j':j,'d_grad':evidence})
        if i%8==7:
            print('row',i+1,'of',cells,'seconds',time.time()-started,flush=True)
    assert np.all(np.isfinite(moments)) and np.min(moments)>2**-43
    np.savez(ROOT/'facet_moment_certificate_raw.npz',moments=moments,U=U,V=V)
    (ROOT/'facet_moment_certificate_cells.json').write_text(json.dumps(cache)+'\n')
    # Interval conversion of positive cubature and analytic model errors.
    lower_factor=1/((1+FP)*(1+ETA)**2)
    upper_factor=EPS.exp()/((1-FP)*(1-ETA)**2)
    ml={};mu={}
    for p in range(61):
        for q in range(0,61-p,2):
            f=arb(float(moments[p,q//2]))
            ml[p,q]=((f-UNDERFLOW)*lower_factor).lower()
            mu[p,q]=((f+UNDERFLOW)*upper_factor).upper()
    sig6=(arb(8)/9)**3
    low=arb(0);high=arb(0);abs_high=arb(0);terms=[]
    facts=[math.factorial(k) for k in range(61)]
    for k in range(61):
        blo=arb(0);bhi=arb(0)
        # Same-face term, after multiplication by (3/4)^k/k!.
        for q in range(0,k+1,2):
            p=k-q;coef=arb(1)/(facts[p]*facts[q])
            blo+=coef*ml[p,q]*ml[p,q];bhi+=coef*mu[p,q]*mu[p,q]
        # Adjacent-face contraction; nonzero iff l,m,n all same parity.
        for l in range(k+1):
            for m in range(k-l+1):
                n=k-l-m
                if (l-n)%2 or (m-n)%2:continue
                coef=arb(1)/(facts[l]*facts[m]*facts[n]*2**((l+m)//2+n))
                blo+=coef*ml[l,m+n]*ml[m,l+n]
                bhi+=coef*mu[l,m+n]*mu[m,l+n]
        factor=24*(arb(3)/4)**k/sig6
        blo*=factor;bhi*=factor
        if k%2==0:low+=blo;high+=bhi
        else:low-=bhi;high-=blo
        abs_high+=bhi
        terms.append({'k':k,'lower':txt(blo),'upper':txt(bhi)})
    # Exact rational global absolute-tail envelope supplied independently.
    def Jbound(n):
        val=arb(32)/27 if n%2==0 else arb(8)/9
        for j in range(n%2,n,2):val*=arb(8)*(j+1)/9
        return val
    def tbound(k):
        ii=Jbound(k+1)+2*Jbound(k+2)+Jbound(k+3)
        return 3456*(arb(3)/4)**k*ii*ii/arb(math.factorial(k))
    def qbound(k):return arb(4)*(k+4)**2/(9*(k+1)*(k+2))
    series_tail=tbound(61)/(1-qbound(61))+tbound(62)/(1-qbound(62))
    spatial_tail=arb(1)/10**7
    total_low=low-series_tail
    total_high=high+series_tail+spatial_tail
    # U=integral d dλ and V=integral 1/d dλ, with exponent factors differing.
    Ulo=arb(U)*lower_factor*(-EPS).exp()
    Uhi=arb(U)/((1-FP)*(1-ETA)**2)+arb(1)/10**40
    Vlo=arb(V)*lower_factor
    Vhi=arb(V)*upper_factor+arb(1)/10**30
    s=(-arb(1)/3).acos()/(2*arb.pi())**arb('1.5')
    delta_hi=1-s*s/(Uhi*Vhi)
    hhi=(total_high-30).sqrt()
    rayleigh_hi=hhi+(3-hhi)*delta_hi
    out={'status':'Certificate candidate: Arb analytic enclosures plus explicit positive-double forward error; requires independent code audit',
         'N':N,'mesh_h':'1/8','q_cutoff':14,'rectangles':6216,'triangles':112,
         'Taylor_degree':18,'Gauss_orders':[49,67],'floating_relative_envelope':txt(FP),
         'maximum_computed_abs_Taylor_argument':MAX_ABS_T,
         'exact_rational_Gaussian_tail_checks':tail_certificate,
         'exact_rational_forward_error_budget':arithmetic_certificate,
         'absolute_underflow_envelope_per_moment':txt(UNDERFLOW),
         'log_diagonal_curvature_error':txt(EPS),'single_exp_relative_error':txt(ETA),
         'lower_moment_factor':txt(lower_factor),'upper_moment_factor':txt(upper_factor),
         'absolute_partial_coefficient_sum_upper':txt(abs_high),
         'partial_HS_lower':txt(low),'partial_HS_upper':txt(high),
         'series_tail_upper':txt(series_tail),'spatial_tail_upper':txt(spatial_tail),
         'total_HS_lower':txt(total_low),'total_HS_upper':txt(total_high),
         'U_lower':txt(Ulo),'U_upper':txt(Uhi),'V_lower':txt(Vlo),'V_upper':txt(Vhi),
         'delta_upper':txt(delta_hi),'remainder_operator_norm_upper':txt(hhi),
         'mass_constrained_Rayleigh_upper':txt(rayleigh_hi),'seconds':time.time()-started,
         'claims_verified_by_interval_comparison':{'HS_below_30_6':bool(total_high<arb('30.6')),
             'delta_below_005':bool(delta_hi<arb('.05')),'Rayleigh_below_1':bool(rayleigh_hi<1),
             'HS_below_30_plus_3_over_8':bool(total_high<30+arb(3)/8),
             'delta_below_11_over_400':bool(delta_hi<arb(11)/400),
             'Rayleigh_below_17_over_25':bool(rayleigh_hi<arb(17)/25),
             'rational_square_comparison':3*389**2<8*239**2},
         'terms':terms}
    (ROOT/'facet_moment_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='terms'},indent=2),flush=True)

if __name__=='__main__':run()
