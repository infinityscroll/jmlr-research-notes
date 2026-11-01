"""Arb evaluation of actual facet normal derivative and its log gradient."""
from flint import arb, acb, ctx
ctx.prec=96
PI=arb.pi();SQRT2=arb(2).sqrt();SQRTPI=PI.sqrt();S23=(arb(2)/3).sqrt()
CORR=arb(1)/3;SC=(1-CORR*CORR).sqrt()

def Phi(x):return (1+(x/SQRT2).erf())/2
def phi(x):return (-(x*x)/2).exp()/(2*PI).sqrt()

def cdf(u,v):
    def integrand(t,analytic):
        den=1-t*t
        return (-(u*u-2*t*u*v+v*v)/(2*den)).exp()/(2*PI*den.sqrt(analytic=analytic))
    value=acb.integral(integrand,0,CORR,rel_tol=1e-15,abs_tol=1e-45,eval_limit=10000)
    return Phi(u)*Phi(v)+value.real

def diagonal(q,w):
    q=arb(q);w=arb(w)
    means=[-q/(4*SQRT2),-q/(4*SQRT2),(q/2-w)/(2*SQRT2),(q/2+w)/(2*SQRT2)]
    dq=[-1/(4*SQRT2),-1/(4*SQRT2),1/(4*SQRT2),1/(4*SQRT2)]
    dw=[arb(0),arb(0),-1/(2*SQRT2),1/(2*SQRT2)]
    vals=[];grads=[]
    for i,j in [(0,1),(0,2),(0,3)]:
        k,l=[a for a in range(4) if a not in (i,j)]
        delta=means[i]-means[j];avg=(means[i]+means[j])/2
        u=S23*(avg-means[k]);v=S23*(avg-means[l])
        F=cdf(u,v);pref=(-(delta*delta)/4).exp()/(2*SQRTPI)
        Fu=phi(u)*Phi((v-CORR*u)/SC);Fv=phi(v)*Phi((u-CORR*v)/SC)
        vals.append(pref*F);gg=[]
        for der in [dq,dw]:
            davg=(der[i]+der[j])/2;ddelta=der[i]-der[j]
            du=S23*(davg-der[k]);dv=S23*(davg-der[l])
            gg.append(pref*(-delta*ddelta*F/2+du*Fu+dv*Fv))
        grads.append(gg)
    d=(2*vals[0]+vals[1]+vals[2])/2
    grad=[(2*grads[0][k]+grads[1][k]+grads[2][k])/(2*d) for k in range(2)]
    return d,grad

if __name__=='__main__':
    import time
    t=time.time()
    for q,w in [(0,0),(1,.5),(6,4),(14,14)]:print(q,w,diagonal(q,w))
    print('seconds',time.time()-t)
