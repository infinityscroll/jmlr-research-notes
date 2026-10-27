"""Exact rational checks for the N=2 weak-diversity anchor-location likelihood.
No simulation and no asymptotic inference. Does not replace the analytic proof.
"""
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
checks=0
def check(condition, label):
    global checks
    if not condition: raise AssertionError(label)
    checks+=1
def mm_row(row,w): return sum(x*y for x,y in zip(row,w))
def topic(K,M,a,theta,j):
    b=F(3,4)-M*a
    rows=[[F(1,4)]*K]
    for k in range(M):
        t=F(0) if j is None or j==k else theta
        rows += [[a*(1-t),a*t]+[F(0)]*(K-2),
                 [a*t,a*(1-t)]+[F(0)]*(K-2)]
    t=F(0) if j is None else theta
    rows += [[b*(F(3,4)-t/2),b*(F(1,4)+t/2)]+[F(0)]*(K-2),
             [b*(F(1,4)+t/2),b*(F(3,4)-t/2)]+[F(0)]*(K-2)]
    for k in range(2,K):
        row=[F(0)]*K; row[k]=F(3,4); rows.append(row)
    return rows
def designs(K):
    u=[F(1,K)]*K
    if K==2:return [u]
    out=[]
    for k in range(2,K):
        for sign in [-1,1]:
            b=u.copy()
            b[0]-=F(sign,4*K);b[1]-=F(sign,4*K)
            b[k]+=F(sign,2*K)
            out.append(b)
    return out
def inverse(w,theta):
    out=w.copy();den=1-2*theta
    out[0]=((1-theta)*w[0]-theta*w[1])/den
    out[1]=((1-theta)*w[1]-theta*w[0])/den
    return out
def ordered_law(A,baseline,amp,theta):
    ws=[]
    for sign in [-1,1]:
        w=baseline.copy();w[0]+=sign*amp;w[1]-=sign*amp
        w=inverse(w,theta)
        check(sum(w)==1 and min(w)>=F(1,4*len(w)),"physical mixture")
        ws.append([mm_row(row,w) for row in A])
    return [[(ws[0][x]*ws[0][y]+ws[1][x]*ws[1][y])/2
             for y in range(len(A))] for x in range(len(A))]
def inner(P,Q,P0):
    return sum(P[x][y]*Q[x][y]/P0[x][y]
               for x in range(len(P0)) for y in range(len(P0)))
fixtures=[]
for K,M in product(range(2,6),range(1,5)):
    a=F(1,64);theta=F(1,8192*K);amp=F(1,64*K)
    beta=amp*amp/8
    kappa=2*theta/(1-2*theta)
    A0=topic(K,M,a,theta,None)
    As=[topic(K,M,a,theta,j) for j in range(M)]
    b=F(3,4)-M*a
    for A in [A0]+As:
        check(all(sum(row[k] for row in A)==1 for k in range(K)),"stochastic A")
        for k in range(K):
            values=sorted((row[k] for row in A),reverse=True)
            check(all((i+1)**2*x<=16 for i,x in enumerate(values)),"weak qhalf radius4")
    for j,A in enumerate(As):
        mindist=min(sum(abs(A[x][k]-A0[x][perm[k]]) for x in range(len(A)) for k in range(K))
                    for perm in permutations(range(K)))
        check(mindist>=2*b*theta,"full topic quotient separation")
    for B in designs(K):
        t=B[0];r=amp/t;c=2*a*t
        d=[mm_row(row,B) for row in A0]
        z=[F(0)]*len(A0)
        for j in range(M):z[1+2*j]=r;z[2+2*j]=-r
        z[1+2*M]=r/2;z[2+2*M]=-r/2
        P0=ordered_law(A0,B,amp,F(0))
        Ps=[ordered_law(A,B,amp,theta) for A in As]
        check(sum(map(sum,P0))==1 and min(map(min,P0))>0,"null full law")
        check(all(P0[x][y]==d[x]*d[y]*(1+z[x]*z[y])
                  for x in range(len(d)) for y in range(len(d))),"null sign mixture")
        D=2*c*kappa*kappa*r*r*sum(d[x]*z[x]**2/(1-r*r*z[x]**2)
                     for x in range(len(d)) if x not in [1,2])
        D+=c*c*(2*kappa+kappa*kappa)**2*r**4/(1-r**4)
        O=2*c*c*kappa*kappa*r**4/(1-r**4)
        check(D<=2**16*K*K*a*theta*theta*beta*beta,"diagonal beta bound")
        check(O<=2**16*K*K*a*a*theta*theta*beta*beta,"cross beta bound")
        for j,P in enumerate(Ps):
            check(sum(map(sum,P))==1 and min(map(min,P))>0,"alternative full law")
            zz=z.copy();zz[1+2*j]*=1+kappa;zz[2+2*j]*=1+kappa
            check(all(P[x][y]==d[x]*d[y]*(1+zz[x]*zz[y])
                      for x in range(len(d)) for y in range(len(d))),"alternative sign mixture")
            check(inner(P,P,P0)-1==D,"exact diagonal")
            for k in range(j):
                check(inner(P,Ps[k],P0)-1==O,"exact positive cross")
        # In the count experiment, off-diagonal ordered pairs aggregate in twos.
        for j,P in enumerate(Ps):
            for k,Q in enumerate(Ps):
                count_inner=sum(P[x][x]*Q[x][x]/P0[x][x] for x in range(len(d)))
                count_inner+=sum(2*P[x][y]*Q[x][y]/P0[x][y]
                               for x in range(len(d)) for y in range(x))
                check(count_inner==inner(P,Q,P0),"count experiment inner product")
        fixtures.append({"K":K,"M":M,"B":[str(x) for x in B],
                         "a":str(a),"theta":str(theta),"beta":str(beta),
                         "diagonal":str(D),"off_diagonal":str(O)})
out={"status":"PASS","assertions":checks,"fixtures":fixtures,
     "scope":"Finite exact checks of A13-A16 and quotient separation, not a theorem proof",
     "source_sha256":sha256((HERE/"unknown_anchor_short_document_lower.md").read_bytes()).hexdigest(),
     "checker_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}
target=HERE/"unknown_anchor_short_document_certificate.json"
if target.exists(): raise RuntimeError("Refusing to replace existing certificate")
target.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"status":out["status"],"assertions":checks,"fixtures":len(fixtures),
                  "source_sha256":out["source_sha256"]}))

