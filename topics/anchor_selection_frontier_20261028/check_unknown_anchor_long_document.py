from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
checks=0
def check(v,msg):
    global checks
    if not v:raise AssertionError(msg)
    checks+=1
def comps(n,k):
    if k==1:
        yield (n,)
    else:
        for v in range(n+1):
            for tail in comps(n-v,k-1):yield (v,)+tail
def countlaw(p,N):
    result=[]
    for counts in comps(N,len(p)):
        weight=F(factorial(N))
        for x,z in zip(counts,p):weight=weight*z**x/factorial(x)
        result.append(weight)
    return result
results=[]
for M,N in product([1,2,3],[2,3,4]):
    a=F(1,64);b=F(3,4)-M*a;r=F(1,16);kap=F(1,128)
    d=[F(1,4)]+[a/2]*(2*M)+[b/2,b/2]
    z=[F(0)]+[v for _ in range(M) for v in [r,-r]]+[r/2,-r/2]
    chi=a*kap**2*r**2/(1-r*r)
    for sign in [-1,1]:
        p0=[dx*(1+sign*zx) for dx,zx in zip(d,z)]
        laws=[countlaw(p0,N)]
        for j in range(M):
            zj=z.copy();zj[1+2*j]*=1+kap;zj[2+2*j]*=1+kap
            pj=[dx*(1+sign*zx) for dx,zx in zip(d,zj)]
            check(sum(pj)==1 and min(pj)>0,"positive conditional law")
            check(sum((pj[x]-p0[x])**2/p0[x] for x in range(len(d)))==chi,"token diagonal")
            laws.append(countlaw(pj,N))
        for j in range(M):
            for k in range(M):
                v=sum(x*y/base for x,y,base in zip(laws[j+1],laws[k+1],laws[0]))
                check(v==((1+chi)**N if j==k else 1),"full multinomial inner product")
        check(all(sum(law)==1 for law in laws),"normalized full count laws")
    # A parameter-independent legal-style conditioning event: retain balanced signs.
    xis=[x for x in product([-1,1],repeat=4) if F(sum(x),4)**2<=F(1,2)]
    check(len(xis)==14,"conditioning event")
    for j in range(M):
        for k in range(M):
            avg=sum(((1+chi)**(4*N) if j==k else F(1)) for x in xis)/len(xis)
            check(avg==((1+chi)**(4*N) if j==k else 1),"conditioned common sign prior")
    results.append({"M":M,"N":N,"states":len(laws[0]),"one_token_chi":str(chi)})
out={"status":"PASS","assertions":checks,"fixtures":results,
     "scope":"Exact complete multinomial likelihood identities and common-sign conditioning; not a replacement for the proof",
     "source_sha256":sha256((HERE/"unknown_anchor_long_document_lower.md").read_bytes()).hexdigest(),
     "checker_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}
target=HERE/"unknown_anchor_long_document_certificate.json"
if target.exists():raise RuntimeError("Refuse certificate replacement")
target.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"status":"PASS","assertions":checks,"fixtures":len(results)}))

