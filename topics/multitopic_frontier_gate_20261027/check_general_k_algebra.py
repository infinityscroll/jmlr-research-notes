"""Bounded exact algebra; this does not verify stochastic inequalities or rates."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import hashlib, json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'general_k_upper.md'
EXPECTED='56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6'
counts={}
def check(x, group):
    assert x, group
    counts[group]=counts.get(group,0)+1
def tr(a): return list(map(list,zip(*a)))
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a): return [[-x for x in row] for row in a]
def scale(a,s): return [[x*s for x in row] for row in a]
def eye(k): return [[F(i==j) for j in range(k)] for i in range(k)]
def inv(a):
    n=len(a); b=[row[:]+e for row,e in zip(a,eye(n))]
    for j in range(n):
        q=next(i for i in range(j,n) if b[i][j]); b[j],b[q]=b[q],b[j]
        z=b[j][j]; b[j]=[x/z for x in b[j]]
        for i in range(n):
            if i!=j:
                z=b[i][j]; b[i]=[x-z*y for x,y in zip(b[i],b[j])]
    return [row[n:] for row in b]
def det(a):
    b=[row[:] for row in a]; out=F(1); n=len(b)
    for j in range(n):
        q=next((i for i in range(j,n) if b[i][j]),None)
        if q is None:return F(0)
        if q!=j:b[j],b[q]=b[q],b[j];out=-out
        z=b[j][j];out*=z
        for i in range(j+1,n):
            z1=b[i][j]/z
            b[i]=[x-z1*y for x,y in zip(b[i],b[j])]
    return out
def eq(a,b,group):
    check(len(a)==len(b) and len(a[0])==len(b[0]),group)
    for ar,br in zip(a,b):
        for x,y in zip(ar,br): check(x==y,group)

check(hashlib.sha256(SOURCE.read_bytes()).hexdigest()==EXPECTED,'source_binding')
fixtures=[]
for k in range(2,6):
    p=2*k;n=2*k;a=F(1,8)
    A=[[a*F(i==j) for j in range(k)] for i in range(k)]
    A += [[(1-a)*(F(3,4)*F(i==j)+F(1,4*k)) for j in range(k)] for i in range(k)]
    for eps in (F(1,4),F(1,16)):
        W=tr([[F(1,k)+sign*eps*(F(t==j)-F(1,k)) for t in range(k)]
              for j in range(k) for sign in (-1,1)])
        Sigma=scale(mm(W,tr(W)),F(1,n)); Si=inv(Sigma)
        mu=[sum(row)/n for row in W]
        pi=mm(A,W)
        for N in (2,3):
            # Fixed legal count outcomes, not stochastic simulation.
            X=[[0]*n for _ in range(p)]
            for i in range(n):
                for t in range(N): X[(i+2*t)%p][i]+=1
            X=[[F(x) for x in row] for row in X]
            Eps=add(scale(X,F(1,N)),neg(pi))
            Chat=[[sum(X[j][i]*(X[r][i]-F(j==r)) for i in range(n))/F(n*N*(N-1))
                   for r in range(p)] for j in range(p)]
            C=mm(mm(A,Sigma),tr(A))
            Cross=scale(mm(Eps,tr(W)),F(1,n))
            Q=add(add(Chat,neg(C)),neg(add(mm(A,tr(Cross)),mm(Cross,tr(A)))))
            E0=mm(Cross,Si); M0=add(A,E0)
            R=add(Q,neg(mm(mm(E0,Sigma),tr(E0))))
            eq(Chat,add(mm(mm(M0,Sigma),tr(M0)),R),'factor_completion')
            # Exact trace leverage identity, independent of topic probabilities.
            check(sum(mm(mm(tr(W),Si),W)[i][i] for i in range(n))==n*k,'leverage_identity')
            eq(mm(Sigma,Si),eye(k),'covariance_inverse')
            fixtures.append({'K':k,'N':N,'epsilon':str(eps)})

    # Population recovery and arbitrary nonsingular right-coordinate invariance.
    mu=[F(1,k)]*k; d=[sum(row)/k for row in A]
    Xpop=[[x/k for x in row] for row in A]
    P=[[x/dj for x in row] for row,dj in zip(Xpop,d)]
    T=[[F(i==j)*(j+2)+F(j==i+1) for j in range(k)] for i in range(k)]
    Z=mm(Xpop,T)
    candidates=list(combinations(range(p),k))
    vols=[abs(det([P[i] for i in I])) for I in candidates]
    zvols=[abs(det([[x/d[i] for x in Z[i]] for i in I])) for I in candidates]
    check(max(vols)==1,'population_max_volume')
    for x,y in zip(vols,zvols):check(y==abs(det(T))*x,'coordinate_invariance')
    I=candidates[vols.index(max(vols))]
    B=[[x/d[i] for x in Z[i]] for i in I]
    eq(mm(Z,inv(B)),Xpop,'population_reconstruction')

# Exact ordered-token Q variance, including diagonal and overlapping positions.
pi=[F(1,8),F(3,8),F(1,2)]
for N in (2,3,4):
    first=[[F(0)]*3 for _ in range(3)]
    second=[[F(0)]*3 for _ in range(3)]
    for tokens in product(range(3),repeat=N):
        prob=F(1)
        for x in tokens:prob*=pi[x]
        tt=[[F(x==j)-pi[j] for j in range(3)] for x in tokens]
        for j in range(3):
            for r in range(3):
                q=sum(tt[a][j]*tt[b][r] for a in range(N) for b in range(N) if a!=b)/F(N*(N-1))
                first[j][r]+=prob*q;second[j][r]+=prob*q*q
    for j in range(3):
        for r in range(3):
            vj=pi[j]*(1-pi[j]);vr=pi[r]*(1-pi[r]);cov=F(j==r)*pi[j]-pi[j]*pi[r]
            check(first[j][r]==0,'pair_centering')
            check(second[j][r]==(vj*vr+cov*cov)/F(N*(N-1)),'exact_pair_variance')

out={'status':'PASS','source_sha256':EXPECTED,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'counts':counts,'total_assertions':sum(counts.values()),'fixtures':fixtures,
     'scope':'Exact factor completion, covariance leverage, affine determinant/reconstruction, and full-token degenerate-pair variance only. No stochastic experiment or verification of continuum risk inequalities.'}
(HERE/'general_k_algebra_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
