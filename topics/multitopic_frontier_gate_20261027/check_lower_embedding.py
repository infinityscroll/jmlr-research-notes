"""Exact original-family checks. No simulation and no continuum-proof substitute."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import hashlib,json,math

HERE=Path(__file__).resolve().parent
SRC=HERE/'general_k_lower.md'
SHA='3edaed4fc1d02c5f6f5f58c8c9ed2ab1874d5e8df26d4c0d86281e60ce1dffe2'
counts={}
def ck(x,g):
    assert x,g
    counts[g]=counts.get(g,0)+1
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)]for row in a]
def tr(a):return list(map(list,zip(*a)))
def positive_definite(a):
    b=[row[:] for row in a]
    for j in range(len(b)):
        if b[j][j]<=0:return False
        for x in range(j+1,len(b)):
            for y in range(j+1,len(b)):
                b[x][y]-=b[x][j]*b[j][y]/b[j][j]
    return True
def spectrum_floor(a,floor):return positive_definite([[x-floor*F(i==j) for j,x in enumerate(row)] for i,row in enumerate(a)])
def topics(k,alpha,s):
    a=k*alpha;h=(F(15,16)-4*a)/2;e=F(1,128);p=k+10
    A=[[F(0)]*k for _ in range(p)]
    A[0][0]=4*a;A[1][1]=4*a
    A[2][0]=h+s;A[2][1]=h-s;A[3][0]=h-s;A[3][1]=h+s
    for j in range(4,12):A[j][0]=e;A[j][1]=e
    for t in range(2,k):
        for j in range(2,12):A[j][t]=F(1,20)
        A[t+10][t]=F(1,2)
    return A

ck(hashlib.sha256(SRC.read_bytes()).hexdigest()==SHA,'source_binding')
fixtures=[]
for k in range(3,7):
    alpha=F(1,128*k);q=F(1,1000*k);beta=2*q*q
    ck(alpha<=F(1,64*k) and beta<=F(1,256*k*k*(k-2)),'parameter_domain')
    base=[]
    for j in range(2,k):
        z=[F(0)]*k;z[0]=z[1]=F(-1,2);z[j]=1
        for sign in (-1,1):base.append([F(1,k)+sign*F(1,2*k)*x for x in z])
    # Two complete opposite-sign blocks force the projection quantity to zero.
    records=[(b,sign) for sign in (-1,1) for b in base]
    repeats=math.ceil(F(128*(k-1),len(records)));n=repeats*len(records)
    ck(n>=128*(k-1),'document_domain')
    for j in range(k):ck(sum(sign*b[j] for b,sign in records)==0,'projection_event_zero')
    old_d=None
    for s in (F(3,16),F(1,4)):
        A=topics(k,alpha,s);G=mm(tr(A),A)
        ck(all(sum(row[j] for row in A)==1 for j in range(k)),'topic_stochasticity')
        ck(all(x>=0 for row in A for x in row),'topic_nonnegativity')
        ck(all(x>=F(1,64) for row in G for x in row),'gram_floor')
        ck(spectrum_floor(G,F(1,64*k)),'singular_value_floor')
        W=[]
        for b,sign in records:
            w=b[:];w[0]+=sign*q/s;w[1]-=sign*q/s;W.append(w)
            ck(sum(w)==1 and min(w)>=F(1,4*k),'interior_mixture')
        S=[[sum(w[i]*w[j] for w in W)/len(W) for j in range(k)] for i in range(k)]
        ck(spectrum_floor(S,beta),'mixture_spectral_floor')
        mu=[sum(w[j] for w in W)/len(W) for j in range(k)]
        d=[sum(row[j]*mu[j] for j in range(k)) for row in A]
        for j in [0,1]+list(range(12,k+10)):
            ck(d[j]>=alpha and sum(x>0 for x in A[j])==1,'corpus_anchor_floor')
        baselines=[];maxV=F(0);maxU=F(0)
        for b in base:
            di=[sum(x*y for x,y in zip(row,b)) for row in A];baselines.append(di)
            shift=[q*(row[0]-row[1])/s for row in A]
            deriv=[F(0)]*len(A);deriv[0]=-4*k*alpha*q/(s*s);deriv[1]=-deriv[0]
            bs=[x/y for x,y in zip(shift,di)];db=[x/y for x,y in zip(deriv,di)]
            ck(min(di)>0 and max(abs(x) for x in bs)<=F(1,2),'positive_likelihood')
            ck(sum(shift)==0 and sum(deriv)==0,'score_centering')
            maxV=max(maxV,sum(dj*x*x for dj,x in zip(di,bs))/beta)
            maxU=max(maxU,sum(dj*x*x for dj,x in zip(di,db))/(alpha*beta))
        if old_d is not None:ck(baselines==old_d,'parameter_free_baseline')
        old_d=baselines
        fixtures.append({'K':k,'p':k+10,'n':n,'s':str(s),'alpha':str(alpha),'beta':str(beta),
                         'max_V_over_beta':str(maxV),'max_U_over_alpha_beta':str(maxU)})
    A0=topics(k,alpha,F(3,16));A1=topics(k,alpha,F(1,4))
    dist=[]
    for perm in permutations(range(k)):
        loss=sum(abs(A1[i][j]-A0[i][perm[j]]) for i in range(k+10) for j in range(k))
        dist.append(loss)
        if any(perm[j]!=j for j in range(2,k)):
            ck(loss>=1,'all_extra_topic_permutations')
    ck(min(dist)==F(1,4),'exact_quotient_distance')

out={'status':'PASS','source_sha256':SHA,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'counts':counts,'total_assertions':sum(counts.values()),'fixtures':fixtures,
     'scope':'Exact admissible original-family fixtures for K3..6, both parameter endpoints, full permutations, positive rational spectral floors and score identities. Conditioning event has zero projection in these fixtures. Does not replace the continuum Fisher, conditioning-probability, or minimax proof.'}
(HERE/'lower_embedding_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'counts':counts,'total_assertions':out['total_assertions']},indent=2))
