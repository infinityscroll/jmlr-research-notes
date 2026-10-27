"""Exact Bernstein/PSD certificates for released default-damping ASkotchV2.

Standard library only. No numerical eigensolver, Monte Carlo, or substituted
spectral stepsize. All triples of allowed block stepsizes are covered.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product, permutations
import hashlib
import json

HERE = Path(__file__).resolve().parent
OFFICIAL = HERE.parent/'official'

def zeros(m,n): return [[F(0) for _ in range(n)] for _ in range(m)]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def tr(a): return list(map(list,zip(*a)))
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(c,a): return [[c*x for x in r] for r in a]
def sub(a,b): return add(a,scale(-1,b))
def mul(a,b): return [[sum(x*y for x,y in zip(ar,bc)) for bc in tr(b)] for ar in a]
def hcat(a,b): return [x+y for x,y in zip(a,b)]
def block(a,b,c,d): return hcat(a,b)+hcat(c,d)

I=eye(3); E=[[F(1,3)]*3 for _ in range(3)]; P=sub(I,E); Z=zeros(3,3)
LAM=F(3,20000); DELTA=F(1,10**7); COR=1-DELTA; RHO=LAM+DELTA
S=F(1,100); GAMMA=F(200,3); NU=F(3,2)
K=add(scale(DELTA,I),scale(3*COR,E)); H=add(K,scale(LAM,I))
Y=hcat(scale(1/(1+S),I),scale(S/(1+S),I)); W=hcat(I,Z); V=hcat(Z,I)
BASE=Y+add(scale(1-S,V),scale(S,Y))
LO=(2+LAM)/(2+LAM-DELTA)
HI=(LAM+2*DELTA)/(LAM+DELTA)
MID=(LO+HI)/2
BLOCKS=[(0,1),(0,2),(1,2)]

def native_matrix(indices,eta,stale):
    d=1+RHO
    inverse=[[d/(d*d-COR*COR),-COR/(d*d-COR*COR)],
             [-COR/(d*d-COR*COR),d/(d*d-COR*COR)]]
    pre=zeros(3,3)
    for i,bi in enumerate(indices):
        for j,bj in enumerate(indices): pre[bi][bj]=inverse[i][j]
    grad=add(mul(K,Y),scale(LAM,W)) if stale else mul(H,Y)
    step=mul(pre,grad)
    return sub(BASE,scale(eta,step+scale(GAMMA,step)))

def covariance(x):
    a,b,c,d,e,f=x
    return block(add(scale(a,P),scale(b,E)),add(scale(c,P),scale(d,E)),
                 add(scale(c,P),scale(d,E)),add(scale(e,P),scale(f,E)))

def coordinates(C):
    result=[]
    for r,c in [(0,0),(0,3),(3,3)]:
        diag,off=C[r][c],C[r][c+1]
        result.extend([diag-off,diag+2*off])
    assert covariance(result)==C
    return result

def phi(C,eta,stale):
    result=zeros(6,6)
    for b in BLOCKS:
        M=native_matrix(b,eta,stale)
        result=add(result,scale(F(1,3),mul(mul(M,C),tr(M))))
    return result

def solve(A,b):
    M=[row[:]+[v] for row,v in zip(A,b)]
    for j in range(len(M)):
        pivot=next(i for i in range(j,len(M)) if M[i][j])
        M[j],M[pivot]=M[pivot],M[j]
        M[j]=[x/M[j][j] for x in M[j]]
        for i in range(len(M)):
            if i!=j:
                c=M[i][j]
                M[i]=[x-c*y for x,y in zip(M[i],M[j])]
    return [row[-1] for row in M]

def pd_pivots(A):
    assert A==tr(A)
    n=len(A); L=eye(n); D=[]
    for j in range(n):
        d=A[j][j]-sum(L[j][k]**2*D[k] for k in range(j))
        assert d>0, ('nonpositive exact pivot',j,d)
        D.append(d)
        for i in range(j+1,n):
            L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*D[k] for k in range(j)))/d
    assert mul(mul(L,[[D[i] if i==j else F(0) for j in range(n)] for i in range(n)]),tr(L))==A
    return list(map(str,D))

# A fixed basis for the orthogonal complement of z=(-gamma*1,1).
T=tr([[F(1),F(-1),F(0),F(0),F(0),F(0)],
      [F(1),F(1),F(-2),F(0),F(0),F(0)],
      [F(0),F(0),F(0),F(1),F(-1),F(0)],
      [F(0),F(0),F(0),F(1),F(1),F(-2)],
      [F(1),F(1),F(1),GAMMA,GAMMA,GAMMA]])
NULL=[[-GAMMA]]*3+[[F(1)]]*3
assert mul(tr(T),NULL)==zeros(5,1)

def psd_on_five_space(A):
    assert mul(A,NULL)==zeros(6,1)
    return pd_pivots(mul(mul(tr(T),A),T))

def bernstein_block(C,indices,stale):
    vals=[]
    for eta in [LO,MID,HI]:
        M=native_matrix(indices,eta,stale)
        vals.append(mul(mul(M,C),tr(M)))
    middle=sub(scale(2,vals[1]),scale(F(1,2),add(vals[0],vals[2])))
    # Exact check at an extra rational t verifies the polynomial reconstruction.
    t=F(2,7); eta=(1-t)*LO+t*HI; M=native_matrix(indices,eta,stale)
    reconstructed=add(add(scale((1-t)**2,vals[0]),scale(2*t*(1-t),middle)),scale(t*t,vals[2]))
    assert reconstructed==mul(mul(M,C),tr(M))
    return [vals[0],middle,vals[2]]

def uniform_certificate(C,stale,offset,sign,projected):
    # coefficient matrix = sign*(average image - offset), for each tensor Bernstein index.
    pieces=[bernstein_block(C,b,stale) for b in BLOCKS]
    records=[]
    for indices in product(range(3),repeat=3):
        A=zeros(6,6)
        for j,i in enumerate(indices): A=add(A,scale(F(1,3),pieces[j][i]))
        A=scale(sign,sub(A,offset))
        pivots=psd_on_five_space(A) if projected else pd_pivots(A)
        records.append({'bernstein_indices':list(indices),'exact_positive_LDL_pivots':pivots})
    return records

def main():
    assert LAM<NU and LAM*NU<1 and S*S==LAM/NU and GAMMA*GAMMA==1/(LAM*NU)
    assert LO<HI and DELTA>F(1,2**52)
    Cinit=covariance([F(1),F(0),F(1),F(0),F(1),F(0)])
    Cstar=covariance([F(1),F(0),F(61,2),F(0),F(2810),F(0)])
    assert F(2810)-F(61,2)**2>0
    growth=F(26,25); rate=F(99,100)
    growth_cert=uniform_certificate(Cstar,True,scale(growth,Cstar),1,True)
    start_cert=uniform_certificate(Cinit,True,scale(F(1,4),Cstar),1,True)

    # Select one rational corrected supercovariance, then verify it uniformly.
    cols=[]
    for j in range(6):
        basis=covariance([F(i==j) for i in range(6)])
        cols.append(coordinates(phi(basis,MID,False)))
    G=tr(cols)
    x=solve(sub(scale(rate,eye(6)),G),[F(1),F(1),F(0),F(0),F(1000),F(1000)])
    x=[F(round(v*10**6),10**6) for v in x]
    Cbar=covariance(x)
    bar_pd=pd_pivots(Cbar)
    # This also dominates every deterministic coordinate permutation of the actual zero-start error.
    domination=pd_pivots(sub(Cbar,scale(2,Cinit)))
    fixed_cert=uniform_certificate(Cbar,False,scale(rate,Cbar),-1,False)

    # Actual zero initialization: w*=u, b=H u, so error is (-u,-u).
    u=[F(1),F(-1),F(0)]; average=zeros(6,6)
    for perm in permutations(range(3)):
        z=[[-u[i]] for i in perm]*2
        actual=mul(z,tr(z))
        orth=[F(1),F(1),F(-2)]
        zorth=[[orth[i]] for i in perm]*2
        assert sub(scale(2,Cinit),actual)==scale(F(1,3),mul(zorth,tr(zorth)))
        average=add(average,scale(F(1,6),actual))
    assert average==Cinit
    rhs=mul(H,[[v] for v in u])
    assert rhs==[[(LAM+DELTA)*v] for v in u]

    sources=['models/full_krr.py','opts/askotchv2.py','opts/utils/bcd.py','opts/utils/general.py','preconditioners/nystrom.py']
    result={
        'status':'PASS','arithmetic':'Fraction-only rational Bernstein coefficients and exact LDL factorizations',
        'parameters':{'n':3,'block_size':2,'rank':2,'lambda':str(LAM),'delta':str(DELTA),'correlation':str(COR),
                      'default_damping_rho':str(RHO),'mu':str(LAM),'nu':str(NU),'gamma':str(GAMMA)},
        'eta_interval':[str(LO),str(HI)],'growth_factor':str(growth),'corrected_contraction_factor':str(rate),
        'stale_subcovariance_coordinates':['1','0','61/2','0','2810','0'],
        'growth_27_coefficients':growth_cert,'zero_start_27_coefficients':start_cert,
        'corrected_supercovariance_coordinates':list(map(str,x)),
        'corrected_supercovariance_PD_pivots':bar_pd,'corrected_domination_2Cinit_PD_pivots':domination,
        'corrected_contraction_27_coefficients':fixed_cert,
        'official_source_hashes':{p:hashlib.sha256((OFFICIAL/'fast_krr'/p).read_bytes()).hexdigest() for p in sources},
        'theorem_sha256':hashlib.sha256((HERE/'theorem.md').read_bytes()).hexdigest() if (HERE/'theorem.md').exists() else None,
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE/'uniform_stepsize_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','eta_interval','growth_factor','corrected_contraction_factor','corrected_supercovariance_coordinates','theorem_sha256']}))

if __name__=='__main__': main()
