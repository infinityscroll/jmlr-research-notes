"""Exact finite checks of the preprocessing reduction, not statistical validation."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
SOURCE = HERE/'classical_spa_contraction_reduction.md'
BOUND = '6f6613f2758ffca32473fea5392a19775be72ee06384ef9a63e711e74335827d'
counts = {}

def check(name, condition):
    assert condition, name
    counts[name] = counts.get(name, 0)+1

def dot(x,y):
    return sum((a*b for a,b in zip(x,y)),F(0))

def rowmul(x,a):
    return [dot(x,col) for col in zip(*a)]

def inverse(a):
    n=len(a)
    b=[row[:]+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        i=next(i for i in range(j,n) if b[i][j])
        b[i],b[j]=b[j],b[i]
        pivot=b[j][j]
        b[j]=[x/pivot for x in b[j]]
        for i in range(n):
            if i!=j:
                f=b[i][j]
                b[i]=[x-f*y for x,y in zip(b[i],b[j])]
    return [row[n:] for row in b]

def main():
    check('source_hash',hashlib.sha256(SOURCE.read_bytes()).hexdigest()==BOUND)
    cases=0
    for k in range(2,6):
        nu=F(3,4)
        v=[[nu*F(i==j)+(1-nu)/k for j in range(k)] for i in range(k)]
        vi=inverse(v)
        br=[[F(4,5)*F(i==j)+F(1,5*k) for j in range(k)] for i in range(k)]
        core=[rowmul(row,v) for row in br]
        center=[sum(row[j] for row in core)/(k+1) for j in range(k)]
        radius=nu**2/(2*k*(k+1))
        bcenter=rowmul(center,vi)
        check('core_center_barycentric_floor',min(bcenter)>=nu/(k+1) and sum(bcenter)==F(k,k+1))
        for i in range(k):
            for sign in (-1,1):
                pert=[x+sign*radius*F(j==i) for j,x in enumerate(center)]
                weights=rowmul(pert,vi)
                check('axis_ball_membership',min(weights)>=0 and sum(weights)<=1)
        for seed in range(5):
            rng=random.Random(100*k+seed)
            raw=[rng.randrange(1,10) for _ in range(k)]
            b=[F(x,1+sum(raw)) for x in raw]
            y=rowmul(b,v)
            ep=[F(j==seed%k) for j in range(k)]
            eq=[F(j==(seed+1)%k) for j in range(k)]
            for lam in (F(0),F(1,100),F(1,4),F(1,2)):
                for zeta in (F(0),F(1,1000)):
                    for delta in (F(0),F(1,10000)):
                        cases+=1
                        pen=2*lam; z=2*zeta; xi=2*delta
                        a=radius/(radius+pen)
                        e0=[lam*(t-x) for x,t in zip(y,ep)]
                        e1=[zeta*(t-x) for x,t in zip(y,eq)]
                        yh=[x+u+w for x,u,w in zip(y,e0,e1)]
                        ch=[(1-delta)*x+delta*t for x,t in zip(center,eq)]
                        transformed=[a*x+(1-a)*c for x,c in zip(yh,ch)]
                        ideal=[a*x+(1-a)*c+a*u for x,c,u in zip(y,center,e0)]
                        weights=rowmul(ideal,vi)
                        check('ideal_substochastic_coefficients',min(weights)>=0 and sum(weights)<=1)
                        diff=[x-y for x,y in zip(transformed,ideal)]
                        rhs=[a*u+(1-a)*(x-y) for u,x,y in zip(e1,ch,center)]
                        check('exact_contraction_error_identity',diff==rhs)
                        check('uniform_transformed_error_envelope',dot(diff,diff)<=(z+xi)**2)
                        check('empirical_row_subprobability',min(yh)>=0 and sum(yh)<=1)
                        for vertex in v:
                            anchorhat=[(1-lam-zeta)*x+lam*u+zeta*w for x,u,w in zip(vertex,ep,eq)]
                            at=[a*x+(1-a)*c for x,c in zip(anchorhat,ch)]
                            err=[x-y for x,y in zip(at,vertex)]
                            check('anchor_reassignment_envelope',dot(err,err)<=((1+2/radius)*pen+z)**2)
    # The exact three-point example in the comparison note.
    v=[[F(7,8),F(1,8)],[F(1,8),F(7,8)]]
    out=[F(1),F(0)]; c=[F(1,3),F(1,3)]; r=F(3,64)
    transformed=[r/(r+1)*x+1/(r+1)*y for x,y in zip(out,c)]
    check('counterexample_raw_spa_selects_outlier',dot(out,out)>max(dot(row,row) for row in v))
    check('example_transformed_coordinates',transformed==[F(73,201),F(64,201)])
    check('example_substochastic_coordinates',rowmul(transformed,inverse(v))==[F(149,402),F(125,402)])
    result={'status':'PASS','source_sha256':BOUND,
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'cases':cases,'assertions':sum(counts.values()),'counts':counts,
            'scope':'Exact finite contraction identities and coefficient/error checks; no validation of probabilistic concentration, expected risk, numerical stability, or historical novelty.'}
    (HERE/'contraction_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','cases','assertions')}))

if __name__=='__main__':
    main()
