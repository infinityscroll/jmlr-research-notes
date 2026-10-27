"""Bounded exact pair-identity checks and non-certifying constant sanity checks."""
from fractions import Fraction as F
from itertools import permutations, combinations
from pathlib import Path
import hashlib
import json
import math

HERE=Path(__file__).resolve().parent
SOURCE='empirical_frequency_maximum_lemma.md'
EXPECTED='82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8'
assert hashlib.sha256((HERE/SOURCE).read_bytes()).hexdigest()==EXPECTED
pair_cases=0
row_cases=0
for N in range(2,6):
    perms=list(permutations(range(N)))
    for x0 in range(N+1):
        for x1 in range(N-x0+1):
            counts=[x0,x1,N-x0-x1]
            tokens=sum(([j]*counts[j] for j in range(3)),[])
            empirical={}
            for j in range(3):
                for r in range(3):
                    factorial=F(counts[j]*(counts[r]-(j==r)),N*(N-1))
                    total=F(0)
                    for perm in perms:
                        pairs=[(tokens[perm[t]],tokens[perm[t+1]]) for t in range(0,N-1,2)]
                        total+=sum((F(int(a==j and b==r)+int(b==j and a==r),2) for a,b in pairs),F(0))/len(pairs)
                    assert total/len(perms)==factorial
                    empirical[j,r]=factorial
                    pair_cases+=1
            for j in range(3):
                if counts[j]==0:continue
                for size in range(1,4):
                    for core in combinations(range(3),size):
                        mass=sum((empirical[j,r] for r in core),F(0))
                        assert 0<=mass<=F(counts[j],N)
                        row_cases+=1
# These floating checks supplement, rather than certify, the analytic inequalities.
constant_cases=0
for r in [1,2,3,8,32]:
    H=6*(math.sqrt(r)+1); A=12*H; K=A*A/4; c=1/(64*H*H)
    assert K>=96 and 2*math.sqrt(6)*(math.sqrt(r)+1)<=H
    assert 4*(math.sqrt(r)+1)<=H
    for t in [.001,.1,.5,1,1.999]:
        assert H*math.sqrt(c)*t+H*c*t*t<t
        constant_cases+=1
for exponent in range(1,50):
    z=2.0**(-exponent)
    g=math.log(1/z)-1+z
    assert g>=math.log(1/z)/4 and g>=1/8
    for u in [.001,.01,.1,.5,.9]:
        d=u*z;K=96;k=K*math.log(2+1/u)
        assert k*g+1e-12>=3*math.log(1/d)+(k*d/u)/16
        constant_cases+=1
result={'status':'PASS','source_sha256':EXPECTED,
        'exact_pairing_factorial_identities':pair_cases,
        'exact_empirical_subprobability_checks':row_cases,
        'noncertifying_constant_sanity_cases':constant_cases,
        'analytic_proof_required':True,'paid_jobs':0,'outcomes_inspected':False}
result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(HERE/'empirical_frequency_lemma_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
