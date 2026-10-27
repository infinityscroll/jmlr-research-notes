"""Exact finite checks of the two-document likelihood identities.

Checks the actual pair of multinomial count vectors, not independent pairs
of tokens. All arithmetic is rational. This supplements the all-N proof;
it does not certify asymptotic constants or the statistical theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for j in range(n + 1):
            for rest in compositions(n-j, k-1):
                yield (j,) + rest


def weighted_product(values, counts):
    answer = F(1)
    for x, k in zip(values, counts):
        answer *= x**k
    return answer


def g(s, length):
    return ((1+s)**length + (1-s)**length)/2


def run(N, theta, r):
    # The common padding and shared row have zero contrast. Aggregating them
    # preserves the likelihood, so this seven-cell check covers their exact
    # contribution without enumerating uninformative padding allocations.
    v0, v = F(1,8), F(1,64)
    padding = sum((F(1,32)*F(1,2)**(2*(j+6)) for j in range(1,6)), F(0))
    b = F(5,8)-v-padding
    d = [F(1,4)+padding,v0/2,v0/2,v/2,v/2,b/2,b/2]
    z = [F(0),r,-r,r,-r,r/2,-r/2]
    kappa = 2*theta/(1-2*theta)
    w = z.copy()
    w[3] *= 1+kappa
    w[4] *= 1+kappa
    assert sum(d)==1 and sum(x*y for x,y in zip(d,z))==0
    assert sum(x*y for x,y in zip(d,w))==0
    data=[]
    for counts in compositions(N,7):
        denom=1
        for c in counts:
            denom*=factorial(c)
        coefficient=factorial(N)//denom
        base=coefficient*weighted_product(d,counts)
        vals=[]
        for contrast in (z,w):
            vals.extend(weighted_product([1+s*x for x in contrast],counts)
                        for s in (1,-1))
        data.append((base,*vals))
    normalization=[F(0),F(0)]
    moment=[F(0),F(0),F(0)]
    chi=F(0)
    for left,right in product(data,repeat=2):
        base=left[0]*right[0]
        f0=(left[1]*right[2]+left[2]*right[1])/2
        f1=(left[3]*right[4]+left[4]*right[3])/2
        assert f0>0 and f1>0
        normalization[0]+=base*f0
        normalization[1]+=base*f1
        moment[0]+=base*f0*f0
        moment[1]+=base*f0*f1
        moment[2]+=base*f1*f1
        chi+=base*(f1-f0)**2/f0
    assert normalization==[1,1]
    V=sum(x*y*y for x,y in zip(d,z))
    u=v*r*r
    expected=[g(V,2*N),g(V+kappa*u,2*N),
              g(V+(2*kappa+kappa*kappa)*u,2*N)]
    assert moment==expected
    numerator=moment[2]-2*moment[1]+moment[0]
    assert numerator>=0 and chi>=0
    # F0>=product sqrt(1-z_t^2)>=(1-r^2)^N.
    assert chi<=numerator/(1-r*r)**N
    # Revealing the sign supplies this exact complete second moment.
    token_chi=v*kappa*kappa*r*r/(1-r*r)
    complete=(1+token_chi)**(2*N)-1
    assert chi<=complete
    # Exact nuisance covariance, for every pair sign.
    beta=r*r/4
    for sign in (-1,1):
        mixtures=[[F(1,2)+sign*r/2,F(1,2)-sign*r/2],
                  [F(1,2)-sign*r/2,F(1,2)+sign*r/2]]
        mean=[sum(row[j] for row in mixtures)/2 for j in range(2)]
        assert mean==[F(1,2),F(1,2)]
        contrast=sum((row[0]-row[1])**2/2 for row in mixtures)/2
        assert contrast==2*beta
    return {'N':N,'theta':str(theta),'r':str(r),'count_pairs':len(data)**2,
            'exact_identity_checks':3,'normalization_checks':2,
            'chi_square_float_for_readability':float(chi),
            'complete_chi_square_float_for_readability':float(complete),
            'short_scale_float_for_readability':float(v*theta**2*N*(N-1)*beta**2),
            'chi_square_exact_sha256':hashlib.sha256(str(chi).encode()).hexdigest()}


if __name__=='__main__':
    here=Path(__file__).resolve().parent
    output=here/'paired_sign_identity_certificate.json'
    if output.exists():
        raise FileExistsError(output)
    result={'arithmetic':'fractions.Fraction, exact',
            'scope':'finite full-count checks; not all-N proof certification',
            'fixtures':[run(2,F(1,16),F(1,64)),run(3,F(1,32),F(1,128))],
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'proof_sha256':hashlib.sha256((here/'paired_sign_constrained_lower.md').read_bytes()).hexdigest()}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
