"""Independent construction from scalar update equations and full 6x6 LDL checks.

No imports from the proposed certificate or its matrix helpers. Standard library.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
lam, c, s, gamma = F(3, 20000), F(99999, 100000), F(1, 100), F(200, 3)


def step(z, block, stale):
    w, v = z[:3], z[3:]
    y = [(w[i] + s*v[i])/(1+s) for i in range(3)]
    grad = [sum((F(1) if i == j else c)*y[j] for j in range(3))
            + lam*(w[i] if stale else y[i]) for i in range(3)]
    i, j = block
    denom = (1+lam)**2-c*c
    direction = [F(0)]*3
    direction[i] = ((1+lam)*grad[i]-c*grad[j])/denom
    direction[j] = ((1+lam)*grad[j]-c*grad[i])/denom
    return [y[i]-direction[i] for i in range(3)] + [
        (1-s)*v[i]+s*y[i]-gamma*direction[i] for i in range(3)]


def phi(C, stale):
    result = [[F(0) for _ in range(6)] for _ in range(6)]
    for b in combinations(range(3), 2):
        columns = [step([F(i == j) for i in range(6)], b, stale) for j in range(6)]
        for i in range(6):
            for j in range(6):
                result[i][j] += sum(columns[k][i]*C[k][l]*columns[l][j]
                                    for k in range(6) for l in range(6))/3
    return result


def cov(x):
    a, b, c0, d, e, f = map(F, x)
    params = [[(a,b),(c0,d)],[(c0,d),(e,f)]]
    return [[params[i//3][j//3][0]*(F(i%3 == j%3)-F(1,3))
             + params[i//3][j//3][1]/3 for j in range(6)] for i in range(6)]


def difference(A, B, multiplier=F(1)):
    return [[A[i][j]-multiplier*B[i][j] for j in range(6)] for i in range(6)]


def exact_ldl(A, strict=False):
    """Schur complements, including zero pivots. No invariant-block assumption."""
    M = [r[:] for r in A]
    assert all(M[i][j] == M[j][i] for i in range(6) for j in range(6))
    pivots = []
    for k in range(6):
        p = M[k][k]
        assert p > 0 if strict else p >= 0
        pivots.append(str(p))
        if p == 0:
            assert all(M[k][j] == 0 for j in range(k+1,6))
        else:
            for i in range(k+1,6):
                for j in range(k+1,6):
                    M[i][j] -= M[i][k]*M[k][j]/p
    return pivots


def main():
    C0 = cov([1,0,1,0,1,0])
    Cstar = cov([1,0,F(61,2),0,2810,0])
    Cbar = cov([F(49101403,500000),F(1010101,1000000),
                F(810265583,250000),-F(33,25000),
                F(65082583763,200000),F(4994384331,1000000)])
    avg = [[F(0) for _ in range(6)] for _ in range(6)]
    for p in permutations([-1,1,0]):
        v = p+p
        for i in range(6):
            for j in range(6): avg[i][j] += F(v[i]*v[j],6)
    assert avg == C0
    checks = {
        'subcovariance': exact_ldl(Cstar),
        'growth': exact_ldl(difference(phi(Cstar,True),Cstar,F(26,25))),
        'reachable': exact_ldl(difference(phi(C0,True),Cstar,F(1,4))),
        'supercovariance': exact_ldl(Cbar,True),
        'initial_domination': exact_ldl(difference(Cbar,C0),True),
        'contraction': exact_ldl(difference(
            [[F(99,100)*v for v in r] for r in Cbar],phi(Cbar,False)),True),
    }
    result = {'status':'PASS','method':'Independent scalar update; full 6x6 exact LDL',
              'checks':checks, 'theorem_sha256':hashlib.sha256((HERE/'theorem.md').read_bytes()).hexdigest(),
              'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'root_exact_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'checks':list(checks)}))


if __name__ == '__main__': main()
