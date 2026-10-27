"""Independent scalar-equation construction, Bernstein recovery at t=1/3,
and full 6x6 semidefinite Schur complements. No proposed-checker imports.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import importlib.util
import hashlib
import json

HERE=Path(__file__).resolve().parent
old=HERE.parent/'stale_regularizer_instability_20261027/root_exact_audit.py'
spec=importlib.util.spec_from_file_location('root_prior',old)
root=importlib.util.module_from_spec(spec); spec.loader.exec_module(root)
cov,ldl=root.cov,root.exact_ldl
lam=F(3,20000); delta=F(1,10**7); rho=lam+delta; c=1-delta
s=F(1,100); gamma=F(200,3)
lo=(2+lam)/(2+lam-delta); hi=(lam+2*delta)/(lam+delta)


def step(z,block,eta,stale):
    w,v=z[:3],z[3:]
    y=[(w[i]+s*v[i])/(1+s) for i in range(3)]
    g=[sum((F(1) if i==j else c)*y[j] for j in range(3))
       +lam*(w[i] if stale else y[i]) for i in range(3)]
    i,j=block; denom=(1+rho)**2-c*c; d=[F(0)]*3
    d[i]=((1+rho)*g[i]-c*g[j])/denom
    d[j]=((1+rho)*g[j]-c*g[i])/denom
    return [y[i]-eta*d[i] for i in range(3)]+[
        (1-s)*v[i]+s*y[i]-gamma*eta*d[i] for i in range(3)]


def image(C,block,t,stale):
    eta=lo+(hi-lo)*t
    columns=[step([F(i==j) for i in range(6)],block,eta,stale) for j in range(6)]
    return [[sum(columns[k][i]*C[k][l]*columns[l][j] for k in range(6) for l in range(6))
             for j in range(6)] for i in range(6)]


def bernstein(C,block,stale):
    A0,Athird,A1=[image(C,block,t,stale) for t in [F(0),F(1,3),F(1)]]
    quadratic=[[F(3,2)*(A1[i][j]-3*Athird[i][j]+2*A0[i][j])
                for j in range(6)] for i in range(6)]
    middle=[[(A0[i][j]+A1[i][j]-quadratic[i][j])/2 for j in range(6)] for i in range(6)]
    # Also reconstruct a different rational point, not a coefficient sample.
    t=F(3,5)
    assert image(C,block,t,stale)==[[(1-t)**2*A0[i][j]+2*t*(1-t)*middle[i][j]+t*t*A1[i][j]
                                    for j in range(6)] for i in range(6)]
    return [A0,middle,A1]


def main():
    witness=json.loads((HERE/'uniform_stepsize_certificate.json').read_text())
    C0=cov([1,0,1,0,1,0]); Cstar=cov([1,0,F(61,2),0,2810,0])
    Cbar=cov([F(x) for x in witness['corrected_supercovariance_coordinates']])
    ldl(Cstar);ldl(Cbar,True)
    ldl([[Cbar[i][j]-2*C0[i][j] for j in range(6)] for i in range(6)],True)
    checks={}
    for name,C,stale,target,multiplier,sign,strict in [
        ('growth',Cstar,True,Cstar,F(26,25),1,False),
        ('reachable',C0,True,Cstar,F(1,4),1,False),
        ('corrected',Cbar,False,Cbar,F(99,100),-1,True)]:
        blocks=[bernstein(C,b,stale) for b in combinations(range(3),2)]
        records=[]
        for ix in product(range(3),repeat=3):
            residual=[[sign*(sum(blocks[k][ix[k]][i][j] for k in range(3))/3-multiplier*target[i][j])
                       for j in range(6)] for i in range(6)]
            pivots=ldl(residual,strict)
            records.append({'index':ix,'full_6x6_pivots':pivots})
        checks[name]=records
    result={'status':'PASS','method':'Independent scalar equations; t=1/3 polynomial recovery; full6x6 exact Schur complements',
            'coefficient_checks':sum(map(len,checks.values())),'checks':checks,
            'theorem_sha256':hashlib.sha256((HERE/'theorem.md').read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'prior_root_helper_sha256':hashlib.sha256(old.read_bytes()).hexdigest()}
    (HERE/'root_uniform_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','coefficient_checks','theorem_sha256']}))


if __name__=='__main__':main()
