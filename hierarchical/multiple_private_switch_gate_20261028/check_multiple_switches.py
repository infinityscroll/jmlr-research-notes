"""Fraction-only independent-private-switch kernel and support checks."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
SRC=HERE/'multiple_policy_completeness.md'
PIN='acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf'
OUT=HERE/'multiple_switch_certificate.json'
SIGNS=(-1,1)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def phi(j,z):return F(1) if z<=j else F(-j) if z==j+1 else F(0)
def flag_mass(t):return (F(2,3) if t[0] else F(1,3))*(F(3,4) if t[1] else F(1,4))

def supports():
    rows=[]
    for k in range(1,9):
        probs=[F(k+j-1,k+j) for j in range(1,k+1)]
        total=F(0);all_on=F(0);all_off=F(0)
        for t in product([0,1],repeat=k):
            p=F(1)
            for bit,pj in zip(t,probs):p*=pj if bit else 1-pj
            assert p>0;total+=p
            if all(t):all_on+=p
            if not any(t):all_off+=p
        assert total==1 and all_on==F(1,2) and all_off==F(factorial(k),factorial(2*k))
        rows.append({'k':k,'switch_probabilities':[str(p) for p in probs],
                     'all_on':str(all_on),'joint_policy_support':str(all_off),'all_label_states_positive':True})
    return rows

def check_records(laws):
    atoms=list(laws[1,(0,0)]);count=0
    for m in [1,2,3]:
        for record in product(atoms,repeat=m):
            natural=[]
            for sigma in [-1,1]:
                v=F(0)
                for t in product([0,1],repeat=2):
                    w=flag_mass(t)
                    for atom in record:w*=laws[sigma,t][atom]
                    v+=w
                natural.append(v)
            assert natural[0]==natural[1];count+=1
    return count

def minimal():
    laws={};minimum=F(1)
    for sigma,t in product([-1,1],product([0,1],repeat=2)):
        q={}
        for a,b,y in product(SIGNS,repeat=3):
            q[a,b,y]=F(0)
            for h,j in product(SIGNS,repeat=2):
                p1=F(1,2)+F(t[0],8)*a*h
                p2=F(1,2)+F(t[1],8)*a*b*h*j
                py=F(1,2)+sigma*y*(F(1,128)-F(b*j,4))
                minimum=min(minimum,p1,p2,py)
                assert 0<p1<1 and 0<p2<1 and 0<py<1
                q[a,b,y]+=p1*p2*py/4
            assert q[a,b,y]==(1+F(sigma*(1-2*t[0]*t[1])*y,64))/8
        assert sum(q.values())==1;laws[sigma,t]=q
    risks={sigma:sum(laws[sigma,(0,0)][a,b,1] for a,b in product(SIGNS,repeat=2)) for sigma in [-1,1]}
    assert minimum==F(31,128)
    assert risks[1]==F(65,128) and risks[-1]==F(63,128)
    records=check_records(laws)
    return {'observed_nodes':3,'treated_nodes':2,'hidden_roots':2,'hidden_root_states':2,
            'minimum_cell':str(minimum),'policy_risks':{str(k):str(v) for k,v in risks.items()},
            'risk_gap':str(risks[1]-risks[-1]),'joint_support':'1/12','finite_record_checks':records}

def nonuniform(alpha,beta):
    # Same original graph, with4 outer Fourier labels on uniform5-state roots.
    # This tests the actual arbitrary product-policy factor in c_F.
    mu,nu=2*alpha-1,2*beta-1
    coeff=[mu*nu/8,nu/8,mu/8,F(1,8)]
    modes=[(False,False),(True,False),(False,True),(True,True)]
    norm=[F(j*(j+1),5) for j in range(1,5)]
    rho=F(1,512);lam=F(1,2**30);laws={};minimum=F(1)
    tables={}
    for sigma,t in product([-1,1],product([0,1],repeat=2)):
        q={};table={}
        for a,b,y in product(SIGNS,repeat=3):
            value=F(0)
            for h,j in product(range(1,6),repeat=2):
                p1=(alpha if a==1 else 1-alpha)+t[0]*a*rho*sum(phi(l,h) for l in range(1,5))
                p2=(beta if b==1 else 1-beta)+t[1]*b*rho*sum((a if modes[l-1][0] else 1)*phi(l,h)*phi(l,j) for l in range(1,5))
                outer=sum((-2*sigma*lam*coeff[l-1]/(rho*rho*norm[l-1]**2))*(b if modes[l-1][1] else 1)*phi(l,j) for l in range(1,5))
                py=F(1,2)+y*(sigma*lam/2+outer)
                assert 0<p1<1 and 0<p2<1 and 0<py<1
                minimum=min(minimum,p1,p2,py);value+=p1*p2*py/25
                table[a,b,h,j]=(p1,p2)
            base=(alpha if a==1 else 1-alpha)*(beta if b==1 else 1-beta)
            assert value==base*(1+sigma*(1-2*t[0]*t[1])*lam*y)/2
            q[a,b,y]=value
        assert sum(q.values())==1;laws[sigma,t]=q;tables[sigma,t]=table
    for t in product([0,1],repeat=2):assert tables[1,t]==tables[-1,t]
    gap=sum(laws[1,(0,0)][a,b,1]-laws[-1,(0,0)][a,b,1] for a,b in product(SIGNS,repeat=2))
    assert gap==lam
    return {'pi1_plus':str(alpha),'pi2_plus':str(beta),'minimum_cell':str(minimum),
            'risk_gap':str(gap),'table_distributions_common':True,'joint_policy_support':'1/12',
            'finite_record_checks':check_records(laws),'hidden_states_per_root':5}

def main():
    assert sha(SRC)==PIN and not OUT.exists()
    rows=[nonuniform(a,b) for a,b in [(F(1,3),F(2,3)),(F(1,4),F(3,5)),(F(3,4),F(1,2))]]
    result={'status':'PASS','source_sha256':PIN,'checker_sha256':sha(Path(__file__)),
            'independent_flag_support':supports(),'smallest_observed_fixture':minimal(),
            'nonuniform_product_policies':rows,
            'scope':'Exact finite kernel/support/record checks; arbitrary graph completeness still depends on the analytic nested-mode argument.'}
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','support_dimensions':8,'original_kernel_fixtures':4,
                      'finite_record_checks':result['smallest_observed_fixture']['finite_record_checks']+sum(r['finite_record_checks'] for r in rows)}))
if __name__=='__main__':main()
