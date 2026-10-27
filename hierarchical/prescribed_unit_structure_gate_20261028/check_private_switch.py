"""Exact original-kernel checks of the private policy-switch construction."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'private_switch_completeness.md'
PIN='274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755'
OUT=HERE/'private_switch_certificate.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def phi(j,z):
    if z<=j:return F(1)
    if z==j+1:return F(-j)
    return F(0)
def prob_sign(x,mean):return (1+x*mean)/2

def bow():
    qs={};minimum=F(1)
    for s,t in product([-1,1],[0,1]):
        q={}
        for a,y in product([-1,1],repeat=2):
            q[a,y]=F(0)
            for h in [-1,1]:
                pa=prob_sign(a,F(t,2)*h)
                py=prob_sign(y,s*(F(1,16)-F(1,4)*a*h))
                minimum=min(minimum,pa,py)
                q[a,y]+=pa*py/2
            assert q[a,y]==(1+s*(1-2*t)*F(y,16))/4
        qs[s,t]=q
    assert qs[1,0]==qs[-1,1] and qs[1,1]==qs[-1,0]
    gap=sum(qs[1,0][a,1]-qs[-1,0][a,1] for a in [-1,1])
    assert gap==F(1,16)
    return {'minimum_physical_cell':str(minimum),'selected_probability_gap':str(gap),
            'whole_policy_support':'1/2','natural_atom_swap':'PASS'}

def overlapping_tree(alpha):
    # Observed graph A->B->Y; hidden edges A<->B<->Y.
    # F={A,B,Y}, I={B,Y}. Both roots are independent uniform4.
    # Outer labels1,2 use both edges; inner label3 uses only B--Y.
    rho=F(1,64);lam=F(1,2**24);mu=2*alpha-1
    norm={j:F(j*(j+1),4) for j in [1,2,3]}
    coeff={1:mu/8,2:F(1,8)}
    minimum=F(1);laws={};a_tables={}
    for sigma,t in product([-1,1],[0,1]):
        q={}
        table={}
        for a,b,y in product([-1,1],repeat=3):
            value=F(0)
            for hab,hby in product(range(1,5),repeat=2):
                pa=(alpha if a==1 else 1-alpha)+t*a*rho*sum(phi(j,hab) for j in [1,2])
                pb=F(1,2)+b*rho*(phi(1,hab)*phi(1,hby)+a*phi(2,hab)*phi(2,hby)+phi(3,hby))
                outer=sum((-2*sigma*lam*coeff[j]/(rho*rho*norm[j]**2))*b*phi(j,hby) for j in [1,2])
                inner=(sigma*lam/(4*rho*norm[3]))*b*phi(3,hby)
                py=F(1,2)+y*(outer+inner)
                assert 0<pa<1 and 0<pb<1 and 0<py<1
                minimum=min(minimum,pa,pb,py)
                value+=pa*pb*py/16
                table[a,hab]=pa
            expected=(alpha if a==1 else 1-alpha)*(1+sigma*(1-2*t)*lam*y)/4
            assert value==expected
            q[a,b,y]=value
        assert sum(q.values())==1
        laws[sigma,t]=q;a_tables[sigma,t]=table
    assert a_tables[1,0]==a_tables[-1,0] and a_tables[1,1]==a_tables[-1,1]
    assert a_tables[1,0]!=a_tables[1,1]
    assert laws[1,0]==laws[-1,1] and laws[1,1]==laws[-1,0]
    # Exact arbitrary-record identity follows algebraically; enumerate m<=3 as checks.
    atoms=list(laws[1,0]);checked=0
    for m in [1,2,3]:
        for record in product(atoms,repeat=m):
            mixture=[]
            for s in [-1,1]:
                terms=[]
                for t in [0,1]:
                    v=F(1,2)
                    for atom in record:v*=laws[s,t][atom]
                    terms.append(v)
                mixture.append(sum(terms))
            assert mixture[0]==mixture[1];checked+=1
    gap=sum(laws[1,0][a,b,1]-laws[-1,0][a,b,1] for a,b in product([-1,1],repeat=2))
    assert gap==lam
    # Positive observed unit DAG C0->C1, ignored by all subunit mechanisms.
    c_law={(c0,c1):prob_sign(c0,F(-1,3))*prob_sign(c1,F(2*c0,5))
           for c0,c1 in product([-1,1],repeat=2)}
    assert min(c_law.values())>0 and sum(c_law.values())==1
    for c,pc in c_law.items():
        for atom in atoms:
            assert pc*(laws[1,0][atom]+laws[1,1][atom])/2 == pc*(laws[-1,0][atom]+laws[-1,1][atom])/2
    return {'pi_plus':str(alpha),'lambda':str(lam),'minimum_physical_cell':str(minimum),
            'all_original_kernel_states':4*8*16,'finite_record_checks':checked,
            'selected_policy_probability_gap':str(gap),'hidden_states_per_edge':4,
            'policy_tables_identical_across_models':True,'common_positive_unit_dag':'C0->C1',
            'natural_atom_swap':'PASS'}

def label_patterns():
    # Use a5-node outer tree extending a3-node inner tree, with4 outer modes.
    # This isolates every mixed-label pattern, including shared-tree edges.
    outer=[(0,1),(1,2),(2,3),(3,4)];inner={(1,2),(2,3)}
    inner_vertices={1,2,3};survivors=[];total=0
    choices=[range(5) if v not in inner_vertices else range(6) for v in range(5)]
    for labels in product(*choices):
        total+=1;ok=True
        for edge in outer:
            a,b=edge
            la=labels[a] if labels[a]!=5 or edge in inner else 0
            lb=labels[b] if labels[b]!=5 or edge in inner else 0
            if la!=lb:ok=False;break
        if ok:survivors.append(labels)
    expected=[(0,0,0,0,0),(0,5,5,5,0)]+[(j,)*5 for j in range(1,5)]
    assert set(survivors)==set(expected)
    return {'patterns':total,'survivors':survivors,'mixed_survivors':0}

def main():
    assert sha(SOURCE)==PIN
    assert not OUT.exists(),'Preserve certificate'
    result={'status':'PASS','source_sha256':PIN,'checker_sha256':sha(Path(__file__)),
            'bow':bow(),'nested_mode_contraction':label_patterns(),
            'overlap_fixtures':[overlapping_tree(a) for a in [F(1,4),F(1,3),F(1,2),F(2,3),F(3,4)]],
            'scope':'Finite exact original-kernel and label-contraction certificates; arbitrary-graph theorem and arbitrary-record identity remain analytic arguments.'}
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','overlap_fixtures':5,'label_patterns':result['nested_mode_contraction']['patterns'],
                      'finite_records':sum(v['finite_record_checks'] for v in result['overlap_fixtures'])}))
if __name__=='__main__':main()
