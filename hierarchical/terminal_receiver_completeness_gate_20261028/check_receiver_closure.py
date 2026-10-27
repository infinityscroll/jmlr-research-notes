#!/usr/bin/env python3
"""Exact finite checks, not a proof of the graph-wide theorem."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
SIGN = (-1, 1)
BIT = (0, 1)
def pm(b, p):
    return p if b else 1-p
def add(d, k, v):
    d[k] = d.get(k, F(0)) + v
def jdump(obj):
    if isinstance(obj, F): return str(obj)
    if isinstance(obj, dict): return {str(k): jdump(v) for k,v in obj.items()}
    if isinstance(obj, (list, tuple)): return [jdump(v) for v in obj]
    return obj

# Nonreset front-door fixture: enumerate the ORIGINAL hidden subunit H.
def fd_joint(u, flag, forced_a=None):
    out = {}
    for h,a,m,z in product(SIGN,BIT,BIT,BIT):
        pa = F(1,2) if flag == 0 else F(1,2)+F(h,8)+F(u,16)
        if forced_a is not None: pa=F(forced_a)
        p = F(1,2)*pm(a,pa)*pm(m,F(1,4)+F(a,2)+F(u,16))*pm(z,F(1,4)+F(m,4)+F(h,8)+F(u,32))
        add(out,(a,m,z),p)
    assert sum(out.values()) == 1
    return out

def frontdoor(q, forced_a):
    p_a = {a:sum(v for (aa,m,z),v in q.items() if aa==a) for a in BIT}
    p_am = {(a,m):sum(v for (aa,mm,z),v in q.items() if (aa,mm)==(a,m)) for a,m in product(BIT,BIT)}
    return sum(p_am[forced_a,m]/p_a[forced_a] *
               sum(q[a,m,1]/p_am[a,m]*p_a[a] for a in BIT) for m in BIT)

fd = []
natural_risk = F(0)
policy_risk = F(0)
natural_inputs = set()
for u,flag in product(SIGN,BIT):
    q=fd_joint(u,flag)
    s=sum(v for (a,m,z),v in q.items() if z==1)
    natural_inputs.add(s)
    # Hard queries plus stochastic mixture are independently compared.
    for a in BIT:
        physical=sum(v for (aa,m,z),v in fd_joint(u,flag,a).items() if z==1)
        assert frontdoor(q,a)==physical
    f=sum(frontdoor(q,a) for a in BIT)/2
    assert f==F(3,8)+F(3*u,64)
    nat=F(1,4)+s*s/2
    pol=F(1,4)+f*f/2
    natural_risk += nat/4
    policy_risk += pol/4
    fd.append(dict(u=u,flag=flag,natural_input=s,policy_input=f,risk=pol))
assert all(row["policy_input"] in natural_inputs for row in fd)
assert policy_risk == F(2633,8192)
assert natural_risk == F(21077,65536)

# Necessity fixture: binary upstream bow plus a shared, observed-input receiver.
def bow_q(sig,t):
    q={}
    for h,a,z in product(SIGN,SIGN,SIGN):
        p=F(1,2)*(F(1,2)+F(t*a*h,4))*(F(1,2)+sig*z*(F(1,32)-F(a*h,8)))
        add(q,(a,z),p)
    assert sum(q.values())==1
    return q

natural_atoms={}
for sig in SIGN:
    atoms={}
    for t in BIT:
        q=bow_q(sig,t)
        qs=tuple(q[k] for k in product(SIGN,SIGN))
        s=sum(v for (a,z),v in q.items() if z==1)
        risk=F(1,4)+s/2
        for y in BIT: add(atoms,(qs,y),pm(y,risk)/2)
    natural_atoms[sig]=atoms
assert natural_atoms[-1]==natural_atoms[1]
bow_risks={sig:F(1,4)+sum(v for (a,z),v in bow_q(sig,0).items() if z==1)/2 for sig in SIGN}
assert bow_risks=={-1:F(31,64),1:F(33,64)}

finite_checks=0
for m in (1,2,3):
    for rec in product(tuple(product(SIGN,SIGN)),repeat=m):
        empirical=sum(1 for a,z in rec if z==1)/F(m)
        for y in BIT:
            vals=[]
            for sig in SIGN:
                v=F(0)
                for t in BIT:
                    q=bow_q(sig,t)
                    mass=F(1,2)
                    for atom in rec: mass*=q[atom]
                    v+=mass*pm(y,F(1,4)+empirical/2)
                vals.append(v)
            assert vals[0]==vals[1]
            finite_checks+=1

# Shared unit cause defeats response transport even with a known constant input law.
confounded={}
confounded_policy={}
for model,(v,w) in enumerate(((F(1,8),F(1,4)),(F(3,16),F(1,8)))):
    obs={}
    for u,r,y in product(SIGN,SIGN,SIGN):
        add(obs,(r,y),F(1,2)*(F(1,2)+F(r*u,4))*(1+y*(v*r+w*u))/2)
    confounded[model]=obs
    confounded_policy[model]=(1+v)/2
assert confounded[0]==confounded[1]
assert confounded_policy=={0:F(9,16),1:F(19,32)}
assert confounded[0][1,1]/sum(v for (r,y),v in confounded[0].items() if r==1)==F(5,8)

# Separate received marginals versus one joint received law.
# Original graph A->D2, A<->D1<->D2. The second hidden root has four states.
def joint_only_q(sig,t):
    q={}
    for h1,hi,ho,a,b,d in product(SIGN,repeat=6):
        pa=F(1,2)+F(t*a*h1,4)
        pb=F(1,2)+sig*b*(F(hi,16)-F(h1*ho,16))
        pd=F(1,2)+d*(F(hi,16)+F(a*ho,4))
        assert min(pa,1-pa,pb,1-pb,pd,1-pd)>=F(3,16)
        add(q,(a,b,d),pa*pb*pd/8)
    for (a,b,d),p in q.items():
        assert p==F(1,8)+F(sig*(1-2*t)*b*d,512)
    return q
jo={}
for sig in SIGN:
    jo[sig]=[]
    for t in BIT:
        q=joint_only_q(sig,t)
        assert sum(v for (a,b,d),v in q.items() if b==1)==F(1,2)
        assert sum(v for (a,b,d),v in q.items() if d==1)==F(1,2)
        jo[sig].append(tuple(q[k] for k in product(SIGN,repeat=3)))
assert sorted(jo[-1])==sorted(jo[1])
joint_gap=sum(v for (a,b,d),v in joint_only_q(1,0).items() if b==d)-sum(v for (a,b,d),v in joint_only_q(-1,0).items() if b==d)
assert joint_gap==F(1,64)

result=dict(
    status="PASS",
    source_sha256=hashlib.sha256((HERE/"separated_receiver_completeness.md").read_bytes()).hexdigest(),
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    frontdoor_cases=fd,
    frontdoor_natural_risk=natural_risk,
    frontdoor_policy_risk=policy_risk,
    frontdoor_policy_minus_natural=policy_risk-natural_risk,
    necessity_receiver_risks=bow_risks,
    finite_record_atom_equalities=finite_checks,
    shared_cause_observation=confounded[0],
    shared_cause_policy_risks=confounded_policy,
    shared_cause_observational_conditioning=F(5,8),
    separate_inputs_each=F(1,2),
    jointly_received_parity_gap=joint_gap,
    limits="Finite exact algebra only; no rate simulation, general proof or novelty certification.")
(HERE/"receiver_closure_certificate.json").write_text(json.dumps(jdump(result),indent=2)+"\n")
print(json.dumps(jdump(result),indent=2))

