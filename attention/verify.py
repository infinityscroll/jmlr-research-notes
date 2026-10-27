"""Portable bounded checks. No training, downloads, or proof-certification claims."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import importlib.util
import json
import platform
import numpy as np

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_integrity():
    provenance = json.loads((ROOT/'provenance/source_manifest.json').read_text())
    for name, entry in provenance['unchanged_copies'].items():
        assert sha(ROOT/name) == entry['sha256'], 'Changed archival copy: ' + name
    return {'byte_identical_copies_checked':len(provenance['unchanged_copies'])}

def mm(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def transpose(a):
    return list(map(list,zip(*a)))

def exact_algebra():
    fixtures = [
        ([[F(41,70),F(26,35)],[F(26,35),F(48,25)]],
         [[F(-5,4),F(7,4)],[F(5,16),F(-15,16)]], F(1,5), 3),
        ([[F(109,198),F(28,33)],[F(28,33),F(320,81)]],
         [[F(-9,8),F(11,8)],[F(9,64),F(-27,64)]], F(1,10), 5)]
    for P,J,floor,ceiling in fixtures:
        a,b=mm(transpose(J),P),mm(P,J)
        assert [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)] == [[-1,0],[0,-1]]
        assert P[0][0]>floor
        assert (P[0][0]-floor)*(P[1][1]-floor)-P[0][1]**2>0
        assert P[0][0]+P[1][1]<ceiling
    d=[F(1,2),F(-1)];cd=sum(v*v for v in d)
    bad=[[a*b/cd for b in d] for a in [F(1),F(-1,2)]]
    C=[[a*b for b in d] for a in [F(1),F(0)]]
    assert sum(v*v for row in bad for v in row)==1
    assert sum(bad[i][j]*C[i][j] for i in range(2) for j in range(2))==1
    assert sum(v*v for row in C for v in row)==F(5,4)
    d=[F(3,4),F(-1)];c=sum(abs(v)**3 for v in d)
    assert c==F(91,64)
    rows=0
    signed_square=lambda z:z*abs(z)
    for ri in range(-8,9):
        if ri==0:continue
        for ei in range(-3,4):
            r=F(ri);E=[F(ei,20),F(3*ei,80)]
            assert sum(x*y for x,y in zip(E,d))==0
            assert all((r*x+y)*r*x>0 for x,y in zip(d,E))
            h=sum(abs(x)*x*y for x,y in zip(d,E))/c
            e=sum(abs(x)*y*y for x,y in zip(d,E))-c*h*h
            assert e>=0
            value=sum(x*signed_square(r*x+y) for x,y in zip(d,E))
            sign=1 if r>0 else -1
            assert value==sign*(c*(r+h)**2+e)
            dr=F(1,101)
            updated=sum(x*signed_square((r+dr)*x+y) for x,y in zip(d,E))
            assert updated-value==sign*c*(2*(r+h)*dr+dr*dr)
            rows+=1
    assert 1-F(9,8)+F(1,4)*F(1,2)==0
    assert F(1,4)*F(9,8)-F(9,16)*F(1,2)==0
    assert F(1,20000)<F(1,6144) # printed p=2 cone corollary
    return {'lyapunov_identities':2,'exact_offset_and_finite_step_cases':rows,
            'exact_margin_and_cone_arithmetic':'PASS'}

def softmax_rows(a):
    e=np.exp(a-a.max(axis=1,keepdims=True))
    return e/e.sum(axis=1,keepdims=True)

def retained_states():
    data=ROOT/'data'
    protocol=json.loads((data/'diagnostic_protocol.json').read_text())
    results=json.loads((data/'diagnostic_results.json').read_text())
    state=np.load(data/'diagnostic_states.npz',allow_pickle=False)
    assert protocol['deltas']==[0.,.5] and protocol['steps']==50000
    assert protocol['seed'] is None and not protocol['outcome_adaptive_choices']
    assert results['protocol_sha256']==sha(data/'diagnostic_protocol.json')
    assert results['states_sha256']==sha(data/'diagnostic_states.npz')
    n=len(results['records'])
    assert state['W1'].shape==state['W2'].shape==(n,2,2,2)
    assert state['steps'].tolist()==[r['step'] for r in results['records']]
    assert len(set(state['steps'].tolist()))==n
    assert state['steps'][0]==0 and state['steps'][-1]==50000
    max_error=0.;max_gauge=0.;count=0
    for ti,record in enumerate(results['records']):
        for ci,case in enumerate(record['cases']):
            X=state['X'][ci];W1=state['W1'][ti,ci];W2=state['W2'][ti,ci]
            H=softmax_rows(X@W1@X.T)@X
            O=softmax_rows(H@W2@H.T)@H
            Hminus=softmax_rows((-X)@W1@(-X).T)@(-X)
            Ominus=softmax_rows(Hminus@W2@Hminus.T)@Hminus
            diff=X[0]-X[1];l=X@W1@diff;k=W2@diff
            C1=np.outer(X[0],diff);C2=np.outer(H[0],H[0]-H[1])
            values={'prediction':O[0,0],'loss':np.logaddexp(0,-O[0,0]),
              'lower_margin_fraction':np.sum(C1*W1)/(np.linalg.norm(C1)*np.linalg.norm(W1)),
              'upper_margin_fraction':np.sum(C2*W2)/(np.linalg.norm(C2)*np.linalg.norm(W2)),
              'upper_optimal_margin':np.linalg.norm(C2),
              'memory_distance':np.linalg.norm(H[0]-H[1]),
              'a':softmax_rows(X@W1@X.T)[0,0],
              'b':softmax_rows(X@W1@X.T)[1,0],
              'm':H[0]@W2@(H[0]-H[1])}
            errors=[abs(v-case[key]) for key,v in values.items()]
            errors+=list(abs(l-np.asarray(case['l'])))+list(abs(k-np.asarray(case['k'])))
            errors.append(abs(O[0,0]+Ominus[0,0]))
            max_error=max(max_error,max(errors));count+=len(errors)
            for W,arr in [(W1,state['W1']),(W2,state['W2'])]:
                gauge=W-np.outer(W@diff,diff)/(diff@diff)
                W0=arr[0,ci];gauge0=W0-np.outer(W0@diff,diff)/(diff@diff)
                max_gauge=max(max_gauge,float(np.max(np.abs(gauge-gauge0))))
    assert max_error<2e-12 and max_gauge<2e-12
    return {'checkpoints':n,'cases':2,'scalar_values':count,
            'max_saved_value_error':float(max_error),'max_gauge_error':max_gauge}

def metric_order():
    d=np.array([.75,-1.]);c=float(np.sum(abs(d)**3));jd=d*abs(d)
    target=np.outer([1.,0.],jd)/c;bad=np.outer([1.,-.25],jd)/c
    norm=lambda M:np.sum(abs(M)**1.5)**(2/3)
    T=target/norm(target);B=bad/norm(bad)
    ratio=float(np.sum(np.outer([1.,0.],d)*B)/c**(1/3))
    official=float(1-np.sum(np.sign(B)*np.sqrt(abs(B))*T))
    reverse=float(1-np.sum(np.sign(T)*np.sqrt(abs(T))*B))
    assert abs(ratio-(8/9)**(2/3))<1e-14
    assert abs(official-(1-(8/9)**(1/3)))<1e-14
    assert abs(reverse-(1-(8/9)**(2/3)))<1e-14
    return {'margin_fraction':ratio,'svm_first_bregman_gap':official,
            'reverse_bregman_gap':reverse}

def generic_p_geometry():
    """Exact KKT/clock checks for integer p, then finite metric spot checks."""
    x1=[F(1),F(1)];x2=[F(2),F(1,2)];q=[F(-1,3),F(4,3)]
    assert sum(a*b for a,b in zip(x1,q))==1
    assert sum(a*b for a,b in zip(x2,q))==0
    for p in [2,3,4,5]:
        aa=F(1,3)**(p-1);bb=F(4,3)**(p-1)
        lam=(aa+4*bb)/3;mu=2*(aa+bb)/3
        assert lam>0 and mu>0
        assert [lam*a-mu*b for a,b in zip(x1,x2)]==[-aa,bb]
        weights=[abs(v)**(2-p) for v in q]
        X=[x1,x2]
        M=[[sum(X[i][k]*X[j][k]*weights[k] for k in range(2)) for j in range(2)] for i in range(2)]
        top=2*F(1,2)**(2-p)
        g=[[v/top for v in row] for row in M]
        det=g[0][0]*g[1][1]-g[0][1]**2
        assert det>0 and g[0][1]>0
        u=g[1][1]/det;v=g[0][1]/det
        assert 1-g[0][0]*u+g[0][1]*v==0
        assert g[0][1]*u-g[1][1]*v==0
        J=[[-g[0][0]*u,g[0][0]*u+g[0][1]],
           [v*g[0][1]*u,-v*(g[0][1]*u+g[1][1])]]
        assert J[0][0]+J[1][1]<0
        assert J[0][0]*J[1][1]-J[0][1]*J[1][0]==u*v*det
    metrics=[]
    for p in [1.25,1.5,2.,3.,4.,5.]:
        qp=p/(p-1);diff=np.array([-1.,.5]);xx=np.array([1.,1.])
        qbad=np.array([-1/3,4/3]);kt=np.array([.5,.5])
        zd=np.sign(diff)*abs(diff)**(qp-1);c=np.sum(abs(diff)**qp)
        W=np.outer(qbad,zd)/c;T=np.outer(kt,zd)/c
        norm=lambda z:float(np.sum(abs(z)**p)**(1/p))
        wn=W/norm(W);tn=T/norm(T)
        normal=np.outer(xx,diff)
        frac=float(np.sum(normal*wn)/np.sum(abs(normal)**qp)**(1/qp))
        expected=3/(2**(1-1/p)*(1+4**p)**(1/p))
        gap=float(1-np.sum(np.sign(wn)*abs(wn)**(p-1)*tn))
        expected_gap=1-np.sum(np.sign(qbad)*abs(qbad/norm(qbad))**(p-1)*kt/norm(kt))
        assert abs(frac-expected)<1e-13 and 0<frac<1
        assert abs(gap-expected_gap)<1e-13 and gap>0
        metrics.append({'p':p,'margin_fraction':frac,'svm_first_bregman_gap':gap})
    return {'exact_KKT_and_Hurwitz_fixtures':4,'finite_metric_checks':metrics,
            'scope':'Finite checks; the all-p theorem is an analytic claim, not proved by this grid.'}

def native_interface():
    import torch
    from fetch_optimizer import checked_path,EXPECTED
    torch.set_num_threads(1)
    optpath=checked_path()
    spec=importlib.util.spec_from_file_location('pinned_released_smd',optpath)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    X=np.array([[1.,0.],[.25,1.]]);d=X[0]-X[1]
    grad_error=0.;update_error=0.;prediction_error=0.;cases=0
    for p in [2.,1.5]:
        for j in range(24):
            r1=np.array([2.+j/20,-1.-j/40]);r2=np.array([2.4+j/30,(-1.)**j*.2])
            coeff=np.array([[(j%5-2)/20,(j%7-3)/30],[(j%3-1)/25,(j%4-2)/40]])
            offsets=[np.outer(coeff[l],np.array([1.,.75])) for l in range(2)]
            dual=[np.outer(r,d)+E for r,E in zip([r1,r2],offsets)]
            inv=lambda Z:np.sign(Z)*abs(Z)**(1/(p-1))
            Ws=[torch.tensor(inv(Z),dtype=torch.float64,requires_grad=True) for Z in dual]
            Xt=torch.tensor(np.stack([X,-X]),dtype=torch.float64)
            H=torch.softmax(Xt@Ws[0]@Xt.transpose(-1,-2),dim=-1)@Xt
            O=torch.softmax(H@Ws[1]@H.transpose(-1,-2),dim=-1)@H
            signed=O[:,0,0]*torch.tensor([1.,-1.],dtype=torch.float64)
            loss=torch.nn.functional.softplus(-signed).mean();loss.backward()
            old=[W.detach().numpy().copy() for W in Ws]
            q1=old[0]@d;k=old[1]@d;l=X@q1
            a,b=1/(1+np.exp(-l));h1=X[1]+a*d;m=(a-b)*(h1@k)
            pi=1/(1+np.exp(-m));f=.25+.75*(b+pi*(a-b));Q=1/(1+np.exp(f))
            ca=pi+pi*(1-pi)*(m+(a-b)**2*(d@k));cb=(1-pi)*(1-pi*m)
            A=a*(1-a)*ca;B=b*(1-b)*cb;U=(a-b)**2*pi*(1-pi)
            gradients=[-Q*.75*np.outer(A*X[0]+B*X[1],d),-Q*.75*U*np.outer(h1,d)]
            for i in range(2):
                grad_error=max(grad_error,float(np.max(abs(gradients[i]-Ws[i].grad.numpy()))))
            prediction_error=max(prediction_error,float(np.max(abs(signed.detach().numpy()-f))))
            eta=.001*(j+1)
            expected=[inv(Z-eta*g) for Z,g in zip(dual,gradients)]
            opt=mod.SMD(Ws,p=p,normalize=False);opt.param_groups[0]['lr']=eta;opt.step()
            for i in range(2):
                update_error=max(update_error,float(np.max(abs(expected[i]-Ws[i].detach().numpy()))))
            cases+=1
    assert grad_error<1e-12 and update_error<1e-11 and prediction_error<1e-12
    return {'cases':cases,'max_gradient_error':grad_error,'max_update_error':update_error,
            'max_prediction_error':prediction_error,'optimizer_sha256':EXPECTED,
            'torch_version':torch.__version__}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native',action='store_true',help='Also check full autograd + pinned released SMD (no training)')
    parser.add_argument('--output',type=Path,help='Optional new JSON report; existing files are never overwritten')
    args=parser.parse_args()
    report={'scope':'Bounded reproducibility checks, not analytic/formal proof verification',
      'python_version':platform.python_version(),'numpy_version':np.__version__,
      'source_integrity':source_integrity(),'exact_algebra':exact_algebra(),
      'saved_diagnostics':retained_states(),'metric_orientation':metric_order(),
      'generic_p_geometry':generic_p_geometry(),
      'training_steps':0,'network_calls':0}
    report['native_interface']=native_interface() if args.native else 'NOT RUN (use --native)'
    report['status']='PASS'
    rendered=json.dumps(report,indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f:f.write(rendered)
    print(rendered,end='')

if __name__=='__main__':
    main()
