"""Independent rational check of all-simplex local/chain identities.

The positive parameters w_e,D_g,kappa_h are FORMAL scaled stratum masses.
Their boundary-moment formulas need not come from a Gaussian instance.
This checks the exact algebra and signs, not covariance PSD or a theorem.
"""
import itertools
import json
import time
import sympy as sp


def subsets(m, k):
    return list(itertools.combinations(range(m), k))


def boundary(lower, upper):
    loc = {x:i for i,x in enumerate(lower)}
    out = sp.zeros(len(lower), len(upper))
    for j, cell in enumerate(upper):
        for r in range(len(cell)):
            out[loc[cell[:r]+cell[r+1:]], j] = (-1)**r
    return out


def run(d):
    started = time.time()
    m = d+1
    mat = sp.Matrix(d,d,lambda i,j: (i+2 if i==j else
                                    ((i+2*j)%3-1 if j<i else 0)))
    sites = [sp.zeros(d,1)]+[mat.row(i).T for i in range(d)]
    v = [None]+[-mat.inv()[:,k] for k in range(d)]
    v[0] = -sum(v[1:], sp.zeros(d,1))
    apex = sp.Matrix([sp.Rational((-1)**i*(i+1),i+3) for i in range(d)])
    edges,triangles,quads = [subsets(m,k) for k in [2,3,4]]
    w = {e:sp.Rational(i+2,i+3) for i,e in enumerate(edges)}
    ds = {g:sp.Rational(2*i+3,i+2) for i,g in enumerate(triangles)}
    kap = {h:sp.Rational(i+1,i+4) for i,h in enumerate(quads)}
    projectors = {}
    for cell in edges+triangles:
        differences = sp.Matrix.hstack(*[sites[i]-sites[cell[0]] for i in cell[1:]])
        projectors[cell] = sp.eye(d)-differences*(differences.T*differences).inv()*differences.T
    means = {}
    for e in edges:
        pe=projectors[e]
        means[e]=(sp.eye(d)-pe)*apex
        for k in range(m):
            if k not in e:
                g=tuple(sorted(e+(k,)))
                means[e]+=pe*(sites[e[0]]-sites[k])/(w[e]*ds[g])
    for g in triangles:
        pg=projectors[g]
        means[g]=(sp.eye(d)-pg)*apex
        for k in range(m):
            if k not in g:
                h=tuple(sorted(g+(k,)))
                means[g]+=ds[g]*kap[h]*pg*(sites[g[0]]-sites[k])
    p2=boundary(edges,triangles)
    p3=boundary(triangles,quads)
    assert p2*p3 == sp.zeros(len(edges),len(quads))
    aa=p2.T*sp.diag(*[1/w[e] for e in edges])*p2
    bb=sp.zeros(len(triangles))
    local_checks=0
    for ei,e in enumerate(edges):
        gs=[g for g in triangles if set(e).issubset(g)]
        ks=[next(k for k in g if k not in e) for g in gs]
        pe=projectors[e]
        nn=sp.Matrix.hstack(*[pe*(sites[e[0]]-sites[k])/ds[g]
                             for k,g in zip(ks,gs)])
        rr=sp.Matrix.vstack(*[ds[g]*v[k].T for k,g in zip(ks,gs)])
        assert rr*nn==sp.eye(d-1)
        tt=sp.Matrix.hstack(*[means[e]-means[g] for g in gs])
        dd=nn*tt.T
        assert dd==dd.T
        be=rr*tt
        assert be==be.T
        assert tt==dd*rr.T
        for r,g in enumerate(gs):
            k=ks[r]
            gi=triangles.index(g)
            for s,gp in enumerate(gs):
                gj=triangles.index(gp)
                expected=1/w[e]-ds[g]*(v[k].dot(means[gp]))
                assert be[r,s]==expected
                if g!=gp:
                    h=tuple(sorted(set(g)|set(gp)))
                    assert be[r,s]==1/w[e]-ds[g]*ds[gp]*kap[h]
                bb[gi,gj]+=p2[ei,gi]*p2[ei,gj]*be[r,s]
                local_checks+=1
    diagd=sp.diag(*[ds[g] for g in triangles])
    target=-diagd*p3*sp.diag(*[kap[h] for h in quads])*p3.T*diagd
    assert aa-bb==target
    assert p3.rank()==len(triangles)-p2.rank()
    pairs=[(i,j) for i in range(d) for j in range(i,d)]
    dyads=sp.Matrix([[((sites[e[0]]-sites[e[1]])[i]*(sites[e[0]]-sites[e[1]])[j])
                     for i,j in pairs] for e in edges])
    assert dyads.rank()==d*(d+1)//2
    return dict(d=d,edges=len(edges),triangles=len(triangles),quads=len(quads),
                local_entry_checks=local_checks,chain_rank=p3.rank(),
                identity_entries=len(triangles)**2,exact=True,
                elapsed_seconds=round(time.time()-started,3))


if __name__=='__main__':
    output=dict(status='PASS', arithmetic='SymPy exact rational',
                scope='Formal boundary-moment and simplex-chain algebra; no Gaussian PSD inference.',
                cases=[run(d) for d in range(2,7)])
    print(json.dumps(output,indent=2))
