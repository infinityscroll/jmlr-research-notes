"""Bounded exact checks; not a substitute for the selector/risk proof."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

D = Path(__file__).resolve().parent
SOURCE = D / "design_compression_selector_theorem.md"
BOUND = "188c39bfbe31e11b668bddd7d31d251a56ba4d179b72fb7d23fbfb6339b70a16"
COUNTS = {}

def check(name, value):
    assert value, name
    COUNTS[name] = COUNTS.get(name, 0) + 1

def tr(a):
    return [list(x) for x in zip(*a)]

def mm(a, b):
    return [[sum(x*y for x, y in zip(r, c)) for c in zip(*b)] for r in a]

def eye(k):
    return [[F(i == j) for j in range(k)] for i in range(k)]

def det(a):
    a = [r[:] for r in a]
    out = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            out = -out
        t = a[j][j]
        out *= t
        for i in range(j+1, len(a)):
            c = a[i][j]/t
            a[i] = [u-c*v for u, v in zip(a[i], a[j])]
    return out

def inv(a):
    k = len(a)
    a = [r[:] + q for r, q in zip(a, eye(k))]
    for j in range(k):
        p = next(i for i in range(j, k) if a[i][j])
        a[j], a[p] = a[p], a[j]
        t = a[j][j]
        a[j] = [x/t for x in a[j]]
        for i in range(k):
            if i != j:
                t = a[i][j]
                a[i] = [x-t*y for x, y in zip(a[i], a[j])]
    return [r[k:] for r in a]

def cov(rows, weights):
    k = len(rows[0])
    return [[sum(w*x[i]*x[j] for x, w in zip(rows, weights))
             for j in range(k)] for i in range(k)]

def quad(x, m, y=None):
    if y is None:
        y = x
    return sum(x[i]*m[i][j]*y[j] for i in range(len(x)) for j in range(len(x)))

def null(a):
    a = [r[:] for r in a]
    nr, nc = len(a), len(a[0])
    pivots = []
    rr = 0
    for col in range(nc):
        p = next((i for i in range(rr, nr) if a[i][col]), None)
        if p is None:
            continue
        a[rr], a[p] = a[p], a[rr]
        t = a[rr][col]
        a[rr] = [x/t for x in a[rr]]
        for i in range(nr):
            if i != rr:
                t = a[i][col]
                a[i] = [x-t*y for x, y in zip(a[i], a[rr])]
        pivots.append(col)
        rr += 1
        if rr == nr:
            break
    free = next(j for j in range(nc) if j not in pivots)
    out = [F(0)]*nc
    out[free] = F(1)
    for i, col in enumerate(pivots):
        out[col] = -a[i][free]
    return out

def compress(rows, weights):
    k = len(rows[0])
    size = 1+k*(k+1)//2
    weights = weights[:]
    phi = [[F(1)]+[x[i]*x[j] for i in range(k) for j in range(i,k)] for x in rows]
    while sum(w > 0 for w in weights) > size:
        ids = [j for j,w in enumerate(weights) if w > 0][:size+1]
        c = null(tr([phi[j] for j in ids]))
        check("compression_dependence_mass", sum(c) == 0)
        check("compression_dependence_covariance", all(
            sum(c[t]*phi[j][r] for t,j in enumerate(ids)) == 0
            for r in range(size)))
        step = min(weights[j]/c[t] for t,j in enumerate(ids) if c[t] > 0)
        for t,j in enumerate(ids):
            weights[j] -= step*c[t]
        check("compression_nonnegative", all(w >= 0 for w in weights))
    return weights

def residual(x, selected, metric):
    base = quad(x, metric)
    if not selected:
        return base
    gram = [[quad(a,metric,b) for b in selected] for a in selected]
    z = [quad(x,metric,a) for a in selected]
    return base-quad(z, inv(gram))

def greedy(rows, ids, metric, k):
    chosen = []
    for _ in range(k):
        j = max((j for j in ids if j not in chosen),
                key=lambda j: (residual(rows[j], [rows[t] for t in chosen], metric), -j))
        check("positive_greedy_pivot", residual(rows[j], [rows[t] for t in chosen], metric) > 0)
        chosen.append(j)
    return chosen

check("source_sha256", hashlib.sha256(SOURCE.read_bytes()).hexdigest() == BOUND)
fixtures = []
for k in range(2,6):
    for e in [F(1,10000),F(1,100000)]:
        rows=[]; labels=[]
        for j in range(k):
            for _ in range(3):
                rows.append([F(i==j)/(1+4*e) for i in range(k)])
                labels.append(j)
        for j in range(k):
            for sign in [-1,1]:
                b=[F(i in [j,(j+1)%k],2) for i in range(k)]
                b[j]+=F(sign,2)
                rows.append([x/5 for x in b])
                labels.append(None)
        weights=[(1-e)/(3*k)]*(3*k)+[e/(2*k)]*(2*k)
        m=cov(rows,weights)
        check("fixture_probability_weights",sum(weights)==1)
        check("fixture_positive_covariance",det(m)>0)
        compressed=compress(rows,weights)
        J=1+k*(k+1)//2
        check("compressed_covariance_exact",cov(rows,compressed)==m)
        check("compressed_mass_exact",sum(compressed)==1)
        check("compressed_support_bound",sum(w>0 for w in compressed)<=J)
        heavy=[j for j,w in enumerate(compressed) if w>=F(1,8*k*J)]
        check("heavy_atoms_are_anchor_clusters",all(labels[j] is not None for j in heavy))
        check("heavy_atoms_cover_vertices",set(labels[j] for j in heavy)==set(range(k)))
        chosen=greedy(rows,heavy,inv(m),k)
        check("greedy_distinct_vertices",set(labels[j] for j in chosen)==set(range(k)))
        transform=[[F(0) for _ in range(k)] for _ in range(k)]
        for j in range(k):
            transform[j][j]=F(10**(2*j))
            if j+1<k:
                transform[j][j+1]=F(3,7)
        raw=mm(rows,transform)
        mr=cov(raw,weights)
        ir=inv(mr); ix=inv(m)
        check("congruence_covariance",mr==mm(mm(tr(transform),m),transform))
        for x,y in zip(rows,raw):
            check("affine_leverage_exact",quad(x,ix)==quad(y,ir))
        check("affine_greedy_indices_exact",greedy(raw,heavy,ir,k)==chosen)
        cr=compress(raw,weights)
        check("raw_compression_preserves_covariance",cov(raw,cr)==mr)
        check("raw_compression_preserves_mass",sum(cr)==1)
        hr=[j for j,w in enumerate(cr) if w>=F(1,8*k*J)]
        check("raw_compression_heavy_coverage",set(labels[j] for j in hr)==set(range(k)))
        check("raw_compression_heavy_purity",all(labels[j] is not None for j in hr))
        check("raw_compressed_greedy_coverage",set(labels[j] for j in greedy(raw,hr,ir,k))==set(range(k)))
        # Exact determinant identity and fixed-step polynomial inequality.
        for delta in [F(1),F(1,2),F(1,10)]:
            t=delta/(2*(k+delta)**2)
            point=rows[0]; score=quad(point,ix)
            new=[[(1-t)*m[i][j]+t*point[i]*point[j] for j in range(k)] for i in range(k)]
            check("rank_one_determinant_identity",det(new)/det(m)==(1-t)**(k-1)*(1+t*(score-1)))
            dd=k+delta
            bracket=(k-1)+(dd-1)**2/2
            check("progress_polynomial_bound",t*delta-t*t*bracket>=delta**2/(4*dd*dd))
        fixtures.append({'K':k,'e':str(e),'p':len(rows),'support':sum(w>0 for w in compressed),'heavy':len(heavy)})

certificate={'status':'PASS','source_sha256':BOUND,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'assertions':sum(COUNTS.values()),'counts':COUNTS,'fixtures':fixtures,
             'scope':'Exact finite algebra only. No statistical theorem, arbitrary-input QR, log inequality, finite-bit stability, or runtime claim is inferred from these fixtures.'}
(D/'selector_algebra_certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
print(json.dumps({'status':'PASS','assertions':certificate['assertions'],'fixtures':len(fixtures)},indent=2))
