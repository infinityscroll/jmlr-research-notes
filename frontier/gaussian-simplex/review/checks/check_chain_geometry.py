#!/usr/bin/env python3
"""Independent exact geometry/chain audit. No engine or prior checker imports.

The moments below are formal positive stratum parameters, not sampled Gaussian
integrals. Gaussian IBP supplies their interpretation in the analytic proof.
All arithmetic is Fraction; this tests the uniform identity on finite fixtures.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def add(a, b):
    return [x+y for x, y in zip(a, b)]


def sub(a, b):
    return [x-y for x, y in zip(a, b)]


def scale(s, a):
    return [s*x for x in a]


def solve(a, b):
    if not a:
        return []
    n = len(a)
    aug = [[Q(x) for x in row]+[Q(y)] for row, y in zip(a, b)]
    for j in range(n):
        k = next(k for k in range(j, n) if aug[k][j])
        aug[j], aug[k] = aug[k], aug[j]
        s = aug[j][j]
        aug[j] = [v/s for v in aug[j]]
        for k in range(n):
            if k != j and aug[k][j]:
                s = aug[k][j]
                aug[k] = [u-s*v for u, v in zip(aug[k], aug[j])]
    return [row[-1] for row in aug]


def projection(a, basis):
    gram = [[dot(x, y) for y in basis] for x in basis]
    coeff = solve(gram, [dot(x, a) for x in basis])
    ans = [Q(0)]*len(a)
    for c, x in zip(coeff, basis):
        ans = add(ans, scale(c, x))
    return ans


def det(a):
    n = len(a)
    if not n:
        return Q(1)
    return sum(((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]])
                for j in range(n)), Q(0))


def boundary(simplex):
    return [(simplex[:j]+simplex[j+1:], (-1)**j)
            for j in range(len(simplex))]


checks = []
fixtures = []


def check(name, value):
    if not value:
        raise AssertionError(name)
    checks.append(name)


def fixture(d, seed):
    rng = random.Random(seed)
    zero = [Q(0)]*d
    # An invertible, nonregular rational simplex; translated target and fan.
    base = [Q(rng.randrange(-3, 4), 2) for _ in range(d)]
    columns = [[Q(rng.randrange(-2, 3) if j < i else
                  (rng.randrange(1, 4) if j == i else 0))
                for j in range(d)] for i in range(d)]
    ys = [base]+[add(base, x) for x in columns]
    a = [Q(rng.randrange(-4, 5), 3) for _ in range(d)]
    edges = list(combinations(range(d+1), 2))
    tris = list(combinations(range(d+1), 3))
    tets = list(combinations(range(d+1), 4))
    D = {g: Q(rng.randrange(1, 6)) for g in tris}
    c = {h: Q(rng.randrange(1, 6), 7) for h in tets}
    w = {e: Q(rng.randrange(1, 6), 3) for e in edges}
    # v_i = minus barycentric gradient, computed independently by linear solve.
    v = {}
    for k in range(1, d+1):
        v[k] = solve(columns, [-Q(i+1 == k) for i in range(d)])
    v[0] = scale(-1, [sum((v[k][j] for k in range(1, d+1)), Q(0))
                       for j in range(d)])
    check('d%d-s%d-barycentric-pairings' % (d, seed),
          all(dot(v[k], sub(ys[i], ys[j])) == Q(k == j)-Q(k == i)
              for k in range(d+1) for i, j in edges))
    # Triangle conditional means via the first-moment stratum identity.
    mg = {}
    height_ok = True
    for g in tris:
        b = [sub(ys[j], ys[g[0]]) for j in g[1:]]
        gram2 = [[dot(x, y) for y in b] for x in b]
        mean = projection(a, b)
        for k in range(d+1):
            if k in g:
                continue
            gap = sub(ys[g[0]], ys[k])
            tangent = sub(gap, projection(gap, b))
            h = tuple(sorted(g+(k,)))
            mean = add(mean, scale(c[h]*D[g], tangent))
            gram3 = [[dot(x, y) for y in b+[gap]] for x in b+[gap]]
            height_ok &= dot(tangent, tangent)*det(gram2) == det(gram3)
        mg[g] = mean
    check('d%d-s%d-intrinsic-height-factors' % (d, seed), height_ok)
    tid = {g: i for i, g in enumerate(tris)}
    nt = len(tris)
    A = [[Q(0)]*nt for _ in tris]
    B = [[Q(0)]*nt for _ in tris]
    symmetry = True
    duality = True
    for e in edges:
        gap = sub(ys[e[0]], ys[e[1]])
        local = [(tuple(sorted(e+(k,))), k) for k in range(d+1) if k not in e]
        u = {g: sub(sub(ys[e[0]], ys[k]),
                    scale(dot(sub(ys[e[0]], ys[k]), gap)/dot(gap, gap), gap))
             for g, k in local}
        me = scale(dot(a, gap)/dot(gap, gap), gap)
        for g, _ in local:
            me = add(me, scale(1/(w[e]*D[g]), u[g]))
        Be = [[D[g]*dot(v[k], sub(me, mg[g2])) for g2, _ in local]
              for g, k in local]
        symmetry &= all(Be[i][j] == Be[j][i]
                        for i in range(len(local)) for j in range(len(local)))
        duality &= all(dot(scale(D[g], v[k]), scale(1/D[g2], u[g2])) == Q(g == g2)
                       for g, k in local for g2, _ in local)
        for i, (g, _) in enumerate(local):
            si = dict(boundary(g))[e]
            for j, (g2, _) in enumerate(local):
                sj = dict(boundary(g2))[e]
                A[tid[g]][tid[g2]] += si*sj/w[e]
                B[tid[g]][tid[g2]] += si*sj*Be[i][j]
    check('d%d-s%d-facet-dual-bases' % (d, seed), duality)
    check('d%d-s%d-facet-matrix-symmetry' % (d, seed), symmetry)
    correction = [[Q(0)]*nt for _ in tris]
    for h in tets:
        for g, si in boundary(h):
            for g2, sj in boundary(h):
                correction[tid[g]][tid[g2]] += D[g]*D[g2]*si*sj*c[h]
    check('d%d-s%d-full-entry-factorization' % (d, seed),
          all(B[i][j]-A[i][j] == correction[i][j]
              for i in range(nt) for j in range(nt)))
    # Gauge independently projected using only the tetrahedra coned to vertex0.
    J = []
    for rest in combinations(range(1, d+1), 3):
        col = [Q(0)]*nt
        for g, s in boundary((0,)+rest):
            col[tid[g]] = Q(s)
        J.append(col)
    lam = [Q(rng.randrange(-3, 4)) for _ in tris]
    gram = [[sum((D[g]*x[i]*y[i] for i, g in enumerate(tris)), Q(0))
             for y in J] for x in J]
    rhs = [-sum((D[g]*x[i]*lam[i] for i, g in enumerate(tris)), Q(0)) for x in J]
    shift = solve(gram, rhs)
    gauged = list(lam)
    for z, x in zip(shift, J):
        gauged = add(gauged, scale(z, x))
    check('d%d-s%d-full-gauge-not-just-independent-boundaries' % (d, seed),
          all(sum((s*D[g]*gauged[tid[g]] for g, s in boundary(h)), Q(0)) == 0
              for h in tets))
    check('d%d-s%d-gauge-keeps-cycle-flow' % (d, seed),
          all(sum((dict(boundary(g)).get(e, 0)*(gauged[i]-lam[i])
                   for i, g in enumerate(tris)), Q(0)) == 0 for e in edges))
    def quadratic(M, z):
        return sum((z[i]*M[i][j]*z[j] for i in range(nt) for j in range(nt)), Q(0))
    check('d%d-s%d-gauged-quadratic-equality' % (d, seed),
          quadratic(A, gauged) == quadratic(B, gauged))
    fixtures.append(dict(dimension=d, seed=seed, edges=len(edges), triangles=nt,
                         tetrahedra=len(tets), independent_gauge_dimensions=len(J)))


if __name__ == '__main__':
    for d in range(2, 8):
        for seed in (3102026, 3102027):
            fixture(d, seed)
    result = dict(status='PASS', check_count=len(checks), fixtures=fixtures,
                  checks=checks, arithmetic='Python fractions.Fraction only',
                  limits='Finite algebra fixtures only; Gaussian IBP, covariance positivity and uniform proof are audited separately.',
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out = Path(__file__).with_name('CHAIN_GEOMETRY_CHECKS.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status', 'check_count', 'checker_sha256')}, indent=2))
