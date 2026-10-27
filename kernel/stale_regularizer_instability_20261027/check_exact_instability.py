"""Rational second-moment certificates; standard library only, no simulation.

Coordinates are (w error, v error). The three equally likely blocks have size 2.
Source code is read and hashed, never edited. Run with ordinary Python 3.9+.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
OFFICIAL = HERE.parent / 'official'


def zeros(m, n): return [[F(0) for _ in range(n)] for _ in range(m)]
def eye(n): return [[F(i == j) for j in range(n)] for i in range(n)]
def tr(a): return list(map(list, zip(*a)))
def add(a, b): return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]
def scale(c, a): return [[c*x for x in row] for row in a]
def sub(a, b): return add(a, scale(-1, b))
def mul(a, b):
    return [[sum(x*y for x, y in zip(ar, bc)) for bc in tr(b)] for ar in a]
def hcat(a, b): return [x+y for x, y in zip(a, b)]
def block(a, b, c, d): return hcat(a, b)+hcat(c, d)


I = eye(3)
E = [[F(1, 3)]*3 for _ in range(3)]
P = sub(I, E)
Z = zeros(3, 3)
LAM = F(3, 20000)
COR = F(99999, 100000)
S = F(1, 100)
GAMMA = F(200, 3)
K = add(scale(1-COR, I), scale(3*COR, E))
H = add(K, scale(LAM, I))
Y = hcat(scale(1/(1+S), I), scale(S/(1+S), I))
W = hcat(I, Z)
V = hcat(Z, I)
BLOCKS = [(0, 1), (0, 2), (1, 2)]


def native_matrix(indices, stale):
    d = 1 + LAM
    inv = [[d/(d*d-COR*COR), -COR/(d*d-COR*COR)],
           [-COR/(d*d-COR*COR), d/(d*d-COR*COR)]]
    pre = zeros(3, 3)
    for i, bi in enumerate(indices):
        for j, bj in enumerate(indices): pre[bi][bj] = inv[i][j]
    grad = add(mul(K, Y), scale(LAM, W)) if stale else mul(H, Y)
    step = mul(pre, grad)
    return sub(Y, step)+sub(add(scale(1-S, V), scale(S, Y)), scale(GAMMA, step))


def covariance(x):
    a, b, c, d, e, f = x
    return block(add(scale(a, P), scale(b, E)), add(scale(c, P), scale(d, E)),
                 add(scale(c, P), scale(d, E)), add(scale(e, P), scale(f, E)))


def coordinates(C):
    # An invariant 3x3 block is a P+b E: a=diagonal-offdiagonal, b=diagonal+2off.
    ans = []
    for r, c in [(0, 0), (0, 3), (3, 3)]:
        diag, off = C[r][c], C[r][c+1]
        ans += [diag-off, diag+2*off]
    assert covariance(ans) == C, 'Permutation-invariance check failed'
    return ans


def phi(C, stale):
    result = zeros(6, 6)
    for indices in BLOCKS:
        M = native_matrix(indices, stale)
        result = add(result, scale(F(1, 3), mul(mul(M, C), tr(M))))
    return result


def psd_certificate(C, strict=False):
    a, b, c, d, e, f = coordinates(C)
    minors = [a, e, a*e-c*c, b, f, b*f-d*d]
    assert all(x > 0 if strict else x >= 0 for x in minors), minors
    return {'contrast_2x2': [[str(a), str(c)], [str(c), str(e)]],
            'common_2x2': [[str(b), str(d)], [str(d), str(f)]],
            'principal_minors': list(map(str, minors)), 'positive_definite': strict}


def moment_matrix(stale):
    columns = []
    for j in range(6):
        x = [F(int(i == j)) for i in range(6)]
        columns.append(coordinates(phi(covariance(x), stale)))
    return tr(columns)


def solve(a, b):
    m = [row[:]+[v] for row, v in zip(a, b)]
    for j in range(len(m)):
        pivot = next(i for i in range(j, len(m)) if m[i][j])
        m[j], m[pivot] = m[pivot], m[j]
        m[j] = [v/m[j][j] for v in m[j]]
        for i in range(len(m)):
            if i != j:
                c = m[i][j]
                m[i] = [v-c*w for v, w in zip(m[i], m[j])]
    return [row[-1] for row in m]


def main():
    # Printed default-parameter checks; all strict here.
    nu = F(3, 2)
    assert LAM < nu and LAM*nu < 1
    assert S*S == LAM/nu and GAMMA*GAMMA == 1/(LAM*nu)
    assert 1/(1+GAMMA*nu) == S/(1+S)

    Cinit = covariance([F(1), F(0), F(1), F(0), F(1), F(0)])
    Csub = covariance([F(1), F(0), F(61, 2), F(0), F(2810), F(0)])
    growth = F(26, 25)
    sub_psd = psd_certificate(Csub)
    growth_psd = psd_certificate(sub(phi(Csub, True), scale(growth, Csub)))
    reachable_psd = psd_certificate(sub(phi(Cinit, True), scale(F(1, 4), Csub)))

    # Same kernel, blocks, parameters and initialization, changing ONLY λw to λy.
    Gfixed = moment_matrix(False)
    contraction = F(99, 100)
    exact_super = solve(sub(scale(contraction, eye(6)), Gfixed), [F(1), F(1), F(0), F(0), F(1), F(1)])
    # Small, explicitly printed rational witness; the following PSD tests, not rounding,
    # establish its validity. No floating-point arithmetic enters this script.
    super_x = [F(round(x*10**6), 10**6) for x in exact_super]
    Csuper = covariance(super_x)
    super_pd = psd_certificate(Csuper, strict=True)
    correction_psd = psd_certificate(sub(scale(contraction, Csuper), phi(Csuper, False)), strict=True)
    domination_psd = psd_certificate(sub(Csuper, Cinit), strict=True)

    # Right-hand side y=H u, solution u, zero native initialization.
    u = [[F(1)], [F(-1)], [F(0)]]
    rhs = mul(H, u)
    assert rhs == [[F(1, 6250)], [F(-1, 6250)], [F(0)]]
    # Averaging all six permutations of (-u,-u)(-u,-u)' equals Cinit.
    import itertools
    avg = zeros(6, 6)
    for perm in itertools.permutations(range(3)):
        v = [[-u[i][0]] for i in perm]*2
        avg = add(avg, scale(F(1, 6), mul(v, tr(v))))
    assert avg == Cinit
    assert H == add(scale(F(1, 6250), P), scale(F(300013, 100000), E))

    files = ['fast_krr/models/full_krr.py', 'fast_krr/opts/askotchv2.py',
             'fast_krr/opts/utils/bcd.py', 'fast_krr/opts/utils/general.py',
             'fast_krr/preconditioners/newton.py']
    hashes = {p: hashlib.sha256((OFFICIAL/p).read_bytes()).hexdigest() for p in files}
    theorem = HERE/'theorem.md'
    result = {
        'status': 'PASS', 'arithmetic': 'exact fractions only',
        'parameters': {'n': 3, 'block_size': 2, 'lambda': str(LAM), 'off_diagonal_RBF': str(COR),
                       'mu': str(LAM), 'nu': str(nu), 'beta': str(1-S), 'gamma': str(GAMMA), 'alpha': str(S/(1+S))},
        'stale_growth_factor': str(growth),
        'stale_subcovariance': sub_psd, 'stale_growth_residual': growth_psd,
        'reachable_after_one_step': reachable_psd,
        'corrected_contraction_factor': str(contraction),
        'corrected_supercovariance_coordinates': list(map(str, super_x)),
        'corrected_supercovariance': super_pd, 'corrected_contraction_residual': correction_psd,
        'corrected_initial_domination': domination_psd,
        'stale_reduced_moment_matrix': [[str(v) for v in row] for row in moment_matrix(True)],
        'corrected_reduced_moment_matrix': [[str(v) for v in row] for row in Gfixed],
        'official_source_hashes': hashes,
        'theorem_sha256': hashlib.sha256(theorem.read_bytes()).hexdigest() if theorem.exists() else None,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE/'exact_certificate.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ['status', 'stale_growth_factor', 'corrected_contraction_factor',
                                             'corrected_supercovariance_coordinates', 'theorem_sha256']}))


if __name__ == '__main__': main()
