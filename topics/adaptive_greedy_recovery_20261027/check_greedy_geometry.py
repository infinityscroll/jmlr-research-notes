"""Bounded exact arithmetic checks; not a proof of concentration or expected risk."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import itertools
import json
import random

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "penalized_successive_projection_theorem.md"
BOUND = "93a8dcf921f94cc594ef08f01b7620ff8427be8c686fbc90704771165b36b7a7"
COUNTS = {}


def check(name, predicate):
    if not predicate:
        raise AssertionError(name)
    COUNTS[name] = COUNTS.get(name, 0) + 1


def dot(x, y):
    return sum((a*b for a, b in zip(x, y)), F(0))


def ident(k):
    return [[F(i == j) for j in range(k)] for i in range(k)]


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def inverse(a):
    n = len(a)
    aug = [list(row)+eye for row, eye in zip(a, ident(n))]
    for j in range(n):
        r = next((i for i in range(j, n) if aug[i][j]), None)
        if r is None:
            raise ValueError("singular")
        aug[j], aug[r] = aug[r], aug[j]
        pivot = aug[j][j]
        aug[j] = [x/pivot for x in aug[j]]
        for i in range(n):
            if i != j:
                factor = aug[i][j]
                aug[i] = [x-factor*y for x, y in zip(aug[i], aug[j])]
    return [row[n:] for row in aug]


def complement(rows, k):
    q = ident(k)
    if rows:
        proj = mm(mm(transpose(rows), inverse(mm(rows, transpose(rows)))), rows)
        q = [[x-y for x, y in zip(a, b)] for a, b in zip(q, proj)]
    return q


def projected(row, q):
    return [dot(row, col) for col in transpose(q)]


def norm2(row):
    return dot(row, row)


def psd_positive(a):
    """Exact LDL test for positive definiteness (stronger than required PSD)."""
    a = [row[:] for row in a]
    for j in range(len(a)):
        pivot = a[j][j]
        if pivot <= 0:
            return False
        for i in range(j+1, len(a)):
            for l in range(j+1, len(a)):
                a[i][l] -= a[i][j]*a[j][l]/pivot
    return True


def select(yhat, penalties, k):
    chosen = []
    residual = [row[:] for row in yhat]
    history = []
    for _ in range(k):
        q = complement([yhat[j] for j in chosen], k)
        dense = [projected(row, q) for row in yhat]
        check("rank_one_residual_equals_dense_projector", dense == residual)
        scores = [norm2(row)-4*p for row, p in zip(residual, penalties)]
        j = max((j for j in range(len(yhat)) if j not in chosen),
                key=lambda j: (scores[j], -j))
        direction = residual[j][:]
        d2 = norm2(direction)
        if not d2:
            raise ValueError("zero-residual fallback")
        history.append((j, q))
        chosen.append(j)
        residual = [[x-dot(row, direction)*u/d2 for x, u in zip(row, direction)]
                    for row in residual]
    return chosen, history


def constants(k, nu):
    c = 4/nu**2+F(1, 2)
    levels = [F(0)]
    for _ in range(k):
        levels.append((1+8*c/nu)*levels[-1]+6*c+1)
    eps0 = min(nu/(2*levels[-1]), nu**2/(8*(6+8*levels[-1]/nu)))
    return levels, eps0


def fixture(k, seed, mode):
    rng = random.Random(seed)
    nu = F(3, 4)
    v = [[nu*F(i == j)+(1-nu)/k for j in range(k)] for i in range(k)]
    levels, eps0 = constants(k, nu)
    delta = eps0/(100*k)
    b = ident(k)
    # Close nonanchors may beat penalized anchors; no anchor/nonanchor gap is assumed.
    for i in range(k):
        row = [F(0)]*k
        row[i] = 1-delta
        row[(i+1) % k] = delta
        b.append(row)
    b.extend(ident(k))  # Duplicate exact vertices with separate empirical errors.
    b.append([F(0)]*k)
    for _ in range(3*k):
        raw = [rng.randint(0, 9) for _ in range(k)]
        denom = 1+sum(raw)
        b.append([F(x, denom) for x in raw])
    b.extend([[F(1, k)]*k, [F(1, k)]*k])
    y = mm(b, v)
    yhat = [row[:] for row in y]
    penalties = [F(0)]*len(y)
    z = F(0)
    if mode in (1, 2):
        for j in range(k):
            target = [F(t == (j+1) % k) for t in range(k)]
            yhat[j] = [(1-delta)*x+delta*t for x, t in zip(y[j], target)]
            if mode == 1:
                penalties[j] = 2*delta
            else:
                z = 2*delta
        # Lower-penalty almost-pure rows must be allowed to win.
        for j in range(2*k, 3*k):
            penalties[j] = 3*delta
    # Grossly corrupted rare rows: their raw errors are not small.
    yhat[-2] = [F(t == 0) for t in range(k)]
    yhat[-1] = [F(0)]*k
    penalties[-2] = penalties[-1] = F(2)
    pt = sum(penalties[:k])
    epsilon = pt+z
    check("small_oracle_error_event", epsilon <= eps0)
    for truth, obs, pen in zip(y, yhat, penalties):
        check("subprobability_inputs", min(obs) >= 0 and sum(obs) <= 1)
        check("row_error_envelope", norm2([a-c for a, c in zip(obs, truth)]) <= (pen+z)**2)
    check("uniform_raw_noise_not_small", norm2([a-c for a, c in zip(yhat[-2], y[-2])]) > F(1, 8))
    chosen, history = select(yhat, penalties, k)
    matched = []
    for t, (j, qhat) in enumerate(history):
        q = complement([v[l] for l in matched], k)
        xs = {l: projected(v[l], q) for l in range(k) if l not in matched}
        m2 = max(map(norm2, xs.values()))
        check("remaining_vertex_norm", all(norm2(x) >= nu**2 for x in xs.values()))
        for x, xx in itertools.combinations(xs.values(), 2):
            check("remaining_pair_separation", norm2([a-c for a, c in zip(x, xx)]) >= 2*nu**2)
        h_upper = sum(abs(a-c) for qr, qhr in zip(q, qhat) for a, c in zip(qr, qhr))
        d = 6*pt+4*z+2*h_upper
        gap = m2-norm2(projected(y[j], q))
        check("selected_penalty_and_norm_deficit", gap+2*penalties[j] <= d)
        w = [1-sum(b[j][l] for l in xs)] + [b[j][l] for l in xs]
        atoms = [[F(0)]*k]+list(xs.values())
        identity = sum(ww*(m2-norm2(x)) for ww, x in zip(w, atoms))
        identity += sum(w[i]*w[l]*norm2([a-c for a, c in zip(atoms[i], atoms[l])])
                        for i in range(len(w)) for l in range(i+1, len(w)))
        check("zero_atom_variance_identity", gap == identity)
        dominant = max(range(k), key=lambda l: b[j][l])
        check("new_vertex_not_previously_matched", dominant not in matched)
        check("linear_barycentric_error", 1-b[j][dominant] <= 2*d/nu**2)
        if j < k:
            check("designated_anchor_matches_own_vertex", dominant == j)
        matched.append(dominant)
        e2 = sum(norm2([x-xx for x, xx in zip(yhat[s], v[l])])
                 for s, l in zip(chosen[:t+1], matched))
        check("full_inductive_vertex_bound", e2 <= (levels[t+1]*epsilon)**2)
        check("unused_designated_anchors_available",
              all(l not in chosen[:t+1] for l in range(k) if l not in matched))
    gram = mm([yhat[j] for j in chosen], transpose([yhat[j] for j in chosen]))
    shifted = [[x-F(i == j)*nu**2/4 for j, x in enumerate(row)] for i, row in enumerate(gram)]
    check("final_singular_guard_exact_LDL", psd_positive(shifted))
    check("all_vertices_once", sorted(matched) == list(range(k)))
    if mode == 0:
        # With no anchor error and a penalty covering raw contamination, recovery is exact.
        check("gross_errors_zero_oracle_exact_recovery", [yhat[j] for j in chosen] == [v[l] for l in matched])
    return int(any(j >= k and j < 2*k for j in chosen))


def main():
    check("source_sha256", hashlib.sha256(SOURCE.read_bytes()).hexdigest() == BOUND)
    almost_pure_selections = 0
    for k in range(2, 6):
        for seed in range(4):
            for mode in range(3):
                almost_pure_selections += fixture(k, seed, mode)
    # Negative control: unpenalized SPA selects a grossly wrong first vertex.
    v = [[F(7, 8), F(1, 8)], [F(1, 8), F(7, 8)]]
    yhat = v+[[F(1), F(0)]]
    unpen = max(range(3), key=lambda j: norm2(yhat[j]))
    check("negative_control_unpenalized_wrong_first_selection", unpen == 2)
    chosen, _ = select(yhat, [F(0), F(0), F(2)], 2)
    check("penalty_removes_gross_contamination", sorted(chosen) == [0, 1])
    check("almost_pure_nonanchor_recovery_exercised", almost_pure_selections > 0)
    result = {
        "status": "PASS", "source_sha256": BOUND,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixtures": 48, "K": [2, 3, 4, 5],
        "almost_pure_nonanchor_selected_fixtures": almost_pure_selections,
        "assertions": sum(COUNTS.values()), "counts": COUNTS,
        "scope": "Exact Fraction checks of finite geometry, scores, projection updates, matching, and inverse guards; arbitrary deterministic penalties and supplied error envelopes. No concentration, expected-risk, finite-sample performance, or numerical-stability validation."
    }
    (HERE/"greedy_geometry_certificate.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("status", "fixtures", "assertions", "almost_pure_nonanchor_selected_fixtures")}))


if __name__ == "__main__":
    main()
