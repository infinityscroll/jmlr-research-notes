"""Independent dense rational operator and saved-certificate verification.

Small instances enumerate every sampled block and invert the dense block
matrix by Gauss-Jordan. The producer's row reduction is used only as the
comparison target. Large-instance checks evaluate the saved Bernstein data;
they do not invoke its interpolation or coefficient-generation routines.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
START = time.monotonic()
checks = 0


def check(x):
    global checks
    checks += 1
    assert x
    if time.monotonic() - START > 90:
        raise TimeoutError("Independent bounded check exceeded 90 seconds")


def zeros(n, m=None):
    return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(x) for x in zip(*a)]


def mm(a, b):
    bt = transpose(b)
    return [[sum((x*y for x, y in zip(row, col)), F(0)) for col in bt] for row in a]


def inverse(a):
    n = len(a)
    rows = [a[i][:] + eye(n)[i] for i in range(n)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        den = rows[j][j]
        rows[j] = [x/den for x in rows[j]]
        for i in range(n):
            if i != j:
                fac = rows[i][j]
                rows[i] = [x-fac*y for x, y in zip(rows[i], rows[j])]
    result = [x[n:] for x in rows]
    check(mm(a, result) == eye(n))
    return result


def covariance(n, c):
    out = zeros(2*n)
    for bi, bj, ia, ib in [(0, 0, 0, 1), (0, 1, 2, 3),
                            (1, 0, 2, 3), (1, 1, 4, 5)]:
        for i in range(n):
            for j in range(n):
                out[bi*n+i][bj*n+j] = c[ia]*F(i == j) + (c[ib]-c[ia])/n
    return out


def dense_state_matrix(n, block, s, delta, eta, stale):
    b = len(block)
    lam, gamma = F(n, b)*s*s, 1/(F(n, b)*s)
    K = [[delta*F(i == j) + 1-delta for j in range(n)] for i in range(n)]
    KB = [[K[i][j] + (lam+delta)*F(i == j) for j in block] for i in block]
    inv = inverse(KB)
    pre = zeros(n)
    for i, ii in enumerate(block):
        for j, jj in enumerate(block):
            pre[ii][jj] = inv[i][j]
    # Build the gradient map as n-by-2n directly from the native equations.
    G = zeros(n, 2*n)
    for i in range(n):
        for j in range(n):
            G[i][j] = K[i][j]/(1+s) + (lam if stale else lam/(1+s))*F(i == j)
            G[i][n+j] = K[i][j]*s/(1+s) + (F(0) if stale else lam*s/(1+s))*F(i == j)
    PG = mm(pre, G)
    M = zeros(2*n)
    for i in range(n):
        for j in range(2*n):
            y = (F(i == j) + s*F(n+i == j))/(1+s)
            M[i][j] = y-eta*PG[i][j]
            M[n+i][j] = (1-s)*F(n+i == j)+s*y-gamma*eta*PG[i][j]
    return M


def main():
    source = HERE / "theorem.md"
    check(hashlib.sha256(source.read_bytes()).hexdigest() ==
          "1b1cb234971e70130c0072aacac7988c2112ae04ddcd68703847f088f952e57b")
    spec = importlib.util.spec_from_file_location("producer_general_block_operator", HERE / "general_block_operator.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    dense_records = []
    # Include b=n-1, where the two-unselected-row term has zero weight.
    fixtures = [(4, 3, F(1, 7), F(1, 11), F(4, 3)),
                (5, 3, F(1, 9), F(1, 4), F(7, 6)),
                (6, 4, F(1, 13), F(1, 17), F(5, 4)),
                (5, 4, F(1, 8), F(2, 13), F(9, 8))]
    for n, b, s, delta, eta in fixtures:
        blocks = list(combinations(range(n), b))
        for stale in (False, True):
            maps = [dense_state_matrix(n, block, s, delta, eta, stale) for block in blocks]
            for j in range(6):
                coords = [F(i == j) for i in range(6)]
                C = covariance(n, coords)
                out = zeros(2*n)
                for M in maps:
                    MCMT = mm(mm(M, C), transpose(M))
                    for i in range(2*n):
                        for k in range(2*n):
                            out[i][k] += MCMT[i][k]/len(blocks)
                predicted = covariance(n, module.image(n, b, s, delta, eta, stale, coords))
                check(out == predicted)
            dense_records.append({"n": n, "b": b, "stale": stale,
                                  "all_blocks": len(blocks), "covariance_basis_vectors": 6})

    # Exact deterministic-initialization permutation identity, without random labels.
    n = 4
    u = [F(1), F(2), F(-4), F(1)]
    norm2 = sum(x*x for x in u)
    avg = zeros(2*n)
    perms = list(permutations(range(n)))
    for p in perms:
        z = [-u[i] for i in p] * 2
        for i in range(2*n):
            for j in range(2*n):
                avg[i][j] += z[i]*z[j]/len(perms)
    check(avg == covariance(n, [norm2/(n-1), F(0), norm2/(n-1), F(0), norm2/(n-1), F(0)]))

    cert = json.loads((HERE / "rank100_mean_step_certificate.json").read_text())
    for name, pin in cert["source_hashes"].items():
        check(hashlib.sha256((HERE/name).read_bytes()).hexdigest() == pin)
    n, b, s, lam = 10000, 100, F(1, 100000), F(1, 100000000)
    left, right = F(1, 20000000000), F(1, 5000000000)
    check(F(52, 51)**20 < F(3, 2))
    power_records = 0
    for delta in (left, (left+right)/2, right):
        a = (lam+delta)/(lam+2*delta)
        h = (b+lam-(b-1)*delta)/(b+lam-(b-2)*delta)
        check(0 < a < h < 1)
        check(h/a <= F(52, 51))
        R = (h/a)**18
        check(R < F(3, 2))
        for z in (F(0), F(1, 100), F(1, 2), F(1)):
            # Unnormalized power components avoid square roots and replicate 9 powers.
            eig_mass_low = (1-z)*a**18
            eig_mass_high = z*h**18
            quotient = (a*eig_mass_low+h*eig_mass_high)/(eig_mass_low+eig_mass_high)
            W = R*z/(1+(R-1)*z)
            check(quotient == a+(h-a)*W)
            check(W <= F(3, 2)*z)
            power_records += 1

    witness = [F(1), F(0), F(499), F(0), F(500800), F(0)]
    initial = [F(1), F(0), F(1), F(0), F(1), F(0)]
    bernstein_matrices = 0
    interpolation_values = 0
    for record in cert["checks"]:
        stale = record["update"] == "stale"
        C = witness if record["claim"] == "growth" else initial
        scale = F(1000001, 1000000) if record["claim"] == "growth" else F(1, 1000)
        coefficients = {}
        for entry in record["coefficients"]:
            coords = list(map(F, entry["coordinates"]))
            a0, b0, c0, d0, e0, f0 = coords
            check(a0 > 0 and a0*e0-c0*c0 > 0)
            check(b0 >= 0 and f0 >= 0 and b0*f0-d0*d0 >= 0)
            check(d0 == 1000*b0 and f0 == 1000000*b0)
            key = (entry["delta_index"], entry["mean_eta_index"])
            check(key not in coefficients)
            coefficients[key] = coords
            bernstein_matrices += 1
        check(set(coefficients) == {(i, j) for i in range(9) for j in range(3)})
        # A full unisolvent tensor grid, plus off-grid points. Degree bound is
        # audited analytically; equality here uniquely determines the polynomial.
        points = [(F(i, 8), F(j, 2)) for i in range(9) for j in range(3)]
        points += [(F(2, 7), F(3, 11)), (F(5, 13), F(4, 9))]
        for x, v in points:
            delta = left+(right-left)*x
            lo = (lam+2*delta)/(lam+F(203, 200)*delta)
            hi = (lam+2*delta)/(lam+delta)
            eta = lo+(hi-lo)*v
            D = (lam+2*delta)*(b+lam-(b-2)*delta)*(lam+F(203, 200)*delta)*(lam+delta)
            actual = [D*D*(a0-scale*w) for a0, w in zip(module.image(n, b, s, delta, eta, stale, C), witness)]
            expected = [F(0)]*6
            for (i, j), row in coefficients.items():
                weight = F(comb(8, i)*comb(2, j))*x**i*(1-x)**(8-i)*v**j*(1-v)**(2-j)
                for k in range(6):
                    expected[k] += weight*row[k]
            check(actual == expected)
            interpolation_values += 1

    result = {"status": "PASS", "arithmetic": "Python Fraction only",
              "assertions": checks, "dense_fixtures": dense_records,
              "dense_covariance_images": 6*len(dense_records),
              "native_power_formula_cases": power_records,
              "saved_Bernstein_PSD_matrices": bernstein_matrices,
              "tensor_polynomial_equalities": interpolation_values,
              "elapsed_seconds": time.monotonic()-START,
              "source_hashes": {str(path.relative_to(HERE)): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in [source, HERE/"general_block_operator.py", HERE/"check_rank100_mean_step.py",
                                             HERE/"rank100_mean_step_certificate.json", Path(__file__)]},
              "scope": "Independent dense rational operator and polynomial certificate verification; no native rank100 float64 execution or finite-precision instability claim."}
    (HERE/"independent_dense_certificate.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ["status", "assertions", "dense_covariance_images",
                                           "saved_Bernstein_PSD_matrices", "tensor_polynomial_equalities",
                                           "elapsed_seconds"]}))


if __name__ == "__main__":
    main()
