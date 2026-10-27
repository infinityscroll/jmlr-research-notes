"""Independent rational checks of the COfB endpoint counterexample.

No dependency on the discovery implementation. This verifies finite identities;
the uniform-in-n coverage statement additionally uses the analytic inequalities
recorded in bootstrap/ (not an inference from this finite census).
"""

from fractions import Fraction as F
from itertools import product
import json
import math


def coefficients(n, a):
    current = [F(0)] * n
    initial = F(1)
    summed = [F(0)] * n
    q = F(0)
    for t in range(1, n + 1):
        step = a / t
        initial *= 1 - step
        current = [v * (1 - step) for v in current]
        current[t - 1] += step
        summed = [u + v for u, v in zip(summed, current)]
        q += initial
    return q / n, [v / n for v in summed]


def direct_asgd(data, initial=F(1), a=F(1, 4)):
    x, total = initial, F(0)
    for t, z in enumerate(data, 1):
        x -= a / t * (x - z)
        total += x
    return total / len(data)


def check_exhaustive():
    rows = []
    sigma = F(1, 100)
    for n in range(1, 5):
        q, weights = coefficients(n, F(1, 4))
        v, s = sum(w * w for w in weights), sum(weights)
        e2 = d2 = F(0)
        comparisons = 0
        for data in product([-sigma, sigma], repeat=n):
            original = direct_asgd(data)
            assert original == q + sum(w * z for w, z in zip(weights, data))
            e2 += (original - q) ** 2
            for idx in product(range(n), repeat=n):
                boot = direct_asgd([data[i] for i in idx])
                d2 += (boot - original) ** 2
                comparisons += 1
        e2 /= 2**n
        d2 /= comparisons
        expected_d2 = sigma**2 * (2*v - (v + s*s)/n)
        assert e2 == sigma**2 * v
        assert d2 == expected_d2
        assert d2 <= 2 * e2
        rows.append({"n": n, "resample_comparisons": comparisons,
                     "original_noise_variance": str(e2),
                     "bootstrap_difference_second_moment": str(d2)})
    return rows


def check_coefficient_bounds():
    a = F(1, 4)
    p = F(1)
    for n in range(1, 129):
        p *= 1 - a/n
        # Exact fourth-power form of p_n >= (3/4)n^(-1/4).
        assert p**4 * n >= (1-a)**4
        q, weights = coefficients(n, a)
        assert q + sum(weights) == 1
        assert sum((w/q)**2 for w in weights) < F(1, 3)
    for n in range(1, 129):
        q, weights = coefficients(n, F(1))
        harmonic = sum(F(1, j) for j in range(1, n+1))
        assert q == 0
        assert n * sum(w*w for w in weights) == 2 - harmonic/n
        assert n * sum((w-F(1,n))**2 for w in weights) == 1-harmonic/n


def main():
    census = check_exhaustive()
    check_coefficient_bounds()
    # For Student t_3: density <= 6 sqrt(3)/(pi x^4) for x>0.
    # Thus P(T_3>4) < 2 sqrt(3)/(pi*4^3) < 1/48 < 1/40.
    # Therefore its 97.5% quantile is <4, without numerical inversion.
    assert F(1,48) < F(1,40)
    # sqrt(2)<17/12, so uniform bound is strictly below 1/675.
    assert F(17,12)**2 > 2
    uniform_bound = F(1,100)**2 * (1+4*F(17,12))**2 / 3
    assert uniform_bound == F(1,675)
    cdf4 = .5 + (math.atan(4/math.sqrt(3)) + 4*math.sqrt(3)/19)/math.pi
    print(json.dumps({"status":"passed", "exact_census":census,
                      "coefficient_checks_through_n":128,
                      "all_n_rational_coverage_upper_bound":str(uniform_bound),
                      "upper_bound_percent":100*float(uniform_bound),
                      "t3_cdf_at_4_numeric_crosscheck":cdf4,
                      "scope":"Finite identity checks plus explicit analytic bound; not Lean formalization."},
                     indent=2))


if __name__ == "__main__":
    main()
