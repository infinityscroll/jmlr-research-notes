"""Independent finite checks of critical harmonic averaging identities.

Exact Fraction recursion versus closed-form coefficients; floating asymptotic
diagnostics are explicitly not a proof of the limiting theorem.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math

root = Path(__file__).resolve().parent
checks = 0
for n in range(1, 81):
    current = [F(1)] + [F(0)] * n
    average = [F(0)] * (n + 1)
    products = [F(1)]
    for t in range(1, n + 1):
        current = [(1 - F(1, 2*t)) * x for x in current]
        current[t] += F(1, 2*t)
        average = [x + y / n for x, y in zip(average, current)]
        products.append(products[-1] * (1 - F(1, 2*t)))
    pn = products[n]
    an = F(2*n+1, 2*n) * pn
    closed = [((2*n+1)*pn - 1)/n]
    closed += [an/(t*products[t]) - F(1,n) for t in range(1,n+1)]
    assert average == closed
    checks += n + 1
    variance = sum(x*x for x in average[1:])
    formula = an*an*sum(1/(t*t*products[t]*products[t]) for t in range(1,n+1))
    formula -= 4*an/n * (1/pn-1)
    formula += F(1,n)
    assert variance == formula
    assert sum(products) == (2*n+1)*pn
    assert sum(1/(t*products[t]) for t in range(1,n+1)) == 2*(1/pn-1)
    checks += 3

diagnostics = []
pn, reciprocal_sum = 1.0, 0.0
for n in range(1, 1_000_001):
    pn *= 1 - 1/(2*n)
    reciprocal_sum += 1/(n*n*pn*pn)
    if n in (100, 1000, 10000, 100000, 1000000):
        an = (2*n+1)*pn/(2*n)
        variance = an*an*reciprocal_sum - 4*an/n*(1/pn-1) + 1/n
        qn = ((2*n+1)*pn-1)/n
        diagnostics.append({
            "n": n,
            "n_weight_variance_over_log_n": n*variance/math.log(n),
            "sqrt_n_q_n": math.sqrt(n)*qn,
            "maximum_normalized_weight_squared": n/math.log(n)*(2*an-1/n)**2,
        })
result = {
    "status": "PASS",
    "exact_rational_equalities_checked": checks,
    "source_sha256": hashlib.sha256((root/'critical_online_bootstrap_theorem.md').read_bytes()).hexdigest(),
    "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "diagnostics_not_a_convergence_certificate": diagnostics,
    "limits_of_check": "Checks exact averaging/variance weights, not martingale CLT, coverage, novelty, or the full proof.",
}
(root/'critical_weight_checks.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
