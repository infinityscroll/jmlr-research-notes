"""Display a rigorous upper bound from the analytic cap-free counterexample.

This is not a numerical validation of covariance concavity. The upper bound
follows exactly from Q=(m-1)^2(m-2)/(2m) and R<=alpha^2(m-1). Only logs are
evaluated numerically for display. No packages are required.
"""
from math import log
from fractions import Fraction

print("m, required_row_cap, diagonal_error_Q, upper_bound_on_any_uniform_c")
for m in (10, 100, 1000, 10000, 1000000, 1000000000):
    n = m - 1
    q_exact = Fraction(n * n * (m - 2), 2 * m)
    upper = 2 * m * (1 + log(m)) ** 2 / ((m - 1) * (m - 2))
    print(f"{m}, {Fraction(n, 2)}, {q_exact}, {upper:.12g}")
