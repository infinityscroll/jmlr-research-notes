#!/usr/bin/env python3
"""Independent exact-rational checks for the facet quadrature audit.

All assertions use fractions.Fraction. Decimal displays are diagnostic only.
This script does not change the source certificate or its output files.
"""
from fractions import Fraction as F
from math import factorial


def bracket(a, rhi, rlo):
    return (rhi + 1)**2/(2*a) + 1/(2*a*a) + 1/(2*a*a*rlo)


a = F(3, 16)
B9 = bracket(a, F(891, 70), F(63, 5))
H9 = 2*432*F(121, 18)*28*B9*F(60, 163)**30*F(8, 11)
assert B9 == F(51393334, 99225)
assert H9 < F(6, 10**6)

B14 = bracket(a, F(14), F(14))
H14 = 2*432*F(121, 18)*28*B14*F(60, 163)**36*F(4, 7)
assert H14 < F(1, 10**7)

# d < 1/2, L < 4, (2*pi)^(3/2) > 1, e > 8/3.
U14 = 2*F(3, 8)**98
assert U14 < F(1, 10**40)

# One-facet inverse-diagonal tail constant 3 sigma^3 exp(15/16) < 33/4.
BV14 = bracket(F(7, 16), F(14), F(14))
V14 = F(33, 4)*BV14*F(3, 8)**85*F(4, 7)
assert V14 < F(1, 10**30)

# e upper bound by summing through degree 6 and bounding the rest geometrically.
ehi = sum(F(1, factorial(j)) for j in range(7)) + F(8, 7*factorial(7))
assert ehi < F(87, 32)
eta = ehi**6 * F(3**19, factorial(19))
assert eta < F(1, 10**5)
assert ehi**6/(1-eta) < 404

# Conservative normalized binary64 arithmetic envelope. Input-argument errors
# <1e-11 are treated separately from operation rounding.
unit = F(1, 2**53)
gamma = 2_000_000*unit/(1-2_000_000*unit)
floating = 404*gamma + F(1000, 10**11) + F(1, 10**10)
assert floating < F(1, 10**6)

# Even allowing flush-to-zero, later positive amplification, and >10^10 ops.
underflow = F(2)**(-1022 + 300 + 34)
assert underflow < F(2)**-600

# Consequences once the Arb comparison verifies H<30+3/8 and delta<11/400.
assert 3*389**2 < 8*239**2
assert F(3, 8) < F(5, 8)**2
assert F(389, 400)*F(239, 389)+F(33, 400) == F(17, 25)
assert 1-F(17, 25) == F(8, 25)

for name, value in [('HS_tail_R_9sqrt2', H9), ('HS_tail_R14', H14),
                    ('a0_tail_R14', U14), ('b0_tail_R14', V14),
                    ('Taylor18_eta', eta), ('floating_relative', floating)]:
    print(name, float(value))
print('All exact rational assertions passed.')
