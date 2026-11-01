#!/usr/bin/env python3
"""Exact arithmetic for the global normal-slab interaction remainder."""
from fractions import Fraction as F
from math import factorial

# sqrt(pi)<16/9 and sqrt(3/32)>3/10.
assert F(22, 7) < F(16, 9)**2
assert F(3, 32) > F(3, 10)**2
j0 = F(16, 3) + F(2560, 81) + F(512, 9)
j2 = F(512, 9) + F(40960, 81) + F(32768, 27)
assert j0 == F(7600, 81) < 128
assert j2 == F(143872, 81) < 2048
ehi = sum(F(1, factorial(j)) for j in range(7)) + F(8, 7*factorial(7))
assert ehi**6 < 404
bound = 432*404*(F(9, 8)*128*2048 + F(1, 2)*128**2)
assert bound == 52900134912 < 2**36
eps = F(1, 25*2**16)
assert F(4, 25)-2**17*eps == F(2, 25)
print('Squared remainder coefficient <', bound, '< 2^36')
print('Height threshold =', eps, '=', float(eps))
print('Remaining energy coefficient >= 2/25')
print('All exact rational assertions passed.')
