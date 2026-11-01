#!/usr/bin/env python3
"""Exact final arithmetic for the accompanying analytic operator-tail lemma."""
from fractions import Fraction as F

# e>8/3 follows from its positive series after degree3.
# e<11/4 follows from sum through degree4 plus geometric domination of its tail.
assert F(65, 24) + F(1, 100) < F(11, 4)
assert F(11, 4)**2 < 8
# pi<22/7 implies sqrt(pi/3)<25/24, hence I_0<28.
assert F(22, 21) < F(25, 24)**2
assert F(8, 3) + F(128, 9) + F(32, 3)*F(25, 24) == 28

radius = 16
def tail_bracket(a):
    return F((radius+1)**2, 1)/(2*a)+1/(2*a*a)+1/(2*a*a*radius)
assert tail_bracket(F(3, 16)) == F(7072, 9)
assert tail_bracket(F(7, 16)) == F(16320, 49)
hs_squared = F(2*432*8*28)*F(7072, 9)*F(3, 8)**48
mass_squared = F(108)*F(16320, 49)*F(3, 8)**112
assert hs_squared < F(1, 10**12)
assert mass_squared < F(1, 10**42)
print('PASS: squared Hilbert--Schmidt tail at radius16 < 10^-12.')
print('PASS: summed squared mass-representer tail at radius16 < 10^-42.')
print('These exact checks certify final arithmetic, conditional on the analytic lemma.')
