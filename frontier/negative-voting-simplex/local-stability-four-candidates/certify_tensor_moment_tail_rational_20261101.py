#!/usr/bin/env python3
"""Exact rational final arithmetic for the analytic moment-series tail.
No floating-point assertion or quadrature enters these certificates.
"""
from fractions import Fraction as F
from math import factorial

# pi <22/7 <(16/9)^2 gives J0=(2/3)sqrt(pi)<32/27.
assert F(22,7) < F(16,9)**2
# e<11/4 gives exp(15/8)<e^2<8; hence C<3456.
assert F(11,4)**2 < 8
KMAX=204
J=[F(0)]*(KMAX+5)
J[0]=F(32,27)
J[1]=F(8,9)
for n in range(KMAX+3):
    J[n+2]=F(8,9)*(n+1)*J[n]
I=[J[k+1]+2*J[k+2]+J[k+3] for k in range(KMAX+1)]
def T(k):
    return F(3456)*F(3,4)**k*I[k]**2/factorial(k)
def ratio2(k):
    return F(4,9)*F((k+4)**2,(k+1)*(k+2))
def ratio1(k):
    return F(2,3)*F(k+4,k+1)
def tail(N):
    assert N>=3
    return T(N+1)/(1-ratio2(N+1))+T(N+2)/(1-ratio2(N+2))
assert ratio2(4)==F(128,135)<1
for k in range(KMAX-2):
    assert ratio2(k)-ratio2(k+1)==F(4,9)*F(5*k+23,(k+1)*(k+2)*(k+3))
    assert I[k+2] <= F(8,9)*(k+4)*I[k]
# The one-step statement is analytic Cauchy--Schwarz for the exact I_k;
# no assertion is needed for the rational envelope's altered base J0.
limits={60:F(8218,10**6),80:F(456,10**8),100:F(223,10**11),120:F(1005,10**15),140:F(428,10**18),160:F(174,10**21),200:F(263,10**28)}
for N,bound in limits.items():
    assert tail(N)<bound
    print(f'CERTIFIED: moment-series tail after degree {N} < {bound}')
total=sum((T(k) for k in range(81)),F(0))+tail(80)
assert total<F(1551114)
eps=F(1,10**8)
err=(2*eps+eps*eps)*F(1551114)
assert err<F(311,10000)
print('CERTIFIED: total absolute coefficient envelope < 1551114.')
print('CERTIFIED: relative moment error 1e-8 induces series error < 0.0311.')
print('Analytic hypotheses are proved in the companion TXT; this script checks exact final arithmetic.')
