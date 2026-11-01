#!/usr/bin/env python3
"""Exact-rational certificate for 1/8 < p_i < 3/8.
No floating-point arithmetic, external packages, or convergence assumptions
are used in any asserted inequality. See COMMON_MASS_LOCALIZATION_20261101.txt.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from pathlib import Path

SCALE = 10**24
PANELS = 512

def atan_bounds(x, even_degree=30):
    assert even_degree % 2 == 0 and 0 < x < 1
    upper = sum(((-1)**k*x**(2*k+1)/Q(2*k+1)
                 for k in range(even_degree+1)), Q(0))
    lower = upper-x**(2*even_degree+3)/Q(2*even_degree+3)
    return lower, upper

def asin_third_bounds(last_degree=30):
    x=Q(1,3); term=x; lower=term
    for k in range(last_degree):
        term *= x*x*Q((2*k+1)**2, 2*(k+1)*(2*k+3))
        lower += term
    k=last_degree
    next_term=term*x*x*Q((2*k+1)**2, 2*(k+1)*(2*k+3))
    # Every subsequent ratio is < x^2=1/9.
    return lower, lower+Q(9,8)*next_term

def sqrt_lower(x):
    assert x>0
    a=isqrt((x.numerator*SCALE*SCALE)//x.denominator)
    lo=Q(a,SCALE)
    assert lo*lo<=x and (lo+Q(1,SCALE))**2>x
    return lo

def exp_minus_upper(x):
    # Taylor's integral remainder has negative sign after even degree 20.
    assert 0<=x<=2
    value=Q(1,factorial(20))
    for k in range(19,-1,-1):
        value=-x*value+Q(1,factorial(k))
    assert value>0
    return value

def ceil_scaled(x):
    n=x.numerator*SCALE
    return (n+x.denominator-1)//x.denominator

def integral_phi_upper(z, pi_lower):
    # Integral from 0 to z of exp(-t^2/2); the degree-16 alternating
    # integrated Taylor polynomial is an upper bound.
    integral=sum(((-1)**k*z**(2*k+1)/
                  Q((2*k+1)*2**k*factorial(k))
                  for k in range(17)),Q(0))
    return Q(1,2)+integral/sqrt_lower(2*pi_lower)

a_lo,a_hi=atan_bounds(Q(1,5))
b_lo,b_hi=atan_bounds(Q(1,239))
pi_lo=16*a_lo-4*b_hi
pi_hi=16*a_hi-4*b_lo
asin_lo,asin_hi=asin_third_bounds()
L_lo,L_hi=pi_lo/2+asin_lo,pi_hi/2+asin_hi
w_lo=3*L_lo**2/pi_hi**3
w_hi=3*L_hi**2/pi_lo**3
U_upper=Q(7,27)-Q(28,81)*w_lo+Q(8,81)/pi_lo**2
assert U_upper<Q(147171,10**6)

quantile_lower={
    Q(1,8):Q(1150349,10**6),
    Q(7,24):Q(548522,10**6),
    Q(3,8):Q(318639,10**6),
    Q(5,24):Q(812217,10**6),
}
rows=[]
j_lower={}
for p,z in quantile_lower.items():
    # Phi(z)<1-p proves z < -Phi^{-1}(p).
    phi_upper=integral_phi_upper(z,pi_lo)
    assert phi_upper<1-p
    total=0
    for k in range(PANELS):
        left=Q(k,3*PANELS)
        right=Q(k+1,3*PANELS)
        exponential=exp_minus_upper(z*z/(1-left))
        denominator=sqrt_lower(1-right*right)
        total += ceil_scaled(exponential/denominator)
    integral_upper=Q(total,SCALE*3*PANELS)
    j_lower[p]=p*p-integral_upper/(2*pi_lo)
    rows.append((p,z,1-p-phi_upper,j_lower[p]))

F_low=j_lower[Q(1,8)]+3*j_lower[Q(7,24)]
F_high=j_lower[Q(3,8)]+3*j_lower[Q(5,24)]
assert F_low>Q(147281,10**6)
assert F_high>Q(150071,10**6)
assert F_low-U_upper>Q(110,10**6)
assert F_high-U_upper>Q(2900,10**6)

def lower_decimal(x, digits=15):
    scale=10**digits
    n=(x.numerator*scale)//x.denominator
    return f"{n//scale}.{n%scale:0{digits}d}"

def upper_decimal(x, digits=15):
    scale=10**digits
    n=(x.numerator*scale+x.denominator-1)//x.denominator
    return f"{n//scale}.{n%scale:0{digits}d}"

out=[
 "EXACT RATIONAL CERTIFICATE: COMMON MASS BOX",
 f"Uniform Plackett-integral panels: {PANELS}",
 "Every assertion uses Python arbitrary-precision integers and Fraction.",
 "Pi: Machin formula with alternating arctangent remainders.",
 "Quantiles: one-sided integrated Gaussian Taylor bounds.",
 "Integral upper bounds: rectangle bounds and degree-20 exponential Taylor bounds.",
 "Square roots: exact integer-isqrt lower bounds, denominator 10^24.",
 f"w in [{lower_decimal(w_lo)}, {upper_decimal(w_hi)}]",
 f"Tetra Hermite upper U < {upper_decimal(U_upper)}",
]
for p,z,gap,j in rows:
    out.append(f"p={p}, z_lower={z}, certified (1-p)-Phi(z_lower) > {lower_decimal(gap)}; J(p) > {lower_decimal(j)}")
out += [
 f"F(1/8) > {lower_decimal(F_low)} > 147281/1000000",
 f"F(3/8) > {lower_decimal(F_high)} > 150071/1000000",
 "U < 147171/1000000",
 f"F(1/8)-U > {lower_decimal(F_low-U_upper)} > 110/1000000",
 f"F(3/8)-U > {lower_decimal(F_high-U_upper)} > 2900/1000000",
 "PASS: any matched-mass pair with agreement <= tetra agreement has 1/8 < p_i < 3/8.",
 "This certifies localization only, not tetrahedral optimality.",
]
text="\n".join(out)+"\n"
print(text,end="")
Path(__file__).with_name("COMMON_MASS_BOX_RATIONAL_CERTIFICATE_20261101.txt").write_text(text)

