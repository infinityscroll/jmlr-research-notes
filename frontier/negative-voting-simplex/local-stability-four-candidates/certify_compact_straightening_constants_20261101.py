#!/usr/bin/env python3
"""Arb check of explicit constants in the compact straightening lemma.
This verifies a stated sufficient epsilon, not existence of a minimizer.
"""
from flint import arb, ctx

ctx.prec=160
R=arb(2)
margin=arb(1)/2
epsilon=arb('1e-30')
pi=arb.pi()
c=(-arb(9)/8).exp()/(64*(2*pi).sqrt())

def C(radius):
    return (arb(81)/80).sqrt().sqrt()**3*(radius*radius/20).exp()

B1=(R*R/100+arb(9)/80).sqrt()
B2=(R/10+arb(3).sqrt().sqrt()*3/arb(80).sqrt())**2+arb(1)/8
mean_bound=(arb(3)/32).sqrt()*R
omega=(-(1+mean_bound)**2-(2+mean_bound)**2).exp()/(2*pi*pi)
ell=arb(2).sqrt()*omega
Delta=epsilon/(c*pi.sqrt())+C(arb(3)/2)*(2*epsilon).sqrt()
eta0=C(R)*epsilon.sqrt()+2*Delta
eta1=C(R)*B1*epsilon.sqrt()
displacement=eta0/ell
derivative=2/ell*(eta1+C(R)*B2*displacement)

assert epsilon<c/8
assert eta1<ell/2
assert eta0<ell*margin/2
assert displacement<arb('1e-8')
assert derivative<arb('1e-3')

print('COMPACT STRAIGHTENING CONSTANT CERTIFICATE')
print('R=2; margin=1/2; epsilon<=10^-30; covered physical ball B_1.')
for name,value in [('prism_constant_lower',c.lower()),
                   ('reference_derivative_lower',ell.lower()),
                   ('potential_error_upper',eta0.upper()),
                   ('derivative_error_upper',eta1.upper()),
                   ('displacement_upper',displacement.upper()),
                   ('diffeomorphism_derivative_error_upper',derivative.upper())]:
    print(name,value)
print('PASS: displacement<10^-8 and ||D Psi-I||<10^-3.')
print('This is a compact minimizer-regularity lemma, not a global-isolation certificate.')
