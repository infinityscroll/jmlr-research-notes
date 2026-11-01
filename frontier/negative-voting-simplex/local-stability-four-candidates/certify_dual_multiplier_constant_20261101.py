#!/usr/bin/env python3
"""Enclose the explicit constant in the proved near-minimizer dual bound."""
from flint import arb,ctx
ctx.prec=160
pi=arb.pi()
c=(-arb(9)/8).exp()/(64*(2*pi).sqrt())
C0=(arb(81)/80).sqrt().sqrt()**3*(arb(9)/80).exp()
K=2*(1/(8*pi*c).sqrt()+arb(2).sqrt()*C0)
assert K<13
print('c =',c)
print('dual coefficient K =',K)
print('PASS: ||lambda||_2 < 13 sqrt(epsilon) for 0<epsilon<c/8.')
print('The routing/prism argument is proved in the companion TXT note.')
