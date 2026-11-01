#!/usr/bin/env python3
"""Outward interval checks for explicit finite-normal-graph basin examples."""
from flint import arb,ctx
from pathlib import Path
import json
ctx.prec=128
L=(-arb(1)/3).acos();pi=arb.pi()
d0=L/(2*pi**arb('1.5'))
kappa=(2*pi/3).sqrt()/(4*L)
C3=arb(3).sqrt()/16
R=arb(3);clearance=arb(1)/10
dmin=d0*(-kappa*R-R*R/16).exp()
rotation_tail=d0*pi.sqrt()*R**3*(-9*(R+1)**2/16-kappa*(R+1)).exp()
cases=[]
for label,c,eps in [('compact_no_rotation_gauge',3*rotation_tail/16,arb(2)/10**6),
                    ('exact_common_rotation_gauge',arb(4)/25,arb(1)/250)]:
    eta=3*R*eps/4+eps*eps/2
    routing=arb(0)  # Exact all-height routing lower bound; no adverse remainder.
    cross=(arb(243)/8).sqrt()*(eta.exp()-1)/2
    tests={
        'clearance':bool(eps<=clearance/3),
        'height_le_one':bool(eps<=1),
        'linear_remainder_condition':bool(eps<=c/(9*(R+1))),
        'direct_remainder_below_half_gap':bool(routing+cross<c/2)}
    assert all(tests.values()),tests
    cases.append({'case':label,'height':eps.str(30),'leading_gap_c':c.str(30),
                  'routing_error_coefficient':routing.str(30),
                  'cross_error_coefficient':cross.str(30),
                  'certified_finite_gap_coefficient':(c/2).str(30),'checks':tests})
out={'R':3,'normalized_other_label_clearance':'1/10','d0':d0.str(30),
     'kappa':kappa.str(30),'d_min_on_radius_R':dmin.str(30),
     'rotation_tail_fraction_lower':rotation_tail.str(30),'cases':cases,
     'scope':'Finite disjoint normal-graph slabs only; not a global partition theorem.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
