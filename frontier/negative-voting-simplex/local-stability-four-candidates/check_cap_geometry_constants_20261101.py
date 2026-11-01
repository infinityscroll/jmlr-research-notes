"""Exact small geometric/kernel inequalities; not a global-C certificate."""
from fractions import Fraction as F
import json
from pathlib import Path

A = 4096
eta = F(1, 2**20)
checks = {
    "triple_projection_absorption": 4*eta < F(1, 2),
    "negative_ray_vertex_absorption": 12*eta < F(1, 2),
    "s_below_half_radius_contradiction": F(4, A)+4*eta < F(4, 5),
    "sqrt3_over2_above_4_over5": F(3, 4) > F(16, 25),
    "narrow_tube_ratio": F(8, A)+8*eta < F(1, 100),
    "sqrt_two_thirds_above_13_over16": F(2, 3) > F(169, 256),
    "inverse_sqrt3_below_three_fifths": F(1, 3) < F(9, 25),
    "fourth_gap_above_four_fifths": F(13, 16)-F(3, 5)*F(1, 100) > F(4, 5),
    "fourth_height_below_hundredth": F(2, A)+4*eta < F(1, 100),
    "all_facet_shifted_kernel_norm_below_2pow18": 3*432*404*128**2 < 2**36,
}
assert all(checks.values()), checks
result = {
    "scope": "Exact inequalities used in the cap cover and positive-kernel bound. Does not collect the universal nonlinear constant C.",
    "A": A,
    "eta_upper": str(eta),
    "all_facet_shifted_kernel_HS_square_upper": 3*432*404*128**2,
    "checks": checks,
}
Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
