"""Exact arithmetic checks for the global good-transfer rotation envelope."""
from fractions import Fraction as F
from pathlib import Path
import json

checks = {
    "origin_gradient_square_below_one": F(9, 64)*F(32, 9) < 1,
    "extended_gradient_factor": F(9, 8) < 2,
    "extended_hessian_factor": F(1, 8)+4 < 5,
    "F_second_derivative_factor": F(9, 64)+F(1, 2)+5 < 6,
    "normal_first_derivative_factor": 1+F(17, 8) < 4,
    "normal_second_derivative_factor": F(17, 4)+6 < 11,
    "mixed_second_derivative_factor": 2+F(1, 4)+5 < 8,
    "gradient_norm_factor": 4**2+2*2**2 < 8**2,
    "hessian_operator_factor": 3*11 < 64,
    "rotation_derivative_factor": 8+64 < 128,
    "weighted_envelope_square": 216*32*(2+768) < 2**24,
    "final_good_gauge_factor": 128*2**12*2 == 2**20,
    "cross_remainder_factor": 2**18*4//2 == 2**19,
}
assert all(checks.values()), checks
result={
    "scope":"Exact constant bookkeeping only; the analytic inequalities are proved in the companion TXT source.",
    "weighted_envelope_square_upper":216*32*(2+768),
    "one_partition_good_gauge_coefficient":2**20,
    "pair_good_cross_remainder_coefficient":2**19,
    "checks":checks,
}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
