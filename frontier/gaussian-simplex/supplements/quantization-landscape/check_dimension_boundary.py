"""Exact rational certificate for the three-cell dimension-boundary example."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys

base = Path(__file__).resolve().parent
source = base / 'DIMENSION_BOUNDARY_AND_LLOYD_SEPARATION_20261031.txt'
source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
assert source_hash == 'ead4e863136e4a0b143ae6ad0fccc6e8ccee0ae74546c0daca66dfd8880af2aa'
checks = {
    'pi_upper': Q(52, 15) < Q(32, 9),
    'integral_lower_value': Q(3, 4) - Q(3, 4)**3 / 6 == Q(87, 128),
    'normal_quartile_test': Q(1, 2) + Q(3, 8) * Q(87, 128) > Q(3, 4),
    'exponential_bound_value': 1 + Q(9, 32) + (Q(9, 32)**2 / 2) / (1 - Q(9, 32) / 3) == Q(2459, 1856),
    'exponential_bound_upper': Q(2459, 1856) < Q(4, 3),
    'density_ratio_lower': Q(1856, 2459) > Q(3, 4),
    'density_gap_factor': 4 * Q(1856, 2459) - 3 == Q(47, 2459),
    'variance_gap_value': 2 * Q(9, 64) * Q(47, 2459) == Q(423, 78688),
    'variance_gap_positive': Q(423, 78688) > 0,
}
assert all(checks.values())
record = {
    'source_sha256': source_hash,
    'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'python': sys.version,
    'arithmetic': 'stdlib fractions.Fraction; exact rational operations',
    'checks': checks,
    'passed': sum(checks.values()),
    'total': len(checks),
}
(base / 'DIMENSION_BOUNDARY_RATIONAL_CHECK.json').write_text(json.dumps(record, indent=2) + '\n')
print(f"PASS {sum(checks.values())}/{len(checks)}")
