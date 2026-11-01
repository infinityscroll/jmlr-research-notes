#!/usr/bin/env python3
"""Exact exponent bookkeeping; not a numerical or formal proof of inputs."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json


# Each entry is r**a * m**b * L**c. At r=m**(-7/8)*L**(-2),
# it becomes m**(b-7*a/8)*L**(c-2*a). Fixed multiplicative
# constants do not change the asymptotic limit recorded here.
terms = [
    ("trace_and_factorization_rL", F(1), F(0), F(1)),
    ("boundary_trace_at_r_over_t", F(2), F(0), F(2)),
    ("range_exponential", F(1), F(0), F(3, 2)),
    ("damping_q_eta_rank", F(2), F(1), F(2)),
    ("odd_square_absorption", F(2), F(0), F(8)),
    ("mass_offset", F(1), F(0), F(2)),
    ("mass_second_chaos", F(2), F(1), F(7)),
    ("mass_signed_tail", F(3), F(0), F(10)),
    ("remainder_second_chaos", F(1), F(1, 2), F(13)),
    ("remainder_signed_tail", F(2), F(1), F(11)),
    ("cap_ceiling_full_mass_box", F(1), F(3, 4), F(4)),
    ("cap_ceiling_odd_forcing", F(2), F(5, 4), F(4)),
    ("cap_ceiling_score_radius", F(1), F(1, 4), F(4)),
]


def rational(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


results = []
for name, a, b, c in terms:
    m_power = b - F(7, 8) * a
    l_power = c - 2 * a
    tends_to_zero = m_power < 0 or (m_power == 0 and l_power < 0)
    assert a > 0, "Each condition must be monotone in positive r."
    assert tends_to_zero, f"Endpoint condition does not vanish: {name}"
    results.append({
        "condition": name,
        "before": {"r": rational(a), "m": rational(b), "L": rational(c)},
        "after": {"m": rational(m_power), "L": rational(l_power)},
        "tends_to_zero": tends_to_zero,
    })

out = Path(__file__).resolve().with_name("extended_local_exponent_checks_20261101.json")
source = Path(__file__).resolve()
out.write_text(json.dumps({
    "method": "Exact rational exponent substitution; analytic lemmas are not machine-verified.",
    "endpoint": "r=m^(-7/8)*(1+log(m))^(-2)",
    "script_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "conditions": results,
}, indent=2) + "\n")
print(f"Verified {len(results)} endpoint monomials vanish; wrote {out.name}.")
