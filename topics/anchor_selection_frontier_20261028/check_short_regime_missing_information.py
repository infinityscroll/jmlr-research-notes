"""Exact conditional-sign check of the all-N short-regime cross identity.

No simulation or numerical integration. Does not certify the analytic bounds.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "unknown_anchor_short_regime_all_N_lower.md"
EXPECTED = "3b7a7c77c4f46761fd8e1c5708fe9b1709bdebe579f2eccdd3ab27ef28a5c851"
OUT = HERE / "short_regime_missing_information_certificate.json"


def prod(xs):
    answer = F(1)
    for x in xs:
        answer *= x
    return answer


def check(groups, r, kappa):
    """j,k are candidate pairs; c is the common pair; 0 is a singleton."""
    active = [i for i, g in enumerate(groups) if g != "0"]
    fair_mass = F(1, 2 ** len(active))
    result = {name: F(0) for name in (
        "cross", "posterior_covariance", "rational_hyperbolic",
        "dj", "dk", "complete_plus", "complete_minus",
        "observed_j", "observed_k", "null_mass")}
    for bits in product((-1, 1), repeat=len(active)):
        eps = dict(zip(active, bits))
        contrasts = {i: (r / 2 if groups[i] == "c" else r) for i in active}
        plus = prod(1 + contrasts[i] * eps[i] for i in active)
        minus = prod(1 - contrasts[i] * eps[i] for i in active)
        f0 = (plus + minus) / 2
        assert f0 > 0
        ljp = prod(1 + kappa * r * eps[i] / (1 + r * eps[i])
                   for i in active if groups[i] == "j")
        ljm = prod(1 - kappa * r * eps[i] / (1 - r * eps[i])
                   for i in active if groups[i] == "j")
        lkp = prod(1 + kappa * r * eps[i] / (1 + r * eps[i])
                   for i in active if groups[i] == "k")
        lkm = prod(1 - kappa * r * eps[i] / (1 - r * eps[i])
                   for i in active if groups[i] == "k")
        dj, dk = ljp - ljm, lkp - lkm
        posterior = plus / (plus + minus)
        lj = posterior * ljp + (1 - posterior) * ljm
        lk = posterior * lkp + (1 - posterior) * lkm
        q_squared = prod(1 - contrasts[i] ** 2 for i in active)
        assert plus * minus == q_squared
        values = {
            "cross": f0 * lj * lk,
            "posterior_covariance": -f0 * posterior * (1 - posterior) * dj * dk,
            "rational_hyperbolic": -q_squared * dj * dk / (4 * f0),
            "dj": dj, "dk": dk,
            "complete_plus": plus * ljp * lkp,
            "complete_minus": minus * ljm * lkm,
            "observed_j": f0 * lj, "observed_k": f0 * lk,
            "null_mass": f0,
        }
        for name, value in values.items():
            result[name] += fair_mass * value
    result["cross"] -= 1
    assert result["cross"] == result["posterior_covariance"]
    assert result["cross"] == result["rational_hyperbolic"]
    assert result["dj"] == result["dk"] == 0
    for name in ("complete_plus", "complete_minus", "observed_j", "observed_k", "null_mass"):
        assert result[name] == 1
    return {"groups": "".join(groups), "r": str(r), "kappa": str(kappa),
            "fair_sign_patterns": 2 ** len(active),
            "observed_cross_minus_one": str(result["cross"]),
            "identities_passed": 8}


def main():
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED
    assert not OUT.exists(), "Preserve existing certificates; do not overwrite."
    fixtures = []
    for groups in ("jkc", "jjkc", "jjkkc", "jjkkcc", "jk0", "jjccc"):
        for r, kappa in ((F(1, 8), F(1, 16)), (F(1, 6), F(1, 8))):
            fixtures.append(check(groups, r, kappa))
    certificate = {
        "status": "PASS", "method": "exact Fraction enumeration, no random numbers",
        "source_sha256": EXPECTED,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixtures": fixtures,
        "total_fair_sign_patterns": sum(row["fair_sign_patterns"] for row in fixtures),
        "identity_assertions": sum(row["identities_passed"] for row in fixtures),
        "scope": "Conditional C5 identity, its 1/4 factor and sign, fair centering, and likelihood normalization only."
    }
    OUT.write_text(json.dumps(certificate, indent=2) + "\n")
    print(json.dumps({k: certificate[k] for k in ("status", "total_fair_sign_patterns", "identity_assertions")}))


if __name__ == "__main__":
    main()
