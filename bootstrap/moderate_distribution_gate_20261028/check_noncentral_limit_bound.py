"""Exact rational arithmetic for T7; no trajectories or normal integration."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'triangular_exponent_coverage_theorem.md'
EXPECTED='59ce6000f9c72fb8fc575c8d45c562ae4caf146b11353a8363d065a554aa8e9c'


def main():
    out=HERE/'noncentral_limit_bound_certificate.json'
    assert not out.exists()
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==EXPECTED
    # Machin's identity with alternating Taylor enclosures.
    pi_lower=16*sum((-1)**j*F(1,5)**(2*j+1)/F(2*j+1) for j in range(6))-4*F(1,239)
    assert pi_lower>F(157,50)
    sqrt3_upper=F(173206,100000)
    assert sqrt3_upper**2>3
    x=sqrt3_upper/F(16,5)
    atan_upper=sum((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(9))
    t3_tail_upper=2*(atan_upper-x/(1+x*x))/pi_lower
    assert 0<t3_tail_upper<F(1,20)
    # Beta(3/2,3/2) acceptance for qbar=16/5.
    threshold=F(256,331)
    beta_argument=2*threshold-1
    y=F(11,20)
    assert beta_argument==F(181,331) and 0<beta_argument<y
    assert 2*y*y<1
    assert F(21,25)**2>1-y*y
    asin_upper=y+y**3/6+3*y**5/40+y**7/(1-y*y)
    beta_cdf_upper=F(1,2)+(asin_upper+y*F(21,25))/F(157,50)
    assert beta_cdf_upper<F(21,25)
    # exp(-1/8)>1-1/8 and kappa=(47/25)exp(-1/8).
    kappa_lower=F(47,25)*F(7,8)
    assert kappa_lower==F(329,200) and kappa_lower>F(8,5)
    poisson_mean_lower=F(8,5)**2/2
    assert poisson_mean_lower==F(32,25)
    exp_lower=1+poisson_mean_lower+poisson_mean_lower**2/2+poisson_mean_lower**3/6
    assert exp_lower>F(10,3)
    probability_zero_upper=1/exp_lower
    assert probability_zero_upper<F(3,10)
    simple_bound=F(3,10)+F(7,10)*F(21,25)
    assert simple_bound==F(111,125)<F(19,20)
    sharper_rational_bound=probability_zero_upper+(1-probability_zero_upper)*beta_cdf_upper
    assert sharper_rational_bound<simple_bound
    result={'status':'PASS','source_sha256':EXPECTED,
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            't3_tail_at_16_over_5_upper':str(t3_tail_upper),
            'beta_cdf_at_256_over_331_upper':str(beta_cdf_upper),
            'poisson_zero_probability_upper':str(probability_zero_upper),
            'limiting_coverage_strict_upper':'111/125',
            'sharper_rational_upper':str(sharper_rational_bound),
            'display_only':{'t3_tail_upper':float(t3_tail_upper),
                            'beta_cdf_upper':float(beta_cdf_upper),
                            'sharper_limiting_upper':float(sharper_rational_bound)},
            'new_random_draws':0,'new_sgd_trajectories':0,
            'scope':'Arithmetic inequalities for the limiting noncentral law only; analytic theorem required, no finite-n coverage claim.'}
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
