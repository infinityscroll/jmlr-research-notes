# Root review of the nonlinear SGD coverage boundary

28 October 2026. Bound source `triangular_exponent_coverage_theorem.md`, SHA256
`59ce6000f9c72fb8fc575c8d45c562ae4caf146b11353a8363d065a554aa8e9c`.
This records a full analytic reconstruction and subsequent inspection of the
independent hostile audit and primary comparison. No new SGD experiment was
run. The finite arithmetic certificate is distinct from the asymptotic proof.

**Verdict: no blocking error found in the stated triangular-array theorem.**

For g(x)=x+(1/4)log cosh(2x), the first update is exceptional but uniformly
bounded. From update two onward the sample map is increasing and contracts
centered errors by 1-gamma/2, uniformly over alpha in [1/2,3/5] and tilted
two-point means u in [-1,1]. The bounded invariant interval and the
recent/old-index decomposition give uniform convolution constants. Merely
quoting a fixed-alpha theorem would not have justified this step.

The moment recurrences imply E e_t^2=O(gamma_t) and E e_t^4=O(gamma_t^2),
including nonsymmetric tilted noise. Subtracting the local linear stationary
variance, not a global-curvature approximation, gives

    E e_t^2 = sigma_u^2 gamma_t/(2H) + O(gamma_t^(3/2)+1/t).

Replacing a single observation changes later errors by a contracting product.
Combining that pathwise bound with the moment bound gives an L2 change of
O(sqrt(gamma_i)) in the sum of squared errors. Efron-Stein therefore controls
its variance by O(sum gamma_i). This proves concentration of the leading
quadratic bias; it does not pretend the iterates are independent.

I checked the summation-by-parts signs, terminal term, and pre/post-update
averaging difference. The terminal and weighted terms, divided by sqrt(n),
are O(n^(-1/5)) uniformly over the compact exponent interval. Cubic Taylor
remainders and the quadratic fluctuation are smaller. The resulting scaled
bias coefficient is eta J sigma_u^2/[4H^2(1-alpha)] times n^(1/2-alpha).
At u=0 this gives the negative standardized shift (47/25) exp(-c).

The empirical distribution is exactly a member of the tilted two-point family,
with u equal to the original sample mean. Uniform expansion at that random u
is consequently legitimate on an event tending to probability one. The
optimization biases in original and resampled averages cancel upon subtraction,
while the original estimator itself retains its bias. Conditional bounded-noise
CLTs give the B independent Gaussian rerun coordinates. The original-data
remainder is measurable given the data and o_P(1); it need not have conditional
mean zero. Conditional characteristic functions converging to a deterministic
limit justify independence from the original limiting Gaussian coordinate.

The noncentral-Student conclusion then follows by continuous mapping. The
denominator has no atom at zero. Conditioning on the independent radius shows
strict undercoverage at every nonzero shift. I also reconstructed the exact
conservative arithmetic: t_(3,.975)<16/5, kappa>8/5, the positive-Poisson-index
beta acceptance is <21/25, and its zero-index mass is <3/10. Hence limiting
coverage is strictly below 111/125=.888 in the displayed c=1/8 sequence.

This is a failure of uniform calibration as the tuning exponent approaches
one half. It is not a counterexample to the target paper's theorem with a
fixed interior exponent. The uniform remainder has no supplied usable finite
constant, so this argument does not certify the earlier empirical 79.1%
coverage at n=10^6. General nonlinear-SA bias and centered-bootstrap bias
mismatch are established prior work. The bounded primary comparison identifies
that overlap rather than claiming the mechanism as a discovery. The possible
contribution is the explicit original-procedure boundary and its uniform
nonlinear/conditional proof, with historical priority unresolved.
