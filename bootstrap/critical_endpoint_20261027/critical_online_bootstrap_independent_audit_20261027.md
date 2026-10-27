# Independent mathematical audit: critical harmonic online bootstrap

27 October 2026. Auditor: `hcm_adversarial_boundary`. Bound source: `critical_online_bootstrap_theorem.md`, SHA256 `b61ce8aec7b3dd187021c1788f74c21746a2e6cd4c0417dc145e34948d878e0d`.

**Verdict: no blocking mathematical gap found under the stated scalar quadratic, iid finite-fourth-moment, independent Exp(1)-multiplier assumptions and fixed finite B.** This is a source-level probability proof audit, not formal verification, a finite-sample coverage guarantee, a conditional-bootstrap consistency theorem, or novelty clearance. The audited source is unchanged.

## 1. Random coefficients are retained exactly

Subtracting the original recursion from a bootstrap recursion gives

\[
D_t^b=(1-1/(2t))D_{t-1}^b
+(W_t^b-1)(Z_t-X_{t-1}^b)/(2t).
\]

The common deterministic drift is legitimate: the remaining random coefficient is inside the martingale innovation. It has not been dropped. Conditional on the past, `W_t^b` is independent of current `Z_t` and of the other bootstrap weights. Its centered first moment is zero and variance is one. Consequently the conditional innovation covariance is exactly diagonal, with first entry `sigma^2` and entry `b` equal to `sigma^2+(X_(t-1)^b)^2`. In particular the covariance between coordinate zero and coordinate b vanishes because `E(W-1)=0`, even though they share `Z_t`. For distinct b,c the product of centered multiplier means is zero.

## 2. Exact deterministic weights and the logarithmic variance

The central-binomial recursion gives

\[
\sum_{j=t}^n p_j=(2n+1)p_n-2t p_t.
\]

Dividing by `2nt p_t` yields exactly the displayed weight `A_n/(t p_t)-1/n`. Positivity follows from its original sum representation. The inverse-product identity telescopes to `sum 1/(t p_t)=2(1/p_n-1)`, so the three-term square-weight formula is exact, including the factor four in its cross term.

Stirling expansion gives `1/(t^2 p_t^2)=pi/t+O(t^-2)` and `A_n^2=(pi n)^-1(1+O(n^-1))`. The cross term and final `1/n` term are both `O(1/n)`. Thus `sum w^2=(log n+O(1))/n`, with leading constant one. The uniform bound `w<=C/sqrt(nt)` and the initialization estimate follow directly. After multiplication by `sqrt(n/log n)`, the initialization tends to zero for every fixed deterministic `x0`; it need not be uniformly small over varying initializations.

## 3. Moment estimates close without symmetry of the noise

The exact second-moment recurrence is correct. For `t>=2`, multiplying it by t makes the coefficient on `(t-1)u_(t-1)` exactly

\[
1+\frac1{2t(t-1)}.
\]

These products are bounded and the forcing is `sigma^2/(2t)`, proving `u_t=O(log(et)/t)`.

For the fourth moment, with `A=1-W/(2t)` and `C=W/(2t)`, the coefficient `E A^4` is the one printed in the source. The `X^3 Z` term vanishes because `E Z=0`; this does not require a symmetric noise law. The `X^2 Z^2` term has coefficient `O(t^-2)`. The `X Z^3` term has coefficient `O(t^-3)` and is controlled by the bounded first absolute moment of the iterate and the finite third noise moment implied by the fourth-moment assumption. The `Z^4` term is `O(t^-4)`. For sufficiently large t, `E A^4<=1-1/t`, proving the claimed uniform fourth moment. Independent Exp(1) weights have all needed moments, hence the vector innovations have uniformly bounded fourth moments for fixed B.

## 4. Conditional variance, Lindeberg, and the Student ratio

For any fixed projection vector, the additional conditional variance has expected value bounded by

\[
\frac C{\log n}
\left[x_0^2+\sum_{t=2}^\infty\frac{\log(et)}{t^2}\right],
\]

and therefore vanishes in probability. The deterministic variance part converges to `sigma^2 ||z||^2`. The fourth-moment bound and `max a_(n,t)^2 ->0` make the expected conditional Lindeberg sum vanish. These are the required martingale triangular-array CLT conditions. Cramer–Wold gives the asserted joint normal limit with diagonal covariance, not merely separate marginal limits.

The common limiting variance cancels from the original divisor-B standard error. The joint Gaussian coordinates are independent, so their ratio is exactly Student `t_B`. The scaled denominator has a positive limit almost surely. In particular the probability of a zero finite-n denominator tends to zero, so assigning an arbitrary value to the ratio on that event does not change its limit. Continuity at the Student cutoff establishes the stated unconditional interval coverage.

## 5. Precise scope

The proof establishes a positive endpoint repair at harmonic coefficient exactly one half for the unit-Hessian scalar quadratic. It does not repair every harmonic coefficient, give a uniform Berry–Esseen bound, prove a multivariate or nonlinear result, or imply that an arbitrary fixed initialization has good moderate-n coverage. It proves the joint unconditional limit needed for confidence coverage; a stronger conditional law of the bootstrap given observed data is not asserted. The new normalization and the underlying martingale tools have classical antecedents, and the historical novelty of this exact finite-rerun endpoint statement remains a separate question.
