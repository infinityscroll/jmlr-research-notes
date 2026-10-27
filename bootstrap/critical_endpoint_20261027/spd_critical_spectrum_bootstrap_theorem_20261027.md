# A critical-spectrum repair for the cheap online bootstrap on SPD quadratics

27 October 2026. **New theorem candidate; independent audit pending.** This is a positive finite-rerun validity result for exact symmetric positive definite quadratic losses. The critical stochastic-approximation scaling and martingale tools are classical; no historical novelty or nonlinear extension is asserted.

## 1. Procedure, assumptions, and statement

Let `H` be a fixed symmetric positive definite `d x d` matrix and let `Z_t` be iid vectors with mean zero, positive definite covariance `Sigma`, and `E||Z_t||^4<infinity`. For fixed deterministic `x0`, minimize

\[
f(x,Z)=\tfrac12(x-Z)^TH(x-Z)
\]

using the harmonic step `eta/t`, where `eta>0`. The original and B online-bootstrap recursions are exactly

\[
X_t=(I-A/t)X_{t-1}+AZ_t/t,
\]
\[
X_t^b=(I-W_t^b A/t)X_{t-1}^b+W_t^b AZ_t/t,
\quad A=\eta H,\quad X_0^b=X_0=x_0.
\tag{S1}
\]

For each run and time there is **one scalar** `W_t^b~Exp(1)` multiplying the entire stochastic gradient. These variables are mutually independent and independent of the data. Fix finite `d` and `B>=1`. Average iterates `1,...,n`, and write `bar D_n^b=bar X_n^b-bar X_n`.

Choose an orthogonal eigenbasis `U` with `U^T A U=diag(a_1,...,a_d)`. Assume

\[
a_j\ge\tfrac12\quad\hbox{for every }j.
\tag{S2}
\]

Let `C={j:a_j=1/2}` and `R={j:a_j>1/2}`, and put `tilde Sigma=U^T Sigma U`. Define the diagonal normalization `T_n` to have entry `sqrt(n/log n)` on C and `sqrt n` on R, for `n>=2`.

**Theorem.** The joint vector

\[
\left(T_nU^T\bar X_n,
T_nU^T\bar D_n^1,\ldots,T_nU^T\bar D_n^B\right)
\ \Rightarrow\ N(0,I_{B+1}\otimes\Gamma),
\tag{S3}
\]

where

\[
\Gamma_{CC}=\widetilde\Sigma_{CC},\qquad
\Gamma_{CR}=\Gamma_{RC}=0,
\]
\[
\Gamma_{ij}=\frac{a_i+a_j}{a_i+a_j-1}\widetilde\Sigma_{ij},
\qquad i,j\in R.
\tag{S4}
\]

The matrix Gamma is positive definite. In particular, the original estimator and the B centered bootstrap differences become independent equal-covariance Gaussian blocks under the anisotropic normalization. They are not coordinatewise independent within a block in general.

For every fixed nonzero functional `ell`, without inserting any normalization in the implemented statistic,

\[
\frac{\ell^T\bar X_n}
{\sqrt{B^{-1}\sum_{b=1}^B(\ell^T\bar D_n^b)^2}}
\Rightarrow t_B.
\tag{S5}
\]

Thus the original divisor-B cheap online interval is asymptotically valid for that functional. If `B>=d`, let

\[
\widehat V_n=B^{-1}\sum_{b=1}^B\bar D_n^b(\bar D_n^b)^T.
\]

Then

\[
\bar X_n^T\widehat V_n^{-1}\bar X_n
\Rightarrow\frac{dB}{B-d+1}F_{d,B-d+1}.
\tag{S6}
\]

The probability that the inverse is unavailable tends to zero. With `B<d`, the matrix has rank at most B and (S6) is not asserted. The covariance estimator is uncentered about `bar X_n`; subtracting the bootstrap sample mean would change the degrees of freedom and is a different procedure.

Translation gives the same confidence statements for an arbitrary unknown mean `mu=E Z`, replacing the numerator by `bar X_n-mu` and taking centered-noise moments. This theorem does not give a finite-sample coverage rate, uniformity near `a_j=1/2`, growing B/d, a conditional-bootstrap law given the observations, or a nonlinear-loss result.

## 2. Exact innovations and their conditional covariance

Use eigenbasis coordinates throughout the proof; suppress tildes on iterates and noise. Direct subtraction in (S1) gives

\[
D_t^b=(I-A/t)D_{t-1}^b+(A/t)M_t^b,
\quad
M_t^b=(W_t^b-1)(Z_t-X_{t-1}^b),
\tag{S7}
\]

and set `M_t^0=Z_t`. Let the filtration contain all previous noise and multiplier variables. The stacked innovation is a martingale difference, with exact conditional covariance

\[
\mathbb E[M_t M_t^T\mid\mathcal F_{t-1}]
=\operatorname{blockdiag}\left(
\widetilde\Sigma,
\widetilde\Sigma+X_{t-1}^1(X_{t-1}^1)^T,\ldots,
\widetilde\Sigma+X_{t-1}^B(X_{t-1}^B)^T\right).
\tag{S8}
\]

The within-run blocks are full covariance matrices because the same multiplier acts on every coordinate. Blocks from different runs have zero conditional covariance: the product of their centered multiplier means is zero, even though they share `Z_t`. The covariance with coordinate block zero similarly vanishes. The random coefficient has not been discarded; it remains in each innovation and the additional rank-one conditional covariance.

For any `a>0`, define products without dividing by a potentially zero early factor:

\[
P_{t,u}(a)=\prod_{r=u+1}^t(1-a/r),\qquad
w_{n,u}(a)=\frac{a}{nu}\sum_{t=u}^nP_{t,u}(a),
\tag{S9}
\]

with empty product one, and

\[
q_n(a)=\frac1n\sum_{t=1}^n\prod_{r=1}^t(1-a/r).
\]

Solving (S7) and averaging is exact:

\[
(\bar X_{n,j},\bar D_{n,j}^1,\ldots,\bar D_{n,j}^B)
=(q_n(a_j)x_{0,j},0,\ldots,0)
+\sum_{u=1}^n w_{n,u}(a_j)(M_{u,j}^0,\ldots,M_{u,j}^B).
\tag{S10}
\]

This includes arbitrary large and integer eigenvalues `a_j`: a zero or negative early deterministic factor causes no singularity in the representation.

## 3. Deterministic weight lemma, including mixed critical/regular pairs

For every fixed `a>=1/2`, the normalized maximal weight tends to zero, the squared-weight sums have finite limits, and the normalized initialization term vanishes. The precise covariance limits are

\[
\frac n{\log n}\sum_{u=1}^n w_{n,u}(1/2)^2\to1,
\tag{S11}
\]
\[
n\sum_{u=1}^n w_{n,u}(a)w_{n,u}(b)
\to\frac{a+b}{a+b-1},
\qquad a,b\ge1/2,\ a+b>1.
\tag{S12}
\]

Consequently a critical/regular cross term under the normalizations in (S3) tends to zero: (S12) is divided by `sqrt(log n)`.

**Proof for the critical coordinate.** With `p_t=binom(2t,t)/4^t`, the exact identities in the bound scalar source
`critical_online_bootstrap_theorem.md`, SHA256 `b61ce8aec7b3dd187021c1788f74c21746a2e6cd4c0417dc145e34948d878e0d`, give

\[
w_{n,u}(1/2)=\frac{(2n+1)p_n}{2nup_u}-\frac1n,
\quad
\sum_u w_{n,u}(1/2)^2=\frac{\log n+O(1)}n,
\]

\[
0\le w_{n,u}(1/2)\le C/\sqrt{nu},\quad
q_n(1/2)=2/\sqrt{\pi n}+O(n^{-1}).
\]

Thus (S11), the maximal-weight assertion and the critical bias assertion follow directly.

**Proof of (S12).** Choose a fixed integer `u0>2 max(a,b)`. For `t>=u>=u0`, expanding the logarithm of the product in (S9) gives uniformly

\[
P_{t,u}(a)=(u/t)^a[1+O_a(1/u)],\qquad
0<P_{t,u}(a)\le C_a(u/t)^a.
\tag{S13}
\]

Indeed the harmonic-sum error and the sum of squared reciprocal indices are both `O(1/u)`. On every compact subinterval of `(0,1]`, Riemann sums in (S9) therefore give

\[
n w_{n,\lfloor nx\rfloor}(a)\longrightarrow g_a(x),
\quad
g_a(x)=
\begin{cases}
\dfrac{a}{a-1}(1-x^{a-1}),&a\ne1,\\
-\log x,&a=1.
\end{cases}
\tag{S14}
\]

Useful uniform bounds for `u>=u0` are

\[
|w_{n,u}(a)|\le
\begin{cases}
C_a n^{-a}u^{a-1},&a<1,\\
C_a n^{-1}\log(en/u),&a=1,\\
C_a n^{-1},&a>1.
\end{cases}
\tag{S15}
\]

For a fixed early index `u<u0`, its product is either eventually zero or a constant times `t^-a[1+O(1/t)]`. Thus its weight is respectively `O(n^-a)` for `a<1`, `O(log n/n)` for `a=1`, or `O(1/n)` for `a>1`. The same bounds hold for `q_n(a)`. Every finite early contribution to (S12) vanishes when `a+b>1`.

The remaining small-x cross tail vanishes uniformly. If both exponents are below one, its bound from (S15) is `C epsilon^(a+b-1)` after summing `u<=epsilon n`. If one equals one, the power is accompanied by an integrable logarithm. If one is above one, the other is at least one half and the bound is an integrable power. This proves passage from (S14) to the cross integral even when one exponent is critical. Direct integration gives

\[
\int_0^1g_a(x)g_b(x)\,dx
=\frac{ab}{(a-1)(b-1)}
\left(1-\frac1a-\frac1b+\frac1{a+b-1}\right)
=\frac{a+b}{a+b-1}.
\tag{S16}
\]

When either exponent equals one, the result follows by integrating the logarithmic kernel, or by continuity with a common integrable local envelope. The square-kernel integral is finite exactly in the regular range `a>1/2`.

Finally, (S15) and the finite early bounds give `sqrt n max_u |w_(n,u)(a)|->0` for every regular a: the possible rates are `n^(1/2-a)`, `log n/sqrt n`, or `n^-1/2`. They also give `sqrt n q_n(a)->0`. Together with the critical estimates, this proves every assertion of the weight lemma.

## 4. Uniform moments of the random-coefficient iterates

For each bootstrap coordinate with exponent a, let `u_t=E(X_(t,j)^b)^2`. Independence and `E W^2=2` give exactly

\[
u_t=(1-2a/t+2a^2/t^2)u_{t-1}
+2a^2\widetilde\Sigma_{jj}/t^2.
\tag{S17}
\]

At `a=1/2`, this yields `u_t=O(log(et)/t)` as in the scalar source. At `a>1/2`, multiplying by t makes the coefficient on `(t-1)u_(t-1)` equal to `1-(2a-1)/t+O(t^-2)`. A sufficiently large constant is then an invariant upper bound for `t u_t`, proving `u_t=O(1/t)`. All finite early times, including unstable-looking early step coefficients, have finite moments and are absorbed into the constant. Consequently `E||X_t^b||^2->0` and is uniformly bounded.

For a coordinate fourth moment, the coefficient on its preceding fourth moment is

\[
\mathbb E(1-aW/t)^4
=1-4a/t+12a^2/t^2-24a^3/t^3+24a^4/t^4.
\]

The term with one current noise factor vanishes. The remaining mixed terms are bounded by `C u_(t-1)/t^2`, `C |E X_(t-1,j)^b|/t^3`, and `C/t^4`; finite fourth noise moments suffice even without noise symmetry. At late times the displayed coefficient is at most `1-1/t`, because `a>=1/2`. The bounded second moments therefore give a uniform coordinate fourth moment. The inequality `||x||^4<=(d sum_j x_j^4)` gives the uniform vector fourth moment, and independent Exp(1) weights imply

\[
\sup_t\mathbb E\|M_t\|^4<\infty
\tag{S18}
\]

for the full fixed-dimensional stacked innovation.

## 5. Anisotropic martingale CLT and positive definiteness

Let `r_(n,j)` denote the jth normalization in `T_n`, and define

\[
F_{n,t}=\operatorname{diag}
\{r_{n,j}w_{n,t}(a_j):1\le j\le d\}.
\]

The weight lemma shows

\[
\sup_n\sum_t\|F_{n,t}\|_{\rm op}^2<\infty,
\quad\max_t\|F_{n,t}\|_{\rm op}\to0,
\tag{S19}
\]

and the deterministic noise part of the predictable covariance converges to (S4) in each block. The additional within-run covariance is

\[
\sum_t F_{n,t}X_{t-1}^b(X_{t-1}^b)^TF_{n,t}.
\]

Its expected operator norm is at most `sum_t ||F_(n,t)||_op^2 E||X_(t-1)^b||^2`, which tends to zero. To see this without a uniform rate assumption, first make the iterate second moment below epsilon for all `t>T`; (S19) bounds that tail by `C epsilon`. The finitely many early terms vanish by the maximal-weight bound. Thus the additional covariance converges to zero in probability, including its off-diagonal coordinate terms.

For any fixed linear functional of the full stacked array, the conditional Lindeberg sum has expectation bounded by a constant times

\[
\sum_t\|F_{n,t}\|_{\rm op}^4
\le\max_t\|F_{n,t}\|_{\rm op}^2
\sum_t\|F_{n,t}\|_{\rm op}^2\to0,
\]

using (S18). Markov's inequality yields the conditional Lindeberg condition. The martingale triangular-array CLT and Cramer–Wold prove (S3), after adding the vanishing deterministic initialization from the weight lemma.

The regular covariance has the integral representation

\[
\Gamma_{RR}=\int_0^1
\operatorname{diag}(g_{a_j}(x))\widetilde\Sigma_{RR}
\operatorname{diag}(g_{a_j}(x))\,dx.
\tag{S20}
\]

Every kernel is positive on `(0,1)`, so positive definiteness of `tilde Sigma_RR` makes this matrix positive definite. The critical block is a positive definite principal submatrix; the cross block is zero. Empty C or R blocks cause no difficulty.

Equivalently, in regular eigen-coordinates,

\[
\Gamma_{RR}=\widetilde\Sigma_{RR}+Q,
\quad
(A_R-\tfrac12I)Q+Q(A_R-\tfrac12I)
=\widetilde\Sigma_{RR}.
\tag{S21}
\]

This is a useful description of the regular covariance, but the bootstrap pivot does not need to estimate the spectrum or solve that equation.

## 6. Functional intervals and the uncentered Wishart ellipsoid

For a fixed functional with nonzero projection onto C, multiply both numerator and bootstrap differences in (S5) by `sqrt(n/log n)`. Its regular components vanish in the limit and its critical variance is positive. If its critical projection is zero, use `sqrt n`; its regular variance is positive. In either case (S3) gives B+1 independent equal-variance scalar Gaussian limits. Their Student ratio proves (S5). The normalization cancels from the implemented ratio, so a user need not decide in advance which scale applies to that fixed functional.

For (S6), the invertible deterministic transformation `T_n U^T` leaves the quadratic statistic exactly unchanged. Under that transformation, the numerator tends to `G_0~N(0,Gamma)`, and the covariance estimate tends to `B^-1 sum_(b=1)^B G_bG_b^T`, with independent equal-covariance Gaussian vectors. For `B>=d` the latter is positive definite almost surely. The continuous mapping theorem applies on that event; singular finite-n events have vanishing probability.

Whiten the limiting vectors and let `W=sum_(b=1)^B g_b g_b^T`. Then the limiting statistic is `B g_0^T W^-1 g_0`. Rotational invariance separates `||g_0||^2~chi_d^2` from its direction. The reciprocal of the corresponding directional inverse-Wishart entry is `chi_(B-d+1)^2`: this follows from the Schur complement, projecting the first Gaussian sample column off the other `d-1` columns in `R^B`. It is independent of the numerator. Hence the ratio is exactly `dB/(B-d+1) F_(d,B-d+1)`, proving (S6). Continuity at its finite quantiles gives the stated asymptotic confidence ellipsoid.

## 7. Boundary and originality limits

The multiplier procedure and divisor B are the cheap online procedure of [Lam and Wang](https://arxiv.org/html/2310.11065v2). The claim here is confined to its exact SPD-quadratic specialization. The earlier subcritical harmonic counterexamples are not overwritten; (S2) is an essential scope restriction of this repair.

The scalar critical case is bound above. Standard martingale central limit theory supplies the probabilistic limit; the stochastic-approximation spectrum transition and covariance kernels have classical antecedents. This note does not assert that the combined theorem is historically new, and no broad endpoint theorem for nonlinear SGD is inferred. What is proved is the explicit mixed-spectrum joint limit for the original scalar-multiplier bootstrap and the resulting unchanged functional intervals and precisely calibrated uncentered ellipsoid.
