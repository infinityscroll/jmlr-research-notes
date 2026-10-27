# Independent audit of the nonlinear critical online-bootstrap theorem

27 October 2026. Audited source: `nonlinear_critical_bootstrap_theorem.md`, SHA256 `6eaae8f09c1266cbe1a7b4aab31421f602e9bd409175ae1f7408f5452ab61bb5`.

**Verdict: no blocking mathematical error found under the assumptions as stated.** I independently reconstructed the local moment argument, both remainder estimates, the finite-second-moment joint Gaussian reduction, the covariance constants and the two pivots. This is an internal mathematical audit, not external expert acceptance or novelty clearance. I did not change the source.

The checked dependencies have hashes `44af0d68b27fc67e97557b7155fd48920423dbe0d65413347789f9a75a6d4c10` (SPD theorem) and `b61ce8aec7b3dd187021c1788f74c21746a2e6cd4c0417dc145e34948d878e0d` (scalar critical weights). The source bindings match the saved files.

## 1. The global convergence argument does not require a fast global rate

Translate theta to zero. For either W=1 or W~Exp(1), independence of the current observation and weight from the past gives

\[
E(\|X_t\|^2\mid\mathcal F_{t-1})
\le (1+C/t^2)\|X_{t-1}\|^2
-2\eta\mu\|X_{t-1}\|^2/t+C/t^2.
\]

The integrability requirements follow inductively from the deterministic global Lipschitz constant and `E||g(0,Z)||²<infinity`. The almost-supermartingale lemma gives convergence of the nonnegative squared norm and summability of its `1/t`-weighted values. A positive norm limit would contradict the divergent harmonic series. Therefore each process converges almost surely to zero. There are only finitely many processes, so their convergence events can be intersected without losing probability one.

This proves eventual residence in every fixed local ball. It does not claim a global second-moment rate derived from the local Hessian. In particular, an arbitrarily small positive global strong-convexity constant does not obstruct this part of the proof.

## 2. The killed local estimate is valid and predictable

Choose `h0<lambda_min(H)` with `2 eta h0>1/(1+rho)`. This is possible because `2 eta lambda_min(H)>=1` and rho>0. The local expansion implies

\[
x^T G(x)\ge h_0\|x\|^2\quad\text{for }\|x\|<\epsilon.
\]

Let tau_N be the first index at least N outside this ball. For `t>N`, the event `E_(t-1)={tau_N>t-1}` belongs to the past sigma field and guarantees that the previous iterate lies inside the ball. Consequently

\[
\begin{aligned}
u_t^N
&=E[\|X_t\|^2 1\{\tau_N>t\}]\\
&\le E[1_{E_{t-1}}E(\|X_t\|^2\mid\mathcal F_{t-1})]\\
&\le(1-2\eta h_0/t+C/t^2)u_{t-1}^N+C/t^2.
\end{aligned}
\]

The first inequality only drops a nonnegative quantity. It does not condition the current noise on survival. For any `gamma<min(2 eta h0,1)`, the comparison `u_t^N<=C_N t^(-gamma)` follows by induction at sufficiently large t: the drift gap `(2 eta h0-gamma)C_N t^(-gamma-1)` dominates the forcing `C/t²`. The finite initial segment can be absorbed into C_N.

The source chooses gamma above `1/(1+rho)`, so `beta=gamma(1+rho)/2>1/2`. All choices are strict, including when the smallest spectral exponent equals one half. The constants may depend on N; the proof takes limits in the correct order, first n and then N.

## 3. Nonlinear drift and state-dependent noise are genuinely negligible

Write `xi_t=g(0,Z_t)`, `r(x)=G(x)-Hx`, and

\[
e_t(x)=W_t[g(x,Z_t)-g(0,Z_t)]-G(x).
\]

Because `G(0)=0` and `EW=1`, this e is conditionally centered for every past-measurable x. Moreover, the conditional variance bound is

\[
E(\|e_t(x)\|^2\mid\mathcal F_{t-1})
\le E W_t^2\,L^2\|x\|^2.
\]

Subtracting the conditional mean cannot increase the second moment. The exact recursion is therefore the deterministic linear recursion with innovations `W_t xi_t+r(X_(t-1))+e_t(X_(t-1))`, as claimed.

For the drift term, since `1+rho<=2`, Holder's inequality on the killed event yields

\[
E[\|r(X_{t-1})\|1_{E_{t-1}}]
\le C (u_{t-1}^N)^{(1+\rho)/2}
\le C_Nt^{-\beta}.
\]

The source's coefficient bounds then give, respectively:

- Critical coordinate: `C_N/sqrt(log n) sum_(t>N) t^(-beta-1/2)`, tending to zero.
- `1/2<a<1`: `C_N n^(1/2-a) sum_(t>N)^n t^(a-1-beta)`. If a<beta the sum is bounded; if equal it is logarithmic; if a>beta the bound is `O(n^(1/2-beta))`. Every case vanishes.
- a=1: the extra factor `1+log(n/t)` still gives `O(n^(1/2-beta))` because beta<1, and hence convergence to zero.
- a>1: `C_N n^(-1/2) sum t^(-beta)=O(n^(1/2-beta))`.

For the noise remainder, the truncated terms `1_(E_(t-1)) e_t(X_(t-1))` are martingale differences. Orthogonality across times bounds the normalized squared mean by

\[
C\sum_{t>N}|s_n(a)b_{nt}(a)|^2u_{t-1}^N.
\]

The finite early coefficients vanish individually, while the tail is bounded by `sup_(t>T)u_t^N` times a uniformly bounded squared-coefficient sum. Taking n and then T to infinity proves the result at fixed N. This needs no fourth moment.

Finally, on the event that no process leaves the ball after N, truncated and actual tails coincide. Its complement has probability tending to zero as N tends to infinity by almost-sure convergence. The source does **not** multiply a martingale increment by a future no-exit indicator and then assert conditional centering. This was the principal localization failure mode I checked.

Finite terms at times up to N are harmless: the deterministic normalized coefficients vanish, while global Lipschitz continuity ensures the required finite-time moments. The averaged initialization has the same vanishing property, including its `1/sqrt(log n)` decay in a critical coordinate.

## 4. The leading innovations and covariance constants

After subtracting the original run from each replicate, the leading vector is

\[
(\xi_t,(W_t^1-1)\xi_t,\ldots,(W_t^B-1)\xi_t).
\]

These vectors are iid across t. Their covariance is block diagonal with B+1 identical Sigma blocks. The cross blocks vanish because the centered independent weights have mean zero; this does not make the finite-sample blocks independent. Products of an Exp(1) weight with xi have finite second moments under the stated noise assumption.

The maximal matrix coefficient tends to zero and the sum of squared operator norms stays bounded. This gives the ordinary triangular-array Lindeberg bound using only the integrable tail of `||zeta||²`. Thus finite fourth moments are unnecessary for this proof, even though the earlier martingale formulation used them.

I also checked the deterministic constants independently. In a regular coordinate, the limiting kernel is

\[
h_a(x)=(1-x^{a-1})/(a-1),\qquad h_1(x)=-\log x.
\]

Direct integration, with continuous extension when a or b equals one, gives

\[
\begin{aligned}
\int_0^1h_a(x)h_b(x)\,dx
&=\frac{1-1/a-1/b+1/(a+b-1)}{(a-1)(b-1)}\\
&=\frac{a+b}{ab(a+b-1)}.
\end{aligned}
\]

The factor eta² is required because the present innovations are gradients. In the quadratic specialization with gradient `H(X-Z)`, multiplication by the two Hessian eigenvalues recovers the covariance in the bound SPD theorem. At a=b=1/2 the squared critical kernel is logarithmically divergent, and the exact central-binomial formula gives `4 eta²` after division by log n. A critical/regular product is integrable because a+b>1; its anisotropic normalization then supplies a factor `1/sqrt(log n)`, so the cross block vanishes.

The integral representation of the regular block has strictly positive diagonal kernels on `(0,1)`. Together with positive definiteness of Sigma this proves positive definiteness of Gamma. Integer or large eigenvalues cause no singular product division: the coefficient definition uses finite products directly.

## 5. The pivots and nonlinear example

For a fixed ell, a nonzero critical projection selects the critical scale; otherwise the regular scale applies. In each case the original projection and B centered bootstrap projections tend to independent normals with equal positive variance. Their uncentered divisor-B ratio is exactly Student t_B in the limit.

For the multivariate statistic, the common deterministic anisotropic transformation cancels identically from the quadratic form. Its limiting denominator is `B^-1` times a Wishart matrix with B degrees of freedom. When B>=d it is positive definite almost surely, and

\[
B G_0^T\Big(\sum_{b=1}^B G_bG_b^T\Big)^{-1}G_0
\ \stackrel{d}=\ \frac{dB}{B-d+1}F_{d,B-d+1}
\]

after whitening. The vanishing probability of finite-n singularity follows from convergence to an almost-surely positive definite limiting matrix. The source correctly excludes B<d.

For the displayed nonlinear example, the sample derivative is between 1 and 5, the mean Hessian at zero is 4, and the noise at zero is -Z. With eta=1/8 the spectral exponent is exactly one half and the covariance is `4(1/8)²=1/16`. Its global strong-convexity coefficient can only be taken as one, so the example indeed distinguishes local curvature from the weaker global constant. The Taylor remainder is cubic and satisfies the stated local quadratic remainder bound.

## 6. Scope and bounded source check

I verified [Fang, Xu and Yang (2018), Assumption A5 and Theorem 2](https://www.jmlr.org/papers/volume19/17-370/17-370.pdf): their power exponent is strictly between one half and one. That theorem does not directly establish the harmonic critical case. The [Lam–Wang source](https://arxiv.org/html/2310.11065v2) is the intended cheap online procedure. This comparison does not clear novelty against classical nonlinear stochastic-approximation limit theory or every later bootstrap theorem.

The source proves a fixed-dimensional unconditional joint limit and the resulting fixed-B pivots under strong smoothness, global stability and local spectral assumptions. It does not prove conditional bootstrap consistency, finite-sample accuracy, uniformity as eigenvalues approach one half, or validity below that boundary. None of those stronger claims should be inferred from this audit.
