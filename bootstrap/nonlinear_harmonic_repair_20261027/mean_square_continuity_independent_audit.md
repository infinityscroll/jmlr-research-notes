# Audit of the mean-square continuity extension

27 October 2026. Bound source: `mean_square_continuity_extension.md`, SHA256 `8cf2b32cae345521e8699466f4441801a37809cda5ad1cc0311b6d69d50a4840`. Bound underlying theorem: `nonlinear_critical_bootstrap_theorem.md`, SHA256 `6eaae8f09c1266cbe1a7b4aab31421f602e9bd409175ae1f7408f5452ab61bb5`.

**Verdict: no blocking error found.** The stated weakening preserves the theorem, including the critical and mixed-spectrum limits, with only finite second moments. Both examples satisfy the claimed conditions with the qualifications printed in the source. No source change is requested. This is internal mathematical review, not a novelty or finite-sample accuracy certification.

## 1. Growth is enough for convergence and the deterministic remainder

The global moment bound

\[
E\|g(\theta+x,Z)\|^2\le C_0(1+\|x\|^2)
\]

is exactly the bound needed in the squared-norm recursion. With `EW=1`, `EW²<=2`, and global strong monotonicity of the mean field, it yields finite second moments at each finite time and the same almost-supermartingale convergence proof as the bound theorem. Pointwise Lipschitzness of the random map is unnecessary there.

Inside the fixed local ball, the mean Taylor expansion still gives `x^T G(theta+x)>=h0||x||²`. Consequently the predictable killed moment estimate and the exponent `beta>1/2` used for the nonlinear remainder are unchanged. At the finitely many early times, Jensen gives

\[
\|G(\theta+x)\|^2\le E\|g(\theta+x,Z)\|^2,
\]

so the mean drift and the linearization remainder have adequate finite moments. The extension has not implicitly assumed global Lipschitz continuity of G.

## 2. Mean-square continuity is enough for the martingale remainder

For a past-measurable state x, let `D(x,Z)=g(theta+x,Z)-g(theta,Z)`. Since the mean gradient at theta is zero,

\[
e_t(x)=W_tD(x,Z_t)-G(\theta+x)
\]

is conditionally centered and obeys

\[
E(\|e_t(x)\|^2\mid\mathcal F_{t-1})
\le E W_t^2\,E\|D(x,Z)\|^2
\le2\kappa(x).
\]

The current Z and W are independent of the entire past, so this identity remains valid for each process in the common-data system. Cross-replicate independence is not required for the remainder estimates.

On `tau_N>t-1`, the iterate belongs to a fixed bounded ball. The global growth bound gives the deterministic bound

\[
\kappa(x)\le2C_0(1+\|x\|^2)+2E\|g(\theta,Z)\|^2,
\]

which is uniform on that ball. Almost-sure convergence implies `kappa(X_(t-1)-theta)->0`; multiplication by the bounded survival indicator does not change this pointwise convergence. Dominated convergence therefore proves `v_t^N->0` for every fixed N. This argument uses neither a rate for kappa nor uniform integrability of the unrestricted iterate sequence.

The indicator `1{tau_N>t-1}` is predictable. The stopped increments are genuine martingale differences. Their variance is bounded by twice the weighted sum of v_t^N. The deterministic weights have bounded total squared mass and vanish at every fixed time. Splitting at T, then taking n and T to infinity, proves the weighted sum tends to zero. Finally, the no-exit probability removes the truncation in the same order of limits as the earlier audited theorem. There is no future-survival conditioning error.

The leading iid innovation vector is unchanged. The growth condition at x=0 supplies its finite second moments. All covariance constants and the fixed-B pivots therefore carry over without a new fourth-moment requirement.

## 3. Application checks

**Random sample Lipschitz constants.** If `E L(Z)²<infinity`, then

\[
E\|g(\theta+x,Z)\|^2
\le2E\|g(\theta,Z)\|^2+2E L(Z)^2\|x\|^2,
\qquad\kappa(x)\le E L(Z)^2\|x\|^2.
\]

Thus the asserted sufficient condition is valid. For binary ridge logistic regression, the sample Hessian is `lambda I+sigma(A^Tx)(1-sigma(A^Tx))AA^T`, so its operator norm is at most `lambda+||A||²/4`. Gaussian fourth moments give square integrability of this bound. Gaussian third moments control differences of the mean Hessian. The ridge gives global strong convexity and a unique minimizer. Positive definite noise covariance is an additional requirement, correctly retained by the source; it must not be inferred from the word “Gaussian” alone without a design/response specification.

**Ridge absolute loss.** For standard Gaussian Z,

\[
F(x)=\mu x^2/2+E|x-Z|,
\quad G(x)=\mu x+2\Phi(x)-1,
\quad G'(0)=\mu+\sqrt{2/\pi}.
\]

Differentiating the expected absolute value is justified by its bounded difference quotients and the atomless Gaussian law. The mean field has the unique root zero, is globally mu-strongly monotone, and has a smooth local expansion. The selected sample subgradient need not be differentiable. At any fixed state, the event Z=x has probability zero; since the state in an update is past-measurable, the same is true conditionally for every update. A measurable choice at the kink therefore has no effect on these calculations.

The moment growth bound follows from `|sign|<=1` away from that null event, and

\[
\kappa(x)\le2\mu^2x^2+8P\{Z\text{ is between }0\text{ and }x\}\to0.
\]

The origin noise has variance one. Hence at `eta=1/[2(mu+sqrt(2/pi))]` the critical covariance is indeed `4 eta²=1/H²`. The unchanged Student limit follows. The source correctly labels this as a nonsmooth sample-loss application of the strengthened mean-field theorem, not as satisfaction of a primary-paper hypothesis requiring smooth sample losses.

## 4. Boundaries

The conclusions continue to require global mean stability, the local Holder remainder, nondegenerate origin noise, and the local spectral threshold. They remain unconditional, asymptotic fixed-dimensional/fixed-B statements. Replacing sample Lipschitzness by these moments does not establish conditional bootstrap consistency, finite-sample accuracy, validity below the spectral threshold, or a broader originality claim.
