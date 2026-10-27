# Removing uniform sample-gradient Lipschitzness from the harmonic repair

27 October 2026. Candidate strengthening of `nonlinear_critical_bootstrap_theorem.md`, SHA256 `6eaae8f09c1266cbe1a7b4aab31421f602e9bd409175ae1f7408f5452ab61bb5`. Its source remains unchanged. This addendum changes assumptions and the stochastic-remainder bound; it does not assert a new inference procedure or historical novelty.

## Statement

In the bound theorem, replace the almost-sure deterministic-L Lipschitz condition on g by the following two requirements:

\[
E\|g(\theta+x,Z)\|^2\le C_0(1+\|x\|^2)\quad\text{for every }x,
\tag{M1}
\]

\[
\kappa(x):=E\|g(\theta+x,Z)-g(\theta,Z)\|^2\longrightarrow0
\quad\text{as }x\to0.
\tag{M2}
\]

Keep the mean-field assumptions: `G=E g=gradient F`, F globally mu-strongly convex, local expansion with SPD H and Holder remainder order1+rho for some rho>0, positive definite origin-noise covariance, harmonic step eta/t with eta*lambda_min(H)>=1/2, iid data and Exp(1) weights, and fixed d,B and initial point. Then all conclusions (N2)--(N5), including the same explicit covariance, remain true.

In particular, a random sample Lipschitz constant with finite second moment suffices, and differentiability of each sample gradient is unnecessary if the selected stochastic subgradient has the stipulated smooth mean field. The theorem's statement concerns G, not interchange of differentiation and expectation; that identity must be established for an application.

## Proof of the changed steps

Translate theta to zero. The conditional second-moment recursion (N6) follows directly from strong monotonicity of G and (M1). Thus almost-sure convergence, finite-time second moments, the predictable killed local moments `u_t^N=O_N(t^(-gamma))`, and the nonlinear remainder bound (N16) remain unchanged. Those steps never require pointwise Lipschitzness of g. The mean drift at a finite early time is integrable because `||G(x)||^2<=E||g(x,Z)||^2`; hence the treatment of the finite initial remainder is also valid.

For the exact centered noise remainder from (N10), now use

\[
E[\|e_t(x)\|^2\mid\mathcal F_{t-1}]
\le E(W^2)\,\kappa(x)\le2\kappa(x).
\tag{M3}
\]

This is variance at most second moment, using independence of the current multiplier and data from the past. For the original process take W=1. The mean subtracted from `W(g(x,Z)-g(0,Z))` is exactly G(x).

For fixed deterministic N and its predictable exit time, define

\[
v_t^N=E[\kappa(X_{t-1})1\{\tau_N>t-1\}].
\]

On the local no-exit event, (M1) bounds kappa by a common finite constant, since `kappa(x)<=2E||g(x,Z)||^2+2E||g(0,Z)||^2` and x is in a fixed bounded ball. Almost-sure convergence and (M2) therefore give `v_t^N->0` by dominated convergence. No power-law rate for kappa is required.

Martingale orthogonality bounds the variance of each stopped normalized stochastic remainder by

\[
2\sum_{t>N}|s_n(a)b_{nt}(a)|^2 v_t^N\longrightarrow0.
\tag{M4}
\]

The convergence follows by splitting at a fixed T and using the vanishing individual weights and bounded total squared weights in (N15), then letting T grow. The no-exit probability removes the truncation as before, taking n to infinity first and N second. Only predictable indicators multiply martingale increments. The leading iid triangular array is unchanged and needs only finite second moments, supplied by (M1). This proves the extension.

## Applications and exact scope

**Random-design smooth problems.** If `||g(x,Z)-g(y,Z)||<=L(Z)||x-y||` almost surely with `E L(Z)^2<infinity`, and the origin gradient has finite second moment, then (M1)--(M2) follow immediately. This includes ridge logistic regression with Gaussian covariates: the random Lipschitz constant is bounded by `ridge+||A||^2/4`, Gaussian fourth moments are finite, the ridge supplies global strong convexity, and finite third covariate moments give a locally Lipschitz mean Hessian. A nondegenerate noise covariance at the minimizer is still required. There is no claim of finite-sample accuracy or of validity for a step below the local spectral threshold.

**Nonsmooth sample losses with smooth mean.** In one dimension take

\[
f(x;Z)=\tfrac\mu2 x^2+|x-Z|,\qquad
g(x,Z)=\mu x+\operatorname{sign}(x-Z),
\]

with centered standard Gaussian Z, mu>0, and any measurable sign convention at zero. The mean is `G(x)=mu*x+2Phi(x)-1`, its unique root is0, and `H=mu+sqrt(2/pi)`. It is globally mu-strongly monotone and has a local Holder expansion. The growth condition holds. Furthermore,

`kappa(x)<=2mu^2 x^2+8 P(Z lies between0 and x)->0`.

At `eta=1/(2H)`, the theorem gives critical normalized variance `1/H^2` and the unchanged t_B limit. This is an extension to a nonsmooth sample loss, not a claim that it satisfies a primary-paper assumption demanding twice differentiable sample losses. The smooth nonlinear example in the bound theorem remains available without that qualification.

These weakened conditions closely resemble the classical online-bootstrap mean-square continuity assumptions. The additional issue addressed here is the harmonic critical/mixed-spectrum regime and its finite-B pivot, not invention of stochastic-approximation localization.
