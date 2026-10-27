# Harmonic online-bootstrap validity beyond quadratic losses

27 October 2026. New theorem candidate, awaiting hostile independent audit. This extends the portfolio's SPD-quadratic critical-spectrum result to nonlinear stochastic gradients. Spectral stochastic-approximation scaling, localization, triangular-array CLTs and Student/Wishart pivots are classical. Novelty of this specialization is not established.

## 1. Exact procedure and assumptions

Let observations Z_t be iid and let g(x,Z) be a stochastic gradient in fixed dimension d. Write G(x)=E g(x,Z)=gradient F(x). Assume:

1. F is globally mu-strongly convex, mu>0, with unique minimizer theta. For almost every Z, g is globally L-Lipschitz in x with one finite deterministic L.
2. E||g(theta,Z)||^2 is finite and Sigma=Cov(g(theta,Z)) is positive definite. A finite fourth moment may be imposed, but is not required by this asymptotic argument.
3. H=Hessian F(theta) is symmetric positive definite. For some rho in (0,1], delta>0 and C<infinity, `||G(theta+x)-Hx|| <= C||x||^(1+rho)` whenever `||x||<=delta`.
4. The harmonic step is eta/t with eta>0 and **eta lambda_min(H)>=1/2**. There is no further lower bound on eta*mu. Dimension d and number of bootstrap replicates B>=1 are fixed.

Use the original online multiplier recursions, with one scalar weight per entire gradient:

\[
X_t=X_{t-1}-\frac\eta t g(X_{t-1},Z_t),\qquad
X_t^b=X_{t-1}^b-\frac\eta t W_t^b g(X_{t-1}^b,Z_t).
\tag{N1}
\]

The weights W_t^b are independent Exp(1), mutually independent and independent of the data; all processes start at the same fixed finite x0. Set `bar X_n=n^(-1) sum_(t=1)^n X_t` and `bar D_n^b=bar X_n^b-bar X_n`. There is no burn-in, altered averaging rule or changed divisor in the confidence interval.

Diagonalize `eta H=U diag(a_1,...,a_d) U^T`, with U orthogonal. Let C contain the indices a_j=1/2, and R those with a_j>1/2. Put S=U^T Sigma U and let T_n be diagonal with entries sqrt(n/log n) on C and sqrt(n) on R.

**Theorem.** Under these assumptions,

\[
\big(T_nU^T(\bar X_n-\theta),T_nU^T\bar D_n^1,\ldots,
 T_nU^T\bar D_n^B\big)
\ \Rightarrow\ N(0,I_{B+1}\otimes\Gamma),
\tag{N2}
\]

where

\[
\Gamma_{ij}=4\eta^2 S_{ij}\quad(i,j\in C),\qquad
\Gamma_{CR}=\Gamma_{RC}=0,
\]
\[
\Gamma_{ij}=\eta^2\frac{a_i+a_j}{a_i a_j(a_i+a_j-1)}S_{ij}
\quad(i,j\in R).
\tag{N3}
\]

Gamma is positive definite. For every fixed nonzero vector ell, the unchanged cheap statistic satisfies

\[
\frac{\ell^T(\bar X_n-\theta)}
 {\sqrt{B^{-1}\sum_{b=1}^B(\ell^T\bar D_n^b)^2}}
\Rightarrow t_B.
\tag{N4}
\]

For B>=d, setting `Vhat_n=B^(-1)sum_b bar D_n^b(bar D_n^b)^T`,

\[
(\bar X_n-\theta)^T\widehat V_n^{-1}(\bar X_n-\theta)
\Rightarrow \frac{dB}{B-d+1}F_{d,B-d+1}.
\tag{N5}
\]

The probability of an unavailable inverse tends to zero. B<d is excluded from (N5). No conditional-bootstrap consistency, finite-sample coverage rate, uniformity near the critical threshold, growing B/d, or nonsmooth-gradient claim is made. The theorem concerns the online multiplier procedure, not the separate offline empirical-resampling variant.

## 2. Almost-sure convergence and localized second moments

Translate theta to zero. For either one process or one bootstrap replicate, denote its weight by W, taking W=1 for the original. With x its previous value, conditional expectation gives

\[
E[\|x-\eta Wg(x,Z)/t\|^2\mid x]
\le (1-2\eta\mu/t+C_0/t^2)\|x\|^2+C_0/t^2.
\tag{N6}
\]

Here EW=1, EW^2<=2, `E||g(x,Z)||^2<=2L^2||x||^2+2E||g(0,Z)||^2`, and `x^TG(x)>=mu||x||^2`. All finite-time second moments are finite. The almost-supermartingale convergence lemma applied to (N6) gives convergence of ||X_t||^2 and finiteness of `sum_t ||X_(t-1)||^2/t` almost surely. Their combination forces X_t to zero. The same holds for each of the fixed B replicates.

Choose h0<lambda_min(H) close enough that

\[
2\eta h_0>\frac1{1+\rho}.
\tag{N7}
\]

This is possible even at the critical eigenvalue because rho>0. By the local expansion, shrink a radius epsilon so that `x^TG(x)>=h0||x||^2` inside that ball. Choose

\[
\frac1{1+\rho}<\gamma<\min\{2\eta h_0,1\},\qquad
\beta=\gamma(1+\rho)/2>1/2.
\tag{N8}
\]

For each process and deterministic N, let tau_N be the first t>=N with `||X_t||>=epsilon`. Define the killed second moment `u_t^N=E[||X_t||^2 1{tau_N>t}]`. Dropping the indicator of remaining inside the ball after the current update only increases a nonnegative quantity. Since `{tau_N>t-1}` is predictable, (N6) with local h0 gives

\[
u_t^N\le(1-2\eta h_0/t+C_0/t^2)u_{t-1}^N+C_0/t^2,
\quad t>N.
\]

Comparison of this scalar recursion gives `u_t^N<=C_N t^(-gamma)` for fixed N (absorb finitely many initial indices). Almost-sure convergence implies

\[
P\{\text{any of the B+1 processes exits this ball at or after N}\}
\longrightarrow0\quad(N\to\infty).
\tag{N9}
\]

This localization is essential: a global moment rate based only on mu need not be fast enough. No unproved replacement of mu by the local Hessian in a global moment recursion is used.

## 3. Linearization with vanishing nonlinear and stochastic remainders

Write xi_t=g(0,Z_t), r(x)=G(x)-Hx. For a process with weight W define

\[
e_t(x)=W\{g(x,Z_t)-g(0,Z_t)\}-G(x).
\tag{N10}
\]

For a past-measurable x, `E[e_t(x)|F_(t-1)]=0`, and

\[
E[\|e_t(x)\|^2\mid F_{t-1}]
\le EW^2 L^2\|x\|^2.
\tag{N11}
\]

Thus the exact recursion is

\[
X_t=(I-\eta H/t)X_{t-1}
-\frac\eta t\{W\xi_t+r(X_{t-1})+e_t(X_{t-1})\}.
\tag{N12}
\]

After averaging, coordinate j's deterministic coefficient for an innovation at time t is

\[
b_{nt}(a_j)=\frac\eta{nt}\sum_{k=t}^n
 \prod_{r=t+1}^k(1-a_j/r).
\tag{N13}
\]

Products, rather than quotients of a global product, are used: early factors can be zero or negative when an eigenvalue is an integer or is large. Those finitely many factors cause no singularity.

For fixed a>=1/2 these elementary bounds hold, with constants depending on a,eta:

\[
|b_{nt}(a)|\le
\begin{cases}
C n^{-a}t^{a-1},&1/2\le a<1,\\
C n^{-1}(1+\log(n/t)),&a=1,\\
C/n,&a>1.
\end{cases}
\tag{N14}
\]

For t above the finite exceptional range, compare the product with C(t/k)^a; summing k proves (N14). The finite exceptional t are bounded separately. With s_n(a)=sqrt(n/log n) at a=1/2 and sqrt(n) otherwise, (N14) gives

\[
\max_{t\le n}|s_n(a)b_{nt}(a)|\to0,\qquad
\sup_n\sum_{t\le n}|s_n(a)b_{nt}(a)|^2<\infty.
\tag{N15}
\]

Fix N and truncate each remainder at the predictable event `{tau_N>t-1}` for t>N. The local expansion and Lyapunov's moment inequality give

\[
E[\|r(X_{t-1})\|1\{\tau_N>t-1\}]
\le C(u_{t-1}^N)^{(1+\rho)/2}\le C_N t^{-\beta}.
\tag{N16}
\]

For a=1/2, the expected absolute normalized nonlinear sum is at most
`C_N (log n)^(-1/2) sum_(t>N) t^(-beta-1/2)`, which tends to zero because beta>1/2. For 1/2<a<1, it is bounded by
`C_N n^(1/2-a) sum_(t>N)^n t^(a-1-beta)`; this also tends to zero, whether a is below, equal to or above beta. For a>=1, (N14) gives convergence to zero by the same elementary power-sum bounds; beta<=1 and beta>1/2. The finitely many t<=N terms vanish in probability by (N15) and finite-time moments.

For the truncated stochastic remainders, martingale orthogonality and (N11) bound the mean square of the normalized sum by

\[
C\sum_{t>N}|s_n(a)b_{nt}(a)|^2u_{t-1}^N\to0.
\tag{N17}
\]

To see the limit, split at a fixed large T: each of the finitely many early weights vanishes; the remaining sum is bounded by the supremum of u_t^N beyond T times the bounded sum in (N15). Again finite early terms vanish. On the no-exit event the truncated sums equal the actual tails. Taking first n to infinity, then N to infinity using (N9), proves that **all actual normalized remainders vanish in probability**. Multiplication by future no-exit indicators is never used to claim a martingale property.

The averaged initial-value coefficient is `n^(-1)sum_(k=1)^n product_(r=1)^k(1-a/r)`. It is O(n^(-a)) for a<1, O(log n/n) for a=1 and O(1/n) for a>1, with possible exact zeros. Its normalized contribution vanishes also at a=1/2 because of the extra sqrt(log n).

## 4. Joint Gaussian limit of the leading iid array

The leading innovations for the original and centered bootstrap differences are

\[
\zeta_t=(\xi_t,(W_t^1-1)\xi_t,\ldots,(W_t^B-1)\xi_t).
\tag{N18}
\]

They are iid over t, centered, have finite second moments, and covariance `I_(B+1) tensor Sigma`: EW=1, VarW=1 and independent replicate weights make the cross blocks zero. Finite-n independence between these blocks is neither assumed nor true in general.

The weight limits are

\[
\frac n{\log n}\sum_t b_{nt}(1/2)^2\to4\eta^2,
\]
\[
n\sum_t b_{nt}(a)b_{nt}(a')\to
\eta^2\frac{a+a'}{aa'(a+a'-1)}\quad(a,a'>1/2).
\tag{N19}
\]

For a=1/2 the product formula is the central-binomial identity from the bound scalar theorem, giving the harmonic-sum logarithm. For regular exponents, the pointwise kernel is

\[
\frac n\eta b_{n,\lfloor nx\rfloor}(a)\to
h_a(x)=\frac{1-x^{a-1}}{a-1},\quad
h_1(x)=-\log x.
\]

The bounds (N14) justify the Riemann-sum limit by controlling the small-x tail. Direct integration gives `integral_0^1 h_a h_a'=(a+a')/[aa'(a+a'-1)]`. One critical and one regular exponent also have a finite n-times cross-weight limit; their actual normalization divides that value by sqrt(log n), so the mixed covariance is zero.

The coefficient matrices of the iid triangular array have maximum norm tending to zero and bounded total squared norm by (N15). Finite second moment of zeta implies Lindeberg: bound each tail by `E||zeta||^2 1{||zeta||>epsilon/max coefficient}` times the bounded total squared norm. The multivariate triangular-array CLT and (N19) prove (N2) after the remainder bounds. Gamma is positive definite: on the regular block it is the integral of positive-definite Sigma quadratic forms weighted by the nonzero h_a; on the critical block it is4eta^2 times a positive principal submatrix; the mixed block is zero.

## 5. Student pivots, scope, and a genuinely nonlinear example

If ell has a nonzero critical projection, multiply its numerator and every bootstrap projection by sqrt(n/log n); the regular coordinates vanish and the remaining B+1 limits are independent equal-variance normals. If it has no critical projection, use sqrt n. This proves (N4). For (N5), the common invertible anisotropic transformation leaves the quadratic statistic unchanged. The Gaussian limit gives B independent uncentered outer products and hence the stated Wishart/F pivot. This is the same finite-B argument as in the audited quadratic theorem.

A concrete example satisfying the assumptions is

\[
f(x;Z,A)=\tfrac12x^2+(3+A)\log\cosh x-Zx,
\quad P(A=1)=P(A=-1)=1/2,
\]

with A independent of centered unit-variance Gaussian Z. The sample gradient is `x+(3+A)tanh(x)-Z`, globally5-Lipschitz; every sample loss is strongly convex with constant1. The mean Hessian at theta=0 is4. At eta=1/8 the local drift is exactly critical, while eta times the global convexity constant is only1/8. Thus a global-rate shortcut requiring eta*mu>1/4 would fail. The localized proof covers it, including its nonconstant stochastic gradient noise. Its normalized scalar covariance is1/16 and its unchanged fixed-B Student interval is asymptotically valid.

The argument neither removes the critical spectral condition nor repairs subcritical harmonic counterexamples. It supplies a nonlinear positive regime for the closed harmonic endpoint in [Lam and Wang](https://arxiv.org/html/2310.11065v2). The related [Fang, Xu and Yang online-bootstrap theorem](https://www.jmlr.org/papers/volume19/17-370/17-370.pdf) assumes a power exponent strictly between1/2 and1; it does not by itself state this critical harmonic result. Classical nonlinear SA localization may already provide much of the machinery. A focused theorem-level prior-art comparison and independent audit are required before claiming a new research contribution.

Bound prior source: `../critical_endpoint_20261027/spd_critical_spectrum_bootstrap_theorem_20261027.md`, SHA256 `44af0d68b27fc67e97557b7155fd48920423dbe0d65413347789f9a75a6d4c10`. The scalar critical weights are in `../critical_endpoint_20261027/critical_online_bootstrap_theorem.md`, SHA256 `b61ce8aec7b3dd187021c1788f74c21746a2e6cd4c0417dc145e34948d878e0d`.
