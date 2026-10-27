# Default-damping ASkotchV2 instability with the actual random power stepsize

27 October 2026. New result, awaiting independent audit. The preceding frozen Newton result is unchanged. This note proves a source-bound implementation failure with the **printed default Nyström damping** and the released ten-step random power-method stepsize. It also proves a matched correction. It is not a counterexample to the correctly evaluated algorithm's Theorem 17.

## 1. Supported configuration and claim

Use [`pratikrathore8/fast_krr`](https://github.com/pratikrathore8/fast_krr/tree/61cdb69cb11adea48ecb13c823ad654d46dc15df) at commit `61cdb69cb11adea48ecb13c823ad654d46dc15df`, the source pinned in the previous result. Select CPU `torch.float64`, `ASkotchV2`, uniform block size 2, and

```python
precond_params = {'type': 'nystrom', 'r': 2, 'rho': 'damped'}
```

Keep the acceleration parameters at their released defaults and keep the automatic stepsize routine unchanged. The [paper, Section 2.5 and Table 3, p11](https://www.jmlr.org/papers/volume27/25-0385/25-0385.pdf) recommends damping \(\rho=\lambda+\lambda_r(\widehat K_{BB})\), \(\mu=\lambda\), and \(\nu=n/b\). Block size and rank are chosen here to make a tiny valid example; this is not the rank-100, block-fraction-1/100 benchmark configuration. The argument uses the float64 branch; it does not transfer automatically to the float32 eigenvalue-floor behavior.

Set

\[
\lambda=\frac3{20000},\quad \delta=\frac1{10^7},\quad
c=1-\delta,\quad K=\delta I+c\mathbf1\mathbf1^T,\quad A=K+\lambda I.
\tag{1}
\]

This is the strictly positive definite RBF Gram matrix of an equilateral triangle of side \(\sqrt{-2\log c}\), using bandwidth one. Let

\[
w_*=(1,-1,0)^T,\qquad b=Aw_*=(\lambda+\delta)w_*=
\frac{1501}{10^7}(1,-1,0)^T,
\]

and initialize \(w_0=v_0=y_0=0\). The default parameters are

\[
\mu=\lambda,\quad \nu=3/2,\quad
s=\sqrt{\mu/\nu}=1/100,\quad
\beta=99/100,\quad \gamma=(\mu\nu)^{-1/2}=200/3,
\quad\alpha=1/101.
\tag{2}
\]

They satisfy both printed practical checks strictly: \(\mu<\nu\) and \(\mu\nu=9/40000<1\).

**Theorem.** In the exact-arithmetic interpretation of this released float64 branch, with fresh independent random draws as in the implementation, the released stale-regularization update satisfies, for every integer \(t\ge1\),

\[
\boxed{\mathbb E\|w_t-w_*\|^2\ge
\frac12\left(\frac{26}{25}\right)^{t-1}},\qquad
\boxed{\frac{\mathbb E\|w_t-w_*\|_A^2}{\|w_0-w_*\|_A^2}
\ge\frac14\left(\frac{26}{25}\right)^{t-1}.}
\tag{3}
\]

Replacing only the stale regularization term by the extrapolated regularization term gives geometric mean-square convergence on this same instance, under the same sampled Nyström sketches and random power estimates. A rational certificate below gives contraction factor \(99/100\) for a dominating covariance. No deterministic spectral stepsize replaces the released routine in this result.

## 2. Full-rank Nyström really yields the stated default damping

For each two-by-two block \(B=K_{JJ}\), its eigenvalues are \(\delta\) and \(2-\delta\). The rank-two Gaussian sketch is nonsingular with probability one. Its reduced QR factor \(\Omega\) is square orthogonal. The released stabilized Nyström construction uses \(h=\epsilon_{\rm mach}\operatorname{tr}(B)\), computes

\[
Y=(B+hI)\Omega,\quad LL^T=\Omega^T(B+hI)\Omega,
\quad F=YL^{-T},
\]

and then subtracts h from the squared singular values of F. Since

\[
FF^T=(B+hI)\Omega[\Omega^T(B+hI)\Omega]^{-1}\Omega^T(B+hI)=B+hI,
\]

the reconstructed matrix is exactly B. Its smallest eigenvalue is \(\delta>2^{-52}\), so the float64 eigenvalue-floor branch is inactive. Consequently the **actual default damping rule**, not a chosen substitute, sets

\[
\rho=\lambda+\delta=1501/10^7,
\qquad P_J=I_J^T(B+\rho I)^{-1}I_J.
\tag{4}
\]

The full-rank inverse's orthogonal-complement term vanishes exactly. Thus the preconditioner is independent of the Nyström sketch in exact arithmetic, apart from the probability-zero singular-sketch exception. This statement includes the code's stabilization shift rather than omitting it.

Source: [`preconditioners/nystrom.py`](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/preconditioners/nystrom.py), SHA256 `f8470b8ac5d20bf0d86a35815970e4bb92d34886b24e02290606329f9e844f74`.

## 3. Every output of the released ten-step power routine is covered

The preconditioned block operator is

\[
T_J=(B+\lambda I)(B+\rho I)^{-1}.
\]

Its factors commute, so it is symmetric positive definite with eigenvalues

\[
L_{\min}=\frac{\lambda+\delta}{\lambda+2\delta}=
\frac{1501}{1502},\qquad
L_{\max}=\frac{2-\delta+\lambda}{2+\lambda}=
\frac{20001499}{20001500}.
\]

At each of its ten iterations the released `_get_L` normalizes a vector and computes its Rayleigh quotient against this operator. The final quotient therefore lies between these two eigenvalues, for every nonzero initial vector. The returned stepsize is its reciprocal, so

\[
\boxed{\eta_J\in[\eta_-,\eta_+]
=\left[\frac{20001500}{20001499},\frac{1502}{1501}\right].}
\tag{5}
\]

There is no requirement that ten iterations accurately approximate \(L_{\max}\). The proof covers the entire interval, including either endpoint. The random start and Nyström sketch are independent of the current coefficient state; all three blocks have the same numerical block matrix. Thus the stepsize law is identical for each block and invariant under permutations of the three examples. Fresh random draws give the state-independent covariance transition used below.

Source: [`opts/utils/general.py:13–28`](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/opts/utils/general.py#L13-L28), SHA256 `17f5acbe8e693579e302ca5ac5dd18145b4a5b6f2878525f518098285dce7f51`.

## 4. Exact update and a uniform polynomial certificate

For errors \(e=w-w_*\), \(f=v-w_*\), let \(Y(e,f)=(e+sf)/(1+s)\). The released update is

\[
\begin{aligned}
g(e,f)&=KY(e,f)+\lambda e,\\
e'&=Y(e,f)-\eta_JP_Jg(e,f),\\
f'&=(1-s)f+sY(e,f)-\gamma\eta_JP_Jg(e,f).
\end{aligned}
\tag{6}
\]

The corrected update changes only \(g\) to \(AY(e,f)\). Write \(M_J(\eta)\) for the corresponding rational 6-by-6 matrix. It is affine in \(\eta\). For an arbitrary triple \(\boldsymbol\eta=(\eta_{01},\eta_{02},\eta_{12})\) in (5), define

\[
\Phi_{\boldsymbol\eta}(C)=\frac13\sum_JM_J(\eta_J)C M_J(\eta_J)^T.
\tag{7}
\]

Let \(E=\mathbf1\mathbf1^T/3\), \(P=I-E\), and

\[
\mathcal C(a,b,c_0,d,e,f)=
\begin{pmatrix}aP+bE&c_0P+dE\\c_0P+dE&eP+fE\end{pmatrix}.
\]

Use

\[
C_0=\mathcal C(1,0,1,0,1,0),\qquad
C_*=\mathcal C(1,0,61/2,0,2810,0).
\]

The exact certificate establishes, **simultaneously for every triple** \(\boldsymbol\eta\) in the interval cube,

\[
C_*\succeq0,\quad
\Phi^{\rm stale}_{\boldsymbol\eta}(C_*)\succeq\frac{26}{25}C_*,\quad
\Phi^{\rm stale}_{\boldsymbol\eta}(C_0)\succeq\frac14C_*.
\tag{8}
\]

Here is why a finite certificate proves the universal quantifier. For a fixed block and fixed covariance C, put \(A_J(\eta)=M_J(\eta)CM_J(\eta)^T\). At \(\eta(t)=(1-t)\eta_-+t\eta_+\), this is an exact quadratic matrix polynomial. Its Bernstein coefficient matrices are

\[
B_{J,0}=A_J(\eta_-),\quad B_{J,2}=A_J(\eta_+),\quad
B_{J,1}=2A_J((\eta_-+\eta_+)/2)-\tfrac12(B_{J,0}+B_{J,2}).
\]

For each desired residual \(\Phi(C)-D\), the tensor Bernstein coefficients on the three-dimensional cube are the **27** matrices

\[
\frac13\sum_J B_{J,i_J}-D,\qquad (i_{01},i_{02},i_{12})\in\{0,1,2\}^3.
\tag{9}
\]

If all are positive semidefinite, the residual is positive semidefinite everywhere, because every tensor Bernstein weight is nonnegative and the weights sum to one. This is not a grid check. It even permits different stepsizes for the three blocks.

For both stale residuals in (8), all 27 coefficient matrices annihilate \(z=(-\gamma\mathbf1,\mathbf1)\). The checker uses a fixed rational basis for \(z^\perp\) and proves each resulting five-by-five matrix strictly positive definite by exact LDL factorization. It verifies the null-vector identities and each LDL reconstruction. These finite identities prove (8) in the full six-dimensional state space.

The code uses only Python `Fraction`. All rational pivots are preserved in `uniform_stepsize_certificate.json`; `check_uniform_stepsizes.py` generates and verifies them independently from (4) and (6). Floating-point eigenvalues, sampled stepsizes and trajectory averages play no role in this proof.

## 5. Deterministic zero start and the actual random law

The true initial error is \((-u,-u)\), \(u=(1,-1,0)\). Averaging its rank-one covariance over the six permutations gives exactly C0. The actual released transition law is permutation equivariant: uniform blocks, identical numerical block kernels and fresh identically distributed normal draws ensure this. The expected squared norm and A-energy are themselves invariant. Hence their expectations from the true deterministic initialization equal those calculated from C0; labels or initialization are not randomly chosen in the example.

Integrating (8) over the actual stepsize law preserves the inequalities. The mean covariance operator is positive. Induction yields

\[
\mathbb E[C_t]\succeq\frac14(26/25)^{t-1}C_*.
\]

Taking the top-left trace proves (3), because that block of C* is P and \(A P=(\lambda+\delta)P\). The certificate's stronger cube statement is valid for any state-independent block-conditional stepsize distributions in (5); the stated fixed-initialization conclusion uses the actual permutation-equivariant released law. No claim is made for arbitrary state-dependent or history-selected stepsizes.

## 6. Same sampled stepsizes, isolated correction, uniform contraction

Define the rational positive definite matrix

\[
\bar C=\mathcal C\left(
\frac{55254681}{500000},\frac{1010101}{1000000},
\frac{365527821}{100000},\frac{224}{15625},
\frac{183751413061}{500000},\frac{38311211}{6250}
\right).
\]

The checker proves

\[
\bar C\succ0,\qquad \bar C-2C_0\succ0,
\qquad
\frac{99}{100}\bar C-\Phi^{\rm corrected}_{\boldsymbol\eta}(\bar C)\succ0
\quad\hbox{for every allowed triple}.                     \tag{10}
\]

The last statement uses another 27 tensor Bernstein coefficient matrices, each strictly positive definite by an exact full six-by-six LDL factorization. The single deterministic initial covariance is bounded above by 2C0: if \(v=(1,1,-2)\), then \(2P-uu^T=vv^T/3\). Thus the corrected covariance is bounded above by \((99/100)^t\bar C\), and the corrected coefficient error converges geometrically in mean square. This proof does not rely on symmetrization for the corrected conclusion.

The only correction is in [`models/full_krr.py:43`](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/models/full_krr.py#L43): use the function's evaluation argument in its regularization term, rather than stored `self.w`. The paired reproduction adds exactly \(\lambda(y_J-w_J)\), leaving the preconditioner and power stepsize untouched. These routines depend on the data and fresh random draws, not the gradient, so paired random seeds give identical sampled stepsizes in both versions. The correction is not claimed to stabilize arbitrary acceleration heuristics on every dataset.

## 7. Verification boundary

`check_uniform_stepsizes.py` proves the 81 universal coefficient conditions with exact rational arithmetic and binds the source files. `check_released_damped_interface.py` executes the actual released rank-two **damped** Nyström preconditioner and its actual ten-step random power routine on CPU in float64. It covers all three blocks, all six native state directions, the fixed point and the reachable zero-start state in both versions. It records every returned random stepsize and compares the actual output with (6) evaluated at that observed stepsize. It also verifies that the paired corrected and released runs use exactly the same randomized preconditioner and stepsize.

This is an exact-arithmetic mean-square instability result with a numerical source-interface check. It is not an assertion about infinite-time finite-precision trajectories, almost-sure divergence, every random block sequence, typical runtime, or the paper's benchmark rankings. The printed damping and acceleration defaults are used; the small block/rank and float64 choices are explicit. In particular, this delta is below float32 machine epsilon, so the release's float32 eigenvalue floor would require a separate analysis. The theoretical block/sampling/spectral hypotheses of Theorem 17 are not asserted. No frozen source has been changed, and nothing has been published or sent externally.
