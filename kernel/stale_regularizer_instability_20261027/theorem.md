# A three-point RBF instance with mean-square instability in released ASkotchV2

Date: 2026-10-27. Status: an exact finite rational certificate for a **code-level correction**, awaiting independent review. This does not refute the convergence theorem for the correctly evaluated algorithm. No source files were modified and nothing was submitted externally.

## 1. Precisely identified implementation and claim

The inspected repository is [`pratikrathore8/fast_krr`](https://github.com/pratikrathore8/fast_krr/tree/61cdb69cb11adea48ecb13c823ad654d46dc15df), commit `61cdb69cb11adea48ecb13c823ad654d46dc15df`. A read-only `git ls-remote origin HEAD` on 2026-10-27 returned this same commit; the pinned source is therefore also the then-current repository HEAD.

[`fast_krr/models/full_krr.py:39–43`](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/models/full_krr.py#L39-L43) accepts an evaluation argument `w`, but its regularization term uses the stored `self.w`. When the accelerated optimizer passes its extrapolated point, this produces

\[
g_B=I_B(Ky+\lambda w-b)
\quad\hbox{instead of}\quad
I_B((K+\lambda I)y-b).
\tag{1}
\]

This note strengthens the previous two-point slow-convergence example: a supported exact block preconditioner, the printed default acceleration parameters, and a valid three-point RBF kernel give **exponentially diverging expected squared coefficient error from the usual zero initialization**. Replacing only the stale regularization term makes this same example converge in mean square.

Source bindings:

| File | SHA256 |
|---|---|
| `fast_krr/models/full_krr.py` | `3b853b5fff803ab20796cf5c0373c882afcb7fe2ef03065343f868ee76dfc1e6` |
| `fast_krr/opts/askotchv2.py` | `dead2dc97aed91e485133dc39e86f1980053b3372d67ca4540612366750f3cad` |
| `fast_krr/opts/utils/bcd.py` | `18d1c33169965f9dc3cb2ea8458d0da5795a9ed96d4ebae2ab1a376dfc6ea17d` |
| `fast_krr/opts/utils/general.py` | `17f5acbe8e693579e302ca5ac5dd18145b4a5b6f2878525f518098285dce7f51` |
| `fast_krr/preconditioners/newton.py` | `db03b8aee93490276a6809278ec9bb12e0765c134a37c06a455b4fc7d6cdceac` |

## 2. Kernel, labels, initialization and all optimizer choices

Let

\[
n=3,\quad b_{\rm size}=2,\quad
c=\frac{99999}{100000},\quad
K=(1-c)I+c\mathbf1\mathbf1^T,\quad
\lambda=\frac3{20000},\quad A=K+\lambda I.
\tag{2}
\]

This is a strictly positive definite, unit-diagonal RBF Gram matrix. For the kernel \(k(x,z)=\exp(-\|x-z\|^2/2)\), take an equilateral triangle of side \(d=\sqrt{-2\log c}>0\):
\(x_1=(0,0), x_2=(d,0), x_3=(d/2,\sqrt3d/2)\).

Use regression labels

\[
b=A(1,-1,0)^T=\frac1{6250}(1,-1,0)^T.
\]

The unique target is \(w_*=(1,-1,0)^T\). Initialize the released native state at \(w_0=v_0=y_0=0\). Sample each of the three two-element subsets independently and uniformly. Set `precond_params={'type':'newton','rho':'regularization'}` and use the released automatic stepsize. This supported preconditioner is exactly \((K_{BB}+\lambda I)^{-1}\); the preconditioned operator is the identity, so every power iteration gives \(L_B=1\) in exact arithmetic, independently of its random starting vector. Thus the block stepsize is exactly one.

Use the unmodified default acceleration settings

\[
\mu=\lambda,\quad \nu=n/b_{\rm size}=\frac32,\quad
s=\sqrt{\mu/\nu}=\frac1{100},\quad
\beta=1-s=\frac{99}{100},\quad
\gamma=(\mu\nu)^{-1/2}=\frac{200}{3},\quad
\alpha=\frac1{1+\gamma\nu}=\frac1{101}.
\tag{3}
\]

Both practical restrictions printed in [the paper, Section 2.5, p.11](https://www.jmlr.org/papers/volume27/25-0385/25-0385.pdf) hold strictly: \(\mu<\nu\) and \(\mu\nu=9/40000<1\). These two checks are not the spectral assumptions of Theorem 17. Neither the Newton option nor this small default-parameter example is asserted to satisfy all of that theorem's block, sampling, rank or parameter requirements. The theorem concerns the correct regularized gradient.

## 3. Exact native error update

Write \(e=w-w_*\), \(f=v-w_*\), and

\[
y-w_*=(e+sf)/(1+s)=:Y(e,f),\qquad
P_B=I_B^T(K_{BB}+\lambda I)^{-1}I_B.
\]

Since \(Aw_*=b\), the released update is exactly linear in the errors:

\[
\begin{aligned}
g(e,f)&=K Y(e,f)+\lambda e,\\
e'&=Y(e,f)-P_Bg(e,f),\\
f'&=(1-s)f+sY(e,f)-\gamma P_Bg(e,f).
\end{aligned}
\tag{4}
\]

Denote its rational \(6\times6\) matrix by \(M_B\). The corrected update has the same expression with only \(g(e,f)=A Y(e,f)\). All matrices in (4) are rational. The explicit inverse of each two-by-two block is

\[
(K_{BB}+\lambda I)^{-1}
=\frac1{(1+\lambda)^2-c^2}
\begin{pmatrix}1+\lambda&-c\\-c&1+\lambda\end{pmatrix}.
\tag{5}
\]

For any error covariance \(C\), define the positive linear operator
\(\Phi(C)=\frac13\sum_B M_B C M_B^T\). Fresh uniform blocks give \(C_t=\Phi^t(C_0)\).

## 4. A small exact certificate proving divergence

Let \(E=\mathbf1\mathbf1^T/3\) and \(P=I-E\). The permutation-invariant covariance family is

\[
\mathcal C(a,b,c_0,d,e,f)=
\begin{pmatrix}
aP+bE&c_0P+dE\\c_0P+dE&eP+fE
\end{pmatrix}.
\tag{6}
\]

Positivity reduces to positivity of the two real symmetric matrices
\(\begin{psmallmatrix}a&c_0\\c_0&e\end{psmallmatrix}\) and
\(\begin{psmallmatrix}b&d\\d&f\end{psmallmatrix}\).

Define

\[
C_{\rm init}=\mathcal C(1,0,1,0,1,0),\qquad
C_*=\mathcal C(1,0,61/2,0,2810,0).
\]

The following three finite inequalities are the certificate:

\[
C_*\succeq0,\qquad
\Phi_{\rm stale}(C_*)\succeq\frac{26}{25}C_*,\qquad
\Phi_{\rm stale}(C_{\rm init})\succeq\frac14 C_*.
\tag{7}
\]

They are proved by direct rational substitution of (4)–(6). The standalone checker `check_exact_instability.py` performs these substitutions and verifies every two-by-two principal minor using `fractions.Fraction`, with no floating-point calculations, eigenvalue solver or Monte Carlo test. The complete rational matrices and minors are in `exact_certificate.json`.

For a compact independently checkable sign summary: the contrast-block leading entry and determinant in the second inequality of (7) are respectively

\[
\frac{31163136304040879}{5876598637431302400}>0,
\qquad
\frac{3060551551054667060974213}{71936619240524058938880000}>0.
\]

Its common block is
\(\frac{1354775}{918218537098641}(1,\gamma)^T(1,\gamma)\), hence positive semidefinite. For the third inequality, the contrast-block leading entry and determinant are

\[
\frac{90002999897}{360050401764}>0,
\qquad
\frac{16212440101321079}{51847257854016}>0,
\]

and its common block is
\(\frac{128}{90012600441}(1,\gamma)^T(1,\gamma)\).

The actual initial state is the deterministic vector \((-u,-u)\), \(u=(1,-1,0)\). Averaging its covariance over the six coordinate permutations gives exactly \(C_{\rm init}\). Both the transition law and \(\|e\|^2\), \(e^TAe\) are permutation invariant. Consequently their expectations for the actual deterministic initialization equal their expectations under this symmetrized covariance. This is a proof device, not a randomized initialization or random-label assumption.

Positivity of \(\Phi\) and (7) now give, for every integer \(t\ge1\),

\[
\Phi_{\rm stale}^{t}(C_{\rm init})
\succeq\frac14\left(\frac{26}{25}\right)^{t-1} C_*.
\]

Taking the trace of the top-left block proves

\[
\boxed{\mathbb E\|w_t-w_*\|^2
\ge\frac12\left(\frac{26}{25}\right)^{t-1}\longrightarrow\infty.}
\tag{8}
\]

Because \(A=\frac1{6250}P+\frac{300013}{100000}E\), the expected energy error also diverges, with the normalized bound

\[
\boxed{\frac{\mathbb E\|w_t-w_*\|_A^2}{\|w_0-w_*\|_A^2}
\ge\frac14\left(\frac{26}{25}\right)^{t-1}.}
\tag{9}
\]

This is mean-square divergence. No claim of almost-sure divergence, divergence of every block sequence, or typical finite-run failure is made.

## 5. Changing just the stale term restores contraction here

The separate patch `fix_stale_regularizer.patch` changes only the stored iterate to the evaluation argument in the regularization term. It is not applied to the pinned checkout. The CPU reproduction uses the equivalent subclass correction \(\lambda(y_B-w_B)\); all solver options, labels and inputs are otherwise identical.

For a second exact certificate, set

\[
\bar C=\mathcal C\left(
\frac{49101403}{500000},\frac{1010101}{1000000},
\frac{810265583}{250000},-\frac{33}{25000},
\frac{65082583763}{200000},\frac{4994384331}{1000000}
\right).
\]

Direct rational principal-minor checks establish

\[
\bar C\succ0,\qquad \bar C-C_{\rm init}\succ0,\qquad
\frac{99}{100}\bar C-\Phi_{\rm corrected}(\bar C)\succ0.
\tag{10}
\]

Thus \(\Phi_{\rm corrected}^{t}(C_{\rm init})\preceq(99/100)^t\bar C\), and the same zero-start instance converges geometrically in mean square after the single-term correction. This is a matched correction, not a simultaneous change of acceleration parameters, kernel, preconditioner or block distribution. The correction is not claimed to make arbitrary heuristic acceleration parameters safe on every kernel.

## 6. Reproduction and limits

Run `python3 check_exact_instability.py` for the exact proof certificate. `check_official_interface.py` executes the pinned released optimizer on CPU in `torch.float64`, enumerating all three blocks, each of six native state-basis directions, the fixed point and the reachable zero-start state. It compares the actual one-step output with (4), then repeats with only the regularization correction. Block selection is controlled solely to exhaust all three cases; the gradient, preconditioner, automatic stepsize and update code execute normally. A fresh source hash and the recorded interface error are saved in `official_interface_certificate.json`.

The finite exact certificate establishes the mathematical claim; floating-point checks establish the link to the inspected implementation. An infinite-time finite-precision execution is not asserted. This example uses the supported Newton preconditioner to make the step completely transparent; it does not establish the same conclusion for every Nyström rank or damping choice, nor explain the paper's benchmark results. The new result is a source-bound failure of mean-square convergence for the released accelerated implementation, plus an isolated corrective change. Novelty and author acceptance remain unassessed.
