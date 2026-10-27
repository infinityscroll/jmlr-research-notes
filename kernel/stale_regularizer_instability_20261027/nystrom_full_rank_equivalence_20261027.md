# Exact full-rank Nyström equivalence for the three-point construction

Date: 2026-10-27. This is an analytic configuration-equivalence addendum, not a new experiment or a claim about Theorem 17's hypotheses. The original Newton theorem remains unchanged at SHA256 `31310da5f52c1ac30237f83b24a16b5d1c1ad4fe8acca10a173aebc5b92659d4`.

Use the same three-point RBF kernel, block size two and all parameters from `theorem.md`, but select the supported option

```python
precond_params = {'type': 'nystrom', 'r': 2, 'rho': 'regularization'}
```

The inspected implementation is [`fast_krr/preconditioners/nystrom.py`](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/preconditioners/nystrom.py) at the same pinned commit, file SHA256 `f8470b8ac5d20bf0d86a35815970e4bb92d34886b24e02290606329f9e844f74`. The constructor accepts this option; the block routine passes the two-by-two block operator into `Nystrom.update`.

Let \(B=K_{JJ}\) denote any positive definite two-by-two block and let \(h=\epsilon_{\rm mach}\operatorname{tr}(B)\) be its computed stabilization shift. With rank equal to the block size, the Gaussian sketch is nonsingular with probability one. Its reduced QR factor \(\Omega\) is a square orthogonal matrix. Ignoring rounding while retaining the specified shift as a fixed positive scalar, the implementation forms

\[
Y=(B+hI)\Omega,\quad LL^T=\Omega^T(B+hI)\Omega,\quad F=YL^{-T}.
\]

Consequently

\[
FF^T=(B+hI)\Omega[\Omega^T(B+hI)\Omega]^{-1}\Omega^T(B+hI)
=B+hI.
\]

The code computes the SVD of \(F\), squares its singular values, and subtracts \(h\). Therefore its reconstructed positive matrix is exactly \(B\): \(U\operatorname{diag}(S)U^T=B\). Here the two eigenvalues of \(B\) are \(1-c=10^{-5}\) and \(1+c\); both exceed the float64 threshold \(\epsilon_{\rm mach}\). The code's subsequent replacement of eigenvalues below that threshold by `1e-4` is therefore inactive in the exact-arithmetic interpretation. No clipping changes the result.

With `rho='regularization'`, the damping is exactly \(\lambda\). In the float64 branch, the inverse map is

\[
U\operatorname{diag}((S+\lambda)^{-1})U^T v
+\lambda^{-1}(v-UU^Tv)
=(B+\lambda I)^{-1}v,
\]

because the square \(U\) is orthogonal. Thus the preconditioned operator in the automatic stepsize routine is again the identity and its estimated \(L\) is exactly one in exact arithmetic. The transition matrices, both rational covariance certificates, and zero-start conclusion in `theorem.md` are unchanged, with probability one over the square sketches.

This establishes a literal supported **full-rank Nyström with regularization damping** counterpart to the Newton construction. It does not cover `rho='damped'`, a rank-deficient approximation, the paper's rank-100 benchmark settings, or floating-point bitwise equivalence. The existing numerical interface certificate executes Newton only. The mathematical equivalence above requires no additional experiment and does not supply the other hypotheses of Theorem 17.
