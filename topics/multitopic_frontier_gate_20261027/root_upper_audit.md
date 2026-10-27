# Independent analytic review of the general-K upper bound

27 October 2026. Root read the entire source and reconstructed its inequalities independently. This is an internal mathematical review, not external peer review or a formal proof-assistant certificate.

Bound source: `general_k_upper.md`, SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`.

**Verdict:** no mathematical blocker found for the exact fixed-p,K statement. The accompanying lower bound must be restricted to its own p=K+10 domain. No growing-dimension, unknown-alpha, or computational-efficiency conclusion follows from this review.

## Checks that carry the claimed rate

1. **Exact decomposition and anisotropic leverage.** With E=(1/n)sum epsilon_i w_i' Sigma^(-1/2), multiplication by V=A Sigma^(1/2) reproduces both first-order pair-moment terms exactly. Completing the Gram matrix gives Chat=(V+E)(V+E)'+Qbar-EE'. The fixed-design identity sum w_i'Sigma^(-1)w_i=nK removes a spurious inverse-beta factor from the variance of E. The pointwise prevalence bound pi_ij<=d_j/mu0 is valid because each w_ki<=1 and d_j=sum A_jk mu_k.

2. **Degenerate-pair variance, including diagonal entries.** For centered independent categorical tokens, only equal or reversed ordered pairs survive in the covariance expansion. Their sum is [Var(T_j)Var(T_r)+Cov(T_j,T_r)^2]/[N(N-1)]. The diagonal becomes 2Var(T_j)^2/[N(N-1)] and obeys the stated bound. This is a variance bound for the degenerate remainder, not for the entire raw pair matrix. The EE' row remainder is controlled by Cauchy–Schwarz; 1/(nN)<=1/sqrt(nN(N-1)) for all n>=1,N>=2.

3. **No hidden eigenvector alignment assumption.** On E0, sigma_min(V+E)>=kappa0 sqrt(beta)/2. For H=(V+E)'Uhat, the identity H'H=Lambda_hat-Uhat'R Uhat yields the floor kappa0^2 beta/8 directly. It does not assume the observed eigenbasis is close to a particular population basis. The invertible analysis-only map T=H^(-1)Sigma^(-1/2)diag(mu) then gives the exact row identity Zhat T=A diag(mu)+D. Its first-order error pays beta^(-1/2); its degenerate remainder pays beta^(-1). Both factors are necessary in the displayed derivation, with no further condition-number assumption.

4. **The estimator does not use the unobserved map.** Right multiplication by any invertible T multiplies every candidate determinant by det(T). Thus the maximizing tuple, including deterministic ties, is unchanged. Reconstruction Zhat Rhat_I^(-1) is exactly invariant. This justifies using random, unobserved population coordinates in the analysis without defining an oracle estimator.

5. **Screening and small masses.** The good screening event retains every designated anchor of mass at least alpha. Every retained row has population mass at least alpha/4 and empirical mass at least half its population mass. False-inclusion and missed-anchor probabilities are at most fixed-p constants times 1/sqrt(nNalpha). Zero-mass rows are deterministically zero. The row error after division has expected maximum at most C a_n/sqrt(alpha); taking a finite maximum by a sum is legitimate only because p is fixed.

6. **Maximum-volume perturbation is linear, not square-root.** The original selected stochastic matrix has determinant at least 1-Crho. Hadamard bounds force every row's squared norm, hence its largest entry, to be at least 1-Crho. Each row is therefore O(rho) from a vertex. Two rows near the same vertex would force determinant O(rho), contradicting the lower bound. This proves the near-permutation claim without an anchor-versus-near-anchor gap. A small perturbation of that permutation has bounded inverse.

7. **Expected loss includes every failure event.** G13-G16 control E0 failure, screening failure and excessive normalized error. Reconstruction has L1 error bounded by sum delta_j+rho on the intersection. Clipping does not increase distance to a nonnegative target. For a target column of mass mu_k, normalization costs at most 2/mu_k, including the zero-column fallback. The output is always stochastic and has loss at most 2K, so integrating on the good event and bounding its complement proves the displayed clipped risk bound. There is no illicit conditioning of mean-zero noise after selection.

## Limits on what this review establishes

The proof uses classical linear algebra, multinomial moment identities and simplex geometry. Its potentially useful conclusion is the uniform parameter dependence, not the invention of those tools. The constants may depend on p,K,mu0,kappa0 and therefore do not settle the growing-vocabulary short-document problem. The estimator enumerates K-row subsets in exact arithmetic and knows alpha. Independent specialist assessment of prior work is still required before calling the matched rate new.
