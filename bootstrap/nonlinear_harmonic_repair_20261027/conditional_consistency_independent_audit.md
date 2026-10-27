# Audit of conditional bootstrap consistency

27 October 2026. Audited source: `conditional_bootstrap_consistency.md`, SHA256 `3ffcd898d38714e72f41b8a83a61dea59246c780b2119d6e3d29e9223b99c0bf`. Its two linearization dependencies are the source-bound nonlinear theorem `6eaae8f09c1266cbe1a7b4aab31421f602e9bd409175ae1f7408f5452ab61bb5` and mean-square extension `8cf2b32cae345521e8699466f4441801a37809cda5ad1cc0311b6d69d50a4840`, audited separately in this folder.

**Verdict: no blocking error found.** The argument proves conditional weak convergence in probability under the stated assumptions. It does not prove almost-sure conditional convergence of the full sequence. No repair is requested, and no bound source was changed.

## 1. The conditioning sigma field is correct

The conditioning field is `D_n=sigma(Z_1,...,Z_n)`, excluding all bootstrap multipliers. With the fixed initial point and deterministic update rule, the original trajectory and its final average are measurable with respect to this field. Each perturbed trajectory retains its independent multiplier sequence as its only conditional randomness. Thus the leading terms in (C3) are independent and centered across times under the conditional law.

This is different from conditioning on the full algorithmic history, which would reveal multiplier information and invalidate the proposed independent triangular array. The source does not make that mistake. Its normalizations and covariance parameters are deterministic population quantities, so conditioning does not randomize the coefficients or the target limiting law.

## 2. Finite second moments suffice for covariance convergence

For integrable iid scalar Y_t, write `Y_t=Y_t 1{|Y_t|<=M}+Y_t 1{|Y_t|>M}`. The variance of the centered, bounded weighted sum is at most

\[
M^2\sum_t c_{nt}^2
\le M^2\max_t|c_{nt}|\sum_t|c_{nt}|\longrightarrow0.
\]

The expected absolute tail sum is at most

\[
2\Big(\sup_n\sum_t|c_{nt}|\Big)E[|Y|1\{|Y|>M\}].
\]

Letting n and then M grow proves the source's L1 weighted law of large numbers. Neither nonnegative weights nor a finite variance for Y is necessary.

In its application `Y_t=xi_(t,i)xi_(t,j)`, integrability follows from Cauchy--Schwarz and the second moments of xi. For `c_nt=d_(nt,i)d_(nt,j)`, Cauchy--Schwarz bounds the total absolute weight by the geometric mean of the two squared-weight sums, and the maximal product weight vanishes. Consequently the empirical conditional covariance differs from its deterministic expectation by a quantity tending to zero in L1, entrywise. The previously proved deterministic limits give Gamma, including the zero critical/regular block. Signed early product weights do not cause a problem.

## 3. Conditional Lindeberg and the mode of convergence

Let `A_n=max_t||D_nt||` and `Zeta=(W-1)xi`. Then

\[
\|D_{nt}\,Zeta\|^2 1\{\|D_{nt}Zeta\|>\epsilon\}
\le \|D_{nt}\|^2\|Zeta\|^2
1\{\|Zeta\|>\epsilon/A_n\}.
\]

Summing and averaging over the data proves (C5). The squared norm of Zeta is integrable because the multiplier and observation are independent and both have finite second moments. The resulting expectation tends to zero, so the nonnegative conditional Lindeberg sum tends to zero in probability.

From any subsequence, one can extract a further subsequence on which the covariance and Lindeberg conditions hold almost surely, simultaneously for all positive rational thresholds. Monotonicity supplies the other thresholds. On that probability-one event, the conditional distributions form an ordinary deterministic triangular array with independent summands and satisfy the multivariate Lindeberg--Feller theorem. Their conditional laws converge weakly, and hence in bounded-Lipschitz distance, to the stated Gaussian.

The subsequence criterion yields convergence **in probability** of the random conditional laws along the original sequence. The almost-sure statement is only about an extracted subsequence; promoting it to almost-sure convergence of the full sequence would be unjustified. The source preserves this distinction.

## 4. The nonlinear remainder transfers without fresh localization

For the actual untruncated remainder R_n already proved negligible,

\[
E\,P(\|R_n\|>\epsilon\mid D_n)
=P(\|R_n\|>\epsilon)\to0.
\]

The conditional tail therefore tends to zero in L1 and in probability. More directly, boundedness and convergence in probability imply `E min(2,||R_n||)->0`. Conditioning and using the same multipliers to couple the actual statistic with its linear approximation gives

\[
d_{\rm BL}(\mathcal L(L_n+R_n\mid D_n),
             \mathcal L(L_n\mid D_n))
\le E[\min(2,\|R_n\|)\mid D_n]\xrightarrow{P}0.
\]

No independence between R_n and L_n is required. No conditional distributional limit for the original data-measurable estimator is assumed. In particular, the original estimator is correctly treated as a fixed center given D_n.

Given D_n, the actual B replicate trajectories are independent functions of independent multiplier sequences. The fixed-B product-law conclusion follows from the single-replicate convergence, or from the same stacked-array argument. Common observations and the common original center do not invalidate this conditional independence.

## 5. Conclusion and boundaries

The note closes the earlier conditional-consistency restriction under the already audited growth, mean-square continuity, stability and spectral conditions. Its proof uses classical weighted-LLN, triangular-array and conditional-probability arguments. It establishes neither finite-sample coverage nor a convergence rate, growing-B behavior, uniformity near a changing spectral boundary, offline-bootstrap validity, or historical novelty.
