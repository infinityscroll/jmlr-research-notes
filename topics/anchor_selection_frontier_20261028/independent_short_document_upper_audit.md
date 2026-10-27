# Independent audit of the sharp short-document anchor upper bound

28 October 2026. Analytic review of `short_document_sharp_log_upper.md`, SHA256 `db1e141e00097be07ad8d884bbe4bda13b2ad098a32445d5ab0d5847876daf8d`. The source and its held dependencies were not edited. This audit does not certify historical novelty or an all-N result with the remainder removed.

**Verdict:** no blocking mathematical issue found within the stated assumptions. The square-root logarithm follows from applying a Hilbert Bernstein inequality to independent whole-document degenerate rows. Its remainder is retained and absorbed only on the explicitly stated domain. The observed-eigenvalue cutoff is analyzed at the actual mixture eigenvalue before passing to the class floor.

## 1. Document concentration

The centered row Q_i,j is an ordered degenerate U-statistic, not a sum of independent overlapping pairs. Its exact variance bound is at most2 pi_ij/[N(N-1)]. For every summand, the scalar coordinate of the centered one-hot token has absolute value at most1, and the vector factor has norm at most sqrt(2); hence the triangle inequality gives ||Q_i,j||<=sqrt(2). Different documents are independent. Applying the held Hilbert Bernstein inequality to Q_i,j/n therefore uses variance at most2d_j/[nN(N-1)] and increment bound sqrt(2)/n. This gives S7, including the **r/n** term. No additional factor N is available from this particular argument.

Combining the held first-order whitened-row moment bound, its factor1/sqrt(b), the degenerate-row factor1/b, and scalar frequency concentration gives S8. Since b<=trace(Sigma)<=1, the scalar and first-order remainders are bounded by the displayed r/(nb). The original dimension-free second moments remain valid and are not replaced by a weaker maximum bound.

## 2. Candidate multiplicity and false inclusions

For J_*={j:d_j>=alpha/4}, every included row contributes at least1/4 to R_alpha(d). Thus |J_*|<=4R_alpha(d), and the choice r=max{2,log(4R_alpha(d))} bounds the Lr maximum factor by e. Dividing the row error by d_j>=alpha/4 yields S10 with the two distinct terms sqrt(L)a(b)/sqrt(alpha) and L/(nbalpha).

For rare rows d_j<alpha/4, their total mass is at most alpha R_alpha(d). The generating-function bound therefore sums to2xR_alpha(d)exp(-cx), x=nNalpha. If x<=C0L, bounded probability is at most C sqrt(L/x). Otherwise R_alpha(d)<=exp(L)<=exp(cx/2), so2xexp(-cx/2) is at most C/sqrt(x). This proves S12 without a vocabulary-size union bound or an unproved independence assumption. Zero-frequency rows cannot be falsely selected.

The layer-cake identity R_alpha(d)=alpha^-1 integral_0^alpha #{j:d_j>=t}dt is exact for finite vocabularies and extends by monotone convergence. Thus the weak-q and p caps in S15 are valid. The constants may depend on fixed q and the radius, as stated.

## 3. Reconstruction and the observed cutoff

On the same good spectral event defined at actual b=lambda_min(Sigma), the held coordinate representation and maximum-volume lemma give a single permutation for the entire matrix, with row error C(delta_j+d_j rho). A small rho retains each true anchor and bounds its frequency denominator. The event F^c prevents an unexamined rare row from entering the selection.

The eigenvalue comparison c0 b<=lambda_K(Chat)<=C0 b gives deterministic constant-factor bounds on the random output cutoff. Consequently the indicator domination and second-moment truncation argument from `observable_conditioning_threshold.md` still apply to the retained rows without conditioning on the random threshold. Clipping, normalization and zero-column fallback retain their held bounded-loss guarantees.

Only after this argument is completed at actual b does the proof use b>=beta. Every risk term is monotone in a(b) or1/b, so the passage to the beta floor is legitimate. The estimator does not need to know that floor. In particular it is not necessary that actual b satisfy the short-document inequality.

## 4. Remainder and scope

With r0=sqrt(L)a(beta)/sqrt(alpha), the assumption N(N-1)beta<=1 implies

    L/(n beta alpha)
      <=L/[nN(N-1)beta^2alpha] <=r0^2.

The remainder is absorbed when r0<=1; bounded loss handles r0>1. This is a valid case split, not a claim that the remainder is uniformly smaller before truncation. For N=2 the domain includes beta<=1/2 and hence all beta values in the new lower construction.

The proof establishes the precise upper counterpart of the unknown-location logarithm at N=2, subject to matching fixed geometry/prevalence constants. It also proves the displayed all-N bound **with** its L/(nbetaalpha) remainder. It does not yet remove that remainder for arbitrary N, justify an all-N matching lower, adapt to unknown alpha, or change the exact-anchor/strong-geometry/fixed-K assumptions. The determinant search remains potentially expensive.

No additional numerical experiment was necessary: the new claims are concentration and deterministic event manipulations. The finite rational checker for the separate lower-bound likelihood does not audit this upper theorem.

