# Independent hostile audit: empirical-frequency maximum-error lemma

27 October 2026. Reviewer: `/root/hcm_adversarial_boundary`. This is a source-level mathematical audit, not a review of a summary or a certificate of historical novelty.

Bound source: `empirical_frequency_maximum_lemma.md`, SHA256
`82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`.

**Verdict: no mathematical blocker found for the statement actually proved.** The lemma gives an expected positive-excess bound of order m^(-1/2) for empirical-frequency-penalized normalized pair-moment rows, uniformly in vocabulary size, document length N>=2, and the document probability vectors. It does not itself establish an adaptive topic estimator or its minimax sharpness.

## 1. Observation model and exact pair estimator

I checked the factorial subtraction on the diagonal and the random-pair argument. For every fixed within-document permutation, n floor(N/2) disjoint symmetric kernels are independent. Their expectation is the stated average C_jr, even when documents have different probability vectors. Because all documents have the same N, each contributes the same number of kernels. The kernel is in [0,1] and its second moment is bounded by its expectation, hence by p_ij. Thus the summed variance is at most M d_j with M>=m/3.

Averaging the paired statistic over permutations gives the ordered factorial estimator exactly for odd or even N, including j=r. Jensen transfers the centered exponential-moment bound; it does not require overlapping pairs to be independent. The displayed threshold sqrt(6d_j u/m)+2u/m is conservative relative to bounded-variable Bernstein. The frequency term has at least as strong a bound.

The result uses independent multinomial tokens conditional on arbitrary deterministic document probability vectors. It does not cover arbitrary dependence among tokens, unequal document lengths without a separate reweighting argument, or a random W whose dependence on the data is left unspecified.

## 2. Deterministic normalized-row bounds and zero frequencies

Both ideal and empirical rows restricted to any set of coordinates are nonnegative subprobability vectors. The exact row-sum identity for C_hat follows from X_ij sum_r(X_ir-1_(j=r))=X_ij(N-1). Therefore their Euclidean distance is at most two. This bound remains true after a data-selected restriction of coordinates.

Rows with d_j=0 have all their underlying token probabilities zero and hence d_hat_j=0 almost surely. Excluding d_hat_j=0 rows creates no undefined population division in the maximum. The cap of two on the penalty makes every capped row's positive excess identically zero. This is a material part of the proof for rare accidental observations, not merely a numerical guard.

## 3. Balanced-frequency calculation

On d/2<=x<=2d, the numerator identity

    Y_hat-Y = [(C_hat-C)-Y(x-d)]/x

and ||Y||_2<=1 give the claimed bound with H=6(sqrt(r)+1): the coefficients 2sqrt(6)(sqrt(r)+1) and 4(sqrt(r)+1) are both at most H.

For u=3ell(d)+c_r md t^2, the remainder after separating the two terms is at most t/8+t/(32H)<t. The function ell(x)/x is decreasing, and ell(d)<=2ell(2d); thus its empirical-frequency value is at least ell(d)/(4d). With A=12H, the uncapped penalty dominates both Hsqrt(3ell(d)/(md)) and 3H ell(d)/(md). A capped penalty makes the event impossible. This proves the d^3 exp(-c_r md t^2) row tail on the balanced event, with the exact prefactor stated in the source.

## 4. The two imbalance cases

The dangerous case is a word of true mass far below 1/m that is observed enough times to make its denominator look reliable. A direct exp(-c md) estimate would not suffice after summing over many words. I reconstructed the active-penalty threshold and its use in both cases.

Positive excess implies mx>K ell(x), K=A^2/4. If m<=K log 3 this is impossible. Otherwise ms=K ell(s) has exactly one solution in (0,1), since mx-Kell(x) is strictly increasing; active rows satisfy x>s.

For underestimation, x<d/2 implies d>2s and md>2Kell(d). Splitting the ordinary lower-tail exponent md/8 into two copies of md/16 pays at least 3ell(d) with one copy and leaves exp(-md/16) with the other. The result is bounded by d^3 exp(-md/16). The event is empty if d<=2s.

For overestimation, put u=max(2d,s), k=mu and z=d/u<=1/2. If u>=1 the event is empty. Otherwise the Poisson-binomial Chernoff exponent is k g(z), with g(z)=log(1/z)-1+z. The source's inequalities g(z)>=log(1/z)/4 and g(z)>=1/8 both hold on (0,1/2]. Their average gives g(z)>=log(1/z)/8+1/16.

Here is the exact accounting in equation (16), the most important seam:

* k>=Kell(u) implies k/8>=3, so (k/8)log(u/d)>=3log(u/d).
* The same bound, K>=96, and ell(u)>=log(1/u) give k/32>=3log(1/u).
* The remaining k/32 is at least md/16 because u>=2d.

The first two contributions sum to 3log(1/d); the third preserves exponential damping. Hence the false-large-frequency event is bounded by d^3 exp(-md/16), even for arbitrarily small positive d. No asymptotic lower bound on md or hidden vocabulary restriction is used.

For 0<t<2, c_r t^2<=1/16, so both imbalance estimates are bounded by the same expression used for the balanced event.

## 5. Maximum, expectation, and random core

The final union bound uses

    sum_j d_j^3 exp(-L d_j)
       <= sup_(x>0)[x^2 exp(-Lx)] sum_j d_j
       =4exp(-2)/L^2.

Thus it is uniform in finite p, rather than hiding a polynomial-p factor. Integrating min(1,K_r/(m^2t^4)) gives exactly (4/3)K_r^(1/4)/sqrt(m). Extending this integral above two only enlarges it. Every discarded event has therefore been charged to expected risk explicitly.

For a data-selected core inside a deterministic set C_* of bounded cardinality, applying the lemma to the full C_* vector dominates every restriction. Constants can use the deterministic upper bound r_* on its size. On a containing event G this applies pathwise; outside G the row error is at most two. No independence between core selection and the empirical rows is needed. This is compatible with the frequent-core construction in the known-alpha theorem, provided its separate failure probability is also included in the final estimator analysis.

## 6. Composition limits

No repairs are requested for the bound source. The large constants and capped penalty may be impractical; the lemma makes no tuning or runtime promise. A complete adaptive theorem still needs all of the following stated separately: an observable selection/guard rule, a deterministic penalized-determinant comparison, anchor-candidate availability and expected anchor penalties, inverse stability, full-column reconstruction and normalization, and the correctly quantified adaptation lower bound. None of those conclusions follows from this audit alone.
