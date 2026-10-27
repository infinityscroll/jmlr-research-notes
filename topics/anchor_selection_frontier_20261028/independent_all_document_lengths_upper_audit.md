# Independent audit of the all-document-length Bernstein refinement

28 October 2026. Reviewed source: `all_document_lengths_bernstein_upper.md`, SHA256 `bd9c774907a8691508d41bf4ea019d4b7b996b99707a0a1e8694aedd74aac2d3`. The source was read in full and not edited. Its short-document dependency was separately reviewed in `independent_short_document_upper_audit.md`.

**Verdict:** no blocking mathematical issue found. The new moment calculation does supply the rare-cell factor and the 1/N document increment scale simultaneously. Consequently the square-root anchor logarithm upper bound extends to every N>=2 under the held estimator's assumptions. This is an upper-bound audit, not an all-N lower-bound or novelty certificate.

## 1. Rare scalar and vector moments

For a centered Binomial(l,pi) count, the lambda=lpi>=1 case follows from scalar Bernstein followed by moment integration. Its r^r remainder may be multiplied by lambda since lambda>=1. When lambda<1, factorial moments give E B^r<=lambda sum_k Stirling2(r,k)<=lambda r^r; centering adds at most the same rare-cell order. Thus B3 retains pi for all integer r>=2, including l=1 and pi=0.

The independent vector average in B4 satisfies dimension-free Lr control C sqrt(r/h): use the held Hilbert Bernstein bound when r<=h, and its deterministic norm bound sqrt(2) when r>h. No covariance invertibility or dimension bound is required.

## 2. The degenerate-row moment is uniform in r and N

The balanced split identity holds conditionally on the original tokens. For an ordered pair (s,t), its probability of being assigned to opposite designated halves is lh/[N(N-1)]; division by lh recovers its exact coefficient in Q. Averaging the two orientations leaves the same identity. This includes odd N and N=2.

Conditional Jensen bounds the row moment by the corresponding product moments for the two halves. Within a fixed split the halves are independent, so the scalar and vector moments can be multiplied. They need not be independent after averaging over splits, and the proof never assumes otherwise.

For 2<=r<=N, the first resulting term is bounded by C^r r^r pi_j/N^r since pi_j^(r/2)<=pi_j. Relative to that bound, the second term has factor

    r^(r/2) N^(1-r/2)
       =r (r/N)^(r/2-1)<=r<=2^r.

The constant factors caused by l,h>=N/3 are also absorbed in C^r. Finally r^r<=e^r r! converts the result to B6. This is a factorial moment bound, not a claim that every row has deterministic norm O(1/N).

For r>N, the exact second moment and deterministic row bound imply E||Q_j||^r<=4 pi_j (sqrt(2))^(r-2)/N^2. Since r!>=(r/e)^r and r>N, a larger universal C gives the same B6 bound. Thus the argument does not leave an unproved large-r tail, which would invalidate Bernstein integration.

The exact second moment itself comes from the only nonzero terms in the degenerate pair expansion: equal ordered pairs and reversed ordered pairs. They contribute Var(T_j) trace(Cov(T)) and ||Cov(T)e_j||^2, both at most pi_j. This confirms the scale 2pi_j/[N(N-1)] used in both ranges.

## 3. Moment-form Hilbert Bernstein

For f(x)=cosh(t||x||), the radial and tangential Hessian eigenvalues are bounded by t^2 f(x), including x=0 by continuity. Along a segment, f(x+s y)<=f(x)exp(ts||y||). The second-order integral remainder is therefore bounded by

    f(x) [exp(t||y||)-1-t||y||].

Independence and centered increments cancel the linear derivative term after conditioning. The moment hypothesis B7 bounds the remaining expectation by v_i t^2/[2(1-tB)], producing the stated cosh moment generating bound after iteration. Chernoff with

    t=s/(1+Bs), s=sqrt(2u/v),

gives the threshold sqrt(2vu)+Bu and probability 2exp(-u); the zero-variance case is trivial. Moment integration yields the Lr statement. This derivation is dimension-free and does not require bounded Y_i of order B.

Applying B6 to Q_i,j/n indeed permits v_i=C0^2 pi_ij/(n^2N^2), B=C0/(nN): taking C0 at least twice the constant in B6 absorbs the 1/2 in B7 for all r>=2. Documents may have different pi_i. Summing their variance parameters uses d_j=(1/n)sum_i pi_ij and proves B9. No token-pair independence has been inserted.

## 4. Statistical composition and the final logarithm

The whitened first-order row error and frequency remainder already scale as r/(nNb) after their prescribed conditioning factors. Combining them with B9 proves B10. The previously audited count R_alpha(d), finite-set maximum, rare false-inclusion argument and maximum-volume reconstruction then replace the old remainder by L/(nNb alpha).

Analysis uses actual b=lambda_min(Sigma). The observed-eigenvalue threshold is still comparable to a(b)^2 on its original spectral event; its row selection is controlled by deterministic indicator domination and unconditional second moments. No independence from the random threshold or chosen anchor core is needed.

For z=sqrt(L)a(b)/sqrt(alpha), the new remainder is at most z^2 because a(b)^2>=1/(nNb), for every N>=2. The small-z/bounded-loss case split absorbs it. Passing afterward from actual b to the class floor beta is valid by monotonicity. The sparse profile and R_alpha(d) envelope are unchanged, so the final result retains the exact p/alpha candidate multiplicity and all three weak-q tail regimes.

## 5. Scope

This verifies a sharper analysis of the same estimator, with known alpha and fixed K, prevalence and strong unnormalized topic geometry. Exact anchors and expensive maximum-volume selection remain. The N=2 likelihood lower in the adjacent new source can match this anchor logarithm on its stated class; the present proof alone does not establish a matching lower for general N. Concentration and truncation methods are classical. No claim of historical novelty, practical superiority, or a general diffuse-vocabulary solution follows from this audit.

