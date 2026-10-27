# Independent audit: the short-information unknown-anchor lower bound for every N

28 October 2026. Reviewer: hcm_end_to_end. Analytic review, with a bounded exact check of the delicate likelihood identity. No producer source was changed.

**Verdict: no mathematical blocker found within the stated class and parameter domain.** The proof closes the weighted cross-likelihood seam left by the N=2 argument. It establishes the claimed anchor-location lower bound for every integer N>=2 with N beta<=2. Together with the separately reviewed revealed-sign long-document lower bound, it covers every N>=2. This verdict is correctness review, not novelty clearance or an external expert review.

## Bound sources and inherited scope

The source reviewed in full is `unknown_anchor_short_regime_all_N_lower.md`, SHA256

`3b7a7c77c4f46761fd8e1c5708fe9b1709bdebe579f2eccdd3ab27ef28a5c851`.

Its construction dependency is `unknown_anchor_short_document_lower.md`, SHA256

`a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56`.

I rechecked the imported parameter/class statement, the candidate-pair construction, and the common conditioning event against that source. This audit does not replace its separate full geometry and mixture-conditioning review. In particular the theorem retains fixed K and q in (0,1), the displayed small-alpha/small-beta domain, p>=2K+8, n>=128(K-1), strong unnormalized A geometry, radius-four weak-q columns, exact anchors with corpus mass at least alpha, interior deterministic W, and loss modulo all topic permutations. Zero padding is allowed. The lower-bound sign prior is not a change to the statistical model: after conditioning, every constituent W is an admissible deterministic nuisance parameter.

## 1. Conditioning on groups is legal

In every candidate pair the two baseline word probabilities are equal, and their perturbations are opposite. The same holds for the common pair. Summing within a group removes the latent sign and the candidate alternative. Thus the entire token-group sequence has exactly the same distribution under every hypothesis and is independent of the hidden sign. Conditional on this sequence, the baseline within-pair signs are independent fair bits.

Writing P_+=product(1+r_g epsilon) and P_-=product(1-r_g epsilon), the null density is F0=(P_++P_-)/2, and the null posterior is p=P_+/(P_++P_-). The relations F0=Q cosh(H) and p(1-p)=1/[4 cosh(H)^2] follow exactly. They introduce no approximation and remain valid with zero-contrast singleton groups.

## 2. The missing-information identity has the correct sign and factor

For distinct candidate groups j,k, complete likelihood ratios have conditional mean one under the true null law given the sign and groups. Their product also has mean one because it uses disjoint token groups. Taking posterior covariance therefore gives

    E0[L_j L_k | groups]-1 = -E0[p(1-p) D_j D_k | groups].

Changing from the null law to the fair-sign law gives exactly

    -(Q/4) E_fair[D_j D_k sech(H)]
      = -(Q^2/4) E_fair[D_j D_k / F0].

The minus sign and 1/4 coefficient are correct. Individual complete ratios do not have fair mean one, and the proof correctly does not use that false assertion. Instead, flipping all fair signs in group j exchanges its plus and minus ratios, proving E_fair D_j=0. This is the centering needed later.

## 3. The derivative-product estimate is uniform in document length

For b=r epsilon/(1+r epsilon), direct two-point averaging gives the displayed negative E b and the displayed E b^2. In the derivative square of product(1+s b), diagonal terms give m E b^2 A_s^(m-1), and ordered off-diagonal terms give m(m-1){E[b(1+s b)]}^2 A_s^(m-2). The source separately handles m=0 and m=1, so no negative-power edge case is being used.

The negative first moment implies A_s<=1+C s^2 r^2. Consequently the derivative second moment is at most C(m r^2+m^2 r^4) exp(C kappa^2 m r^2). The construction and N beta<=2 give m r^2<=C_K. This makes the bound C_K m r^2 uniformly in all varying statistical parameters. Integrating the plus/minus derivative difference from zero gives the C8 second moment, and Cauchy--Schwarz with E H_j^2<=C m_j r^2 gives E|D_j H_j|<=C_K kappa m_j r^2. Constants may be large as functions of fixed K; no practical finite-sample constant is claimed.

## 4. Twice centering preserves the extra rare-group factor

Under the fair law the j, k and remaining sign blocks are independent. Subtracting f(H_out+H_j), f(H_out+H_k), and adding f(H_out) changes no expectation because each removed term is multiplied by an independent centered D_j or D_k. The resulting mixed finite difference is bounded by ||f''||_infinity |H_j H_k|. For f=sech this norm is finite. Combining with C8 yields the conditional cross bound C_K kappa^2 m_j m_k r^4.

The multinomial group-count identity E m_j m_k=N(N-1)c_i^2 for j!=k is exact, not an independence approximation. Since c_i=2a0 t_i, the unconditional bound is proportional to a0^2 theta^2 N(N-1) beta^2. This is the essential improvement over an absolute-value bound taken before centering. The proof does not assume that individual observed cross corrections are positive.

## 5. The diagonal denominator bound is used only on a nonnegative expression

The product-baseline identity E_d F_z F_w=g_N(E_d zw) follows by expanding the two latent signs and independence of the N tokens. The diagonal finite difference in C13 is correct. Split it into a central second difference of step kappa u and an additional increment kappa^2 u. On the actual argument range, g_N'' is bounded by C_K N(N-1), while g_N'(s)<=C_K N(N-1)s because g_N'(0)=0. N beta<=2 controls all exponential factors.

This yields C_K N(N-1) kappa^2(u beta+u^2), hence the claimed a0 theta^2 scale. The pointwise F0 lower bound follows from Q and r_i^2<=1/32. Dividing the squared likelihood difference by F0 is legitimate because that numerator is nonnegative. Applying the same maneuver to the signed cross term would not have been valid; the source does not do so.

## 6. Product likelihoods, conditioning, and the final minimax statement

Before conditioning the latent signs, documents are independent. Every likelihood inner product is nonnegative. For a cross correction O_i, its sign may be negative, but 1+O_i<=exp(C_i) follows from O_i<=C_i; multiplying retains the stated exponential upper bound. The selected theta makes cumulative diagonal and cross bounds at most epsilon L and epsilon a0 L. The same null-versus-mixture chi-square expansion as in the construction source then applies, with theta<=1/16 enforced by the fixed constant.

The event E is common to every hypothesis and has prior failure probability at most1/64. Conditioning changes each observation law by at most that amount, regardless of document dependence induced by conditioning. The stated total-variation bound3/32 follows. The null-to-each-alternative quotient separation supplies the two-hypothesis-versus-mixture test; alternative-to-alternative separation is unnecessary.

For the overlap of information regimes, (N-1)beta<1 implies N beta<1+beta<=2. In that region the pair term dominates the joint scale a(beta) within a factor2. When (N-1)beta>=1, the revealed-sign long-document term dominates within a factor2. Thus there is no uncovered N regime. A matched complete frontier additionally uses the separate sparse-profile lower and upper results on their common class; it is not asserted from this anchor calculation alone.

## 7. Bounded exact check

`check_short_regime_missing_information.py` and `short_regime_missing_information_certificate.json` verify C5 independently using rational arithmetic. The check enumerates312 fair-sign patterns across12 fixed group/r/kappa fixtures, covering N=3 through6, repeated candidate groups, a common group, a zero-contrast singleton, and an empty candidate group. Its96 identity assertions cover both forms of C5, E_fair D_j=E_fair D_k=0, complete cross inner products equal to one, and observed likelihood normalization. No random numbers or floating-point hyperbolic evaluations are used.

These checks target the sign, posterior weight and 1/4 coefficient. They do not certify the analytic moment bounds, the uniform-in-N statement, class membership, or novelty; those conclusions rest on the proof review above and its explicitly named dependencies.
