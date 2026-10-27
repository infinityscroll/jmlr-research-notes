# A matched sparse-topic frontier for every document length

28 October 2026. Integration of the source-bound upper and lower results below. The individual sources and their independent analytic audits are unchanged. This note supplies the common-class statement, the coverage of all document-length regimes, and the vocabulary-padding argument. Internal audits are not external mathematical validation or historical novelty clearance.

**Result.** In the exact-anchor, fixed-topic-count, strongly separated topic class defined below, the expected minimax L1 error is, up to constants,

\[
 \boxed{\quad
 \min\!\left\{1,
 F_{q,p}(a)+a\sqrt{\frac{\log(2+\min\{p,\alpha^{-q}\})}{\alpha}}
 \right\},\qquad
 a=\frac1{\sqrt{nN\beta}}
       +\frac1{\beta\sqrt{nN(N-1)}} .\quad}                 \tag{M1}
\]

This holds for every integer document length N>=2. The upper is attained by one observable estimator that knows K and alpha, but does not know beta, q, W, or the anchor locations. The square-root anchor logarithm is matched; the earlier joint weak-diversity result's logarithmic gap is removed on this class.

## 1. One common statistical class

Fix K>=2 and q in (0,1), and let k0=max(1,K-2). The varying parameters satisfy

    p>=2K+8, n>=128(K-1), N>=2, all integers;
    0<alpha<=1/(64K), 0<beta<=1/[1024 K^2 k0].             (M2)

Observe independent count vectors

    X_i ~ Multinomial(N,A w_i), i=1,...,n.

A is a nonnegative p-by-K matrix with stochastic columns. W=[w_1,...,w_n] is an unknown deterministic K-by-n matrix with stochastic columns. Define Sigma=WW'/n, mu=W1/n and d=A mu. Let C(alpha,beta,q) contain all such pairs satisfying

    w_ki>=1/(4K) for every k,i;
    lambda_min(Sigma)>=beta;
    sigma_min(A)>=1/(8sqrt(K));
    (A'A)_kl>=1/64 for every k,l;
    max_k max_j j [A_(j),k]^q<=4.                         (M3)

Here A_(j),k is the jth largest entry in column k. Each topic must have an exact pure anchor: for some unknown row j_k,

    A_(j_k),k>0, A_(j_k),l=0 for l!=k, d_(j_k)>=alpha.     (M4)

Thus alpha is a lower bound on **corpus anchor probability**, not on the topic-column entry by itself. The common class has positive mean prevalence, uniformly interior document mixtures, a fixed unnormalized topic singular-value floor, positive topic overlaps, and a fixed source-convention weak-q radius four. Every nonzero vocabulary row has positive probability in every document. Unused zero rows are permitted. No assumption that all p rows have positive mass is made.

Use entrywise L1 loss modulo every column permutation,

    ell(Ahat,A)=min_Pi ||Ahat-A Pi||_1,
    R=inf_Ahat sup_(A,W in C(alpha,beta,q)) E_(A,W) ell(Ahat,A).

The estimator can be required to return stochastic columns; its loss is then at most 2K. The lower proofs use testing and apply also without that output restriction. Replacing the loss cap 2K by 1 in a rate expression only changes constants depending on fixed K.

For 0<a<1 define

    F_(q,p)(a)=a,                                      0<q<1/2;
    F_(1/2,p)(a)=a log(2+min{p,1/a});
    F_(q,p)(a)=min{a^(2(1-q)), a p^(1-1/(2q))},         1/2<q<1. (M5)

For a>=1 set F_(q,p)(a)=1. Put Lambda=log(2+min{p,alpha^(-q)}). There are constants 0<c_(K,q)<=C_(K,q)<infinity, independent of n,p,N,alpha,beta, such that

    c_(K,q) min{1,F_(q,p)(a)+sqrt(Lambda)*a/sqrt(alpha)}
       <=R
       <=C_(K,q) min{1,F_(q,p)(a)+sqrt(Lambda)*a/sqrt(alpha)}. (M6)

Constants are not asserted uniform as q approaches 0 or 1, or as K grows. M6 is an expected-risk rate with matching powers and logarithms; it is not an exact-constant, high-confidence, or practical finite-sample performance claim.

## 2. The same observable estimator attains the upper bound

The all-N upper applies on a larger class needing only the fixed mean-prevalence and topic singular-value floors, exact anchors, and the diversity floor. It therefore applies to every pair in M3--M4. Its instance form is

    R_alpha(d)=sum_j min{1,d_j/alpha},
    L_inst=log(2+R_alpha(d)),
    H_a(d)=sum_j min{d_j,a sqrt(d_j)},
    E ell<=C min{1,H_a(d)+sqrt(L_inst)*a/sqrt(alpha)}.       (M7)

Columnwise radius four implies the corpus envelope

    #{j:d_j>=t}<=4K t^(-q),
    R_alpha(d)<=min{p,4K alpha^(-q)/(1-q)}.

Indeed d_j is a convex combination of the K column entries, so d_j>=t requires at least one column entry at least t. Integrating this counting bound gives the displayed effective-row count. Integrating the same envelope in H_a gives M5. Consequently M7 implies the upper side of M6 with constants depending only on K,q.

The algorithm remains the held spectral/max-volume estimator. It forms the exact factorial-pair moment from the counts, screens potential anchor rows using known alpha, recovers the simplex, and reconstructs all rows. It then uses the observed Kth pair-moment eigenvalue lambda_hat to set

    tau_hat=[1/sqrt(nN lambda_hat)
               +1/(lambda_hat sqrt(nN(N-1)))]^2           (M8)

when lambda_hat>0, and thresholds reconstructed output rows by empirical corpus frequency before clipping and column normalization. The held observable guards, including nonpositive lambda_hat, use a fixed bounded stochastic fallback. This is an output threshold after anchor reconstruction, not a rule that discards anchors before estimating their geometry.

The actual unknown b=lambda_min(Sigma) is used only in the proof. On the relative spectral good event, lambda_hat is bounded above and below by fixed multiples of b. Thus the random cutoff is comparable to a(b)^2. The proof uses pointwise indicator bounds and unconditional moments; it does not pretend this cutoff is independent of the data. Neither R_alpha(d), beta, q, nor a sparsity radius is an algorithm input. No claim that the maximum-volume step is computationally efficient is required here.

The new all-N concentration step retains the rare-cell factor in every moment of a single document's degenerate row. It yields a row increment scale 1/(nN), while keeping exact dependence among overlapping token pairs. This is what makes the square-root logarithm uniform over all N; multiplying an independent-pair sample size by N(N-1) would not justify it.

## 3. Why the anchor lower bound covers every N

The unknown-location construction and its legal deterministic-mixture prior are common to the two anchor lower proofs. Both obey every condition in M2--M4, including the radius four and the same corpus anchor threshold. The prior is only a minimax proof device: after its common conditioning event, every constituent W is a legal deterministic nuisance parameter.

The short-information proof gives, whenever N beta<=2,

    R>=c_(K,q) min{1,
          sqrt(Lambda)/[beta sqrt(nN(N-1)alpha)]}.         (M9)

Its diagonal likelihood information is of order alpha theta^2 N(N-1)beta^2, and its distinct-location cross term has the smaller order alpha^2 theta^2 N(N-1)beta^2. Posterior covariance and double centering preserve this extra alpha factor, which is necessary for mixing candidate anchor locations. This is a full multinomial calculation, not an independent-pair argument.

The long-information proof gives, for every N>=2,

    R>=c_(K,q) min{1,sqrt(Lambda/(nN alpha beta))}.         (M10)

It can reveal the generating sign without revealing W: the map from that sign to W differs across hypotheses. The cross likelihood inner products of distinct location alternatives are exactly one in that augmented experiment. Conditioning the common sign prior preserves those identities.

Let r=(N-1)beta. The ratio of the second term of a to its first is 1/sqrt(r).

- If r<1, then N beta<1+beta<=2 under M2. M9 applies, and a is between its second term and twice that term.
- If r>=1, M10 applies, and a is between its first term and twice that term.

These cases cover every N>=2, including the transition. Therefore

    R>=c_(K,q) min{1,sqrt(Lambda)*a/sqrt(alpha)}.           (M11)

## 4. Sparse-tail lower bound and every integer vocabulary size

The separately audited fixed-radius tail lower has the same class conditions and holds for every N>=2. Its original vocabulary size is p0=K+2+2r0 with r0>=4; it permits the weaker restriction beta<=1/[256K^2 k0], so our smaller beta domain is contained in it. It supplies

    R>=c_(K,q) min{1,F_(q,p0)(a)}.                        (M12)

Its information scale is

    G_N=N(N-1)beta^2/[1+(N-1)beta],
    e=1/sqrt(nG_N), e<=a<=sqrt(2)e.

A nonuniform weak-q tail hypercube yields the exact profile sum sum_j min{b_j,e sqrt(b_j)} with b_j proportional to j^(-1/q). This gives all three profiles in M5, including the logarithm at q=1/2. These tail constructions even reveal designated anchors; the unknown-location lower in M11 is a separate difficulty.

For an arbitrary integer p in M2 choose

    r0=floor((p-K-2)/2), p0=K+2+2r0.

Then r0>=4, p0 is either p or p-1, and p0>=p/2. When p0=p-1 append one zero row to every topic matrix. This leaves the stochastic column sums, singular values, Gram matrix, anchor corpus masses, weak-q radius, W, likelihoods, and all quotient distances between constructed parameters unchanged. The appended count coordinate is deterministically zero. Thus the old testing lower applies to this p-row experiment without any new statistical approximation.

For completeness, a stochastic p-row estimate can also be mapped back to p0 rows without increasing loss: remove its last row and normalize each remaining column. If the removed mass is t<1, normalization changes that column by exactly t in L1, so its distance to the true column is at most the old retained-row distance plus t, which is the original full-row error. If t=1, return any stochastic column; both the full-row error and its upper bound are 2. This works for each topic permutation and hence for their minimum.

The profile has only a constant change under p0>=p/2:

- For q<1/2 it is unchanged.
- For q=1/2, min{p0,1/a}>=min{p,1/a}/2 and log(2+t/2)>=log(2+t)/2, so F_(q,p0)(a)>=F_(q,p)(a)/2.
- For q>1/2, put nu=1-1/(2q)>0. Then p0^nu>=2^(-nu)p^nu, so F_(q,p0)(a)>=2^(-nu)F_(q,p)(a).

The a>=1 convention is unchanged. M12 therefore gives the sparse-tail lower for every integer p in M2. The anchor construction already permits arbitrary p by zero padding.

The anchor and tail hard families need not be the same family. They are both subsets of the one class C(alpha,beta,q), so minimax risk is at least the maximum of M11 and M12. For nonnegative x,y,

    max{min(1,x),min(1,y)}>=min(1,x+y)/2.

This proves the lower side of M6 and completes the integrated theorem.

## 5. Fixed-token-budget document-length transition

With m=nN fixed, the common scale is exactly

    a=1/sqrt(m beta) * [1+1/sqrt((N-1)beta)].              (M13)

Within the domain n=m/N>=128(K-1), its two regimes are

| Document information | Joint scale a | Anchor part of the rate |
| --- | --- | --- |
| (N-1)beta<=1 | comparable to 1/[beta sqrt(m(N-1))] | comparable to sqrt(Lambda)/[sqrt(alpha) beta sqrt(m(N-1))] |
| (N-1)beta>=1 | comparable to 1/sqrt(m beta) | comparable to sqrt(Lambda/(m alpha beta)) |

The sparse-tail part is F_(q,p) applied to the same a. The transition is at N-1 comparable to beta^(-1). At fixed total tokens, longer documents reduce the weak-diversity penalty until this scale; after it the rate is within a constant of the first-order plateau. The q=1/2 tail logarithm and the unknown-anchor logarithm Lambda are distinct factors.

A concrete comparison shows the effect without changing topic geometry. Fix admissible K,q,p,alpha. Along even integers T tending to infinity set m=T^4 and beta=T^(-1). Compare N=2, n=T^4/2, with N=T, n=T^3. Both are in M2 for large T. For fixed p, all three sparse profiles are comparable to a as a tends to zero, and Lambda is constant. Thus M6 gives

    N=2: risk comparable to T^(-1)=m^(-1/4);
    N=T: risk comparable to T^(-3/2)=m^(-3/8).            (M14)

This compares statistical classes with their mixture constraints maintained. It does not say that regrouping a given corpus preserves W or improves it, and it is not an empirical allocation recommendation. The plateau is accessible only when the total budget still leaves enough documents after reaching N of order 1/beta. All risks remain capped; rate comparisons are meaningful in the nontrivial range.

## 6. What has changed, and what has not

The previous joint weak-diversity theorem left an anchor logarithm between its bounds. M6 matches that term by combining the new all-N row moments with the short- and long-information unknown-location lower bounds. The ordinary weak-q tail shapes, the fixed-beta anchor-search logarithm, the generic demixing geometry, and the use of Bernstein/likelihood-mixture methods have established antecedents. They are not separately counted as new discoveries.

The contribution candidate is the uniform joint law in alpha, beta, N and p with unknown deterministic W. Here beta concerns WW'/n; it must not be relabeled as a topic-matrix conditioning parameter from another paper. The strong unnormalized sigma_min(A) floor excludes the usual fully diffuse regime in which all word masses are of order 1/p. Exact anchors, fixed K and radius, known alpha, and expected-risk quantifiers remain substantive restrictions. There is no growing-K claim, unknown-alpha adaptation, nonseparable-topic theorem, confidence-level matching to the source paper, or practical superiority claim.

The adjacent primary gate compares the actual published TLD assumptions and other primary theorems. Its fixed-conditioning specialization of the TLD open question was already covered by earlier portfolio work. The new matched weakening-beta law is an extension of that regime, not a second resolution of it. The gate found no directly subsuming theorem among the inspected sources, but explicitly does not establish priority, exhaustive novelty clearance, or a newsworthy breakthrough. A specialist must still assess the full theorem and its relation to existing results.

## 7. Exact source and review bindings

The following hashes identify the source versions used in this integration. The first three completed proof audits reported no blocker in their respective stated scopes. The older family and sparse-tail audits supply the remaining class and profile checks. These are internal analytic reviews, not formal proof-assistant or external certification.

| Item | Source | SHA256 |
| --- | --- | --- |
| All-N upper | [all_document_lengths_bernstein_upper.md](all_document_lengths_bernstein_upper.md) | `bd9c774907a8691508d41bf4ea019d4b7b996b99707a0a1e8694aedd74aac2d3` |
| All-N upper audit | [independent_all_document_lengths_upper_audit.md](independent_all_document_lengths_upper_audit.md) | `e597865ab8c0cb2f3d85557a15386463dc4f94063e725805c78afa5024fac3d2` |
| Short-information all-N lower | [unknown_anchor_short_regime_all_N_lower.md](unknown_anchor_short_regime_all_N_lower.md) | `3b7a7c77c4f46761fd8e1c5708fe9b1709bdebe579f2eccdd3ab27ef28a5c851` |
| Short-information all-N audit | [independent_short_regime_all_N_lower_audit.md](independent_short_regime_all_N_lower_audit.md) | `c8fc75c0d593092452f445203a3c9b58cd1d2f30c03423c73031d366d663ee03` |
| Long-information lower | [unknown_anchor_long_document_lower.md](unknown_anchor_long_document_lower.md) | `7390561c70dea239f91c018446504b240f6246631ce4ede711b2d1e78fd6d7ce` |
| Long-information audit | [independent_long_document_lower_audit.md](independent_long_document_lower_audit.md) | `9d98d508653a69dcdaeb4e4b4d9457a3f380f975d4f68a72cd59f01d0c9c8d50` |
| Unknown-location family and N=2 lower | [unknown_anchor_short_document_lower.md](unknown_anchor_short_document_lower.md) | `a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56` |
| Family/N=2 audit | [independent_unknown_anchor_lower_audit.md](independent_unknown_anchor_lower_audit.md) | `402e219d5fe8d33a5a2fac89f3836241b54146ec42f01febbafb0d1bbd8751e5` |
| Observable conditioning threshold | [observable_conditioning_threshold.md](../weak_sparsity_frontier_gate_20261028/observable_conditioning_threshold.md) | `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8` |
| Sparse-tail lower | [weak_sparsity_joint_lower.md](../weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_lower.md) | `bd43ef4d96e7f7c561bd90b5c90d0a1e32a4e3b4ad527c11bd03380de25f3c09` |
| Sparse-tail audit | [independent_weak_sparsity_lower_audit.md](../weak_sparsity_frontier_gate_20261028/independent_weak_sparsity_lower_audit.md) | `8179d913e5747a1348a39f1ffc6eb8db153b9495741d56a65c45442c69038b5c` |
| Primary significance comparison | [primary_gate.md](primary_gate.md) | `b7a6ce4b21e290ae79880fac7f38613f56c655c504807efea35654df7d7578fe` |
