# Independent audit of the fixed-K lower embedding

27 October 2026. Reviewer: status_claim_check. Source read in full: `general_k_lower.md`, SHA256 `3edaed4fc1d02c5f6f5f58c8c9ed2ab1874d5e8df26d4c0d86281e60ce1dffe2`. This audit is internal mathematical review, not external validation or historical novelty clearance. The separate upper proof was written by this reviewer and is not independently certified by this audit.

**Verdict: no blocking gap found in the stated fixed-K, fixed-vocabulary theorem.** No source edit is requested. The matching consequence must retain p=K+10 for K>=3, the displayed K-dependent alpha/beta/geometry domain, and constants allowed to depend on K. It is not a lower bound for every p>=K.

## Geometry and admissibility

The first two columns are stochastic, and their common-word block has singular values 2h and 2s. Since h>=7/16 and s>=3/16, its least singular value is at least3/8. The extra anchor rows reveal the coefficient vector t/2 exactly. Reconstructing the old coefficient vector from the top block gives the displayed quadratic norm estimate; its coefficient of ||t||^2 is at most16K, so the full smallest-singular-value floor follows. The loose bound ||r0||<=1 is sufficient.

The old-extra Gram entry is exactly (1-4a)/20, at least3/64 because a<=1/64. Different extras overlap by1/40. The old-old entries are bounded as in the two-topic construction. Thus every Gram entry exceeds the claimed1/64 floor. A permutation moving an extra topic creates an L1 discrepancy of exactly one on that extra anchor's row alone; the two affected column positions each contribute1/2. A nontrivial permutation restricted to the old pair costs at least3/2 on rows3,4. Hence the quotient distance is exactly4Delta throughout the designated parameter interval.

In the deterministic cycle, the vectors z_j span the K-2-dimensional mean-zero part of H and have Gram matrix I+11'/2. At least half the design mass can be extracted as complete cycles when n>=2m, giving Sigma_B>=c0 P_H with the stated c0. The larger requirement n>=128(K-1) implies this cycle requirement.

The perturbation r/sqrt2 has square at most1/[18K^2(K-2)], which is at most1/(16K^2). Thus every mixture entry remains at least1/(4K). This verifies actual positivity, not merely positivity of the corpus mean. Old anchor corpus mass is 4Kalpha times the corresponding mean mixture weight, hence at leastalpha; extra anchor corpus mass is at least1/(8K), also at leastalpha. The revealed anchor probabilities in the lower experiment are topic-column masses, not the different corpus masses. They are identical at the two hypotheses.

## Conditioning the nuisance prior

I independently reconstructed the identity

    c' Sigma_B^dagger c=||Pi_B xi||^2/n,

using c=Bxi/n and Sigma_B=BB'/n. On the conditioning event the standardized cross block has norm at most1/sqrt2. For x in H, Cauchy–Schwarz in the Sigma_B metric and 2ab<=a^2+b^2 give exactly the factor1-1/sqrt2 in the source. Since r^2>=16beta and c0>=32beta, the final minimum eigenvalue is strictly greater thanbeta. The sign event does not depend on s. Its complement probability is bounded by2(K-1)/n using the rank K-1 projector, and therefore by1/64 on the stated domain.

This construction is a legitimate prior over deterministic admissible W. Prior averaging temporarily introduces dependence after conditioning, but the proof uses independent-product information only before conditioning and then separately bounds the change of data laws in total variation. There is no hidden iid-mixture assumption in the theorem class.

## Uniform full-document information

The baseline A_s B_i is independent of s because B_i1=B_i2. All its coordinates are positive. The old-anchor masses lie in [3alpha,5alpha]; the common-word masses have positive K-dependent floors. The contrast on rows3,4 is independent of s, while the derivative is supported only on the two rare anchors. This establishes the uniform variance orders V_i=O_K(beta), U_i=O_K(alpha beta), and the stronger pointwise max|b_i|^2=O_K(beta). The displayed |b_i|<=1/2 follows already from the coordinate perturbation and baseline mixture floors.

The derivative expansion over even subsets has orthogonal components: a coordinate in the symmetric difference contributes a mean-zero b or derivative of b. The q^2<=2q(q-1) bound gives L8 without an omitted N factor. The lower likelihood bound uses max|b|^2, not only its average. Its exponential constant is K-dependent and uniformly bounded in the short regime Nbeta<=1. This gives the rare-anchor factoralpha even when Nalpha is small.

For long documents, the complete-sign score has conditional mean zero, so information adds across the N tokens. Marginalization then yields O_K(Nalpha beta). Since (N-1)beta>1/2 when Nbeta>1 and N>=2, this is at most a K-dependent constant times F_N. Combining the two ranges is valid for every N>=2; no overlapping-pair independence or uniform Gaussian approximation is used.

For the unconditioned nuisance prior, document laws are independent but can differ with i. Fisher information still adds and the Hellinger path bound applies. The selected Delta makes its total-variation upper bound at most1/16 in both branches of the minimum. Conditioning adds at most2/64, yielding3/32. The stated quotient-loss testing constant is conservative and sufficient. This proves the displayed lower rate within the source's scope.

## Consequence and remaining gate

Together with an independently audited upper proof, this removes the two-topic/rank-one restriction from the matched alpha–beta–N frontier for every fixed K on the specified vocabularies. It does not remove known alpha, exact anchors, fixed dimension, or strong topic geometry. The prior-art question concerns the uniform joint rate, especially vanishing rare cells and weak mixture diversity across all N. This audit does not answer that historical question.
