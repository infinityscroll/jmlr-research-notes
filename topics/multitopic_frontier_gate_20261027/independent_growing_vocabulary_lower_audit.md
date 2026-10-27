# Independent audit of the growing-vocabulary lower bound

27 October 2026. Reviewer: `/root/hcm_end_to_end`.

Bound source: `growing_vocabulary_lower.md`, SHA256 `a2f855ed3a2bb1ee5280ba04adce315ee1be07ed877da8c72a7815e729582091`. Read dependencies: `general_k_lower.md` SHA256 `3edaed4fc1d02c5f6f5f58c8c9ed2ab1874d5e8df26d4c0d86281e60ce1dffe2` and the model statement of `general_k_upper.md` SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`.

**Verdict: no blocking mathematical error found in the displayed lower-bound theorem.** This is an analytic internal audit, not a proof-assistant certificate, a review of the separate growing-p upper bound, or a novelty determination. No producer source was changed and no Monte Carlo experiment was used.

## 1. Admissible deterministic-mixture priors

The cycle covariance bound is correct. For K>=3, its contrast vectors are orthogonal to the uniform direction and have Gram matrix I+(1/2)11'. A complete balanced cycle therefore controls every direction in H with eigenvalue at least 1/[4K^2(K-2)]. The document restriction supplies at least half a cycle's normalized weight uniformly, yielding V2. For K=2 the single uniform direction has eigenvalue1/2, which is stronger than the stated c0=1/32.

The perturbation 4sqrt(beta) xi_i e has coordinate magnitude sqrt(8beta)<=1/(4K), so the interior weight condition follows. The event E has parameter-independent sign-prior failure probability at most 2(K-1)/n<=1/64. On E, whitening the cross block by Sigma_B gives norm at most1/sqrt2. Hence the stated full covariance lower bound is valid. With c0>=32beta, the other block has eigenvalue16beta, leaving ample slack above beta.

The proof uses independence of document signs ONLY before conditioning. Conditioning E couples the document laws, but the source subsequently uses total-variation transfer, not Fisher additivity for that conditioned law. Thus no false conditional independence enters the testing step. Each support point of the conditioned prior is a legitimate deterministic W, which is the correct minimax parameter interpretation.

## 2. Geometry and quotient distance

Each old topic column sums to 1/16+7/8+1/16=1. The tail perturbations remain nonnegative, and the fixed anchors give the required corpus masses under the interior mixture bound. Extra topics and their anchors also meet the stipulated requirements.

A direct singular-value check avoids relying only on an imported assertion. Write z=(v,t) for the old and extra coefficients. The old common-word 2-by-2 block has smallest singular value1/2. The common vector added by one extra topic has norm at most1/2. If top is the part of A z before the extra anchors, then

    ||v||<=2||top||+sqrt(K-2)||t||,
    ||z||^2<=8||top||^2+[2(K-2)+1]||t||^2,
    ||A z||^2=||top||^2+||t||^2/4.

These inequalities imply the claimed, looser bound ||z||^2<=64K||Az||^2. They are uniform in m and all tail parameters. The Gram-entry floors follow from the unchanged common block and extra anchor structure; the tail cannot subtract any contribution.

A differing hypercube bit changes four entries by gamma/(32m), giving gamma/(8m) exactly. An old-topic swap costs2 on the two common rows; a permutation moving an extra topic costs at least1 on an extra anchor row. Since the identity distance is at most1/8, the quotient distance really equals the displayed Hamming metric. This comparison covers arbitrary column permutations, not just an old-pair swap.

## 3. Full-document information and the crucial1/m factor

The baseline d_i=A_v B_i is independent of the ENTIRE hypercube parameter because B_i1=B_i2. Both its probability normalizations and the signed perturbations have zero parameter derivative in total mass. For a single tail coordinate,

    d_tail=B_i1/(16m),
    partial b_tail=+/-sqrt(2beta)/B_i1.

There are two affected rows, so

    E_d (partial b)^2
       =2*[B_i1/(16m)]*[2beta/B_i1^2]
       =beta/(4m B_i1).

This independently confirms the repaired V10 factor. The other second-moment and maximum bounds on b are uniform in m: all tail rows together have fixed total mass and bounded relative contrast. The anchor and common rows are fixed in number.

For the fair-sign mixture likelihood on all N ordered tokens, even subsets give an exact expansion. Derivatives belonging to distinct subsets are orthogonal because a token index in the symmetric difference contributes a single mean-zero b or partial b. For one subset of size r, Cauchy--Schwarz bounds the squared derivative norm by r^2 U V^(r-1). Summing and using r^2<=2r(r-1) yields the source's finite-N bound. The lower likelihood estimate follows from arithmetic-geometric mean and max b^2<=C_K beta. For Nbeta<=1 it gives information C_K N(N-1)beta^2/m; for Nbeta>1 revealing the sign gives C_K Nbeta/m. These combine to C_K G_N/m uniformly for all N>=2. No Gaussian, pair-subsampling, or fixed-N approximation is hidden here.

## 4. Assouad after conditioning, for arbitrary estimators

The Hellinger path is along one coordinate of length2gamma, so the bound TV<=gamma sqrt(C_K nG_N/m) has the correct factor. The choice of gamma controls it by1/8 even in the capped gamma=1 regime. Adding the two prior-conditioning discrepancies gives5/32, below1/4.

Nearest-hypercube decoding in the permutation-quotient metric is valid: the finite permutation group acts isometrically, so the quotient has the triangle inequality. Estimator loss is at least half the decoded hypercube distance. Pairing the remaining bits then gives at least3/8 average error per bit, yielding3gamma/128. This argument does not assume the estimator outputs a hypercube point or uses a fixed topic labeling.

For fixed K and m>=4, m and p=K+2+2m are comparable with constants depending only on K. The resulting sqrt(p) bound consequently has no concealed p-dependent constant. Designated anchor identities and topic probabilities are constant throughout the hypercube, so disclosing them does not distinguish its vertices.

## 5. Rare-anchor padding and final combination

The K=2 specialization of the earlier rare-anchor family is legitimate. Its only missing cycle directions disappear, while the constant-design covariance is stronger; the beta and n restrictions retain the interior-weight and projected-sign bounds. Its baseline anchor masses remain between3alpha and5alpha, and the same full-document Fisher calculation gives C_K alpha G_N.

Splitting a padding row into equal proportional children is a parameter-independent Markov randomization with a deterministic collapsing inverse. It preserves the full count experiment's statistical information and every entrywise-L1 distance, including after ANY topic permutation. Anchor information is unchanged. The common block and extra anchor rows used above remain intact. The shared extra-topic vector's norm decreases under splitting.

The largest distinct-extra Gram loss is at most1/400, leaving1/40-1/400=9/400>1/64. Old-extra loses at most(1/128)(1/20), and old-old at most(1/128)^2, so their larger floors remain valid. This confirms that the rare-anchor family embeds at every displayed p without a vocabulary-dependent geometric penalty.

Finally,

    1/(nG_N)=1/(nNbeta)+1/[nN(N-1)beta^2].

Thus a_n lies between 1/sqrt(nG_N) and sqrt(2)/sqrt(nG_N). The maximum of the two capped lower bounds controls the capped sum to within factor2. This proves the stated c_K min{1,(sqrt(p)+1/sqrt(alpha))a_n} claim in its precise domain.

## Scope retained

Constants may depend on fixed K. The theorem concerns the displayed vocabulary sizes p=K+2+2m with m>=4, exact anchors, interior deterministic mixtures, and the stated small alpha/beta ranges. It is not a growing-K theorem, unknown-anchor support-recovery theorem, or historical novelty claim. A matched growing-p upper result remains a separate proof obligation; this audit does not certify it by association.
