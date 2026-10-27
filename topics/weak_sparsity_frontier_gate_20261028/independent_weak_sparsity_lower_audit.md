# Independent audit of the weak-sparsity joint lower bound

28 October 2026. Source-bound analytic review by status_claim_check. No source was edited and no simulation was used as evidence for the theorem.

Reviewed source: `weak_sparsity_joint_lower.md`, SHA256 `bd43ef4d96e7f7c561bd90b5c90d0a1e32a4e3b4ad527c11bd03380de25f3c09`.

Read-only proof dependencies inspected: `../multitopic_frontier_gate_20261027/growing_vocabulary_lower.md`, SHA256 `a2f855ed3a2bb1ee5280ba04adce315ee1be07ed877da8c72a7815e729582091`, and the full likelihood/information calculation in `general_k_lower.md`, SHA256 `3edaed4fc1d02c5f6f5f58c8c9ed2ab1874d5e8df26d4c0d86281e60ce1dffe2`.

**Verdict:** no mathematical blocker found in the stated fixed-K, fixed-q, fixed-radius class. The new construction does put the ordinary sparse profile and the rare-anchor obstruction in the same class while retaining the exact all-N, shrinking-beta information scale. This is an internal proof audit, not external validation or novelty clearance.

## 1. The weak-q ledger is valid, including small q

With b_*=min{(1-q)/32,8^(-1/q)}, the decreasing power-law tail satisfies sum_j b_j<=1/32, hence T=2sum b_j<=1/16. Each old topic has exactly three positive core entries. Its lth largest tail entry is bounded by (3/2)b_* ceil(l/2)^(-1/q). For a full order index t>=4, at most three core entries precede it, so

    t A_(t),k^q
      <=2(3/2)^q b_*^q t/(t-3)
      <=(3/2)^q<=3/2.

The first three order indices contribute at most three. Each extra column has only three positive entries. Thus radius four is valid uniformly over vocabulary size and every fixed q in (0,1). There is no tacit growing radius. Constants in the final risk may depend on q; b_* can be extremely small near either endpoint, so the theorem should not be advertised as uniform in q.

The sparse rare-anchor family also has only three nonzero entries per topic, and therefore satisfies the same radius bound independently of alpha. Its zero padding is allowed by the declared class. The source explicitly does not require every vocabulary word to have positive probability.

## 2. Full topic geometry and interior mixtures

For the tail family the two common core rows form a symmetric block with singular values 2h>=7/8 and 2s0=1/2. In the rare-anchor family these are at least 15/16 and 3/8. Extra-topic anchor rows reveal the extra coefficient vector t divided by two. Solving the common two-row block then bounds the old coefficient vector by

    (8/3)[1+sqrt((K-2)/2)] ||Az||_2.

Together with ||t||<=2||Az||, this is more than sufficient for ||z||<=8sqrt(K)||Az||. Thus the stated unnormalized singular-value floor holds in both families, independently of the number of tail rows and alpha.

For the tail family, the common-row old-old inner product is 2[(7/16)^2-(1/4)^2]=33/128, old-extra entries are h/2>=7/32, and distinct extra-extra entries are 1/8. Diagonal entries are larger. The sparse rare-anchor core has larger corresponding bounds. Hence the same Gram floor holds throughout both constructions.

I also checked the deterministic-mixture covariance construction rather than treating conditioning as a formal label. Full signed cycles contribute a covariance floor c0 on H={x1=x2}; discarding any incomplete final cycle only weakens a positive-semidefinite sum. The n restriction ensures the retained complete cycles comprise at least half of the observations. For K=2, B_i=u gives a stronger rank-one floor on H and needs no cycling denominator.

After whitening the H block, the cross covariance with the sign direction has squared norm at most r(s)^2/2 on the stated projection event. Therefore the full covariance is bounded below by (1-1/sqrt(2))min{c0,r(s)^2}. Since c0>=32beta and r(s)^2>=16beta, this exceeds beta. The largest coordinate perturbation in the rare-anchor family is at most 1/(3sqrt(2)K), below 1/(4K); combined with the base floor 1/(2K), it yields the required mixture-entry floor. The tail family's perturbation is smaller.

The sign-conditioning failure probability is at most 2(K-1)/n<=1/64. Conditioning is independent of the topic parameter. The resulting prior is supported on admissible deterministic W, and does not replace the model by an iid random-mixture experiment.

## 3. The all-document-length information calculation retains the tail mass

For tail pair j, the baseline at each of its rows is 2B_i1 b_j. The first-two-topic difference is b_j v_j, so the relative sign contrast is +/-sqrt(2beta)v_j/B_i1. Consequently

    partial_(v_j) z_i,v=+/-sqrt(2beta)/B_i1,
    E_(d_i)[partial_(v_j)z_i,v]^2=8beta b_j/B_i1.

This exact factor agrees with S5. It is the reason the final information has b_j rather than a vocabulary-independent worst-case bound. The full relative contrast is bounded by C_Ksqrt(beta), uniformly over all simultaneous tail coordinates; its second moment is O_K(beta), because the total tail mass is bounded. Both the contrast and its coordinate derivative have baseline mean zero.

The dependency's derivative terms indexed by distinct even token subsets are orthogonal: a position in their symmetric difference contributes a mean-zero contrast or derivative. For a subset of size l, the squared derivative norm is at most l^2 U V^(l-1). Summing l>=2 gives the displayed 2U N(N-1)V(1+V)^(N-2) bound. The likelihood floor follows from the arithmetic-geometric mean inequality and max|z|^2<=C_Kbeta. Thus for Nbeta<=1 the information is at most C_K b_j N(N-1)beta^2. Revealing the sign for Nbeta>1 yields C_K b_j Nbeta. Since (N-1)beta>1/2 in that range, the latter is at most a constant times b_j G_N. No Gaussian approximation, pair independence, or large-N approximation enters this step.

For the rare-anchor family, the common-row additive contrasts are independent of s. At a rare anchor the relative contrast is +/-sqrt(beta)/(s sqrt(2)B_i1), and differentiation contributes an extra factor 1/s. The two baseline masses are 4Kalpha B_i1. Therefore its derivative second moment is exactly 4Kalpha beta/(s^4 B_i1), up to the displayed two opposite signs already summed, and is O_K(alpha beta). The same likelihood argument gives alpha G_N. Unused zero rows have neither probability nor derivative and can simply be removed from this likelihood calculation.

## 4. Quotient loss, coordinate amplitudes, and sparse profiles

A flipped bit changes four entries by b_j gamma_j each. Identity matching therefore costs 4sum_(changed j)b_j gamma_j, at most 1/8 across the whole hypercube. Swapping the old pair costs two on the common rows, while any permutation moving an extra topic costs at least one on an extra anchor row. Identity matching is consequently optimal. This validates the quotient metric used in the weighted Assouad argument.

The coordinate-dependent gamma_j=min{1,c_K/sqrt(nG_N b_j)} makes every unconditioned neighbor total variation at most 1/8. The common conditioning changes the two data laws by at most 1/64 each. Nearest-hypercube decoding is valid for the permutation quotient and loses at most a factor two. The resulting lower profile is therefore

    c_K sum_j min{b_j,e sqrt(b_j)}, e=1/sqrt(nG_N).

Summing the actual b_j=b_*j^(-1/q) sequence gives the three claimed profiles, including the harmonic factor at q=1/2 and the finite-vocabulary alternative for q>1/2. If the balancing index falls below one, the first tail coordinate still supplies a positive q-dependent lower constant. This is consistent with, and necessary for, the theorem's allowed q-dependent constants. Since p=K+2+2r and r>=4, substituting p for r costs only a fixed-K factor. The relation e<=a<=sqrt(2)e transfers the profiles with fixed constants.

The two rare-anchor hypotheses have identity distance 4Delta; old-pair swapping costs at least 3/2 on the common rows and moving extras costs at least one, so the same quotient separation is valid. Their anchor indices and topic-column probabilities are identical. Revealing that information indeed leaves both testing arguments unchanged.

Both lower families satisfy the same class restrictions, including the same weak-q radius, so taking the maximum of their capped lower bounds controls the capped sum within a constant factor. No claim that a single hypercube simultaneously realizes both obstructions is needed.

## 5. What this verdict does not establish

This review establishes no historical priority, practical estimator efficiency, or solution for diffuse topic matrices whose unnormalized singular-value floor shrinks. It does not promote the fixed-K theorem to growing K, the fixed-q constants to uniform endpoint behavior, or the radius-four construction to a strictly positive-every-word class. The upper/lower comparison still retains its displayed anchor logarithm. Earlier fixed-conditioning sparse rates remain antecedents rather than new conclusions.
