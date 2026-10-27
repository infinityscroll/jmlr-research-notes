# Independent audit of penalized successive projection

27 October 2026. Mathematical source review by an agent other than the theorem's author. This is an internal audit, not external expert review, formal verification, a runtime experiment, or novelty clearance.

## Source binding and verdict

Reviewed the complete `penalized_successive_projection_theorem.md`, SHA256
`93a8dcf921f94cc594ef08f01b7620ff8427be8c686fbc90704771165b36b7a7`.
The three dependency hashes printed in that source were recomputed and match:

- Adaptive estimator/frontier: `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`.
- Empirical-frequency lemma: `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`.
- Known-strength experiment/core theorem: `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`.

**Verdict: no blocking mathematical error found in Lemma G1, its transfer to Theorem G, or the stated anchor-stage operation count.** The proof preserves the adaptive risk bound in its fixed-K, fixed-conditioning class. It removes vocabulary-wide anchor-tuple enumeration, while retaining frequent-core enumeration. No source repair is requested.

## 1. Projected geometry and score inequality

For a subset of rows of V, its least row singular value is at least nu: pad the coefficient vector by zeros and apply the full square-matrix lower bound. If B=A+E is the corresponding empirical row matrix, with Frobenius error e<=nu/2, Weyl's bound gives least row singular value at least nu-e. The two one-sided span gaps are at most e/nu and e/(nu-e), respectively. Their sum is at most 3e/nu. Thus the source's more generous projector bound 4e/nu is valid. This argument does not require the selected empirical rows to be nonnegative after projection.

For a still-unmatched vertex, taking distance from the span of already matched true rows retains coefficient one on its own row. For the difference of two unmatched vertices, coefficients one and minus one remain. Consequently their projected norms are at least nu and their pairwise separation at least sqrt(2)nu. Their distances to the zero atom are at least nu. No assumption about a geometric gap between pure anchors and nearly pure nonanchors enters.

Let f_j=||Q y_j||^2 and fhat_j=||Qhat yhat_j||^2. Because both original rows have norm at most one,

    |fhat_j-f_j| <= 2||yhat_j-y_j|| + ||Qhat-Q||
                 <= 2p_j+2Z+h.

The projector contribution is bounded by h, rather than 2h, since the squared norm of an orthogonal projection equals its quadratic form. Comparing the winning score fhat_j-4p_j with an available maximizing anchor gives exactly

    M^2-f_j+2p_j <= 6p_anchor+4Z+2h.

The left-hand terms are separately nonnegative. In particular, a row with a large unpenalized error cannot silently enter the induction: its selected penalty is bounded by half the displayed right side. This is the essential difference from invoking a uniform-noise SPA theorem without accounting for rare rows.

## 2. New-vertex mass, representative availability, and induction

After projection by the TRUE selected span, aggregate all mass on previously matched vertices and all missing substochastic mass into one zero atom. Let its mass be w_0. All other atoms are projected unmatched vertices. Their weights sum to one. With M the largest remaining projected norm, the identity

    M^2-||sum_i w_i x_i||^2
      = sum_i w_i(M^2-||x_i||^2)
        + sum_(i<j) w_i w_j ||x_i-x_j||^2

has only nonnegative terms. If its left side is at most delta, then

    w_0 <= delta/nu^2,
    1-max_i w_i <= 1-sum_i w_i^2 <= 2delta/nu^2.

At delta<=nu^2/8 the maximizing mass is at least 3/4, whereas the zero atom has mass at most 1/8. Therefore the dominant atom must be a previously unmatched vertex. Returning to the unprojected barycentric representation yields

    ||y_j-v_k|| <= 2(1-b_jk) <= 4delta/nu^2.

This is a linear error estimate. It does not use the invalid inference that a squared-norm deficit directly bounds an unprojected vector linearly.

There is no circularity concerning excluded anchor indices. If a chosen index happens to be a designated representative a(l), its exact barycentric vector is e_l. The mass conclusion forces its assigned vertex to be l. A representative for a still-unmatched vertex cannot have been removed earlier. Duplicate anchor rows do not affect this argument.

Combining ideal-row error, selected penalty, and excess error gives the source's one-row bound C_nu delta+Z, with C_nu=4/nu^2+1/2. Stacking rows costs at most the sum of Frobenius errors, so

    E_(t+1) <= (1+8C_nu/nu) E_t + (6C_nu+1) epsilon.

The constants L_t increase. The two parts of epsilon_0 in G6 ensure E_t<=nu/2 and delta_t<=nu^2/8 at every step, including the newly appended matrix. Thus the argument establishes full row rank before excluding the zero-residual guard. At K steps it establishes both a single permutation matching all vertices and the final inverse guard. Zero excess or exact ties require no separate generic-position assumption.

## 3. Statistical composition and guards

The empirical normalized pair-moment rows are indeed subprobability vectors: their entries are nonnegative and the sum over any core is at most the empirical word frequency before division. The population identity gives the same property. Zero empirical counts use the specified zero row and penalty two, so they contribute zero to the positive excess defining Z; they are not discarded from the oracle anchor-penalty calculation.

On the unchanged good-core event, every possible selected core is contained in the deterministic D_* and its population vertex matrix has least singular value at least nu_0. Bounding errors first on D_* and then restricting coordinates therefore remains legitimate for a data-dependent core. No conditional concentration or independence of the selected core is needed.

The stochastic input is exactly E[1_core Z]<=C/sqrt(m) and E P_T<=C rho(alpha). Markov's inequality controls the complement of epsilon<=epsilon_0 inside the core event. The constants are fixed class constants, potentially large; they do not depend on alpha or p. Every fallback has loss at most 2K.

On the stable event, the matched empirical vertex inverse is uniformly bounded by 2/nu_0. Resolvent perturbation and the population identity C_(j,R)V_R^(-1)=A_j diag(mu) give G21 with a single permutation. The population numerator's total mass over all j and core coordinates is at most one, which prevents a spurious p multiplier in the inverse-error term. The random core's numerator fluctuation is bounded by summing over deterministic D_* before taking expectations. Clipping/column normalization then use the same fixed lower bound on mu as the audited predecessor.

These checks preserve the predecessor's alpha-independent estimator, arbitrary N>=2, weak-q tail contribution, and polynomial-vocabulary absorption. They prove no new lower theorem; Theorem B applies because the new estimator inherits the required strong-class upper risk bound. The exact separability and common conditioning assumptions remain substantive.

## 4. What computation is actually improved

Given the p-by-K normalized rows and penalties, maintain all projected residuals. Each new nonzero direction updates every residual by one rank-one orthogonal subtraction, costing O(pK). Repeating K times costs O(pK^2). Original selected rows must be retained for reconstruction; using the projected residual rows in the inverse would be a different estimator.

The final inverse costs O(K^3). For a literal exact-arithmetic interpretation, the singular-value guard can be evaluated by testing positive semidefiniteness of Vhat Vhat'-(nu_0^2/4)I, using an exact symmetric elimination with zero-pivot checks. Thus no claim of exact finite-precision SVD is required. Rank-one projection can also be written without a square root, as rr'/||r||^2. The statement conditions on already formed penalties and moments; their formation is outside this operation count.

The frequent set H has cardinality at most 1/(2tau_*), from its empirical-frequency threshold and total frequency one. Its K-subset core search remains, and this constant can be very large as a function of K or conditioning. The source properly avoids an end-to-end practical-runtime or polynomial-in-K claim.

## 5. Checked primary antecedent and limits of this verdict

The cited [Gillis–Vavasis primary manuscript](https://optimization-online.org/wp-content/uploads/2012/08/3557.pdf) was inspected directly. Algorithm 1 selects by a residual score and projects away the chosen direction; Section 2.3 assumes every column perturbation has norm at most one common epsilon, and Section 4.1 specializes to the squared Euclidean norm. Thus the source correctly credits the basic algorithm and geometry. That cited uniform-noise hypothesis does not directly supply the displayed empirical-frequency oracle inequality. This bounded comparison does not exclude other penalized or heteroscedastic predecessors and is not a priority finding.

This audit independently reconstructs the proof rather than treating a finite simulation or a producer's checker as certification. It does not certify floating-point behavior, tuned practical constants, approximate separability, growing K, or historical novelty.
