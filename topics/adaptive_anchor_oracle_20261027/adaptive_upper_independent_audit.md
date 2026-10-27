# Independent hostile audit of the adaptive upper theorem

27 October 2026. Reviewer: `/root/hcm_adversarial_boundary`. This audit covers **Theorem A and Sections 1--4** of the bound source. Theorem B, its constrained-risk lower proof, and historical novelty are outside this audit.

Bound source: `adaptive_estimator_and_constrained_frontier.md`, SHA256
`e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`.

Read and checked against the bound dependencies:

* `../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256 `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`;
* `empirical_frequency_maximum_lemma.md`, SHA256 `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`.

**Verdict: no mathematical blocker found for Theorem A under its stated class and algorithm.** This is a fresh review of the composition. The earlier independent review of the maximum-error lemma alone would not have justified this verdict.

## 1. The observable procedure and its scope

The algorithm uses the count matrix, m, K, and the fixed common conditioning lower bounds. Its frequent threshold, determinant-core threshold, inverse threshold, and penalty constant depend only on those available quantities. There is no alpha, q, unknown anchor index, unknown W, or population candidate set in its implementation.

The selected frequent core is the same alpha-independent principal-moment core as in the known-strength proof. On that proof's good-core event it lies inside the deterministic set D_* of at most r_* rows and has a population vertex matrix with minimum singular value at least nu_0. Those constants are fixed class constants, even though they can be extremely conservative. Outside the good-core event the eventual topic estimate still has stochastic columns, so its loss is at most 2K.

The theorem is for fixed K and fixed weak-q radius/conditioning, exact anchor separability, independent multinomial documents with a common N>=2, and p<=m^D. Its absence of an upper bound on N is supported by the pair/Jensen concentration argument, not by an asymptotic normal approximation. The proof does not give an efficient growing-K algorithm or practical tuning constants.

## 2. Exact penalized-determinant inequality

I independently reconstructed A4, including the coefficient two in the score. Ideal and empirical normalized rows are nonnegative subprobability vectors and hence have Euclidean norm at most one. Replacing one determinant row while holding the others fixed changes its value by at most the Euclidean norm of that row difference: the cofactor vector has norm at most the product of the other row norms. Replacing all K rows and using the reverse triangle inequality gives

    ||det Yhat_J|-|det Y_J|| <= sum_(j in J)||Yhat_j-Y_j||
                              <= P_J+KZ.

Every ideal tuple satisfies |det Y_J|<=D=|det V|, since its barycentric matrix has substochastic rows and thus determinant of absolute value at most one. For the selected tuple S and a true-anchor tuple T,

    score(S)<=|det Y_S|-P_S+KZ,
    score(T)>=D-3P_T-KZ.

Selection maximality therefore yields exactly

    D-|det Y_S|+P_S<=3P_T+2KZ.

Both terms on the left are nonnegative. The argument controls the selected penalties P_S as well as the ideal determinant deficit. This is the crucial extra conclusion needed to transfer ideal vertex proximity to the observed selected rows. It is not obtained merely by maximizing an unpenalized noisy determinant.

No sign assumption on the determinant is used: absolute values and the determinant perturbation inequality handle arbitrary row ordering.

## 3. Substochastic near-maximal determinants and inverse stability

If |det B_S|>=1-eta and every row of B_S is nonnegative with sum at most one, Hadamard implies that each row has Euclidean norm at least 1-eta. For such a row,

    sum_k b_k^2 <= (max_k b_k) sum_k b_k <= max_k b_k.

Its largest coordinate is therefore at least 1-2eta. Its L1 distance to that coordinate vector is at most 4eta, even when its row sum is strictly below one. If two rows selected the same coordinate, subtracting them would produce a row of norm at most 8eta while all other row norms remain at most one. This contradicts |det B_S|>=1-eta when eta<1/10. Thus the selected coordinate vectors form a permutation.

Since D>=nu_0^K, the ideal vertex error is at most a fixed constant times P_T+Z. The selected empirical-row error has sum at most P_S+KZ and is controlled by the same quantity through A4. Consequently A5 follows with a common row permutation. Choosing a sufficiently small fixed threshold for P_T+Z makes the operator error below nu_0/2, so the displayed inverse guard necessarily passes on the stable event.

This conclusion does not require a separation gap between the best and second-best candidate tuples. Duplicate anchors or multiple exact maximizing tuples cause no issue. Zero-probability rows have barycentric row zero and are covered by the substochastic argument.

## 4. Zero counts, empirical penalties, and the adaptive core

The procedure includes all vocabulary rows. An unobserved row is assigned empirical normalized row zero and penalty two. Its normalized-row error is at most two, so its positive excess above the penalty is zero. This also holds for a true anchor with zero observed count. Such an anchor is not silently dropped from the comparator tuple: it contributes penalty two to P_T and is charged through the expected comparator bound.

For the data-selected core, the maximum-error lemma is applied to the entire deterministic set D_*, with constants based on its deterministic cardinality bound r_*. Restricting to any chosen subset cannot enlarge Euclidean row errors. A larger dimension-bound penalty only decreases positive excess. Therefore A6 is a valid unconditional bound for 1_(E_core) Z. No conditional law of a selected core and no independence from the same counts is assumed.

The true-anchor tuple T can be fixed from the population model before observing counts. It is a valid exact-vertex tuple for every possible core R, since normalizing a pure anchor always returns the corresponding row of V_R. Its choice need not change with the data-selected core.

## 5. Expected anchor penalties and alpha-uniform bad-event control

For a comparator anchor of corpus mass d>=alpha, split at d_hat=d/2. On the upper-frequency event, monotonicity of ell(x)/x bounds the penalty by a constant times

    min{1,sqrt(ell(d)/(md))+ell(d)/(md)}.

On its complement the capped penalty costs at most 2exp(-md/8). The cap handles small md without a hidden consistency requirement. Since ell(d)>=log 3, this exponential term is bounded by a constant times min{1,sqrt(ell(d)/(md))}; the linear term inside the minimum is absorbed by the square-root term with a fixed factor. Finally ell(d)/d decreases in d. Thus A7 holds uniformly in d>=alpha, with constants independent of alpha and its sequence.

Also m^(-1/2)<=C rho(alpha) on the entire allowed alpha range. Hence

    E[1_(E_core)(P_T+Z)]<=C rho(alpha).

The inverse/vertex stable event uses a fixed class-dependent threshold, not an alpha-dependent one. Markov's inequality therefore bounds the probability of its complement inside E_core by C rho(alpha). This explicitly pays for missing empirical anchors, selected capped rows, and observed inverse-guard failure. The bad-event output is stochastic, so multiplying by its loss bound 2K is valid. The good-core complement is separately paid through C p exp(-c_*m).

This argument remains valid when rho(alpha) is order one; it does not condition on a secretly high-probability weak-anchor event. Its starting sample-size threshold depends on the fixed class parameters, not on alpha.

## 6. Reconstruction, ordinary tails, and uniformity

The population identity C_jR V_R^(-1)=A_j diag(mu) is exact for every invertible selected population core. On the stable event, use the guarded empirical inverse for the numerator perturbation and the population numerator for the inverse perturbation. This gives A9 with one common permutation:

    ||Fhat-F Pi'||_1
       <= C sum_j sum_(r in D_*)|C_hat_jr-C_jr|
          +C(P_T+Z).

The second term uses the total population pair mass at most one. It carries neither a factor p nor a factor alpha^(-1). The first sum ranges over a deterministic set of bounded cardinality, so the exact expected pair bound gives the ordinary envelope sum_j min(h_j,sqrt(h_j/m)), despite the random selected core and tuple.

Every true raw column has mass mu_k>=c. Clipping cannot increase its L1 error, and column normalization costs at most 2/c, including zero-column fallback. The data-dependent permutation is harmless because the target loss minimizes over all permutations and all matrix norms in the displayed bounds are invariant under column permutations.

The weak-q envelope then gives the stated three tau_q regimes, with the critical q=1/2 logarithm retained. q appears only in this risk evaluation, not the estimator. Polynomial upper p absorbs the frequent-core exponential failure term; no polynomial lower bound on p is used. The all-N pair concentration and likelihood-free upper argument give uniformity over N>=2, including fixed n with increasing N. The proof is conditional on arbitrary deterministic W in the stated class throughout.

No source repair is requested. Theorem A is approved at this bound version and under the stated scope. This audit does not certify Theorem B, claim an ordinary minimax lower bound for unknown alpha, clear prior art, or establish a newsworthy breakthrough.
