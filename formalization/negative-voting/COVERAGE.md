# Formalization coverage

The end target is `NegativeVoting.FullNegativeVotingStatement`: an absolute
large-alphabet threshold, every allowed finite ambient dimension, the whole
negative voting interval, all AE-measurable fractional assignments, and the
regular-simplex equality characterization. This is a proposition definition,
not a proved theorem or an axiom.

| Part of the argument | Checked content | Remaining obligation |
| --- | --- | --- |
| Actual Gaussian objective | Correlated Gaussian coupling, marginals, integrability, AE representatives, noise-value invariance | None for these statements |
| Infinite spectral representation | Actual Gaussian Hermite basis and Mehler action; absolute convergence; signed expansion for the full AE simplex class | Full comparison of competitors is separate |
| First three chaos levels | Exact masses, centroids, quadratic-moment tensor and integral test-tensor certificate | Quantitative geometric lower bounds for competing affine fans |
| Regular reference | Exact Gram matrix in dimension m−1 and every larger dimension; Gaussian balancing, full centroid vector, and exact centroid energy | Quantitative bounds for the expected maximum and higher reference moments |
| Affine comparison | Actual noise-difference identity, retained centroid square, complete odd/even residuals, same-mass offset cancellation, actual affine routing loss and its nonnegativity | Existence and quantitative control of the prescribed-mass affine reference; the routing-bracket lower bound |
| Local cap calculus | Positive-part fibre integral; signed-forcing short-fibre Gaussian estimate with explicit cubic error; L32 bad-fibre and far-normal estimates; fractional-weight control; actual Gaussian slab bound and derived third-label tangent slope | Normal derivative/supremum bounds, weighted facet energy, finite-fan covering/integration and all-amplitude conclusion |
| Normal trace | Exact Gaussian kernel row square; actual product-integral L32 trace for arbitrary L2 inputs, dimension-independent constant, 0<τ and τ²≤1/31; change of measure and Fubini | Normal derivative/supremum control and orthogonal transport to arbitrary facets |
| Classical Gaussian inputs | Full Gaussian hypercontractivity and the exact cited equal-threshold comparator, with no analytic premise at their concrete endpoints | Other convex Gaussian variance/isoperimetric inputs and their use on the manuscript's facets |
| Covariance algebra | Centered edge-strain identities and finite-dimensional weighted gauge selection | Gaussian stratum identities, the assembled covariance factorization, optimized Hessian, and global covariance/offset estimates |
| Scalar assembly | Conditional local/exterior assembly and eventual thresholds for fixed supplied constants | Derivation of those constants uniformly in dimension and correlation |
| Discrete consequences | No completed discrete transfer formalization | Invariance, voting transfer and computational reductions |

Every geometric or analytic premise in a component theorem remains visible in
its Lean type. In particular, a hypothesis that an affine reference has the
same masses is not a proof that such a reference exists. A local fibre bound
under a normal Lipschitz assumption is not a proof of that assumption. Ordinary
Lq control alone cannot supply the claimed all-amplitude cap; the separate
[local comparison audit](LOCAL_COMPARISON_AUDIT_20261102.txt) records why.

The preserved analytic manuscripts and internal audits are research evidence,
not Lean dependencies. The build uses compiled Lean proofs and explicitly
attributed libraries; it never imports an internal audit verdict as an axiom.
