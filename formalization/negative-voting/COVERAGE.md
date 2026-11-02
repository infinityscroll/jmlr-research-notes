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
| Affine comparison | Actual noise-difference identity, retained centroid square, complete odd/even residuals, same-mass offset cancellation, actual affine routing loss and its nonnegativity | Quantitative control of the prescribed-mass affine reference and the routing-bracket lower bound |
| Local cap calculus | Positive-part fibre integral; signed-forcing short-fibre Gaussian estimate with explicit cubic error; L32 bad-fibre and far-normal estimates; fractional-weight control; actual Gaussian slab bound and derived third-label tangent slope | Actual forcing identification and complete facet/cap assembly, including the all-amplitude conclusion |
| Normal trace | Actual kernel derivatives, literal normal-interval supremum bounds, OU composition, high-chaos projections and variable Lq smoothing; intrinsic Gaussian facet disintegration | Complete use of these estimates in the all-amplitude comparison |
| Classical Gaussian inputs | Full Gaussian hypercontractivity and the exact cited equal-threshold comparator, with no analytic premise at their concrete endpoints | Assembly of these inputs on the manuscript's varying facets |
| Prescribed Gaussian masses | Actual dual minimum, derivative and existence for distinct sites and positive masses | Quantitative offset control and moving-site inverse regularity |
| Offset Jacobian | Actual intrinsic facet Laplacian, symmetry, positive faces under affine independence, kernel exactly constants, strict centered positivity, C1 in offsets | Uniform spectral lower bound and joint moving-site derivatives |
| Convex Gaussian moments | Actual polyhedral first/second moments, covariance boundary identity, Ehrhard concavity and variance correction at least exp(-4)/(2(1+2 log(1/p))) | Use in the actual optimized covariance Hessian |
| Weighted facets | Actual third-label cover and degree estimate; degree-based weighted-energy estimate with explicit factors | Deriving the actual forcing bounds and closing the global comparison |
| Covariance algebra | Centered edge-strain identities, finite-dimensional weighted gauge selection and attributed singular Schur-complement calculus | Gaussian stratum identities, the assembled covariance factorization, optimized Hessian, and global covariance/offset estimates |
| Scalar assembly | Conditional local/exterior assembly and eventual thresholds for fixed supplied constants | Derivation of those constants uniformly in dimension and correlation |
| Discrete consequences | No completed discrete transfer formalization | Invariance, voting transfer and computational reductions |

Every geometric or analytic premise in a component theorem remains visible in
its Lean type. The prescribed-mass existence and normal regularity inputs now have separate
actual proofs; connecting their exact hypotheses to every use in the final
comparison remains an assembly obligation. Ordinary
Lq control alone cannot supply the claimed all-amplitude cap; the separate
[local comparison audit](LOCAL_COMPARISON_AUDIT_20261102.txt) records why.

The preserved analytic manuscripts and internal audits are research evidence,
not Lean dependencies. The build uses compiled Lean proofs and explicitly
attributed libraries; it never imports an internal audit verdict as an axiom.
