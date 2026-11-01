CURRENT SUCCESSOR: ../classical-hodge-normal-strain-20261102/README.txt removes
the recent-preprint regularity dependency using published 2017 results and
adds the finite-simplex normal-strain bound. This earlier record is preserved.

INDEPENDENT HODGE ROUTE TO GAUSSIAN COVARIANCE CONCAVITY
2 November 2026

This supplement gives a second route to the covariance theorem used by the
negative-voting candidate. It does not use the original finite-target
chain-complex proof or assume the global weighted-partition inequality.
The original manuscript, proof archive and theorem scope remain unchanged.

Start with ROOT_INDEPENDENT_HODGE_COVARIANCE_REVIEW_20261102.txt.
The argument is:
  1. A Hessian-weighted Gaussian Hodge estimate, proved for weak L2 fields
     using an exact three-index identity and graph-norm approximation.
  2. A sharp solenoidal discriminant and a Bregman coupling argument giving
     local upper covariance curvature, without differentiating transport maps.
  3. A closed dense class of target densities and an explicit W2 limit,
     using a named external regularity theorem at every covariance base.

PRIMARY PROOF AND INDEPENDENT AUDITS
primary/higher_dimension/HESSIAN_HODGE_LOCAL_STABILITY_20261102.txt
proof/HODGE_TO_COVARIANCE_LOCAL_TRANSFER_20261102.txt
counter/higher_dimension_audit/INDEPENDENT_HODGE_AND_TRANSFER_AUDIT_20261102.txt
counter/higher_dimension_audit/GLOBAL_EXTENSION_AND_GRAPH_DENSITY_ADDENDUM_20261102.txt

EXTERNAL DEPENDENCY
The final all-target extension imports Theorem 3.2 / Corollary 3.6 and
Proposition 3.8 of Maja Gwozdz, Caffarelli Estimates under Lipschitz
Perturbations, arXiv:2609.04052v1 (3 September 2026):
https://arxiv.org/html/2609.04052v1
Its exact statement and applicability were checked; its full proof was not
independently audited here. This route is explicitly conditional on that
recent preprint's regularity statement. The Hodge estimate and local
covariance argument are separate from that external dependency.

VERIFICATION
Run: python verify_hodge_algebra.py
The standard-library checker verifies seven symbolic polynomial identities
and rational fixtures in dimensions 2 through 8, totaling 1,603 exact checks.
It rejects optimized Python execution, which would disable assertions.
ROOT_FRESH_HODGE_ALGEBRA_REPLAY_20261102.json records the independent replay.
The code verifies algebra, not functional analysis or the external theorem.

STATUS
The new analytic chain has independent internal reviews. It is not an
external expert endorsement, a novelty certificate, or a new resolution of
the full named conjecture. No global nuclear-rearrangement or weighted
Gaussian partition theorem is claimed. The stronger large-alphabet
negative-voting candidate retains its existing validation/priority status.
