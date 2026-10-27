# Moderate-conditioning extension: negative exploratory result

28 October 2026. The prespecified local search did not find the faster,
less-extreme instability sought in this equicorrelation family. It does not
support launching another native solver or paid GPU experiment on these cases.

The fixed grid has n=10000, block size and rank 100, lambda=10^(-j) for
j=3,...,9, and delta/lambda in
{.0001,.001,.003,.01,.03,.1,.3,1,3,10}. Both stale and corrected gradient
operators were retained, for 140 cases. The calculation incorporates the
released ten-step Gaussian power estimate through its two required reciprocal
moments and uses the earlier six-coordinate covariance operator.

**No grid case has condition number below 10^9 and covariance spectral radius
above 1.0001.** For the smallest delta/lambda, the stale-operator radii at
lambda=10^(-3),...,10^(-9) are approximately

    .99446604, .99810836, .99940976, .99983469,
    .99997039, 1.00001343, 1.00002706.

The associated condition numbers range from approximately 10^7 to 10^13.
This indicates that the observed instability in this family remains tied to
extreme conditioning and a small growth rate. It does not establish that
moderately conditioned failure is impossible in this or another family.

The initial 128/256-node quadrature comparison had maximum radius discrepancy
5.15e-11. A separate calculation rationalized sqrt(lambda/100), formed the
operator with exact Fraction algebra, and used 512-node quadrature moments.
Across all 140 cases, relative lambda displacement was at most 2.23e-16 and
the largest radius discrepancy was 3.00e-15. This guards against cancellation
in constructing the small covariance matrix. The quadrature and eigensolves
are still numerical; no exact stability theorem or continuum bound follows.

All cases are retained in `exploration.json` and
`rationalized_operator_check.json`. The protocol and both implementations are
included. No native trajectories or random-search successes were added.

Read-only GitHub retrieval also confirmed that the two relevant public files,
`fast_krr/opts/askotchv2.py` and `fast_krr/opts/utils/general.py`, are byte-for-byte
identical to the pinned local versions. Their current blob identities and
contents are retained in `current_github_source.json`, with the comparison in
`current_source_comparison.json`. This is a two-file check, not a claim about
the entire repository's head or unretrieved changes.

This negative search does not upgrade the earlier kernel result, establish an
equal-time generalization advantage, or refute the paper's stated rate theorem.
No new Modal job, account setting change, or expenditure was required.
