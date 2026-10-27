# Root review of the classical-SPA contraction reduction

27 October 2026. Reviewed source SHA256
`6f6613f2758ffca32473fea5392a19775be72ee06384ef9a63e711e74335827d`,
including all six sections, against the locally retained Gillis--Vavasis
primary Theorem 3 and Assumption 1. This is internal mathematical review.

No blocking error was found in the stated reduction. The published H matrix
allows nonnegative columns of sum at most one, so the extra zero vertex in
the contraction argument is represented by a zero coefficient column and
does not increase the requested rank. With the squared norm score, L/mu=1.
The chosen noise threshold nu/[8K(1+80/nu^2)] is strictly below the published
threshold for every K>=2. The resulting Frobenius error is at most
nu/(8sqrt(K)), which suffices for the inverse guard.

The contraction identity is exact: a*p=(1-a)*r. Radially split the row
error into a norm-at-most-p component and an excess of norm at most Z.
The reliable ball absorbs the first component; the second and center error
remain uniform noise. At designated anchors the ideal point must instead
be kept equal to the original vertex; its extra displacement is bounded by
(1+2/r)p+Z. These two different ideal assignments are legitimate for the
classical theorem. The reconstruction must use the selected transformed
rows, as the source explicitly specifies.

The ball construction is also valid. On the original good-core event,
sigma_min(B_R)>=nu. Nonnegative column sums therefore exceed nu. Dividing
the sum of core rows by K+1 yields barycentric coordinates bounded below
by nu/(K+1) and total K/(K+1). A Euclidean perturbation of radius
nu^2/[2K(K+1)] changes the coefficient vector by norm at most
nu/[2K(K+1)], preserving both nonnegativity and total mass at most one.
The empirical center is observable; the population center is analysis-only.

The center-error expectation sums over the fixed frequent set and uses
the observable selected denominators >=2tau_*. This handles selection
dependence without treating the random core as fixed. The existing expected
anchor-penalty and maximum-excess bounds then imply the adaptive rate by
the same stable-event/Markov/reconstruction argument. Constants may be very
large, especially through 1/r; practical superiority does not follow.

This audit supports a concrete alternative derivation of the adaptive
upper guarantee from classical SPA plus the new-to-this-record contraction
step. It does not establish that the preprocessing itself was published
previously, nor that the original penalized recursion is literally the
same algorithm. The result narrows the defensible novelty claim to the
topic-specific statistical frontier and its quantitative ingredients.
