# Independent audit of the unknown-anchor weak-diversity lower bound

28 October 2026. Root's independent analytic reconstruction, binding
`unknown_anchor_short_document_lower.md`, SHA256
`a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56`.
No producer source was edited. The exact fixture checker is supplementary;
this verdict follows from the formulas and the statistical testing argument.

**Verdict: no blocker found for the stated N=2 model and parameter domain.**
The result establishes a square-root anchor-location logarithm uniformly in
shrinking mixture diversity. It does not yet establish that logarithm for all
N or claim historical novelty.

## 1. A common legitimate parameter class

The row count is K+1+2M, so the chosen vocabulary cap fits p; unused rows are
zero in every model. For M=1, Ma<=1/16. For M>=2, the floor defining M gives
Ma<=a^{1-q}/16<=1/16. Thus b>=11/16. The shared, candidate, common and
extra-topic rows have exactly unit column sums. The two common rows have
smallest singular value b(1-2theta)/2>1/4; extra-topic anchor rows contribute
3/4 on disjoint columns. The shared row alone gives a Gram-entry floor1/16.

The weak-q count proof is uniform in alpha and vocabulary: at most two common
rows, one shared row and 2M candidate entries of size at most a contribute
at most 3+2Ma^q<4. For M=1 each old column has at most four nonzero entries,
which supplies the same bound without the floor estimate. Extra columns have
two. Topic anchors remain pure in the designated candidate pair.

Moving any extra topic costs at least3/2 at its own anchor row. If extras are
fixed, the common block costs2b theta under the identity and2b(1-theta) under
the old-topic swap. This establishes the null-to-alternative quotient
separation. Pairwise alternative separation is unnecessary for this test.

The bound log(2+M) comparable to log(2+min(p,alpha^{-q})) is legitimate with
constants depending on K,q: the untruncated integer count is at least
a^{-q}/32, the vocabulary cap is at least p/8 on the stated domain, and
a=4K alpha. Small candidate counts are protected by the additive2 in the log.

## 2. Unknown deterministic mixtures and conditioning

The complete plus/minus cycles span H={w1=w2}, with the common mean direction
orthogonal to the perturbation directions. At least half the samples lie in
complete cycles. Their least covariance eigenvalue on H is therefore at least
1/[8K^2 max(1,K-2)]. This also holds for K=2 directly.

The null and transformed mixtures have nonnegative stochastic columns. The
coordinate perturbation is bounded by1/(4K), leaving every entry at least
1/(4K). Hence every pure candidate row of mass a has corpus mass at least
a/(4K)=alpha, even after the sign prior is conditioned.

The conditioning event is the same for every hypothesis. Its excluded
probability is at most2(K-1)/n<=1/64. Whiten the covariance cross block by
Sigma_B and the contrast scale r. Its norm is at most1/sqrt2. Thus the entire
covariance is bounded below by
`(1-1/sqrt2)min(c0,r^2)`, which is greater than beta because c0>=128beta
and r^2>=16beta. The conditional prior is supported exclusively on legal
deterministic W matrices. Randomization is used only to prove a minimax lower
bound over that deterministic nuisance class.

## 3. Exact likelihood calculation

For a candidate pair the two baseline masses are a t_i and the relative
contrasts are opposite signs of r_i. Mixing the document sign gives the
ordered two-token density `d_x d_y(1+z_x z_y)`. The alternative leaves all
outside probabilities unchanged and multiplies only its candidate contrasts
by1+kappa. The two-token likelihood ratio is symmetric, so passing to actual
multinomial counts preserves these likelihood inner products exactly.

For two distinct alternatives, their likelihood differences overlap only on
the two ordered candidate-pair cross blocks. Each difference is kappa*z_x*z_y.
Averaging the two signs in each pair gives `1/(1-r_i^4)`. This reconstructs
the positive off-diagonal term

    2 c_i^2 kappa^2 r_i^4/(1-r_i^4).

For one alternative, the one-in-pair blocks give the first diagonal term in
A15. The both-in-pair block multiplies the contrast product by(1+kappa)^2,
giving its factor(2kappa+kappa^2)^2. Thus A14 and A15 both hold. In particular
the cross term cannot be discarded as an orthogonality argument.

The numeric envelopes also check. The denominators exceed1/2, kappa<=3theta,
and `sum d z^2<=t_i r_i^2`. The diagonal is bounded by
`(8a+72a^2)t_i^2 kappa^2 r_i^4<=13a t_i^2 kappa^2 r_i^4`.
The off-diagonal is at most16a^2 times the same last factor. Since
`t_i^2 r_i^4<=256K^2 beta^2`, both are smaller than the stated
`2^16 K^2` constants times their respective a or a^2 scales.

## 4. Mixture testing and the logarithm

The document laws are independent before conditioning. Their cross moments
therefore multiply, yielding the displayed exact diagonal/off-diagonal
chi-square expression for the uniform mixture of alternatives. With the
chosen theta, the cumulative diagonal exponent is at most epsilon*L and the
off-diagonal exponent is at most epsilon*a*L.

The elementary bounds used in A18 hold: concavity gives the diagonal
contribution at most2epsilon, and M<=1/a with a<=1/16 gives
`a log(2+M)<=1/4`, so the other contribution is at mostepsilon/2. The resulting
chi-square is below1/64. The standard total-variation bound is at most1/16.
Conditioning the prior changes each data marginal by at most1/64, giving
the claimed total distance3/32.

Testing whether an estimate lies within b theta of the null, and using the
quotient triangle inequality, converts testing error to topic loss in both
hypotheses. This proves the capped rate. At N=2 and beta<=1, the displayed
a_n is uniformly comparable to1/(beta sqrt(n)), so the final parameter
translation does not hide beta in a constant.

## 5. Combination and scope

The sparse tail and unknown-anchor lower bounds use different families in
the same class; the maximum bounds at least half the sum of their capped
rates. Their vocabulary domains must be intersected as the source states.
One can extend a parity-restricted tail vocabulary by a common zero row,
but that extension must be stated when reporting a theorem for every p.

The fixed-beta gauge and unknown-location mechanism are earlier portfolio
work and are correctly credited. The new checked step is the weak-sign
mixture calculation, including its nonzero cross terms. No all-N likelihood
claim, independent external endorsement, or novelty determination follows
from this audit. No repair is requested.
