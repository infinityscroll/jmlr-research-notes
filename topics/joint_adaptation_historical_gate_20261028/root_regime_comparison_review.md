# Root check of the explicit short-document comparison

28 October 2026. Bound primary comparison
`PRIMARY_SUBSUMPTION_AND_SIGNIFICANCE.md`, SHA256
`7a1ae9c8a08f300eb6f8163dbaca9af14230ef801715783542525b0964cf9699`.
This is a bounded check of its new regime and inverse-modulus calculations,
not a fresh proof of the held full statistical theorem or a priority verdict.

The root read the author-hosted Bernoulli 2020 text around Theorem 7,
Corollary 8 and Remark 10. Remark 10 explicitly distinguishes implementation
for N>=2 from its proved recovery range. Its relaxed condition (49) still
requires average anchor mass of order log M/N and maximum document anchor
probability of order (log M)^2/N; it leaves optimality without (49) open.
The web reader timed out on that author URL, so this check used the retained
PDF/text bound by the source manifest, rather than treating a search snippet
as proof of the statement.

For fixed p and K=2, N=2, beta=c_beta n^(-1/8) and
alpha=c_alpha n^(-1/4), I independently computed

    T=n N(N-1) beta²/[1+(N-1)beta] asymp n^(3/4),
    a_beta asymp n^(-3/8),
    a_beta sqrt(log(1/alpha)/alpha)
        asymp n^(-1/4) sqrt(log n).

The fixed-p tail is smaller, of order a_beta. The held constrained lower
has exactly the latter anchor scale. Its small fixed class constants can be
met by sufficiently small c_alpha,c_beta and sufficiently large even n.
Condition (49) cannot hold along this sequence: its right sides grow, while
the relevant probabilities are bounded and the anchor mass shrinks. This
is a genuine uncovered regime of that particular theorem. The adaptation
claim remains constrained to estimators maintaining the strong-class rate;
it is not unrestricted minimax optimality for the entire older model.

I also checked the population inverse calculation. The two rare rows change
the contrast vector by total L1 mass 4 alpha sqrt(beta) kappa; the baseline
contrast norm is at most 2 sqrt(beta). Expanding the two outer products gives
16 alpha beta kappa+16 alpha² beta kappa². With kappa=2theta/(1-2theta)
and theta<=1/16, the displayed 64 alpha beta theta bound is conservative.
Combining it with topic separation at least (3/2)theta forces inverse
Lipschitz constant at least 3/(128 alpha beta). This rules out a uniform
constant-loss substitution of density error for topic error. It does not
rule out a weighted local inversion theorem, nor replace the full paired
count experiment by iid density samples.

The polynomial obstruction to direct C(4) application is also exact: every
N=2 multinomial count probability is of degree at most two in the free
probability coordinates, so every fourth derivative of every CDF value is
zero. A theorem requiring linear independence including that derivative
cannot be applied literally. This does not refute the cited finite-mixture
theorem or exhaust related literature.

The comparison strengthens the contribution case through an explicit
published restriction and a quantitative regime. It does not establish
historical priority, resolve the full printed question, or demonstrate a
practical advantage of the algorithm.
