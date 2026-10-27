# Independent audit of the sparse joint upper bound and observable conditioning threshold

28 October 2026. Analytic hostile review by `hcm_end_to_end`. No producer source or certificate was edited. No new experiment, simulation, remote job or author contact was used.

## Verdict and bound sources

**No mathematical blocker found within the stated scope.** The two new arguments survive independent reconstruction: the known-alpha screen has no ambient-vocabulary factor, and the post-reconstruction empirical threshold gives the exact instance profile despite its dependence on the row errors. The observable-eigenvalue corollary also preserves that profile without an independent tuning sample or a known mixture-conditioning floor.

This verdict binds:

* `weak_sparsity_joint_upper.md`, SHA256 `fb24214c2aab2d510f1182cc3000489a0d117f1fe5f3e7aa4d9ee3db81a83ab9`;
* `observable_conditioning_threshold.md`, SHA256 `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8`.

I also read the imported statistical argument in `../multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md`, SHA256 `de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`, and the coordinate transformation and maximum-volume lemma in `general_k_upper.md`, SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`. The review below distinguishes their imported ingredients from the new truncation/screening step. An internal proof audit is not a novelty assessment or expert peer review.

## 1. Model, scale and what the algorithms know

The model has independent document counts Multinomial(N,A w_i), arbitrary deterministic unknown W, N>=2, fixed K, a fixed positive mean-prevalence floor, a fixed positive unnormalized sigma_min(A) floor, and exact anchors of corpus mass at least the given alpha. Every finite p is permitted. Neither known anchor indices nor random/iid document mixtures are assumed.

Let m=nN and

    a_beta = 1/sqrt(m beta)+1/[beta sqrt(nN(N-1))],
    H_a(d) = sum_j min{d_j,a sqrt(d_j)}.

The first algorithm uses beta only for its final row threshold a_beta^2. The corollary replaces that input by the already computed empirical Kth pair-moment eigenvalue. Both still know K and alpha. The algorithms do not use a weak-sparsity exponent or radius. All outputs are stochastic, including fallback outputs, so the deterministic loss ceiling is 2K.

The corollary's sharper instance statement uses b=lambda_min(WW'/n), the actual eigenvalue. Passing to a class b>=beta is valid because both A(b) and H_(A(b))(d) are monotone in the displayed error scale. This does not require an estimator of the declared class bound beta.

## 2. Imported dimension-free error and spectral facts

The exact factorial-pair decomposition is Chat=MM'+R with M=A Sigma^(1/2)+E and R=Qbar-EE'. It is valid at N=2, odd N, and nonidentical document mixtures. The first-order row second moment uses the exact leverage identity sum_i w_i'Sigma^(-1)w_i=nK; no p-dimensional sum is introduced there.

For the degenerate term, the exact row covariance is

    E||Q_i,j||^2 = [Gamma_i,jj tr(Gamma_i)+||Gamma_i,j:||^2]
                                      /[N(N-1)],

and summing rows gives a bound of order 1/[N(N-1)] independent of p. This justifies the global event and each row's second moment, including the diagonal of the pair matrix.

I checked the dimension-free higher-moment argument used in W5. For a random balanced split of each document, conditional averaging of (a_i b_i'+b_i a_i')/2 reproduces every ordered distinct-token pair with coefficient 1/[N(N-1)]. Conditional Jensen is therefore applied to the actual full factorial statistic. Conditional on one group, the other groups form independent centered Hilbert vectors. The second Hilbert bound for (a_1j,...,a_nj) then gives the q sqrt(d_j)/(sqrt(n)N) term and a remainder bounded by C q^2/(nN). The group sizes floor(N/2), ceil(N/2) are both at least N/3, also at N=2. This is not the invalid substitution of disjoint pairs for an N-squared effective sample size.

The Hilbert Bernstein proof uses the Hessian of cosh(lambda||x||) and conditional centering; its constants are dimension free. The power-series remainder in the exponential yields the stated square-root and linear terms. W5 retains, rather than discards, the linear 1/(m beta) remainder.

On G0, the lower singular bound for M and the bound on R imply invertibility of M'Uhat. The transformation T=(M'Uhat)^(-1)Sigma^(-1/2)diag(mu) is used only in analysis. Its multiplication scales every candidate determinant by the same nonzero factor and cancels from reconstruction. Its row error satisfies delta_j=C(||E_j||/sqrt(beta)+||Qbar_j||/beta); the EE' contribution is absorbed using the global ||E|| bound on G0. These facts justify W4, W5 and W7 with no hidden p-dependent constant.

## 3. The rare false-inclusion calculation is uniform in p

For a row with d_j<alpha/4, let X_j=m dhat_j and mu_j=m d_j. Tokens within and across documents are independent even though their probabilities differ. Thus

    E 2^X_j=product_tokens(1+probability_j)<=exp(mu_j).

Applying Markov to the nonnegative variable 2^X_j-1, not to 2^X_j alone, gives

    P(X_j>=k) <= mu_j exp(mu_j)/(2^k-1).

The factor mu_j is essential. Summing it over rare rows costs at most m, not p. With x=m alpha and k=ceil(x/2), the resulting bound is at most 2m exp(-c x) for x>=2, with c=(log 2)/2-1/4>0.

I checked both regimes in the absorption into C log(2+1/alpha)/sqrt(m alpha). For x<=C0 log(2+1/alpha), that expression is bounded below by a positive universal constant after increasing C. For larger x, 1/alpha<=exp(log(2+1/alpha)) is absorbed into exp(c x/2), leaving 2x exp(-c x/2)<=C/sqrt(x). This also covers arbitrarily small alpha and does not assume a polynomial relation between p and m.

The deterministic frequent set has at most 4/alpha rows. Taking an Lr maximum with r=2+log(4/alpha) gives W8; the maximum factor (4/alpha)^(1/r) is bounded by e. Its error denominator is safe because d_j>=alpha/4. The separate rare-inclusion event is necessary and is explicitly retained. On its complement and small rho, all true anchors survive, all retained rows belong to that deterministic set, and their frequency denominators are bounded below by d_j/2.

The maximum-volume lemma is a K-dimensional statement. The near-unit determinant forces each selected stochastic row near a distinct coordinate vector; it does not require a gap between pure and almost-pure anchors. The number of candidates does not enter its constants. This gives the rowwise reconstruction bound C(delta_j+d_j rho), which is the correct form for the later truncation.

## 4. The empirical output threshold does not need independence

For I_j=1{dhat_j>=a^2}, the critical estimate is

    E[delta_j I_j]
       <=sqrt(E delta_j^2) sqrt(P(I_j=1))
       <=C a sqrt(d_j) min{1,sqrt(d_j)/a}
       =C min{a sqrt(d_j),d_j}.

The first step is unconditional Cauchy--Schwarz. The second uses Markov for the nonnegative empirical frequency and its exact mean d_j. No row-noise/threshold/core independence appears. This controls the total error of arbitrarily many rarely included rows by their probability mass.

For omitted mass, d_j<=2a^2 gives the profile by direct comparison, with factor at most sqrt(2). For d_j>2a^2, the frequency variance gives

    d_j P(dhat_j<a^2)<=4/m.

Since a>=1/sqrt(m) and d_j>2a^2, this is bounded by a constant times a sqrt(d_j). The two cases include d_j=0, where data and all errors are identically zero. Thus the retained-error and omitted-signal terms both sum to H_a(d).

The good-event restriction causes no problem: each nonnegative error term on that event is bounded above by its unconditional expectation. The rho term sums against total population mass one. The clipped-column target has mass at least mu0; clipping cannot increase its L1 error, and normalization costs at most 2/mu0, including the zero-column fallback. Truncation is performed after anchor selection, so it does not erase the information used to identify the simplex.

Finally, the global bad-event terms are bounded by C[a+r+L_alpha^2/(m alpha beta)] with r=L_alpha a/sqrt(alpha). Since r>=a and the last term is at most r^2, it is absorbed when r<=1; otherwise the deterministic loss bound applies. This proves the stated min{1,r+H_a(d)} form without dropping an unbounded Bernstein remainder.

## 5. Weak-q evaluation, including q=1/2

From #{j:d_j>=t}<=S t^(-q), one gets d_(j)<=(S/j)^(1/q). The profile function is increasing, so summation may use this envelope.

For q<1/2, the square-root series converges and H_a(d)<=C_(q,S) a. For q>1/2, splitting at j of order S a^(-2q) gives C_(q,S) a^(2(1-q)); summing a sqrt(d_(j)) only through p gives the alternative C_(q,S) a p^(1-1/(2q)). The minimum of these valid bounds is legitimate.

At q=1/2, d_(j)<=(S/j)^2. The high-frequency part is a harmonic sum up to the lesser of p and a constant times 1/a; the remaining tail has order a. Hence C_S a log(2+min{p,1/a}) is correct. There is no claim of constants uniform as q approaches 1/2 from either side.

The conversion from the source's columnwise weak-q convention is also sound: d_j is a convex combination of the A_jk, so d_j<=max_k A_jk and a union over the fixed K columns gives the corpus envelope. Conversely A_jk<=d_j/mu0. Corpus anchor mass and topic-column anchor mass are not identified without the prevalence factor.

## 6. Observable conditioning: both sides of the spectral comparison matter

Use b=lambda_min(Sigma) in the analysis-only G0. Its lower spectral estimate is

    lambda_K(Chat) >= (9/16-3/32)kappa0^2 b
                   =15kappa0^2 b/32.

For the upper estimate, ||A||_op<=sqrt(K). Testing A Sigma^(1/2) on a unit eigenvector for b gives sigma_K(A Sigma^(1/2))<=sqrt(Kb). Adding E and then R yields exactly the C0 b upper bound printed in O3. It is important that this is a smallest-singular-value test, not an assertion that the entire spectrum has scale b.

Comparison of the two positive terms of A(t) separately now gives cA A(b)<=A(lambda_hat)<=CA A(b). The nonpositive-eigenvalue fallback cannot occur on G0. Outside G0, no accuracy or unbiasedness assertion is needed.

On G, the random retained indicator is pointwise dominated by the deterministic-threshold indicator at cA^2 A(b)^2; the random omitted indicator is dominated by the deterministic-threshold indicator at CA^2 A(b)^2. Therefore the same unconditional Cauchy--Schwarz, Markov and Chebyshev bounds apply. There is no illicit conditioning on a random eigenvalue. Constants introduced by the sandwich depend only on the fixed geometry parameters. The a_b>=1 regime is covered by bounded loss regardless of whether the algorithm detects that population condition.

## Scope that must accompany any summary

This is an upper result with explicit alpha/beta/N dependence and an observable-beta implementation. It is not a matching weak-sparsity lower theorem, unknown-alpha adaptation, a computational efficiency result, or proof of historical novelty. The fixed unnormalized sigma_min(A) floor remains essential and excludes general all-word O(1/p) topic vectors. Exact anchors and fixed K remain. Expensive determinant search and same-sample thresholding are accurately described; the proof resolves the latter statistically, not computationally.

No producer repair is requested by this audit. The completed checks are analytic reconstructions of the stated bounds, not additional finite test counts presented as a substitute for proof.
