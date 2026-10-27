# Weak sparsity with shrinking mixture diversity and every document length

28 October 2026. New mathematical source for independent audit. This is an upper bound, not a novelty clearance or a completed minimax theorem. The fixed-conditioning weak-sparsity rates were already established in the portfolio; the extension here is uniform dependence on mixture conditioning, anchor mass, and every N>=2.

Read-only dependency: `../multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md`, SHA256 `de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`. Its underlying exact estimator and maximum-volume lemma are in `general_k_upper.md`, SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`. We import the proved pair decomposition, dimension-free row moments, global spectral event, and K-dimensional affine geometry, and give the new frequency-screening and sparse-output arguments below.

## 1. Experiment, estimator, and instance theorem

The observations are independent X_i~Multinomial(N,A w_i), i=1,...,n, with N>=2. Both A and W have nonnegative stochastic columns; W is unknown and deterministic. Define

    mu=W1/n, Sigma=WW'/n, d=A mu, m=nN.

Fix K>=2, mu0>0 and kappa0>0. Assume

    p>=K, min_k mu_k>=mu0, sigma_min(A)>=kappa0,
    lambda_min(Sigma)>=beta>0,                            (W1)

and that each topic has an exact pure anchor whose corpus probability d_j is at least alpha>0. The estimator is given K, alpha and beta, but neither W nor the anchor locations. Necessarily beta<=1 and alpha<=1. The loss is

    loss(Ahat,A)=min_(Pi permutation)||Ahat-A Pi||_1,

where the matrix norm is entrywise L1. Every output has stochastic columns, so loss<=2K. Put

    a=1/sqrt(nN beta)+1/[beta sqrt(nN(N-1))],
    L_alpha=log(2+1/alpha),
    H_a(d)=sum_j min{d_j,a sqrt(d_j)}.                    (W2)

**Theorem.** An explicit estimator satisfies, uniformly over W1 and the anchor condition,

    E loss(Ahat,A)
       <= C min{1, L_alpha*a/sqrt(alpha)+H_a(d)}.         (W3)

Here and throughout C depends only on K,mu0,kappa0. In particular it is independent of p,n,N,alpha,beta and of any sparsity exponent or radius. There is no polynomial growth restriction on p.

The algorithm is the dependency's spectral/max-volume estimator, followed by one output-thresholding step:

1. Compute the empirical corpus frequencies dhat and the unbiased factorial-pair matrix Chat. Take Uhat for its K largest eigenvalues and put Zhat=Chat Uhat.
2. Among rows with dhat_j>=alpha/2, choose K distinct normalized rows Zhat_j/dhat_j maximizing absolute determinant, with deterministic tie-breaking. If insufficient rows or the selected matrix is singular, return fixed stochastic columns.
3. Reconstruct the raw matrix Xhat=Zhat times the inverse selected normalized-row matrix. **Only now**, set every row with dhat_j<a^2 to zero. Clip negatives and normalize columns. A zero column or nonfinite result uses a fixed stochastic fallback for that column.

If a>=1 the estimator may return the fixed fallback directly. This causes no issue in W3 because L_alpha*a/sqrt(alpha)>=1. No estimated or oracle population row probabilities enter the algorithm. Thresholding follows anchor identification, and therefore does not remove anchor information from the simplex-selection problem. The estimator uses beta through a; adaptation to unknown beta is not claimed. It does not use q or a weak-sparsity radius.

## 2. Imported rowwise reconstruction bounds

Use the exact notation E,Qbar,G0 of Sections 3--6 of the dependency. Define on all outcomes

    delta_j=C[||E_j||_2/sqrt(beta)+||Qbar_j||_2/beta].

The dimension-free second moments U4--U5 and Minkowski's inequality imply

    E delta_j^2 <= C d_j a^2,  P(G0^c)<=C a.             (W4)

The individual Lr bounds U6--U9, for r>=2, also imply

    ||delta_j+|dhat_j-d_j|||_(Lr)
       <=C[r a sqrt(d_j)+r^2/(m beta)].                 (W5)

The scalar frequency variance is

    E(dhat_j-d_j)^2 <=d_j/m.                            (W6)

These bounds hold for nonidentical document mixtures, include odd N, and have no p-dependent constant. A zero-probability row has zero observations and zero errors identically.

On G0 the analysis-only invertible coordinate transformation T from U10 gives

    Zhat T=X+D, X=A diag(mu), ||D_j||_2<=delta_j.         (W7)

It is not used by the estimator. All candidate determinants receive the same factor det(T), and T cancels in the raw reconstruction.

## 3. Removing the vocabulary factor from anchor screening

Let J_*={j:d_j>=alpha/4}, so |J_*|<=4/alpha. Set

    rho=max_(j in J_*) [delta_j+|dhat_j-d_j|]/d_j.

Choose r=2+log(4/alpha). The finite-set Lr maximum bound and W5 give

    E rho <=C[L_alpha*a/sqrt(alpha)
                       +L_alpha^2/(m alpha beta)].      (W8)

This only controls a deterministic finite high-frequency set. False inclusion of any other row must be bounded separately; it is not silently covered by W8.

Let F be the event that some j with d_j<alpha/4 satisfies dhat_j>=alpha/2. Write x=m alpha, k=ceil(x/2), and X_j=m dhat_j. The token indicators are independent Bernoulli variables, though their means may differ between documents. For mu_j=m d_j,

    E 2^(X_j) <=exp(mu_j),
    P(X_j>=k) <=[E 2^(X_j)-1]/(2^k-1)
                <=mu_j exp(mu_j)/(2^k-1).

Summing over all rare rows and using sum_j mu_j<=m gives, when x>=2,

    P(F)<=min{1, 2m exp(-c x)},
    c=(log 2)/2-1/4>0.                                 (W9)

For x<2 use P(F)<=1. Uniformly in all x>0 and 0<alpha<=1,

    P(F)<=C L_alpha/sqrt(m alpha)
          <=C L_alpha*a/sqrt(alpha).                    (W10)

For completeness, choose C0>=max{2,4/c}. If x<=C0 L_alpha, L_alpha/sqrt(x)>=sqrt(log 3/C0), and a sufficiently large universal C bounds one. If x>C0 L_alpha, then 1/alpha<=exp(L_alpha)<=exp(c x/2), so the right side of W9 is at most 2x exp(-c x/2)<=C/sqrt(x)<=C L_alpha/sqrt(x). This proves W10 without a union factor p or a restriction on how p grows.

On F^c intersect {rho<=rho0}, with rho0 a sufficiently small constant depending only on K, all true anchors are retained, every retained row lies in J_*, and dhat_j>=d_j/2 on J_*. On G0 as well, each retained analysis-coordinate normalized row differs by at most C rho from its stochastic barycentric row X_j/d_j. The dependency's deterministic maximum-volume lemma yields one common permutation Pi and a selected analysis-coordinate matrix Bhat with

    ||Bhat-Pi||_op<=C rho,
    ||Bhat^(-1)||_op<=C,
    ||Bhat^(-1)-Pi'||_op<=C rho.

Thus the actual raw reconstruction, before output thresholding, obeys row by row

    ||Xhat_j-X_j Pi'||_1 <=C(delta_j+d_j rho).            (W11)

Indeed Xhat=(X+D)Bhat^(-1), and ||X_j||_1=d_j. The constants depend on K, not the number of candidate or output rows. This is the rowwise form of U15.

Let G=G0 intersect F^c intersect {rho<=rho0}. By W4, W8--W10 and Markov,

    P(G^c)<=C[a+L_alpha*a/sqrt(alpha)
                         +L_alpha^2/(m alpha beta)].    (W12)

## 4. An exact instance-profile bound from output thresholding

Set tau=a^2, and let I_j=1{dhat_j>=tau}. Assume a<1, since the fallback case is already covered. Let Xtilde have row I_j Xhat_j before clipping/normalization. On G, W11 gives

    ||Xtilde-X Pi'||_1
       <=C sum_j delta_j I_j+C rho+sum_j d_j(1-I_j).    (W13)

No independence between I_j, the row error, and the selected core is assumed.

For the retained row error, Cauchy--Schwarz, W4, and Markov's inequality for the nonnegative dhat_j imply

    E[delta_j I_j]
       <=C a sqrt(d_j) sqrt(P(dhat_j>=tau))
       <=C a sqrt(d_j) min{1,sqrt(d_j/tau)}
       = C min{a sqrt(d_j),d_j}.                        (W14)

This controls arbitrarily many rare false inclusions by their probability mass. It needs no maximum over vocabulary rows and no sparsity assumption.

For the omitted signal mass, if d_j<=2tau then

    d_j P(dhat_j<tau)<=d_j
        <=sqrt(2) min{d_j,a sqrt(d_j)}.

If d_j>2tau, Chebyshev and W6 give

    d_j P(dhat_j<tau)<=d_j^2/[m(d_j-tau)^2]<=4/m.

Since a>=1/sqrt(m beta)>=1/sqrt(m), and d_j>2a^2, this is at most C a sqrt(d_j). In this case min{d_j,a sqrt(d_j)}=a sqrt(d_j). Consequently

    sum_j d_j P(dhat_j<tau)<=C H_a(d).                  (W15)

These statements include d_j=0 by continuity or by the zero-row observation. Taking expectations in W13 restricted to G, then using W14--W15 unconditionally, bounds the expected raw error by C[H_a(d)+E rho].

Each population X column has mass mu_k>=mu0. Clipping and normalization increase the column error relative to A Pi by at most 2/mu0 times its raw error. If an entire clipped column is zero, that raw column error is at least mu0 and the fixed stochastic fallback still satisfies the same bound. Thus neither thresholding away an anchor output row nor a zero output column invalidates the normalization argument.

Use loss<=2K on G^c. W8 and W12 now prove

    E loss<=C[H_a(d)+L_alpha*a/sqrt(alpha)
                             +L_alpha^2/(m alpha beta)].

Write r=L_alpha*a/sqrt(alpha). Since a^2>=1/(m beta), the last term is at most r^2. For r<=1 it is absorbed by r; for r>1 use bounded loss. This proves W3.

## 5. Fixed-radius weak-q consequences

Suppose, in addition, for known or unknown q in (0,1) and radius S<infinity,

    #{j:d_j>=t}<=S t^(-q), 0<t<=1.                      (W16)

The estimator remains unchanged and uses neither q nor S. For fixed S and q, the decreasing rearrangement satisfies d_(j)<=(S/j)^(1/q). Since x->min{x,a sqrt(x)} is increasing, summation up to and beyond j approximately S a^(-2q) gives, for 0<a<1,

    H_a(d)<=C_(q,S) a,                                  0<q<1/2,
    H_a(d)<=C_S a log(2+min{p,1/a}),                     q=1/2,
    H_a(d)<=C_(q,S) min{a^(2(1-q)),
                              a p^(1-1/(2q))},         1/2<q<1.  (W17)

At q=1/2 the high-frequency sum is harmonic and the remaining tail is O(a); at q>1/2 the two expressions follow respectively from splitting at S a^(-2q) and from summing a(S/j)^(1/(2q)) through p. At q<1/2 the square-root series converges. Constants are allowed to depend on the fixed q and radius; no assertion uniform as q approaches 1/2 is made. The profile W3, rather than W17, remains meaningful uniformly across such exponents.

If the source-paper convention is columnwise weak-q, #{j:A_jk>=t}<=S_A t^(-q) for each k, then d_j=sum_k mu_k A_jk<=max_k A_jk implies W16 with S<=K S_A. Conversely the prevalence floor yields A_jk<=d_j/mu0, giving a columnwise envelope with constants changed only by mu0. This explicitly aligns the two conventions without identifying corpus anchor mass alpha with a topic-column anchor mass.

Combining W3 and W17 gives the sparse joint upper frontier with an additive anchor-identification term L_alpha*a/sqrt(alpha). The all-N scale may equivalently be expressed up to universal factors through

    G_N=N(N-1) beta^2/[1+(N-1)beta],
    a approximately 1/sqrt(n G_N).

Indeed the square of the latter quantity is the sum of the squares of the two terms defining a. This retains both the short-document beta^(-1) and long-document beta^(-1/2) regimes. It is not obtained by hiding beta in a fixed constant.

## 6. Existing results and limits

`../novelty_decisive_gate_20261027/strong_anchor_uniform_document_length_minimax.md` already proves the three weak-q rates at fixed mixture conditioning and fixed anchor strength, including the q=1/2 logarithm and unrestricted N. `../adaptive_anchor_oracle_20261027/adaptive_estimator_and_constrained_frontier.md` already supplies unknown-alpha/q adaptation at fixed conditioning using empirical-frequency penalties. We do not re-label either conclusion as new.

The present extension uses the newer anisotropic spectral/degenerate-pair analysis to track shrinking beta jointly with alpha and N, removes ambient p from known-alpha screening, and obtains an exact row-probability profile by a post-reconstruction threshold. The threshold proof itself is a classical second-moment truncation argument. The concentration and maximum-volume geometry are also established tools. A matching lower bound with the same shrinking-beta/all-N dependence and a primary-literature comparison are separate obligations.

Retained limitations: exact anchors; known alpha and beta; fixed K, prevalence floor, and unnormalized sigma_min(A) floor; potentially expensive exact maximum-volume search. In particular, the strong topic-geometry floor excludes a general diffuse regime where all topic probabilities are O(1/p). No unknown-beta adaptation, practical superiority, full Tran--Liu--Donnat class resolution, or newsworthiness is claimed here.
