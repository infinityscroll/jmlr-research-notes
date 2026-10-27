# Independent audit of the matching constrained-risk lower theorem

27 October 2026. Bound source: `adaptive_estimator_and_constrained_frontier.md`, SHA256 `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`.

**Scope:** Theorem B, Section 5, and the scope statements in Section 6. Theorem A's estimator and penalized-selection proof are not certified by this audit. The experiment/class definition was checked against `../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256 `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`.

**Verdict: no mathematical blocker found.** The varying-theta construction yields the stated `liminf >= 1/32` for every positive sequence alpha_m tending to zero, with fixed p>=12, K=2, q=1/2, and the explicitly required uniform strong-class root-m guarantee. It is a constrained-risk conclusion, not an ordinary known-alpha minimax conclusion or a novelty finding.

## 1. Positive experiment and common class

Set a=2alpha<=1/128 and 0<theta<=1/16. For the positive padding rows,

    e=sum_(l=1)^(p-7) (1/32)2^(-2(l+6))
      < (1/32)2^(-14)/(1-1/4)=1/393216.

Thus

    b=5/8-a-e > 242687/393216 > 1/2.

Every topic column sums to zeta+a0+a+b+e=1. The nonrare alternative rows are strictly positive in both topics because theta>0 and B,T have positive entries. The only zero entries are the exact-anchor zeros in the two rare rows. Every observable categorical probability is strictly positive because the mixture weights are positive. The construction therefore has common full count support and does not exploit a positivity failure.

The two W0 document groups have columns (3/4,1/4)' and its reversal. T has eigenvalues 1 and 1-2theta, and

    T^(-1)(3/4,1/4)'
      =(1/2+1/[4(1-2theta)], 1/2-1/[4(1-2theta)])'.

The smallest entry is at least 3/14. Equal groups give the same corpus topic mean mu=(1/2,1/2) under both models. The second-moment eigenvalues are

    eig(W0W0'/n)={1/2,1/8},
    eig(W1W1'/n)={1/2,1/[8(1-2theta)^2]}.

These satisfy the source's `Sigma=WW'/n` conditioning requirement. No random prior on document weights is introduced. Only n even is required; N is arbitrary >=2, with no upper bound. In particular the argument does not require m divisible by four or n tending to infinity separately from m.

The shared row contributes 1/16 to each entry of A'A. The bottom block bBT has smallest singular value b(1-2theta)/2, because B and T are symmetric commuting matrices with contrast eigenvalues 1/2 and 1-2theta. The full topic matrix has at least that singular value by Gram-matrix domination. This is uniformly larger than the class requirement `kappa=sqrt(2)/128`; the null bound is still stronger.

For each alternative column, the sum of entry square roots is bounded by

    1/2 + sqrt(1/8)(1+1/4) + sqrt(1/128)
        +sqrt(2*5/8) +(1/sqrt(32))2^(-6) < 4.

The same bound covers the null. The strong block uses sqrt(1-theta)<=1 and sqrt(theta)<=1/4; the bottom block uses Cauchy–Schwarz and total mass b; the infinite padding sum bounds every fixed p. Therefore `j sqrt(A_(j),k)<=sum_l sqrt(A_lk)<4`. This is the exact radius-four weak-1/2 convention; it is independent of how rare and padding rows interleave in decreasing order.

The null strong anchors have corpus mass 1/16, exceeding alpha_s=1/32. The alternative's only pure anchors have mass a/2=alpha. Both models lie in the same fixed conditioning/overlap/weak-sparsity class for all sufficiently large m. Fixed p>=12 equals or exceeds the source minimum `p0(2)=12` and eventually satisfies p<=m^D for any fixed D>0.

## 2. Exact full-count likelihood-ratio bound

The common rows are unchanged because (1,1)T^(-1)=(1,1); a0 T and bBT cancel the transformed mixture weights. Consequently only the two rare observable probabilities change. In one group they change from a(3/4,1/4) to

    a(3/4+delta,1/4-delta),
    delta=theta/[2(1-2theta)].

The other group reverses the coordinates. The exact one-token null-relative chi-square increment is

    v=(a delta)^2[1/(3a/4)+1/(a/4)]
      =4a theta^2/[3(1-2theta)^2]
      =8alpha theta^2/[3(1-2theta)^2]
      <=(512/147)alpha theta^2.

The last constant uses 1-2theta>=7/8 and is exact: `(8/3)*(8/7)^2=512/147`.

For each observed multinomial count vector X of total N, the likelihood ratio is `prod_j(p1_j/p0_j)^X_j`. Summing its square with the multinomial coefficient gives

    E0 L_i^2=(sum_j p1_j^2/p0_j)^N=(1+v)^N.

Both groups have the same v, and the documents are independent. Thus the exact full-data second moment is `(1+v)^m`, and

    E0 Q^2 <= exp((512/147)m alpha theta^2)
            = exp((2/147) min{m alpha,L}),
    L=log(1/alpha).

This holds for the actual count experiment for every N>=2, not only an ordered-token experiment. The equality on the last line is an equality of the displayed exponential bound after inserting theta; the exact second moment itself remains `(1+v)^m`. There is no KL-to-second-moment substitution.

## 3. Both permutations and target separation

With identity matching, the strong block contributes 4a0 theta and the bottom block contributes 2b theta. The rare, shared, and padding blocks contribute zero. Hence

    Delta_id=(4a0+2b)theta > (3/2)theta.

With the only other K=2 permutation, the distance is

    Delta_swap=(4a0+2b)(1-theta)+4a.

The difference is `(4a0+2b)(1-2theta)+4a>0`. Thus the quotient distance is exactly Delta_id. The separation is not an arbitrary labeling effect, and the positive padding is neutral under both comparisons.

## 4. Uniform strong-class assumption and all weakening sequences

The null A0 changes with m through a and the compensating mass b. This is permitted by B1 only because B1 is uniform over the fixed strong-anchor class, with a finite constant C independent of m and the permitted document arrangement. A pointwise guarantee at a single fixed null would not suffice. The same estimator is applied under both models and is not supplied the two different anchor-strength bounds. These are substantive hypotheses, and the theorem states them.

For E={d_topic(Ahat,A1)<Delta/3}, the quotient triangle inequality gives d_topic(Ahat,A0)>2Delta/3. Markov and B1 imply

    P0(E)<=3C/(2Delta sqrt(m))<=C'/(theta sqrt(m)).

Cauchy–Schwarz under the null law then gives B4:

    P1(E)^2<=C' exp(beta min{m alpha,L})/(theta sqrt(m)),
    beta=2/147<1/2.

The three cases in the source cover every alpha_m>0 tending to zero:

1. If m alpha>=L, then theta=tau sqrt(L/(m alpha)). The bound becomes `C alpha^(1/2-beta)/sqrt(L)`, which tends to zero as alpha tends to zero.
2. If m alpha<L and m alpha<=1, then theta=tau and the numerator is at most exp(beta). The bound is O(m^(-1/2)).
3. If 1<m alpha<L, then theta=tau, alpha>1/m, and L<log m. The bound is at most `C m^(beta-1/2)`, which tends to zero.

A sequence can alternate between these cases. The maximum of their three upper bounds still tends to zero, so no convergence of the regime label is assumed. The conclusion covers super-polynomially tiny alpha as well as slowly vanishing alpha. Randomized estimators are also covered by adjoining an independent random seed with the same distribution under both models.

It follows that

    E1 d_topic(Ahat,A1)>=Delta/3 [1-P1(E)]
                       >=theta/2 [1-o(1)].

Since theta=(1/16)min{1,sqrt(log(1/alpha)/(m alpha))}, dividing by the positive denominator and taking the liminf gives exactly the asserted lower constant 1/32. The o(1) can depend on the estimator's fixed strong-class constant C, but it vanishes for each such estimator; the displayed limiting lower constant does not depend on C.

## 5. Scope statements

The Section 6 qualifications are appropriate:

- The matching constrained lower theorem is for **fixed vocabulary, K=2, q=1/2**. It is not a lower theorem for all K,q.
- At fixed p, tau_(1/2)=O(m^(-1/2)); along alpha tending to zero this is dominated by the displayed coordinate rate. Also log(2+1/alpha)/log(1/alpha) tends to one. Therefore, conditional on a valid Theorem A, the upper and this constrained lower bound have the same order in this subclass.
- Theorem B does not imply a larger ordinary minimax rate for known alpha. Such a procedure is allowed to change with alpha and need not retain B1's root-m behavior at the varying strong null when configured for the weak class.
- In a separately specified polynomial lower-growth regime p>=m^epsilon, the two location logarithms are comparable in the unsaturated region, with constants depending on epsilon and q. The fixed-p adaptation separation does not by itself refute an earlier theorem in that growing-p regime.
- Exact anchors, common conditioning, and the uniform strong-class constraint remain essential to the claim as proved. No efficiency, practical performance, all-model completeness, external-review, or novelty conclusion follows from this audit.

## Audit record

This review reconstructed class membership, the full multinomial second moment, both permutations, every asymptotic regime, and the liminf constant analytically. Small exact rational checks confirmed `e_infinity=1/393216`, `b_min=242687/393216>1/2`, the coefficient `512/147`, and `beta=2/147`. No scientific outcome data, paid compute, or external communications were used; the source was not edited.
