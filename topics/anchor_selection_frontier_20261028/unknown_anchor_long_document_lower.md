# Unknown anchor locations: sharp logarithmic lower bound for long documents

28 October 2026. New analytic source for hostile review. This extension reveals a latent sign as auxiliary information in a lower-bound experiment; it does **not** reveal the unknown mixture matrix W. It proves the logarithmic anchor lower bound at every N in the first-order information scale, and hence the sharp joint scale when (N-1)beta>=1. It does not assert the sharp log lower throughout the short-intermediate regime N>2 with (N-1)beta<1.

Bound dependency: `unknown_anchor_short_document_lower.md`, SHA256 `a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56`. Its exact stochastic matrices, weak-q membership, geometry, quotient separation and conditioned design construction are reused unchanged. No previous source is edited.

## 1. Statement

Keep fixed K>=2, q in (0,1), and all class conditions A1--A2 of the dependency, except replace N=2 by an arbitrary integer N>=2. Thus p>=2K+8, n>=128(K-1), alpha<=1/(64K), beta<=1/[1024K^2 max(1,K-2)]. W is unknown and deterministic, every mixture coordinate is at least1/(4K), A has uniformly strong unnormalized singular value, and every topic has an unknown pure anchor with corpus frequency at least alpha. The columnwise weak-q radius is4. Write

    Lambda=log(2+min{p,alpha^(-q)}),
    a_n=1/sqrt(nN beta)+1/[beta sqrt(nN(N-1))].           (L1)

**Theorem.** The minimax expected entrywise-L1 topic error, modulo topic permutation, obeys

    R>=c_(K,q) min{1,sqrt(Lambda/(nN alpha beta))}.        (L2)

In the long-document regime (N-1)beta>=1, this becomes

    R>=c_(K,q) min{1,sqrt(Lambda)*a_n/sqrt(alpha)}.        (L3)

Combined with the held sparse-tail lower and the new all-N upper, L3 matches the full weak-sparsity rate including the anchor logarithm on the common parameter domain. The threshold (N-1)beta>=1 is exact here up to the fixed constants of equivalence; L2 itself needs no such condition.

## 2. Reuse of the legal family

Use a=4Kalpha, M, b, A_0 and A_j(theta), S_theta and B_i exactly as in A5--A9 of the dependency. Put t_i=B_i1=B_i2 and

    r_i=2sqrt(2beta)/t_i, c_i=2a t_i,
    kappa=2theta/(1-2theta), 0<theta<=1/16.               (L4)

For initially independent signs xi_i, the null mixture is

    w_i^0=B_i+4sqrt(beta)xi_i e,

and every candidate alternative uses w_i^theta=S_theta^(-1)w_i^0. Condition the sign prior on the SAME event E from A10. This event has positive probability and depends only on B and the sign vector, not on theta or the candidate label j. By A11 every conditional constituent W is admissible. In particular the positivity, anchor support and covariance conditions hold separately for every realized sign vector in E, for every document length N.

The conditional sign prior is only a probability distribution on legal deterministic parameters. Introducing it does not alter the fixed-design statistical class. The topic quotient separation is still at least2btheta, regardless of xi.

## 3. The more informative experiment and its exact likelihood

Augment the observed count vectors by the entire sign vector xi. Use the same conditioned sign distribution under the null and all alternatives. These signs do not reveal W: the null assigns w_i^0 while the alternatives assign w_i^theta, and the unknown hypothesis determines which matrix is the actual one.

Conditional on xi, the individual token probabilities are

    p_0^i(x|xi)=d_i(x)[1+xi_i z_i(x)],
    p_j^i(x|xi)=d_i(x)[1+xi_i z_i^j(x)],                 (L5)

with d_i=A_0 B_i and z_i^j differing from z_i only in candidate pair j, where it is multiplied by1+kappa. The two words in that pair have d_i mass a t_i each and opposite contrasts +/-r_i. Thus the token probability change has total sum zero and support confined to that pair.

For distinct candidates j,k the changes have disjoint supports. Therefore, for EVERY fixed sign vector, the one-token likelihood inner product is exactly

    sum_x p_j^i(x|xi)p_k^i(x|xi)/p_0^i(x|xi)=1.          (L6)

The one-token diagonal increment is also exact:

    chi_i=sum_x [p_j^i(x|xi)-p_0^i(x|xi)]^2/p_0^i(x|xi)
         =c_i kappa^2 r_i^2/(1-r_i^2).                  (L7)

It is independent of j AND of the sign xi_i. Since r_i^2<=1/32, t_i>=1/(2K) and kappa<=3theta,

    chi_i<=64K a kappa^2 beta
           <=2^10 K a theta^2 beta.                    (L8)

The exact multinomial likelihood identity gives the Nth power of the one-token inner product for a full count vector. Across documents the laws are independent conditional on xi. Consequently, for the augmented likelihood ratios L_j^aug,

    E_0[L_j^aug L_k^aug]=1, j!=k,
    E_0[(L_j^aug)^2]=product_i(1+chi_i)^N.               (L9)

These equalities survive conditioning the sign prior on E: the quantities inside its expectation are already constant in xi. There is no conditioning total-variation loss in L9, and no assertion of independent signs after conditioning. Nor are overlapping within-document pairs used anywhere in this argument.

## 4. Mixture testing

Let L=log(2+M) and choose

    theta=(2^(-12)/K) min{1,sqrt(L/(nN a beta))}.         (L10)

Then theta<=1/16, and L8 gives

    N sum_i chi_i <= epsilon L, epsilon=1/256,

with ample slack in the numerical constant. Let P_bar^aug be the uniform mixture of augmented alternatives. By L9,

    chi-square(P_bar^aug,P_0^aug)
       =[product_i(1+chi_i)^N-1]/M
       <=[(M+2)^epsilon-1]/M<=2epsilon<1/64.             (L11)

Thus the augmented total variation is at most1/16. Forgetting xi cannot increase total variation, so the same upper bound holds for the actual count experiment. Equivalently, even an estimator additionally given xi cannot separate the null from this mixture well enough to beat the stated risk lower bound.

Using the test based on whether the estimated topic matrix is within btheta of A_0, quotient separation and the triangle inequality give worst expected loss at least ctheta. The relation log(2+M) comparable to Lambda and a=4Kalpha prove L2.

Finally,

    [1/(beta sqrt(nN(N-1)))]/[1/sqrt(nNbeta)]
         =1/sqrt((N-1)beta).

When (N-1)beta>=1, the two-term a_n is between the first term and twice that term. This proves L3. Together with the separately established sparse-tail lower, the maximum of two lower bounds controls half their sum.

## 5. Boundary of the result

The sign revelation is legitimate because it has the same prior under every hypothesis and only makes estimation easier. Revealing W would be different and is not done. In particular, this is not an oracle-known-mixture lower bound: W changes under the null and alternative gauge transformation.

The result covers arbitrarily weak beta with sufficiently long documents and preserves unknown anchor locations, fixed K, fixed weak-q radius and strong topic geometry. The earlier fixed-beta unknown-location mixture and the present use of disjoint likelihood supports are established proof mechanisms. The quantitative contribution is their legal transfer to weak, unknown document mixtures at the long-document information scale. No historical-priority claim is made.

For N=2 the adjacent sign-hidden calculation gives the stronger beta^-1 anchor scale. For general N>2 with (N-1)beta<1, L2 is weaker than the full joint scale; claiming a matching logarithmic lower there requires an additional hidden-sign likelihood argument. In particular, an unweighted even-chaos cross expectation cannot simply be divided by a lower bound for the null likelihood when its integrand can change sign.

