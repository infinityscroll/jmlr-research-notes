# Unknown anchor locations force a square-root logarithm with shrinking mixture diversity

28 October 2026. New analytic source for hostile review. This proves a lower bound for **N=2** with unknown deterministic document mixtures. It does not infer the all-N lower bound by treating overlapping token pairs as independent. Fixed-conditioning unknown-location lower bounds are already in `../anchor_strength_continuum_20261027/known_strength_minimax.md`; the new step here is the exact likelihood mixture after marginalizing weak document contrasts, including the nonzero cross terms between candidate locations.

## 1. Statistical statement

Fix K>=2 and q in (0,1), put k0=max(1,K-2), and suppose

    p>=2K+8, n>=128(K-1), N=2,
    0<alpha<=1/(64K), 0<beta<=1/(1024 K^2 k0).             (A1)

Observe independent X_i~Multinomial(2,A w_i). Both A and W have stochastic nonnegative columns; W is unknown and deterministic. Consider the class requiring

    every w_ki>=1/(4K), lambda_min(WW'/n)>=beta,
    sigma_min(A)>=1/(8sqrt(K)), min_kl(A'A)_kl>=1/64,
    max_k max_j j [A_(j),k]^q<=4,                        (A2)

and at least one exact pure anchor for each topic with corpus frequency d_j=(A W1/n)_j>=alpha. Anchor locations are unknown. Unused zero-probability vocabulary rows are permitted, as in the held sparse lower theorem. All active rows in the constructed family have positive observed probabilities in every document.

Set

    Lambda=log(2+min{p,alpha^(-q)}),
    a_n=1/sqrt(2n beta)+1/[beta sqrt(2n)].                (A3)

For expected entrywise-L1 topic error modulo column permutations,

    inf_Ahat sup_(A,W in class) E min_Pi ||Ahat-A Pi||_1
       >=c_(K,q) min{1, sqrt(Lambda)*a_n/sqrt(alpha)}.   (A4)

The constant does not depend on n,p,alpha,beta. Thus the anchor factor cannot be removed uniformly over shrinking beta, even with fixed topic count and uniformly strong topic geometry. This proves a square-root logarithmic obstruction, not necessity of the full log factor in the current upper bound.

## 2. Topic matrices: the same gauge obstruction with many possible anchors

Let

    a=4K alpha, zeta=1/4,
    M=min{max{1,floor(a^(-q)/16)},floor((p-K-1)/2)},
    B=[[3/4,1/4],[1/4,3/4]], b=1-zeta-Ma,
    T_theta=[[1-theta,theta],[theta,1-theta]],
    S_theta=diag(T_theta,I_(K-2)).                       (A5)

Then M>=1, a<=1/16, Ma<=1/16 and b>=11/16. The argument for Ma is separate when M=1; otherwise M<=a^(-q)/16. Also M<=1/a, and

    log(2+M) is comparable to Lambda,                    (A6)

with constants depending only on K,q. Indeed max{1,floor(a^(-q)/16)}>=a^(-q)/32 and the vocabulary cap is at least p/8 under A1.

The null A_0 has: one shared row zeta(1,...,1); M disjoint candidate blocks a I_2 on topics1,2; two common rows b B on topics1,2; and one row (3/4)e_k for each k>=3. Append zero rows to reach p. For alternative j, keep candidate block j equal to a I_2, replace every other candidate block by a T_theta, and replace the common block by b B T_theta. Shared and extra-topic rows are unchanged. Call the resulting matrix A_j. We use 0<theta<=1/16.

All columns sum to one. The disjoint common and extra-anchor rows give

    sigma_min(A_j)>=min{b(1-2theta)/2,3/4}>1/4,

which is stronger than A2. The shared row alone gives every Gram entry at least1/16. Candidate j supplies both old-topic anchors, and the extra topics retain their anchors.

Weak-q radius4 is uniform in M and p. If M=1, each old column has only four positive entries and each extra column has two. If M>=2, at any threshold u the two common rows contribute at most2 to u^q times the count, the shared row at most1, and the candidate rows at most2M a^q<=1/8. Their sum is less than4. These arguments also cover the null, where some candidate entries are zero.

For any permutation that moves an extra topic, the extra-anchor rows cost at least3/2. If extras stay fixed, the common-block distance for identity is2b theta and for exchanging topics1,2 is2b(1-theta). Hence

    min_Pi ||A_j-A_0 Pi||_1 >=2b theta.                  (A7)

No pairwise separation between the alternatives themselves is required: the test below is the null against a mixture of alternatives.

## 3. A prior supported on legal deterministic W

Let u=1/K times the all-ones vector, e=(e_1-e_2)/sqrt(2), and H={v:v_1=v_2}. For K=2 take B_i=u. For K>=3 cycle the 2(K-2) vectors

    B_i=u +/- (1/(2K))[e_k-(e_1+e_2)/2], k=3,...,K.

Then t_i=B_i1=B_i2>=1/(2K), all coordinates of B_i are at least1/(2K), and

    Sigma_B=BB'/n >=c0 P_H,
    c0=1/(8K^2 k0).                                    (A8)

To see the last bound, complete cycles occupy at least half the documents. Their centered directions are orthogonal to u and have Gram matrix I+(1/2)11', whose least eigenvalue is at least1. The remaining incomplete cycle contributes a positive semidefinite matrix.

Initially draw independent fair signs xi_i and define

    w_i^0=B_i+4sqrt(beta) xi_i e,
    w_i^theta=S_theta^(-1)w_i^0.                        (A9)

The inverse leaves H fixed and multiplies e by1/(1-2theta). On A1 and theta<=1/16, the absolute coordinate perturbation is at most

    2sqrt(2beta)/(1-2theta) <=1/(4K).

Thus every mixture coordinate is at least1/(4K), for both null and alternatives. In particular every pure candidate anchor has corpus mass at least a/(4K)=alpha, including after conditioning below.

Condition the sign prior on the single parameter-independent event

    E={||Pi_B xi||^2/n<=1/2},                            (A10)

where Pi_B projects onto the row space of B. Its complement has probability at most2(K-1)/n<=1/64. Let c=Bxi/n. Then c' Sigma_B^dagger c=||Pi_B xi||^2/n. In the decomposition H plus span(e), the normalized covariance cross block has norm at most1/sqrt(2). For r=4sqrt(beta) or r=4sqrt(beta)/(1-2theta), this gives

    WW'/n >=(1-1/sqrt(2)) min{c0,r^2} I >=beta I.        (A11)

Here c0>=128beta, r^2>=16beta. Every constituent W after conditioning is therefore a legal deterministic nuisance parameter. The independent signs are only a lower-bound prior; the statistical model is not changed to random mixtures.

## 4. Exact N=2 likelihood cross moments

Before conditioning on E, documents are independent after averaging their signs. Their baseline word law d_i=A_0 B_i is also A_j B_i, since B_i belongs to H. All unmentioned zero rows may be deleted in the following sums.

Write r_i=2sqrt(2beta)/t_i. Under the null, the two words of each candidate pair have baseline mass a t_i each and opposite signed relative contrast +/-r_i. The two common words have mass b t_i each and contrast +/-r_i/2. Shared and extra-topic rows have zero contrast. Denote this vector of contrasts by z_i. Conditional on xi_i, the null token probabilities are d_i(x)[1+xi_i z_i(x)].

The product A_j w_i^theta agrees with A_0 w_i^0 outside candidate pair j, exactly. In pair j, its contrast is multiplied by1+kappa, where

    kappa=2theta/(1-2theta).                            (A12)

Let z_i^j be that modified contrast. For ordered two-token documents, the sign-mixture law is exactly

    P_j^i(x,y)=d_i(x)d_i(y)[1+z_i^j(x)z_i^j(y)].         (A13)

The likelihood ratio is symmetric in x,y, so the same likelihood inner products hold for the actual unordered multinomial counts. No independence of overlapping pair observations is used.

Set c_i=2a t_i, the baseline mass of one complete candidate pair. For j!=k, the likelihood changes overlap only when one observed token belongs to pair j and the other to pair k. Averaging their two signs gives the exact identity

    E_0[L_j^i L_k^i]-1
       =O_i:=2 c_i^2 kappa^2 r_i^4/(1-r_i^4).           (A14)

For the diagonal, separate one token in pair j from two tokens in that pair:

    E_0[(L_j^i)^2]-1
       =D_i:=2 c_i kappa^2 r_i^2
                 sum_(x outside pair j) d_i(x)z_i(x)^2
                                      /(1-r_i^2 z_i(x)^2)
              +c_i^2(2kappa+kappa^2)^2 r_i^4/(1-r_i^4). (A15)

Both quantities are independent of the candidate index, though they may vary across documents. Unlike the fixed-mixture construction in the earlier continuum, A14 is **positive**, not zero. Dropping this term would be an invalid lower-bound argument.

On A1, r_i^2<=1/32 and all displayed denominators exceed1/2. Also kappa<=3theta and

    sum_x d_i(x)z_i(x)^2
       =2t_i r_i^2(Ma+b/4)<=t_i r_i^2,
    t_i^2 r_i^4=64 beta^2/t_i^2<=256K^2 beta^2.

Consequently the following deliberately loose bounds hold uniformly:

    D_i<=C_K a theta^2 beta^2,
    O_i<=C_K a^2 theta^2 beta^2,
    C_K=2^16 K^2.                                      (A16)

For details, the first term in D_i is at most8a t_i^2 kappa^2 r_i^4; its second is at most72a^2 t_i^2 kappa^2 r_i^4. Since a<=1/16, their sum is at most13a t_i^2 kappa^2 r_i^4. The off-diagonal term is at most16a^2 t_i^2 kappa^2 r_i^4. Substituting kappa<=3theta proves A16.

## 5. A mixture test that retains the logarithm

Put L=log(2+M), epsilon=1/256, and choose

    theta=(2^(-12)/K) min{1,sqrt(L/(n a beta^2))}.        (A17)

Then theta<=1/16 and, using A16,

    sum_i D_i<=epsilon L,
    sum_i O_i<=epsilon a L.

Let P_bar=(1/M)sum_j P_j denote the unconditioned data mixture. Independence across documents and A14--A15 give

    1+chi-square(P_bar,P_0)
       =(1/M) product_i(1+D_i)
                    +(1-1/M) product_i(1+O_i).

Therefore

    chi-square(P_bar,P_0)
       <=[(M+2)^epsilon-1]/M + exp(epsilon a L)-1
       <=2epsilon+epsilon/2 <1/64.                      (A18)

The first final inequality is concavity of x^epsilon. For the second term, M<=1/a and a<=1/16 give a log(2+M)<=a log(2+1/a)<=1/4. Hence exp(epsilon aL)-1<=epsilon/2. This controls the cross-location correlation instead of pretending the alternatives remain orthogonal after the signs are marginalized.

The total variation distance of the unconditioned null and mixture is at most1/16. Conditioning the latent signs on E changes each marginal data law by at most1/64, so

    TV(P_0(.|E),P_bar(.|E)) <=3/32 <1/8.                (A19)

All conditioned hypotheses satisfy A1--A2 and the unknown-anchor premise. For any estimator, test whether its quotient distance from A_0 is less than b theta. By A7 and the quotient triangle inequality, a test error costs at least b theta under the relevant hypothesis. The sum of the two testing errors is at least1-TV, so the worst expected topic error is at least c theta. Equations A6 and A17 prove

    R>=c_(K,q) min{1,sqrt(Lambda)/(beta sqrt(n alpha))}.

Since beta<=1, a_n in A3 is comparable to1/(beta sqrt(n)), which proves A4.

## 6. Consequence and limitations

Combining A4 with the held weak-sparsity tail lower bound in `../weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_lower.md` yields, on the intersected vocabulary domains and N=2,

    R>=c_(K,q) min{1, sqrt(Lambda)*a_n/sqrt(alpha)
                              +F_(q,p)(a_n)}.           (A20)

The two lower families can differ; taking the maximum controls half their sum. The usual q=1/2 tail logarithm is a separate phenomenon and is not the anchor-location logarithm proved here.

The new calculation concerns weak, unknown document-mixture contrasts. Its information scale is n alpha beta^2, not the fixed-conditioning m alpha scale. Strong topic geometry and fixed K do not eliminate unknown-location multiplicity. At fixed p the logarithm is a constant, as it must be. For genuinely growing candidate sets, a logarithm-free uniform anchor rate is impossible in this short-document regime.

This note does not establish the same exact mixture bound for N>2. Longer sign-mixture likelihoods contain higher even-order terms, so A14 cannot be reused unchanged. It does not prove the current upper's full log factor optimal, adapt to unknown alpha, address diffuse A with vanishing unnormalized singular value, or establish historical novelty. A matching sqrt-log upper and a primary comparison are separate deliverables. The earlier fixed-beta continuum already contains the gauge/location idea; the present contribution is its exact weak-beta full-count likelihood transfer with controlled nonzero cross terms.

