# Unknown anchor strength: an adaptive estimator and a constrained-risk frontier

27 October 2026. New mathematical source for independent review. No historical novelty, external expert approval, computational efficiency, or practical performance claim is made. The constrained lower theorem below is for fixed vocabulary, K=2 and q=1/2; it is not silently promoted to all K,q.

Read-only dependencies:

- `../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256 `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`: the experiment/class, exact count moments, frequent-core construction, and ordinary-tail bounds. Its alpha-dependent anchor screening is NOT used here.
- `empirical_frequency_maximum_lemma.md`, SHA256 `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`: the empirical-frequency expected maximum-error bound, including false rare rows and data-selected cores inside a deterministic set.

## 1. Adaptive upper theorem

Use exactly the class C_q(alpha) in Section 1 of the first dependency: fixed known K>=2, fixed q in (0,1), fixed displayed conditioning/overlap constants, weak-q radius four, p_0(K)<=p<=m^D, n divisible by K, N>=2, m=nN. Mixtures W and topic matrix A are unknown, and anchors have corpus mass at least alpha. Define the permutation entrywise-L1 loss d_topic and tau_q(m,p) as there. Put

    ell(alpha)=log(2+1/alpha),
    rho(alpha)=min{1,sqrt(ell(alpha)/(m alpha))}.

**Theorem A.** A single explicit estimator, using neither alpha nor q nor the anchor locations nor W, satisfies

    sup_(C_q(alpha)) E d_topic(Ahat,A)
       <= C min{1,sqrt(ell(alpha)/(m alpha))+tau_q(m,p)}.    (A1)

The constant and a sufficiently large starting m depend only on the fixed class parameters, K,q,D, not on alpha,n,N,p. Thus the result is uniform over sequences of arbitrarily weakening anchors. The estimator uses K and the common conditioning lower bounds. Exhaustive determinant selection is permitted; no efficient implementation claim is intended.

At a fixed positive alpha, the coordinate cost is m^(-1/2), without an extra log m or log log m. At shrinking alpha the adaptive logarithm is log(2+1/alpha). This differs from the known-strength location logarithm log(2+min{p,alpha^(-q)}).

## 2. Algorithm and a deterministic penalized-determinant inequality

Compute d_hat,C_hat as in the first dependency. Use its fixed frequent set H, maximum principal-moment determinant core R, and frequent-core guards. The constants d_0,d_*,tau_*,v_0 and nu_0 are exactly its C6–C13 constants; none depends on alpha. Set

    r_*=max{1,ceil(1/tau_*)},
    H_*=6(sqrt(r_*)+1), A_*=12H_*,
    pen(x)=min{2,A_*[sqrt(log(2+1/x)/(mx))
                         +log(2+1/x)/(mx)]}, x>0,
    pen(0)=2.                                            (A2)

For every vocabulary row, set Yhat_j=C_hat_jR/d_hat_j when d_hat_j>0, and Yhat_j=0 otherwise. Select K distinct rows S maximizing

    score(S)=|det Yhat_S|-2 sum_(j in S) pen(d_hat_j),      (A3)

with deterministic index tie-breaking. Call the selected matrix Vhat. If sigma_min(Vhat)<nu_0/2, use a fixed stochastic-column fallback. Otherwise compute

    Fhat_j=C_hat_jR Vhat^(-1), all j,

clip at zero, and normalize each column; zero-column and nonfinite guards use a stochastic fallback. This is a fully specified finite mathematical estimator without alpha or q input.

The following deterministic fact supplies the new selection step. Let V be a K-by-K matrix with nonnegative subprobability rows and sigma_min(V)>=nu_0. Suppose each ideal row is Y_j=b_j V, where b_j is nonnegative with row sum at most one, and the data include one exact vertex row per topic. Assume all empirical rows are also subprobability vectors. Let p_j>=0 be arbitrary penalties and define

    Z=max_j(||Yhat_j-Y_j||_2-p_j)_+.

Let T be a tuple of exact vertices, P_T=sum_(j in T)p_j, D=|det V|, and let S maximize A3 with p_j in place of pen. Then

    D-|det Y_S|+sum_(j in S)p_j <= 3P_T+2KZ=:G.           (A4)

To prove it, replace rows one at a time in a determinant. Since every row encountered has Euclidean norm at most one, Hadamard gives the exact Lipschitz bound

    ||det Yhat_J|-|det Y_J|| <= sum_(j in J)||Yhat_j-Y_j||
                              <= sum_(j in J)p_j+KZ.

Also |det Y_J|=|det B_J|D<=D, since each substochastic row of B_J has norm at most one. Thus

    score(S)<=|det Y_S|-sum_(j in S)p_j+KZ,
    score(T)>=D-3P_T-KZ.

Maximality proves A4. In particular it controls BOTH the ideal determinant deficit and the selected tuple's own penalties. Merely controlling the first would not justify recovering the empirical vertices.

If G/D is sufficiently small, put eta=G/D. A4 gives |det B_S|>=1-eta. Hadamard implies every row of B_S has norm at least 1-eta. For a substochastic row b,

    max_k b_k >= sum_k b_k^2 >= (1-eta)^2 >=1-2eta.

The row is therefore within 4eta in L1 of a coordinate vector. These coordinate vectors are distinct for eta<1/10: otherwise subtract two rows close to the same vector, and Hadamard would give |det B_S|<=8eta, contradicting 1-eta. Consequently one permutation Pi satisfies

    ||Y_S-Pi V|| <= C_K G/D,
    ||Vhat-Pi V|| <= C_(K,nu_0)(P_T+Z),                  (A5)

where the second line uses sum_(j in S)||Yhat_j-Y_j||<=G+KZ and D>=nu_0^K. All norms here can be taken as Frobenius with K-dependent constants. For P_T+Z below a fixed class-dependent threshold, the inverse guard passes. Zero-probability vocabulary rows cause no difficulty: use b_j=0, which is substochastic and is covered by the same argument.

## 3. Stochastic oracle bound, including missing empirical anchors

On the good-core event E_core from the first dependency, every possible selected R is contained in the deterministic set D_*={j:d_j>=tau_*}, of size at most r_*. Its population vertex matrix

    V_R=diag(mu)^(-1) Sigma A_R'

has sigma_min at least nu_0, and its rows are subprobability vectors. For d_j>0, Y_j=C_jR/d_j=B_j V_R with stochastic B_j. For d_j=0 use Y_j=B_j=0. Thus the deterministic setting of Section 2 holds pathwise on E_core, despite the randomness of R.

Apply the empirical-frequency lemma to the whole deterministic coordinate set D_* with constants based on r_*. Restriction to R cannot increase row errors. The proof of that lemma also works with this upper bound on the core size; all its constants and penalties are monotone in that bound. Extend it to d_hat_j=0 by our convention: both Y_j and Yhat_j are subprobability vectors, their error is at most two, and pen(0)=2 makes their positive excess zero. Hence

    E[1_(E_core) Z] <= C/sqrt(m).                         (A6)

This is an unconditional expectation bound on the good-core event, not an independence assumption or a conditional concentration claim about a selected core.

Fix one true anchor per topic, each of population mass d>=alpha, and denote that tuple by T. For a single such row, the lower Chernoff bound gives

    P(d_hat<d/2)<=exp(-md/8).

On d_hat>=d/2, monotonicity of x -> log(2+1/x)/x and log(2+2/d)<=C log(2+1/d) bound the capped penalty by

    C min{1,sqrt(ell(d)/(md))+ell(d)/(md)}.

The bad-frequency contribution is at most 2exp(-md/8). The elementary inequalities exp(-u/8)<=C min(1,u^(-1/2)) and min(1,sqrt(v)+v)<=2min(1,sqrt(v)) imply

    E pen(d_hat) <= C min{1,sqrt(ell(d)/(md))}
                 <= C rho(alpha),
    E P_T <= C_K rho(alpha).                             (A7)

An anchor with zero empirical count is therefore already included; there is no missing-anchor event requiring an ambient union bound. Also m^(-1/2)<=C rho(alpha) throughout the permitted alpha range.

Combining A4–A7, the vertex error on its stable event is bounded in expectation by C rho(alpha). The complement within E_core has probability at most C E[1_(E_core)(P_T+Z)] by Markov, since the stability threshold is a fixed positive class constant. Its stochastic-column output loss is at most 2K. Outside E_core the same loss bound costs C p exp(-c_*m). This argument covers observed inverse-guard failures as well as large perturbations.

## 4. Full vocabulary and proof of Theorem A

For the random selected core, the exact population identity remains

    C_jR V_R^(-1)=A_j diag(mu)=F_j.                      (A8)

On the stable event, one common permutation from A5 gives

    ||Fhat-F Pi'||_1
       <=C sum_j sum_(r in D_*) |C_hat_jr-C_jr|
           +C(P_T+Z).                                   (A9)

The inverse bounds are independent of alpha. The second term uses sum_(j,r) C_jr=1, so it carries no p or inverse-alpha multiplier. The exact pair-moment bound in C4 of the first dependency gives

    E sum_j sum_(r in D_*) |C_hat_jr-C_jr|
       <=C sum_j min{h_j,sqrt(h_j/m)}.

Every population F column has mass mu_k>=c. Clipping and column normalization therefore cost at most 2/c times the raw L1 error, including the zero-column fallback. Together with the bounded bad-event losses and A6–A7, this proves the instance bound

    E d_topic(Ahat,A)
       <=C[rho(alpha)+sum_j min{h_j,sqrt(h_j/m)}
                         +p exp(-c_*m)].                (A10)

The weak-q envelope evaluates the sum as tau_q, including the critical q=1/2 logarithm; these calculations are explicit in the first dependency. Since p<=m^D, the exponential term is absorbed by m^(-1/2). Finally loss is always at most 2K, so cap the bound at a constant. This proves A1 with no alpha or q in the estimator.

## 5. A matching constrained-risk price at fixed vocabulary

**Theorem B.** Fix K=2, q=1/2 and any fixed p>=12 in the same class, and fix alpha_s=1/32. Suppose a sequence of estimators, not supplied alpha, satisfies

    sup_(C_(1/2)(alpha_s)) E d_topic(Ahat_m,A)<=C/sqrt(m)   (B1)

for all sufficiently large m. Then for every sequence alpha_m>0 tending to zero, along n even and N>=2 with m=nN tending to infinity,

    liminf_m [sup_(C_(1/2)(alpha_m)) E d_topic(Ahat_m,A)]
                 / min{1,sqrt(log(1/alpha_m)/(m alpha_m))}
       >= 1/32.                                         (B2)

Thus Theorem A attains the constrained adaptive rate in this fixed-vocabulary class, up to constants. Theorem B is a restriction on procedures also satisfying the strong-class performance B1. It is NOT a larger ordinary minimax lower bound for a known-alpha class.

Here is the complete positive count-experiment construction. Write alpha=alpha_m and, for large m with alpha<=1/256, set

    a=2alpha, a0=1/8, zeta=1/4, L=log(1/alpha),
    tau=1/16, theta=tau min{1,sqrt(L/(m alpha))},
    eps_l=(1/32)2^(-2(l+6)), l=1,...,p-7,
    e=sum_l eps_l, b=5/8-a-e,
    B=[[3/4,1/4],[1/4,3/4]],
    T=[[1-theta,theta],[theta,1-theta]].

A0 has rows zeta(1,1), a0 I_2, a I_2, bB, and the p-7 positive common padding rows eps_l(1,1). A1 replaces a0 I_2 by a0 T and bB by bBT; all other rows stay unchanged. Take equal document groups with W0 columns (3/4,1/4)' and their reversal, and W1=T^(-1)W0. These are deterministic mixture matrices, not a prior on W.

Both topic matrices are stochastic-column matrices; b>1/2. All document word probabilities are positive. The smallest eigenvalue of W0W0'/n is 1/8; the alternative only increases the eigenvalue in the first-minus-second direction. The shared row contributes 1/16 to every topic overlap, and the common block supplies sigma_min at least b(1-2theta)/2. These exceed the class constants.

Weak-1/2 radius four follows from a stronger bound on each column: the sum of square roots of all entries is less than

    1/2 + sqrt(1/8)(1+1/4) + sqrt(1/128)
        +sqrt(2*5/8) +(1/sqrt(32))2^(-6) < 4.

Indeed j sqrt(A_(j)) is at most that sum. This also handles any interleaving of rare rows and padding. Null anchors have corpus mass a0/2=1/16>=alpha_s. All alternative nonrare rows are positive in both topics, while its two rare pure anchors have corpus mass a/2=alpha. Thus A0 belongs to the fixed strong class and A1 to C_(1/2)(alpha), with the same common constants and fixed p.

All nonrare observable rows cancel exactly under T and T^(-1). The rare probabilities in a group change from a(3/4,1/4) to a(3/4+delta,1/4-delta), where

    delta=theta/[2(1-2theta)].

The null-relative one-token chi-square is

    a delta^2(4/3+4)=4a theta^2/[3(1-2theta)^2]
       <=(512/147) alpha theta^2.

The multinomial theorem and independent documents therefore give, for the FULL count-experiment likelihood ratio Q=dP1/dP0,

    E0 Q^2 <=exp((512/147)m alpha theta^2)
            =exp(beta min{m alpha,L}), beta=2/147.       (B3)

No KL-to-second-moment inference is used. The identity-permutation topic distance is

    Delta=(4a0+2b)theta >=(3/2)theta.

The swapped distance is (4a0+2b)(1-theta)+4a, which is larger. Thus Delta is the quotient distance; shared and padding rows add zero to both comparisons.

Let E be the event that the estimator is within Delta/3 of A1. By the quotient-metric triangle inequality and B1,

    P0(E)<=3C/(2Delta sqrt(m))<=C'/(theta sqrt(m)).

Cauchy–Schwarz and B3 imply

    P1(E)^2 <= C' exp(beta min{m alpha,L})/(theta sqrt(m)). (B4)

This tends to zero along EVERY alpha_m tending to zero. If m alpha>=L, its right side is bounded by C alpha^(1/2-beta)/sqrt(L). If m alpha<L and m alpha<=1, it is bounded by C/sqrt(m). In the remaining case 1<m alpha<L, alpha>1/m and L<log(m), so it is bounded by C m^(beta-1/2). Every bound tends to zero because beta<1/2.

Consequently the alternative risk is at least Delta/3[1-o(1)]>=(theta/2)[1-o(1)]. Substitute theta=tau times the denominator rate in B2. Since tau/2=1/32, B2 follows. The varying null is legitimate because B1 is a uniform strong-class risk bound. The small additional positive padding places the construction inside the same p>=12 class used by Theorem A and the known-strength theorem.

## 6. Scope and significance boundary

Theorem A is an adaptive upper guarantee for all the stated fixed K,q classes. Theorem B supplies a matching constrained price for fixed vocabulary at K=2,q=1/2, including the inconsistent alpha of order log(m)/m boundary. It strengthens the earlier single-boundary seven-word obstruction by varying theta and adding positive padding. It does not prove a constrained lower bound for every K,q, remove exact separability or common conditioning, or supply an efficient practical algorithm.

In the original polynomially growing vocabulary regime, the known-alpha location logarithm is comparable to this adaptive logarithm in the nontrivial range, so the known-strength lower theorem also supplies the corresponding order comparison there. At fixed vocabulary they genuinely differ. The estimator maintains the strong-anchor expected root-m coordinate rate while paying the larger weak-anchor logarithm when needed.

All ingredients require source-bound independent review of this composition. Earlier separate audits of concentration and known-alpha recovery do not certify the selection and constrained-risk theorems automatically. Constrained-risk arguments and penalized estimation have classical antecedents. No statement here establishes that this topic-model specialization is historically new or newsworthy.
