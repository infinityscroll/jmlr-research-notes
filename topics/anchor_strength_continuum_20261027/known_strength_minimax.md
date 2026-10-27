# Known anchor strength: a uniform minimax continuum

27 October 2026. New mathematical source for independent review. Completed portfolio sources are unchanged. No historical novelty, practical runtime, external review, or empirical performance claim is made.

## 1. Experiment, class, and exact claim

Fix K>=2, 0<q<1, D>0, c=1/(64K), kappa=c sqrt(K), and alpha_0=1/(16K). Let n be divisible by K, N>=2, and m=nN tend to infinity. There is no upper bound on N. Allow every integer vocabulary size

    p_0(K):=2K+8 <= p <= m^D,

including fixed p. The independent observations are X_i~Multinomial(N,AW_i). The unknown nonnegative A and W have stochastic columns. Put

    Sigma=WW'/n, mu=W1/n, h_j=sum_k A_jk, d_j=A_j mu.

The class C_q(alpha), for 0<alpha<=alpha_0, imposes

    sigma_K(A)>=kappa, lambda_min(Sigma)>=c,
    min_(k,l)(A'A)_(k,l)>=c,
    max_(j,k) j A_(j),k^q<=4,                              (C1)

and, for every topic k, an unknown row a(k) satisfying A_a(k),l=0 for l!=k and d_a(k)>=alpha. Here A_(j),k is the decreasing rearrangement in column k. The lower bound alpha is known to the estimator. Neither W, anchor locations, anchor counts, nor q is known. All probability and expectation statements below are uniform over deterministic W satisfying C1; there is no random-mixture prior in the upper result.

Write d_topic(U,A)=min_P ||U-AP||_1, with entrywise L1 norm and P ranging over all K-topic permutations. Define

    Lambda=log(2+min{p,alpha^(-q)}),
    r_alpha=min{1,sqrt(Lambda/(m alpha))},

    tau_q(m,p)=m^(-1/2),                                  q<1/2;
               log(2+min{p,sqrt(m)})/sqrt(m),               q=1/2;
               min{m^(q-1),p^(1-1/(2q))/sqrt(m)},           q>1/2.

**Theorem.** There are positive constants c_1,C_1,m_0 depending only on K,q,D and the displayed class constants, and not on alpha,n,N,p, such that for m>=m_0,

    c_1 min{1,sqrt(Lambda/(m alpha))+tau_q(m,p)}
      <= inf_Ahat sup_C_q(alpha) E d_topic(Ahat,A)
      <= C_1 min{1,sqrt(Lambda/(m alpha))+tau_q(m,p)}.       (C2)

One explicit estimator, described below, achieves the upper bound for every fixed q without using q. Constants and m_0 are uniform over arbitrary sequences 0<alpha<=alpha_0. The procedure may enumerate many K-row subsets; no efficient growing-K or practical complexity claim is intended.

The proof uses a frequent moment core with conditioning independent of alpha. The same core serves both weak-anchor selection and full-vocabulary reconstruction. This is essential: substituting alpha into a strong-anchor inverse bound does not establish C2.

## 2. Exact count moments and concentration

Use

    d_hat_j=m^(-1)sum_i X_ij,
    C_hat_jr=n^(-1)sum_i X_ij(X_ir-1_(j=r))/[N(N-1)],
    C=A Sigma A'.                                        (C3)

Since W_ki>=W_ki^2, mu_k>=Sigma_kk>=c. Thus

    c h_j<=d_j<=h_j, sum_j h_j=K, sum_j d_j=1.

Moreover Sigma 1=mu, C is nonnegative positive semidefinite, and sum_jr C_jr=1. Both C and C_hat have the exact row-sum identity C_j*=d_j and C_hat_j*=d_hat_j. Consequently their nonnegative normalized rows restricted to any column set have norm at most one.

The following bounds have numerical constants, or constants depending only on c:

    P(|d_hat_j-d_j|>C[sqrt(d_j u/m)+u/m])<=2exp(-u),
    P(|C_hat_jr-C_jr|>C[sqrt(d_j u/m)+u/m])<=2exp(-u),
    E|C_hat_jr-C_jr|<=C min{h_j,sqrt(h_j/m)}.              (C4)

For completeness, imagine the N independent tokens behind each count vector, randomly permute them within each document, and form floor(N/2) disjoint unordered pairs. The symmetric pair kernel for j,r is the average of the two ordered indicators. For a fixed pairing the n floor(N/2)>=m/3 kernels are independent, bounded by one, and their total variance is at most C m d_j. Averaging the paired statistic over all pairings gives C3 exactly. Jensen's inequality for its exponential moment transfers the Bernstein bound from each pairing to C_hat. The same argument transfers its variance bound. Nonnegativity and unbiasedness also give E|C_hat_jr-C_jr|<=2C_jr<=2d_j; taking the smaller bound proves the last line. The frequency bound is ordinary Bernstein for m independent, possibly nonidentically distributed indicators. These arguments hold for every N>=2.

Weak sparsity gives a useful counting inequality, for all t>0:

    #{j:d_j>=t}<=#{j:h_j>=t}
       <=4K^(q+1)t^(-q).                                (C5)

Indeed one of the K topic entries must be at least t/K. The estimator does not use C5 or q.

## 3. A fixed-conditioned frequent core

For every stochastic-column A,

    sum_(|R|=K)|det A_R|<=1.

Expand each determinant in absolute value, then allow repeated row indices in the product of the K column sums. Cauchy--Binet now gives

    sum_R det(A_R)^2=det(A'A)>=kappa^(2K),
    max_R |det A_R|>=d_0:=kappa^(2K).                     (C6)

Let R_0 attain the last bound. Hadamard's inequality, ||A_j||_2<=h_j<=K, and C4's frequency comparison imply for every j in R_0

    d_j>=d_*:=c d_0/K^(K-1).

Set tau_*=d_*/4, v_0=c^K d_0^2, and use the observable frequent set

    H={j:d_hat_j>=2tau_*}.

Select a K-row set R in H maximizing det C_hat_RR, with deterministic index tie-breaking. If H has fewer than K rows or the selected determinant is below v_0/2, return a fixed stochastic A as fallback. Additional nonfinite-result guards below also return that fallback.

Here is a uniform good-core event E_core. First require every frequency error to be at most tau_*. Then R_0 subset H subset D_*:={j:d_j>=tau_*}, and |D_*|<=1/tau_* is fixed independently of alpha,m,p. Also

    det C_R0,R0=det(Sigma)det(A_R0)^2>=v_0.

Require the pair-moment errors on D_* times D_* to be below a sufficiently small fixed delta_*, so every K-minor determinant error is at most v_0/4. C4 and a union bound give

    P(E_core^c)<=C p exp(-c_* m).                        (C7)

On E_core, the empirical selected determinant is at least 3v_0/4 and the true selected determinant is at least v_0/2. Since C_RR is positive semidefinite with norm at most one, lambda_min(C_RR)>=v_0/2. Also ||Sigma||<=trace(Sigma)<=1, so C_RR<=A_R A_R' in positive-semidefinite order. Hence

    sigma_min(A_R)>=sqrt(v_0/2).                         (C8)

The deterministic set D_* is used only for analysis. Every possible random selected core on E_core belongs to it. Later bounds sum or maximize over D_* and therefore do not assume independence from core selection.

## 4. Localized screening without an ambient log p penalty

Define the observable anchor-candidate set J={j:d_hat_j>=alpha/2}, and the deterministic set J_*={j:d_j>=alpha/4}. By C5,

    |J_*|<=C min{p,alpha^(-q)}.                          (C9)

Let E_screen require J subset J_*, all true anchors of mass at least alpha to belong to J, and |d_hat_j-d_j|<=d_j/2 for every j in J_*.

For m alpha above a fixed constant, relative Chernoff bounds on J_* give failure probability at most C min{p,alpha^(-q)}exp(-c' m alpha), apart from false inclusions. The latter need a localized argument; the crude p-way union bound alone would lose the fixed-vocabulary/weak-sparsity continuum.

For l>=0, group false candidates by

    alpha/2^(l+3)<d_j<=alpha/2^(l+2).

The Poisson-binomial Chernoff exponent for d_hat_j>=alpha/2 is at least

    (m alpha/2)[(l+1)log 2-1+2^(-l-1)]
       >=c_0 m alpha(l+1),                              (C10)

where c_0>0 is numerical. The number of rows in that group is at most C alpha^(-q)2^(q(l+3)). Summing the geometric series gives C alpha^(-q)exp(-c' m alpha), when m alpha exceeds a fixed q-dependent constant. Separately the per-row bound gives p exp(-c' m alpha). Rows with d_j=0 cannot be selected. Taking the smaller bound proves

    P(E_screen^c)<=C min{p,alpha^(-q)}exp(-c' m alpha).    (C11)

If m alpha<=A Lambda for a sufficiently large fixed constant A, the theorem's upper rate is bounded below by 1/sqrt(A), so bounded loss of any stochastic output proves that part. The algorithm need not know q or perform this case split. In the remaining region, C11 is at most C sqrt(Lambda/(m alpha)).

On E_core, form the K-dimensional normalized rows

    Y_j=C_jR/d_j, Y_hat_j=C_hat_jR/d_hat_j, j in J,
    V=diag(mu)^(-1)Sigma A_R',
    B_jk=A_jk mu_k/d_j.                                  (C12)

Then B_j is stochastic, Y_j=B_j V, and anchor rows equal the K vertex rows V_k. Those vertices have nonnegative entries and row sums at most one. In particular ||V_k||_2<=1. From C8 and mu_k<=1,

    sigma_min(V)>=nu_0:=c sqrt(v_0/2).                   (C13)

This lower bound is independent of alpha.

Define the analysis-only random variable

    Z=max_(j in J_*, r in D_*)
         [|C_hat_jr-C_jr|+|d_hat_j-d_j|]/d_j.

Applying C4 with d_j>=alpha/4 and integrating a union bound over at most |D_*||J_*| entries gives

    E Z<=C[sqrt(Lambda/(m alpha))+Lambda/(m alpha)].      (C14)

More explicitly, in C4 take u=log(4|D_*||J_*|)+t and integrate the exp(-t) tail. C9 bounds the logarithm by C Lambda. On E_screen, changing numerator and denominator separately and using ||Y_j||_2<=1 gives

    max_(j in J)||Y_hat_j-Y_j||_2<=C_K Z.                (C15)

The random core causes no extra factor: the maximum already ranges over its deterministic containing set D_*.

## 5. Maximum-determinant vertex recovery

Choose K distinct rows of Y_hat maximizing their absolute determinant, with deterministic index tie-breaking, and call the resulting square matrix V_hat. If |J|<K or sigma_min(V_hat)<nu_0/2, use the stochastic fallback. No convex hull routine or imported source Assumption 4 is needed.

The following deterministic lemma proves the required local stability. Suppose V is K-by-K with rows of norm at most one and sigma_min(V)>=nu_0, all ideal data rows have form B_j V with B_j stochastic, every vertex is present, and every observed row is within e of its ideal counterpart. Then, for e below a fixed epsilon_0(K,nu_0), the selected V_hat satisfies

    min_P ||V_hat-PV||<=C e,                             (C16)

and its inverse guard passes.

Proof: for any selected ideal K-tuple, |det(B_selected V)|=|det B_selected||det V|<=|det V|, because a stochastic row has Euclidean norm at most one and Hadamard gives |det B_selected|<=1. The true-anchor tuple attains |det V|. Determinants are uniformly Lipschitz on the bounded row ball, so empirical maximization implies

    |det B_selected|>=1-C e/|det V|>=1-C' e.

If a stochastic matrix B has |det B|>=1-eta, Hadamard implies each row has Euclidean norm at least 1-eta. Therefore its largest entry is at least its squared Euclidean norm, and thus at least 1-2eta. That row is within 4eta in L1 of some coordinate vector. The coordinate vectors are distinct when eta is sufficiently small: if two were equal, subtracting those two rows and applying Hadamard would give |det B|<=8eta, contradicting 1-eta. Thus B is within C_K eta of a permutation. Multiplying by V and adding the observation errors proves C16; singular values change by at most the operator error, so the inverse guard follows after shrinking epsilon_0. This proof allows different anchor counts and arbitrary interior rows.

By C14, Markov's inequality gives P(Z>epsilon_0/C_K)<=C E Z. There is no need for an artificial m^(-2) failure target or an extra log m. In the nontrivial region m alpha>A Lambda, both E Z and all screen-failure contributions are O(sqrt(Lambda/(m alpha))).

## 6. Reconstruct all vocabulary rows without inverse-alpha amplification

For every j=1,...,p compute

    F_hat_j=C_hat_jR V_hat^(-1).                         (C17)

Clip each entry at zero and normalize each column to sum one. A zero column uses any fixed probability-vector fallback. The exact population identity is

    C_jR V^(-1)=A_j diag(mu)=:F_j.                       (C18)

Indeed V^(-1)=A_R'^(-1)Sigma^(-1)diag(mu). On E_core, E_screen, and Z<=epsilon_0/C_K, one common permutation P from C16 satisfies

    ||F_hat-FP'||_1
       <=C sum_j sum_(r in D_*) |C_hat_jr-C_jr|+C Z.      (C19)

To see this, change the numerator using the guarded empirical inverse, then change the inverse using the population numerator. The latter sum is bounded because sum_jr C_jr=1; it is not multiplied by p or by alpha^(-1). The inverse constants in both terms depend only on nu_0. C4 bounds the expectation of the first term by C sum_j min{h_j,sqrt(h_j/m)}.

Each population F column has mass mu_k>=c. Clipping cannot increase L1 error from F. For nonnegative u,v with sum v=t>0,

    ||u/sum(u)-v/t||_1 <= (2/t)||u-v||_1,

including the zero-u fallback case. Therefore normalization in C17 costs at most 2/c. On all bad events final loss is at most 2K. Combining C7, C11, C14, and C19 yields the uniform instance bound

    E d_topic(A_hat,A)
       <=C[r_alpha+sum_j min{h_j,sqrt(h_j/m)}
                     +p exp(-c_*m)].                    (C20)

For m alpha<=A Lambda bounded loss absorbs the right side, as explained above. The same estimator is used in both cases.

By C5, h_(j)<=C_(K,q)j^(-1/q). For q<1/2 its square-root series is summable. For q=1/2, split at j of order sqrt(m). For q>1/2, either split at h=1/m or sum sqrt(h_(j)/m) through p. These give respectively tau_q in Section 1. Since p<=m^D, the exponential remainder is absorbed by m^(-1/2), which is itself at most C r_alpha for alpha<=alpha_0. C20 proves the upper half of C2, with constants independent of alpha.

## 7. A uniform unknown-location lower family, including one candidate

The lower construction uses the full multinomial law; the artificial disjoint pairs used for upper concentration are not treated as independent data. Put

    a=K alpha<=1/16, zeta=1/4,
    B=[[3/4,1/4],[1/4,3/4]],
    T_theta=[[1-theta,theta],[theta,1-theta]],
    M=min{max{1,floor(a^(-q)/16)},floor((p-K-1)/2)}.       (C21)

Under p>=p_0(K), M>=1 and log(2+M) is comparable to Lambda, with constants depending only on K,q. In fact max{1,floor(a^(-q)/16)}>=a^(-q)/32, while the vocabulary cap is at least p/8. This also handles fixed p and alpha bounded away from zero.

For l=1,...,p-(2M+K+1), define positive padding rows of common mass

    t_l=(a/32)2^(-(l+4)/q), e=sum_l t_l,
    b=1-zeta-Ma-e, d=1-zeta-e.                           (C22)

An empty padding set is allowed. We have Ma<=1/16: if M>=2 use M<=a^(-q)/16 and a^(1-q)<=1; if M=1 use a<=1/16. Also e<=1/32, so b>=1/2 and d>=23/32.

The null topic matrix A_0 has one shared row zeta(1,...,1); M candidate blocks aI_2 on topics 1,2; two common rows bB on topics 1,2; K-2 extra anchors d e_k for k>=3; and the common padding rows t_l(1,...,1). Unmentioned topic entries are zero. Every column sums to one. Alternative A_j keeps candidate j at aI_2, changes every other candidate block to aT_theta and the common block to bBT_theta, and leaves the remaining rows unchanged.

Let W_0 have K equal groups of n/K columns

    w^(g)=1/(2K)1+(1/2)e_g.

For every alternative use W_theta=S_theta^(-1)W_0, where S_theta=diag(T_theta,I_(K-2)). Choose

    theta=(1/(64K))min{1,sqrt(log(2+M)/(ma))}.            (C23)

Then 0<theta<=1/(64K). All W_theta entries are positive: only groups 1,2 change, and their first two coordinates shift by plus/minus delta=theta/[2(1-2theta)]<1/(2K). Their columns and mean remain stochastic, with mu=1/K. Sigma_0 has eigenvalues 1/K on 1 and 1/(4K) on its orthogonal complement; since sigma_min(S_theta^(-1))=1, lambda_min(Sigma_theta)>=1/(4K).

### Uniform class membership

The common block and disjoint extra anchors give

    sigma_K(A_j)>=min{b(1-2theta)/2,d}>=3/16>kappa.

The shared row gives every Gram entry at least 1/16>c. Each retained candidate anchor has corpus mass a/K=alpha, and the extra anchors have mass d/K>alpha. Every observed word probability is positive.

For weak-q membership when M>=2, the threshold-count contributions from common rows, the shared row, candidate rows, and padding are respectively at most 2, 1, 2Ma^q<=1/8, and 1/2; their sum is below 4. If M=1, use a separate argument rather than the loose 2Ma^q bound. Each first-two-topic column then has exactly four nonpadding positive entries: the shared row, its anchor, and two common entries. All are at least a, whereas every padding entry is smaller than a. The first four ordered entries satisfy j A_(j)^q<=4 trivially. At a later rank l+4,

    (l+4)t_l^q=(l+4)(a/32)^q 2^(-(l+4))<4.

Other topic columns have only two nonpadding positive entries and satisfy the same bound. Thus every null and alternative belongs to the same class C_q(alpha), including the bounded-candidate and small-q cases.

### Exact likelihood calculation and quotient separation

Outside candidate pair j, the observable products A_j W_theta and A_0 W_0 agree exactly. Only groups 1,2 change in that pair. Write u=(K+1)/(2K), v=1/(2K). The changed group-1 probabilities are a(u+delta,v-delta), instead of a(u,v), with reversal in group 2. The one-token null-relative second-moment increment is

    chi_1=a delta^2(1/u+1/v)
      =a theta^2 K(K+2)/[2(K+1)(1-2theta)^2]
      <=2K a theta^2.                                   (C24)

For complete document likelihood ratios L_j=dP_j/dP_0, the multinomial theorem gives

    E_0[L_(j,doc)L_(k,doc)]
      =[sum_r p_j(r)p_k(r)/p_0(r)]^N.

Different candidate alternatives have disjoint zero-sum changes, hence E_0 L_jL_k=1 for j!=k. Exactly 2n/K documents are affected by a given alternative, so

    E_0 L_j^2=(1+chi_1)^(2m/K)<=exp(4ma theta^2).

For the uniform mixture P_bar of the M alternatives,

    chi-square(P_bar,P_0)
      <=[(M+2)^epsilon-1]/M<=2epsilon<1/16,
    epsilon=1/(1024K^2).                                (C25)

The first inequality uses C23, and the second uses concavity x^epsilon<=1+epsilon(x-1). This bound works for every M>=1; it does not require a growing number of candidates or a small-angle asymptotic expansion.

A topic permutation moving any k>=3 costs at least 2d at its extra anchor. If all those topics are fixed, identity and swapping 1,2 have common-block distances 2b theta and 2b(1-theta), respectively. Therefore every alternative satisfies

    d_topic(A_0,A_j)>=2b theta.                          (C26)

Testing the null against its mixture with the event d_topic(A_hat,A_0)<b theta, the triangle inequality and C25 give maximum expected estimation loss at least c b theta. Since log(2+M) is comparable to Lambda and a=K alpha,

    inf_Ahat sup_C_q(alpha) E d_topic(Ahat,A)>=c r_alpha. (C27)

Mixture averaging is only a testing device. W is a deterministic matrix at each constituent model, and the complete count experiments are used exactly.

## 8. Ordinary-vocabulary lower bounds in the same class

These families have stronger, fixed anchors, hence belong to C_q(alpha) for every alpha<=alpha_0. They also cover fixed p. We give the exact families and likelihood bounds; the corresponding algebra appears in the read-only fixed-K source K29--K32 and strong-anchor source Sections 6--7.

Use W_0 from Section 7, zeta=1/4, strong anchor mass a_s=1/8 for topics 1,2, two common rows bB, extra anchors d e_k for k>=3, and positive common padding to complete p rows. The anchor corpus mass a_s/K=1/(8K) exceeds alpha_0. Shared overlap, mixture conditioning, and common-block conditioning have the same fixed floors as above.

For q<1/2, change only topic 1 in the common block by plus/minus b eta in its two rows, with eta=1/(64sqrt(m)). Use padding t_l=(1/32)2^(-(l+4)/q), and set b=1-zeta-a_s-sum t_l, d=1-zeta-sum t_l. There are only four nonpadding positive entries in each first topic, all above the padding, so the ordered-entry argument from Section 7 proves weak-q radius 4. The full quotient distance between the signs is 4b eta for sufficiently large m; competing topic permutations cost a fixed positive amount. A token-level chi-square bound is 36eta^2, so the complete count-law KL is at most 36m eta^2<1/96. Two-point testing gives c/sqrt(m).

For q>1/2, let

    r=min{floor(m^q/8),floor((p-K-3)/2)},
    t=r^(-1/q)/128, gamma=1/(32sqrt(mt)).                 (C28)

Add r independently signed pairs (t(1+gamma omega_j),t) and (t(1-gamma omega_j),t) on topics 1,2. Use common padding t_l^pad=(1/16)2^(-2l), let e be its sum, and put b=1-zeta-a_s-2rt-e, d=1-zeta-e. Here mt>=1/16, gamma<=1/8, 2rt<=1/64, e<=1/48, and b>1/2. The threshold-count contributions to weak-q from anchor, common rows, shared row, packed rows, and padding are respectively below 1/2, 3/2, 1/2, 1/4, and 1/2, totaling less than 4. Other columns have fewer components.

For any document put v=w_1+w_2, w=w_1. A neighboring sign flip changes the probabilities t(v+gamma w),t(v-gamma w) to their reversal. Its directed categorical chi-square is

    8t gamma^2 w^2 v/(v^2-gamma^2 w^2)
       <=(32/3)t gamma^2.                               (C29)

Thus neighboring full-corpus KL is at most 1/96 and TV is below 1/8. Full permutation distance is 4t gamma times Hamming distance: nonidentity permutations cost at least 4a_s or 2d, whereas the identity diameter is at most 1/256. Nearest-family decoding and Assouad give c r t gamma. For p>=p_0 and sufficiently large m, r is comparable to min(m^q,p), even when p is fixed. This proves c tau_q in this case.

For q=1/2, set

    Rbar=min{floor((p-K-3)/4),floor(sqrt(m)/8)},
    L_0=floor(log_2 Rbar), r_l=2^l, l=0,...,L_0,
    t_l=1/(128r_l^2), gamma_l=1/(32sqrt(m t_l)).          (C30)

At scale l include r_l independently signed pairs of the form in C28. The number of packed rows is less than 4Rbar, leaving room for the K+3 core rows. Total packed mass per first topic is at most 1/32. Fill remaining rows by (1/32)2^(-2j); its mass is at most 1/96. Then b=1-zeta-a_s-Mpack-e>1/2. Since gamma_l<1/8, at any threshold u the packed contribution to sqrt(u) times the number of entries is at most

    sqrt(u) 4sqrt(9/(1024u))=3/8.

The anchor, shared row, two common rows, and padding contribute at most 1/2, 1/2, 7/4, and 1/2. Their sum with 3/8 is below 4. Hence the critical weak-sparsity constraint also holds uniformly.

C29 applies at every scale, with m t_l gamma_l^2=1/1024. Neighboring KL is again at most 1/96. Quotient distance is exactly 4 sum_l t_l gamma_l Hamming_l for large m: its entire identity diameter is O(log(m)/sqrt(m)), whereas every competing permutation costs a fixed amount. Weighted Assouad therefore yields

    c sum_l r_l t_l gamma_l
       =c (L_0+1)/(32sqrt(128m))
       >=c' log(2+min{p,sqrt(m)})/sqrt(m).               (C31)

The last comparison holds uniformly for p>=p_0(K), including fixed p, because Rbar is comparable to min(p,sqrt(m)) up to K-dependent constants, and L_0+1 is comparable to log(2+Rbar). The full multinomial KL equals N times the categorical KL in every document. Thus none of these lower families requires N to be bounded.

Combining C27 with these ordinary-vocabulary subfamilies, a maximum of lower bounds controls half their sum. Since r_alpha=min(1,sqrt(Lambda/(m alpha))) and tau_q is bounded and tends to zero in the permitted p range, this is equivalent up to constants to the capped expression in C2. This completes the theorem.

## 9. What this does and does not settle

The known-strength continuum now connects constant anchors, the source's quarter-power boundary, fixed vocabularies, and the consistency boundary in one expected-risk statement. The estimator knows alpha but neither q nor W nor the anchor locations; the frequent core's inverse bounds do not deteriorate with alpha. All claims concern fixed K and fixed weak-q radius/conditioning constants, exact separability, and multinomial documents.

This does not solve unknown-strength adaptation. The separate fixed-p obstruction in `../anchor_continuum_decision_20261027/decision_memo.md` shows why free adaptation to this exact oracle rate can fail. A penalty-based selector may attain a different adaptive logarithm, but no such claim is made here. The concentration tools, co-occurrence geometry, determinant selection, and ordinary weak-sparsity tails have classical antecedents. The existing primary comparison is `../novelty_decisive_gate_20261027/decisive_primary_comparison.md`; absence of direct subsumption there is not historical novelty clearance for C2.
