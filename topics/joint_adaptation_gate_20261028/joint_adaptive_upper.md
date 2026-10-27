# Joint adaptation to unknown anchor strength and mixture diversity

28 October 2026. New analytic source for independent review. This extends the held fixed-conditioning adaptive upper to weakening document-mixture diversity and every document length. The earlier fixed-beta adaptation theorem, its constrained lower bound, and its classical-SPA reduction were inspected first; their scope is not counted as new here. No historical novelty, external validation, efficient implementation or practical superiority is claimed.

## 1. Experiment and theorem

Observe independent X_i~Multinomial(N,A w_i), with integer N>=2, stochastic nonnegative columns of A and W, and unknown deterministic W. K>=2 is fixed. Let

    m=nN, mu=W1/n, Sigma=WW'/n, b=lambda_min(Sigma)>0,
    d=A mu, min_k mu_k>=mu0>0, sigma_min(A)>=kappa0>0.

Each topic has an unknown exact pure anchor row with corpus frequency at least alpha>0. This is a property of the parameter, NOT an input to the new estimator. Vocabulary size p is any finite integer at least K. Zero rows are allowed. Define, for t>0,

    a(t)=1/sqrt(nN t)+1/[t sqrt(nN(N-1))],
    ell(x)=log(2+1/x), x>0,
    H_a(d)=sum_j min{d_j,a sqrt(d_j)}.

Loss is expected entrywise L1 error modulo column permutations. The estimator below returns stochastic columns and uses K and the fixed class constants mu0,kappa0, but neither alpha, beta, b, q, sparsity radius, W nor anchor locations.

**Theorem A.** There is a sufficiently large fixed penalty constant A0=A0(K,mu0,kappa0) for which the single observable estimator in Section 2 satisfies

    E loss <= C min{1,
       H_(a(b))(d)+a(b) sqrt(ell(alpha)/alpha)}.             (J1)

Constants are uniform in p,n,N,alpha,b. On a class specified by b>=beta and columnwise weak-q radius S_A, for any fixed 0<q<1,

    E loss <= C_(K,mu0,kappa0,q,S_A) min{1,
       F_(q,p)(a(beta))+a(beta) sqrt(ell(alpha)/alpha)},     (J2)

where for 0<a<1,

    F_(q,p)(a)=a,                                      q<1/2;
    F_(1/2,p)(a)=a log(2+min{p,1/a});
    F_(q,p)(a)=min{a^(2(1-q)),a p^(1-1/(2q))},          q>1/2,

and F=1 for a>=1. The estimator itself is independent of q and beta. In particular J2 applies to the fixed radius-four class in the held matched all-N frontier, without its known-alpha input.

This is an adaptive upper, not yet a new constrained-risk lower. The adaptation logarithm ell(alpha) differs from the known-alpha location logarithm log(2+min(p,alpha^(-q))). At fixed p their ratio can diverge. No claim of attaining the known-alpha rate simultaneously at every strength is made.

## 2. Observable algorithm: multiplicative row penalties

Compute the empirical frequency dhat and factorial-pair matrix

    dhat_j=(nN)^(-1)sum_i X_ij,
    Chat_jr=n^(-1)sum_i X_ij(X_ir-1_(j=r))/[N(N-1)].

Let lambda_hat be the Kth largest eigenvalue of the symmetric Chat, and Uhat an orthonormal basis for its K largest eigenvalues, using a fixed measurable tie convention. If lambda_hat<=0, return a fixed stochastic-column estimate. Otherwise put Zhat=Chat Uhat. For every row with x=dhat_j>0 set

    pen_j=A0 [a(lambda_hat) sqrt(ell(x)/x)
                                  +ell(x)/(m lambda_hat x)],
    w_j=1/(1+4pen_j), Vtilde_j=w_j Zhat_j/x.                (J3)

For x=0 set Vtilde_j=0 and w_j=0. The penalty is **uncapped**. Select K distinct rows S maximizing |det Vtilde_S|, with deterministic index tie-breaking, and set Vhat=Vtilde_S. If the maximal determinant is zero, return the bounded stochastic fallback. Otherwise form the raw reconstruction

    Fhat=Zhat Vhat^(-1).                                  (J4)

Use the observed-eigenvalue output cutoff tau_hat=a(lambda_hat)^2: set reconstructed row j to zero if dhat_j<tau_hat. Clip remaining negative entries to zero and normalize every column to sum one. A zero column or nonfinite arithmetic uses a fixed stochastic-column fallback. These steps define a mathematical exact-arithmetic estimator; numerical conditioning and efficient maximization are separate questions.

Multiplicative row weights are essential to the stated proof. For any invertible K-by-K right factor T, every candidate determinant acquires the SAME factor det(T). Thus selection is unchanged and

    Zhat Vhat^(-1)=(Zhat T)(Vhat T)^(-1).

An additive penalty applied directly to raw spectral determinants would not have this invariance. The estimator does not compute the population coordinate map T used below.

## 3. Held spectral identities and the two uniform row facts

The following precise premises are supplied by the bound sources listed in Section 9. Analyze at the actual b, not at a supplied beta. Write pi_i=A w_i, T_it=Z_it-pi_i for categorical token indicators, epsilon_i=N^(-1)sum_t T_it, and

    E=n^(-1)sum_i epsilon_i w_i' Sigma^(-1/2),
    Qbar=n^(-1)sum_i [N(N-1)]^(-1)sum_(s!=t) T_is T_it',
    M=A Sigma^(1/2)+E, R=Qbar-EE', Chat=MM'+R.

Set

    G0={||E||op<=kappa0 sqrt(b)/4,
         ||Qbar||op<=kappa0^2 b/32}.

There are constants depending only on the fixed geometry such that

    P(G0^c)<=C a(b),
    c_lambda b<=lambda_hat<=C_lambda b on G0.             (J5)

On G0, H0=M'Uhat is invertible and the analysis-only map

    T=H0^(-1) Sigma^(-1/2)diag(mu)

satisfies

    Zhat T=A diag(mu)+D,
    ||T||op<=C_T/b,
    ||D_j||<=delta_j=C[||E_j||/sqrt(b)+||Qbar_j||/b].       (J6)

Define delta_j by this expression on all outcomes. Put a=a(b) and c=1/(m b); then c<=a^2 and b<=1. The all-N variance-sensitive row moments and frequency concentration give, for u>=2,

    P(delta_j+|dhat_j-d_j|>
                 C[a sqrt(d_j u)+c u])<=C exp(-u),
    E delta_j^2<=C d_j a^2.                              (J7)

The first display follows also directly by taking the integer moment r=ceil(u) in the held moment bound and Markov at e times its Lr norm. Constants absorb ceil(u)/u. It retains the actual full-document statistic; overlapping pairs are not treated as independent.

For d_j>0 define the ideal simplex row B_j=A_j diag(mu)/d_j, which is stochastic. If d_j=0 use B_j=0. Such a row has dhat_j=0 almost surely. For x=dhat_j>0 let

    Yhat_j=Zhat_j T/x, R_j=||Yhat_j-B_j||.

Two different bounds will be used:

    R_j<=[delta_j+|x-d_j|]/x on G0;                      (J8)
    R_j<=C_R/b on G0.                                   (J9)

For J9, Chat has nonnegative entries and its jth row sums exactly to x, so ||Chat_j||2<=x. Since ||Uhat||op=1, J6 gives ||Yhat_j||<=C_T/b. Also ||B_j||<=1 and b<=1. Thus C_R=C_T+1 works. J9 is a deterministic bound on the good spectral event, not a fixed-beta bound smuggled into a constant.

On G0, J5 implies two-sided comparisons

    c_P A0 [a sqrt(ell(x)/x)+c ell(x)/x]
       <=pen_j
       <=C_P A0 [a sqrt(ell(x)/x)+c ell(x)/x].            (J10)

All comparison constants are fixed. In particular they have no alpha or b dependence. These inequalities justify using the random eigenvalue in the penalties without conditioning on it.

## 4. A truncated expected maximum excess, with false rare rows

On outcomes in G0 define

    Z=max_(j:dhat_j>0)(R_j-pen_j)_+,

with the maximum of an empty set zero. Only truncated expectations and fixed-threshold tail probabilities of Z are needed. We prove

    E[1_G0 min{1,Z}]<=C min{1,a}.                        (J11)

The event involving G0 is retained throughout; no claim about T or R_j outside G0 is used.

**Balanced frequencies.** Fix d=d_j>0, 0<t<1, and d/2<=x<=2d. Let

    u=3ell(d)+c0 d t^2/a^2,

where c0>0 is a sufficiently small fixed constant. It is at least2. Apply J7 then J8. The resulting upper threshold for R_j is at most

    C1[a sqrt(ell(d)/d)+c ell(d)/d]
                      +C2 sqrt(c0)t+C2 c0(c/a^2)t^2.

Choose c0 so the last two terms are at most t/2. The function ell(x)/x decreases, and x<=2d implies ell(x)/x>=ell(d)/(4d). By increasing A0 in J10 the first bracket is dominated by pen_j. Therefore

    P(G0,R_j>pen_j+t,d/2<=x<=2d)
       <=C d^3 exp(-c0 d t^2/a^2).                      (J12)

**Active penalties force enough empirical counts.** On G0, a positive excess requires pen_j<C_R/b by J9. The second term of J10 then implies

    m x>K_* ell(x), K_*=c_P A0/C_R.                      (J13)

Choose A0 so K_*>=96 as well. If m<=K_* log3 there is no positive excess. Otherwise let s in (0,1) solve m s=K_* ell(s); J13 requires x>s. This condition is independent of b after cancellation. It is why an arbitrarily small true row appearing by chance does not force an extra logarithm of 1/b or m.

**Underestimated frequency x<d/2.** Active excess requires d>2s, so m d>2K_* ell(s)>=2K_* ell(d). The Poisson-binomial lower Chernoff bound for m dhat_j gives

    P(G0,R_j>pen_j+t,x<d/2)
       <=exp(-md/8)<=d^3 exp(-md/16).                   (J14)

If d<=2s the event is empty. The final inequality follows from md/16>=3ell(d), using K_*>=96.

**Overestimated frequency x>2d.** Let v=max{2d,s}. Active excess implies x>v. If v>=1 the event is empty. Otherwise set k=mv and z=d/v<=1/2. Poisson-binomial Chernoff gives

    P(x>=v)<=exp{-k[log(1/z)-1+z]}.

For 0<z<=1/2,

    log(1/z)-1+z >=(1/8)log(1/z)+1/16.

Also k>=K_* ell(v), so k/8>=3 and k/32>=3log(1/v). Splitting the final k/16 into two terms yields

    k[log(1/z)-1+z]
       >=3log(v/d)+3log(1/v)+k/32
       >=3log(1/d)+md/16.

Consequently

    P(G0,R_j>pen_j+t,x>2d)<=d^3 exp(-md/16).             (J15)

These are bounds for the actual independent token indicators, valid for nonidentical document probabilities. They do not condition on a selected row or on lambda_hat.

Because a^2>=1/(mb)>=1/m and t<1, choosing c0<=1/16 bounds both J14 and J15 by d^3 exp(-c0 d t^2/a^2). Combining with J12 and summing over all rows uses only sum_j d_j=1:

    sum_j d_j^3 exp(-L d_j)
        <=sup_(x>0) x^2 exp(-Lx)=4e^(-2)/L^2.

Thus

    P(G0,Z>t)<=min{1,C a^4/t^4}, 0<t<1.                 (J16)

Integrating this inequality over (0,1) proves J11. This avoids any ambient-vocabulary union factor or polynomial-p condition. It also avoids asserting an untruncated expected maximum bound when R_j may be of order 1/b.

## 5. Designated anchors pay only the adaptive strength cost

Fix one true anchor per topic and call their tuple T0; it is used only for analysis. For a positive-count row define h_j=min{1,pen_j}; for zero empirical count define h_j=1. Put P0=sum_(j in T0)h_j. Then

    E[1_G0 P0]<=C min{1,a sqrt(ell(alpha)/alpha)}.         (J17)

For a designated row of true mass d>=alpha, the event x<d/2 has probability at most exp(-md/8), covering zero observed counts. On x>=d/2 intersect G0, the upper comparison in J10 and monotonicity of ell(x)/x imply

    h_j<=C min{1,r_d+r_d^2}<=C min{1,r_d},
    r_d=a sqrt(ell(d)/d),

because c<=a^2. The bad-count probability is also at most C min{1,r_d}, using a>=m^(-1/2). Finally r_d<=a sqrt(ell(alpha)/alpha). Sum over the fixed K anchors. This argument bounds a data-dependent penalty on G0 by deterministic quantities; no independence of counts and eigenvalue is invoked.

## 6. Deterministic weighted-determinant recovery

This is a finite K-dimensional lemma. Suppose ideal rows B_j are nonnegative with sum at most one and include all K coordinate vertices at designated indices T0. For positive-count rows suppose ||Yhat_j-B_j||<=p_j+z with p_j>=0. Define

    w_j=1/(1+4p_j), Vtilde_j=w_j Yhat_j,
    h_j=min{1,p_j}, theta_j=p_j/(1+4p_j).

A zero-count row is instead Vtilde_j=0, h_j=1, theta_j=1/4. Let P0=sum_T0 h_j and e=P0+z. Assume 0<=z<=1. For every candidate row,

    ||Vtilde_j||<=1-3theta_j+z.                         (J18)

For positive counts, w_j(1+p_j+z)=1-3theta_j+w_j z. The zero-row convention also satisfies J18. At designated anchors,

    ||Vtilde_j-B_j||<=5theta_j+z<=C h_j+z,              (J19)

including zero counts, whose error is one.

If e is below a fixed sufficiently small epsilon_K, telescoping the determinant over the K anchor rows, whose norms are at most1+z, gives

    |det Vtilde_T0|>=1-C_K e.

Let S maximize |det Vtilde_S|. Its determinant is at least this value. By Hadamard and the bound1+z on every other row, each selected row has norm at least

    (1-C_K e)/(1+z)^(K-1)>=1-C'_K e.

Combining with J18 gives theta_j<=C_K e for every j in S. For smaller epsilon_K this excludes a zero-count row and ensures theta_j<1/8. Solving p_j=theta_j/(1-4theta_j) then gives p_j<=2theta_j<=C_K e. J19, now without the need for j to be an anchor because ||B_j||<=1, gives

    ||Vtilde_j-B_j||<=C_K e, j in S.

Another determinant telescoping therefore yields |det B_S|>=1-C_K e. The elementary stochastic-simplex determinant lemma finishes the argument: Hadamard forces each row norm near one; for a substochastic row b, max b_k>=sum b_k^2, so it is O(e) from a coordinate vector. Two rows cannot be close to the same coordinate without making the determinant O(e). Hence one permutation Pi satisfies

    ||Vtilde_S-Pi||F<=C_K e, ||Vtilde_S^(-1)||op<=C_K.    (J20)

This lemma is deterministic and affine-invariant when the estimator's selection is described in raw coordinates. It is not asserted as a new general vertex-hunting theorem. Its crucial conclusion controls the selected penalties, rather than merely the determinant of the unknown ideal rows.

## 7. Applying the lemma and controlling the entire vocabulary

On G0 apply Section 6 in the analysis coordinates. Selection of S is identical to the observable selection because all weighted determinants acquire det(T). Use p_j=pen_j and z=Z. The designated ideal anchor rows are the coordinate vertices. Let

    G1=G0 intersect {P0+Z<=epsilon_K}.

On G1, the selected matrix Vhat T is within C(P0+Z) of a permutation and has uniformly bounded inverse. In particular the algorithm's zero-determinant fallback cannot occur. From J4 and J6,

    Fhat=(A diag(mu)+D)(Vhat T)^(-1).

After one common permutation, the raw row reconstruction error is at most

    C delta_j+C d_j(P0+Z).                              (J21)

The held observed-eigenvalue comparison gives, on G0,

    c_a a^2<=tau_hat<=C_a a^2.                          (J22)

Exactly as in the bound observable-threshold proof, J22 and unconditional Cauchy--Schwarz yield

    E[1_G1 delta_j 1_(dhat_j>=tau_hat)]
       <=C a sqrt(d_j) min{1,sqrt(d_j)/a}
       <=C min{d_j,a sqrt(d_j)}.

For omitted mass, if d_j<=2C_a a^2 the same bound is deterministic. Otherwise frequency variance gives

    E[1_G1 d_j 1_(dhat_j<tau_hat)]<=C/m
       <=C a sqrt(d_j).

The first inequality uses |dhat_j-d_j|>=d_j/2 on omission; the second follows from a>=m^(-1/2) and d_j>2C_a a^2, with constants adjusted for C_a. Thus the retained-error and omitted-mass sums are bounded by C H_a(d). The remaining term in J21 sums to C(P0+Z) because sum_j d_j=1. Clipping and normalizing columns cost only fixed factors since every true column of A diag(mu) has mass mu_k>=mu0.

Finally the total loss is always at most2K. Equations J5, J11 and J17 imply

    P(G1^c)<=C[a+E(1_G0 P0)+E(1_G0 min{1,Z})],
    E[1_G1(P0+Z)]<=E(1_G0 P0)+E(1_G0 min{1,Z}).

The first line uses a fixed-threshold Markov bound, not an untruncated expectation of Z. For a>=1 bounded loss proves J1 directly. For a<1, a<=C a sqrt(ell(alpha)/alpha), since alpha<=1. Combining the preceding bounds proves J1. The weak-q profile evaluation and b>=beta give J2 by monotonicity of a(t) and H_a.

## 8. What this proof does and does not remove

The estimator no longer needs alpha, beta or q, while preserving the distinct first-order and degenerate document-noise scales. The proof does not substitute an effective sample size into the old fixed-beta theorem. It replaces the fixed frequent-core coordinates with the actual relative spectral map, handles that map's C/b norm explicitly, uses uncapped penalties to control false rare rows, and uses a multiplicative selection rule that survives the unknown affine change of coordinates.

The old fixed-conditioning result already gives the ell(alpha) adaptation cost. Its fixed-p K=2,q=1/2 constrained lower remains an obstruction to free adaptation. Extending that constrained lower uniformly through weakening beta and all N is separate work. This source establishes only the upper side of that joint adaptive question.

The known-alpha sharp minimax theorem remains unchanged. At polynomially large vocabularies its location logarithm can be comparable to ell(alpha), whereas at fixed p the new upper pays a potentially larger adaptive logarithm. No ordinary minimax lower is inferred from this upper. Strong unnormalized topic geometry, exact anchors, fixed class constants and fixed K remain. There is no practical-runtime, all-diffuse-topic, approximate-anchor, confidence-interval or historical-priority claim.

## 9. Read-only source bindings

- All-N row Bernstein theorem: `../anchor_selection_frontier_20261028/all_document_lengths_bernstein_upper.md`, SHA256 `bd9c774907a8691508d41bf4ea019d4b7b996b99707a0a1e8694aedd74aac2d3`; independent audit `e597865ab8c0cb2f3d85557a15386463dc4f94063e725805c78afa5024fac3d2`.
- Relative spectral map and dimension-free second moments: `../multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md`, SHA256 `de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`.
- Observed-eigenvalue comparison and random output cutoff: `../weak_sparsity_frontier_gate_20261028/observable_conditioning_threshold.md`, SHA256 `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8`.
- Earlier fixed-beta adaptive theorem and deterministic determinant lemma: `../adaptive_anchor_oracle_20261027/adaptive_estimator_and_constrained_frontier.md`, SHA256 `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`.
- Earlier mass-weighted empirical-frequency excess lemma, whose imbalance proof is repeated with the new spectral active-penalty premise: `../adaptive_anchor_oracle_20261027/empirical_frequency_maximum_lemma.md`, SHA256 `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`.
- Earlier classical-SPA contraction reduction: `../greedy_decisive_prior_gate_20261027/classical_spa_contraction_reduction.md`, SHA256 `6f6613f2758ffca32473fea5392a19775be72ee06384ef9a63e711e74335827d`.

No held source or registry entry was modified. The new proof requires its own independent review; the existing audits do not automatically certify Sections 4--7.
