# A matching document-length lower bound for any fixed topic count

27 October 2026. New candidate, written by root for independent review. No prior frozen source is changed. This is a statistical theorem, not a claim of historical priority.

## 1. Claim and scope

Fix K>=3 and p=K+10. Observe independent documents

    X_i ~ Multinomial(N,A w_i), i=1,...,n,

where A and W have stochastic columns and W is deterministic but unknown. Define mu=W1/n, Sigma=WW'/n, and d=A mu. Use entrywise L1 topic loss modulo column permutations. Let

    0<alpha<=1/(64K),
    0<beta<=beta0(K)=1/[256 K^2(K-2)],
    n>=128(K-1), N>=2.

Consider the class with a pure anchor of corpus mass at least alpha for every topic, every w_ki>=1/(4K), sigma_min(A)>=1/(8 sqrt(K)), every entry of A'A at least 1/64, and lambda_min(Sigma)>=beta. There is a constant c_K>0 such that its minimax risk is at least

    c_K min{1, sqrt([1+(N-1)beta]/[n alpha N(N-1)beta^2])}.    (L1)

The lower bound holds even if the estimator is told the designated anchor indices and their topic-column masses. The result at K=2 is proved separately in the preceding document-length gate. Together with general_k_upper.md, (L1) yields matching rates for every fixed K>=2 on the displayed fixed vocabularies; it does not claim the lower bound for every p>=K or uniform constants as K grows.

The proof introduces random signs only as a prior over admissible deterministic W. It does not change the sampling model to iid random mixtures.

## 2. Stochastic topics, strong geometry, and separation

Let a=K alpha, epsilon=1/128, h=(15/16-4a)/2, and s in [3/16,1/4]. The first two columns on the first twelve rows are

    (4a,0), (0,4a), (h+s,h-s), (h-s,h+s),
    eight copies of (epsilon,epsilon).

They vanish on the remaining K-2 rows. Let r0 be uniform on rows 3,...,12 and zero elsewhere. For k=3,...,K set

    A_:k=(1/2)r0+(1/2)e_(k+10).

All columns are nonnegative and sum to one. The designated anchors are rows 1,2,13,...,K+10. The first two column singular values are bounded below by 2s>=3/8 using their common-word 2-by-2 block. For any coefficient vector z=(v,t), where v has two entries, the extra rows of A z are t/2, whereas its first twelve rows are A_pair v+(r0/2)sum t. Hence

    ||v|| <= (8/3)[||top||+(sqrt(K-2)/2)||t||],
    ||z||^2 <= (128/9)||top||^2+[1+32(K-2)/9]||t||^2
            <=64K ||A z||^2.

Thus sigma_min(A)>=1/(8 sqrt(K)). Old-old Gram entries exceed 1/16; old-extra entries equal (1-4a)/20>=3/64; distinct extra-extra entries equal 1/40. The stated 1/64 Gram floor follows, including the diagonal entries.

For s1=s0+Delta, 0<Delta<=1/16, the entrywise distance for the identity topic matching is 4Delta. A swap of the first two topics costs at least 8(3/16)=3/2 on rows 3,4. A permutation moving any extra topic costs at least one on the extra anchor rows: each moved extra coordinate contributes half a unit in each of the two affected column positions. The same conclusion holds when an extra topic exchanges with an old one. Consequently

    min_P ||A_(s1)-A_(s0) P||_1=4Delta.                  (L2)

## 3. Deterministic strong directions in the mixture design

Put u=1/K times the all-ones vector, e=(e_1-e_2)/sqrt(2), and

    H={x:x_1=x_2}, z_j=e_j-(e_1+e_2)/2, j=3,...,K,
    h0=1/(2K), m=2(K-2).

Cycle the m vectors u+h0 z_j, u-h0 z_j to form columns B_i, stopping at n. These are stochastic, every entry is at least 1/(2K), and B_i1=B_i2. Their balanced covariance is

    u u'+[h0^2/(K-2)] sum_(j=3)^K z_j z_j'.

The z_j are orthogonal to u and have Gram matrix I+(1/2)11'. They span H intersect 1-perp. Thus the balanced covariance is at least [4K^2(K-2)]^(-1) times the projector onto H. Since n>=2m, every cycle point appears at least n/(2m) times. The actual covariance obeys

    Sigma_B=BB'/n >=c0 P_H,
    c0=1/[8K^2(K-2)].                                  (L3)

For signs xi_i in {-1,+1}, set

    r(s)=sqrt(beta)/s,
    w_i(s,xi)=B_i+r(s) xi_i e.                          (L4)

The largest coordinate perturbation is 16 sqrt(beta)/(3 sqrt(2)), which is at most 1/(4K) under the beta restriction: its square is at most 1/[18K^2(K-2)]<=1/(16K^2). Thus all w_ki>=1/(4K), and columns remain stochastic. In particular mu_k>=1/(4K), the two old anchor corpus masses are at least 4K alpha/(4K)=alpha, and the extra anchor masses are at least 1/(8K)>=alpha.

## 4. Conditioning a sign prior keeps every mixture admissible

Initially take independent fair signs xi. Let Pi_B be the orthogonal projector in R^n onto the row space of B. Define the event

    E={||Pi_B xi||^2/n<=1/2}.

It is independent of s. Since E||Pi_B xi||^2=rank(B)=K-1, Markov's inequality gives

    P(E^c)<=2(K-1)/n<=1/64.                            (L5)

Write c=B xi/n. On E,

    c' Sigma_B^dagger c=||Pi_B xi||^2/n<=1/2.

Decomposing an arbitrary vector as x+z e, x in H, its quadratic form under Sigma=WW'/n is

    x' Sigma_B x+2 r z x'c+r^2 z^2
      >=(1-1/sqrt(2))[x' Sigma_B x+r^2 z^2]
      >=(1-1/sqrt(2))min(c0,r^2)(||x||^2+z^2).

Here r^2>=16 beta and c0>=32 beta. Therefore Sigma>=beta I. The prior obtained by conditioning on E is supported entirely on deterministic parameter matrices satisfying all the hypotheses.

## 5. Nonidentical document laws and their full-length information

For each fixed i, define d_i=A_s B_i. Because B_i1=B_i2, d_i does not depend on s. It has strictly positive coordinates. Conditional on a sign, the token probability vector is

    p_i(s,xi_i)=d_i+xi_i [sqrt(beta)/(s sqrt(2))](A_s,:1-A_s,:2)
               =d_i (1+xi_i b_i,s),                    (L6)

where the final product is coordinatewise. On rows 3,4 the additive contrast is respectively +sqrt(2 beta), -sqrt(2 beta), independent of s. The only nonzero derivatives with respect to s occur at rows 1,2, whose additive contrasts are +/-2 sqrt(2)K alpha sqrt(beta)/s. All other contrasts are zero.

The baseline masses at rows 1,2 are both 4K alpha B_i1, between 3alpha and 5alpha. Baseline masses at rows 3,4 have a positive lower bound depending only on K. Consequently, uniformly over i and s,

    E_(d_i) b_i,s=E_(d_i) dot b_i,s=0,
    V_i=E_(d_i) b_i,s^2 <=C_K beta,
    U_i=E_(d_i) dot b_i,s^2 <=C_K alpha beta.            (L7)

Moreover |b_i,s|<=1/2. Indeed the relative pair-weight perturbation is at most (1/(4K))/(1/(2K))=1/2; mixing other nonnegative topic contributions only decreases the tokenwise relative perturbation. The same bound follows directly from the explicit four nonzero coordinates.

For clarity, all following likelihood arguments can be performed on ordered tokens; taking counts is a measurable map and cannot increase Hellinger or total-variation distances. Under the baseline product law d_i^N, the fair-sign mixture likelihood is

    L_i,s=(1/2)prod_(t=1)^N(1+b_i,s(Y_t))
           +(1/2)prod_(t=1)^N(1-b_i,s(Y_t)).

It is the sum over even subsets S of the products of b(Y_t) on S. Derivative terms indexed by distinct S are orthogonal, since a coordinate in the symmetric difference has mean-zero b or dot b. For |S|=q, the squared L2 norm of the derivative is at most q^2 U_i V_i^(q-1). Therefore

    E_(d_i^N) dot L_i,s^2
      <= U_i sum_(q=2)^N binom(N,q) q^2 V_i^(q-1)
      <=2 U_i N(N-1)V_i (1+V_i)^(N-2)
      <=C_K alpha N(N-1)beta^2 exp(C_K N beta).         (L8)

For the middle inequality use q^2<=2q(q-1) for q>=2 and include all subset sizes rather than only even ones.

The arithmetic-geometric mean inequality gives

    L_i,s >=prod_t sqrt(1-b_i,s(Y_t)^2)
           >=exp(-C_K N beta),                         (L9)

using max_j b_i,s(j)^2<=C_K beta and |b|<=1/2. If N beta<=1, (L8)-(L9) imply the Fisher-information bound

    I_i,N(s)=E_(d_i^N)[dot L_i,s^2/L_i,s]
       <=C_K alpha N(N-1) beta^2.                      (L10)

If N beta>1, reveal the independent latent sign. The resulting complete-data Fisher information is

    (N/2) sum_(xi=+/-1) E_(d_i)[dot b_i,s^2/(1+xi b_i,s)]
       <=2 N U_i<=C_K N alpha beta.                    (L11)

Marginalization decreases Fisher information (the observed score is a conditional expectation of the complete-data score). For

    F_N=alpha N(N-1) beta^2/[1+(N-1)beta],

the two ranges imply I_i,N(s)<=C_K F_N uniformly. In the second range (N-1)beta>1/2, so N alpha beta<=3F_N. In the first range 1+(N-1)beta<=2.

This step uses all N tokens exactly, with no pair subsampling or Gaussian approximation. It also accommodates the different baseline d_i for different documents.

## 6. Hellinger path, admissible priors, and minimax loss

Before conditioning signs on E, documents are independent although not identically distributed. For the full ordered-data law P_s, its Fisher information is the sum of document informations, at most C_K nF_N. In the convention H^2(P,Q)=integral(sqrt(p)-sqrt(q))^2, the L2 path-length bound gives

    H(P_(s0),P_(s1)) <=(Delta/2)sqrt(C_K nF_N).

Take s0=3/16 and

    Delta=min{1/16, 1/[8sqrt(C_K nF_N)]}.

Then TV(P_(s0),P_(s1))<=H<=1/16. At each endpoint, conditioning the underlying sign prior on E changes its data marginal in total variation by at most P(E^c)<=1/64. The two conditioned observation laws therefore have total variation at most 3/32, and both are supported on the admissible deterministic parameter class by Section 4.

The topic matrices within each of the two priors are fixed, separated by 4Delta in the permutation-quotient metric (L2). The triangle inequality for that metric and the two-point testing lower bound imply average expected loss at least (4Delta/4)(1-3/32). Hence the minimax risk is at least a positive K-dependent constant times min{1,(nF_N)^(-1/2)}, proving (L1).

Both endpoints have identical designated anchor indices and topic-column anchor masses (4Kalpha for the old topics, 1/2 for the others). Revealing this information does not distinguish the endpoints and leaves the lower bound intact.

## 7. Combined consequence and limits

The general-K upper bound applies to this class with mu0=1/(4K) and kappa0=1/(8sqrt(K)). Its two terms have squared sum within a factor two of

    [1+(N-1)beta]/[n alpha N(N-1) beta^2].

Thus the upper and lower bounds match in order, including the transition at (N-1)beta of constant order. For short documents the effective information is of order alpha N(N-1)beta^2 per document; for long documents it is of order alpha N beta. This conclusion is uniform in alpha,beta,N,n over the displayed domain, with constants depending on the fixed topic count.

It is not a refutation of a published theorem, an unknown-anchor support-recovery guarantee, an adaptive result for unknown alpha, a growing-dimension theorem, or a claim that the estimator/geometry/information mechanisms themselves are new. The prospective contribution is the matched joint rare-anchor, weak-mixture, and document-length law. It requires independent mathematical and prior-art review.
