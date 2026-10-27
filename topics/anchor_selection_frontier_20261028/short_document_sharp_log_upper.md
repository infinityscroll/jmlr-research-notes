# A sharper anchor-search bound in the short-document regime

28 October 2026. New upper proof by root for independent audit. The estimator
is unchanged. The refinement uses document-level concentration where the
bounded-increment remainder is affordable, rather than the earlier nested
moment bound. This is not a novelty claim or a lower bound.

## 1. Model, observable estimator and result

Use independent X_i ~ Multinomial(N,A w_i), unknown deterministic stochastic
W, fixed K>=2, mean prevalence at least mu0, sigma_min(A)>=kappa0, and one
exact anchor per topic with corpus probability at least alpha. Put

    Sigma=WW'/n, b=lambda_min(Sigma)>=beta>0, d=A(W1/n),
    a(t)=1/sqrt(nN t)+1/[t sqrt(nN(N-1))],
    R_alpha(d)=sum_j min(1,d_j/alpha),
    L=log(2+R_alpha(d)), H_a(d)=sum_j min(d_j,a sqrt(d_j)).   (S1)

All constants below depend only on fixed K,mu0,kappa0. Vocabulary size p,
alpha,beta,n,N are not hidden in constants. Loss is expected entrywise L1
error modulo topic permutation, with stochastic output columns and thus
pointwise loss at most 2K.

Use exactly the known-alpha spectral/max-volume estimator followed by the
observed-eigenvalue output threshold in
`../weak_sparsity_frontier_gate_20261028/observable_conditioning_threshold.md`,
SHA256 `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8`.
It uses K and alpha, not beta, b, q or anchor locations. On nonpositive Kth
pair-moment eigenvalue it returns fixed stochastic columns. Otherwise the
output cutoff is a(lambda_K(Chat))^2, after anchor selection/reconstruction.

**Theorem.** For every N>=2 the same observable estimator obeys

    E loss <= C min{1,
          H_{a(beta)}(d) + sqrt(L) a(beta)/sqrt(alpha)
                         + L/(n beta alpha)}.              (S2)

In particular, if

    N(N-1) beta <= 1,                                      (S3)

then

    E loss <= C min{1,
          H_{a(beta)}(d) + sqrt(L) a(beta)/sqrt(alpha)}.     (S4)

For N=2 and beta<=1/2 this always applies. All lower-bound classes in the
previous joint frontier have a smaller beta floor. The class condition S3
is on its specified floor beta; no promise that the actual b satisfies S3 is
needed. Weak-q consequences replace H by the same three profiles in the
previous frontier. The only change here is the anchor logarithm. Neither
R_alpha(d) nor L is an estimator input; they describe its risk at the true
distribution. Since K<=R_alpha(d)<=min(p,1/alpha), L is always finite and
bounded below by a positive constant.

The previous all-N bound with log(2+1/alpha) remains valid for this same
estimator. One can take the smaller of the two upper bounds. S4 is not
asserted for unrestricted N under the present argument.

## 2. A different bound for the degenerate document term

Retain the exact pair decomposition of
`../multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md`,
SHA256 `de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`.
For independent one-hot tokens Z_it with mean pi_i=A w_i, write T_it=Z_it-pi_i
and

    Q_i = [N(N-1)]^{-1} sum_{s!=t} T_is T_it',
    Qbar = (1/n) sum_i Q_i.

The jth row is a vector in the vocabulary Hilbert space. It is centered,
and the exact degenerate-pair variance identity gives

    E ||Q_i,j||_2^2 <= 2 pi_ij/[N(N-1)].                    (S5)

Each |T_is,j|<=1 and ||T_it||_2<=sqrt(2), so the triangle inequality for the
ordered-pair average gives the deterministic bound

    ||Q_i,j||_2 <= sqrt(2).                               (S6)

Apply the dimension-free Hilbert Bernstein moment inequality U2 of the
dependency DIRECTLY to the n independent centered row vectors Q_i,j/n.
The variance sum is at most 2d_j/[nN(N-1)], and their norm bound is sqrt(2)/n.
For every r>=2,

    ||Qbar_j||_{Lr}
       <= C [sqrt(r d_j/[nN(N-1)]) + r/n].                (S7)

This does not assert independence of pairs within a document. S5 retains
their exact covariance; only whole documents are treated as independent.
The price is the r/n remainder. It must not be replaced by r/(nN) here.

## 3. Sharper maximum over possible anchor rows

Analyze at the actual b. On all outcomes define the existing row-error
envelope

    delta_j=C[||E_j||_2/sqrt(b)+||Qbar_j||_2/b],

where E is the whitened first-order noise matrix from the dependency.
Its U6 first-order moment and scalar-frequency U7, combined with S7, imply

    ||delta_j+|dhat_j-d_j|||_{Lr}
       <= C [sqrt(r) a(b) sqrt(d_j) + r/(n b)].           (S8)

Indeed the first-order bounded-increment term is r/(nN b), which is no
larger than the retained r/(n b); b<=1 follows from trace(Sigma)<=1.
The existing second moments remain

    E delta_j^2 <= C d_j a(b)^2.                          (S9)

Let J_*={j:d_j>=alpha/4}; then |J_*|<=4R_alpha(d). Define

    rho=max_{j in J_*} [delta_j+|dhat_j-d_j|]/d_j.

Choose r=max(2,log(4R_alpha(d))). The finite-set Lr maximum bound has factor at
most e, and d_j>=alpha/4. Thus

    E rho <= C [sqrt(L) a(b)/sqrt(alpha)
                                  + L/(n b alpha)].     (S10)

There is no maximum over arbitrary zero/rare rows in this argument. Their
false inclusion is dealt with next.

## 4. False inclusion without a vocabulary factor

Let F mean some d_j<alpha/4 nevertheless has dhat_j>=alpha/2. The unchanged
Bernoulli generating-function argument W9 of
`../weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_upper.md`,
SHA256 `fb24214c2aab2d510f1182cc3000489a0d117f1fe5f3e7aa4d9ee3db81a83ab9`,
gives, for x=nN alpha>=2 and the individual token count X_j=nN dhat_j,

    P(X_j>=ceil(x/2)) <= 2nN d_j exp(-c x),  d_j<alpha/4,
    c=(log 2)/2-1/4>0.                                  (S11)

For those rare rows, sum d_j<=alpha R_alpha(d). Therefore summing S11
gives P(F)<=min(1,2x R_alpha(d) exp(-c x)). This uses their total mass,
not a vocabulary union factor.

Its consequence can be sharpened to

    P(F) <= C sqrt(L/(nN alpha)).                        (S12)

Here is the complete case split. Fix C0>=max(2,4/c). If x<=C0 L, the
right-hand scale sqrt(L/x) is at least 1/sqrt(C0), so bounded probability
suffices, including x<2. If x>C0 L, use R_alpha(d)<=exp(L)<=exp(c x/2)
in S11 to get P(F)<=2x exp(-c x/2). This is at most C/sqrt(x), hence at
most C sqrt(L/x), since L>=log(3)>1. This proves S12 for arbitrary p.
Its right side is at most C sqrt(L) a(b)/sqrt(alpha).

## 5. Reconstruction, the random cutoff and the class-floor bound

The previous spectral event G0, defined using actual b, satisfies
P(G0^c)<=C a(b). On it the same analysis-coordinate row representation is
X+D, X=A diag(mu), with ||D_j||<=delta_j. On

    G=G0 intersect F^c intersect {rho<=rho0},

the exact maximum-volume lemma gives, for one common permutation Pi,

    ||Xhat_j-X_j Pi||_1 <= C(delta_j+d_j rho).            (S13)

Every true anchor is retained, and every retained candidate lies in J_*.
The constant rho0 depends only on K and the fixed geometry floors.

On G0, the observed Kth pair-moment eigenvalue lies between c0 b and C0 b
for positive fixed constants. Consequently the observed cutoff is between
fixed multiples of a(b)^2. Equations O5--O7 of the observable-threshold
dependency apply without alteration: retained row-error and omitted signal
mass have total expectation at most C H_{a(b)}(d). Their proof uses pointwise
indicator comparison on G and unconditional second moments S9, not an
independence assumption for the data-dependent cutoff.

Clipping and column normalization multiply the raw error bound by at most a
constant depending on mu0; zero columns use the same bounded fallback.
On G^c use loss<=2K, S10, S12 and Markov's inequality for rho. This gives

    E loss <= C min{1,
         H_{a(b)}(d)+sqrt(L) a(b)/sqrt(alpha)+L/(n b alpha)}.

Monotonicity b>=beta bounds each term by its beta version and proves S2.
This order of argument matters: the cutoff tracks actual b, whereas the
class condition S3 need only hold at the floor beta.

Finally set r0=sqrt(L) a(beta)/sqrt(alpha). Under S3,

    L/(n beta alpha)
       <= L/[n N(N-1) beta^2 alpha] <= r0^2.             (S14)

If r0<=1 this remainder is at most r0; otherwise bounded loss proves S4.
No n-, alpha- or N-dependent remainder has been discarded.

## 6. Fixed weak-sparsity radius and vocabulary dependence

If the corpus probabilities have counting envelope
`#{j:d_j>=t}<=S t^(-q)` for fixed q in (0,1), then

    R_alpha(d) = alpha^{-1} integral_0^alpha #{j:d_j>=t} dt
               <= S alpha^{-q}/(1-q).                    (S15)

Also R_alpha(d)<=p. Thus for fixed S,q, S4 implies

    E loss <= C_{K,q,S} min{1,
          F_{q,p}(a(beta))
          + a(beta)/sqrt(alpha)
                 * sqrt(log(2+min(p,alpha^{-q})))}.      (S16)

Here F is a for q<1/2, a log(2+min(p,1/a)) for q=1/2, and
min(a^{2(1-q)}, a p^{1-1/(2q)}) for q>1/2, with the existing bounded-loss
convention. For columnwise weak-q radius S_A the corpus bound holds with
S=K S_A, as already proved in the sparse-upper dependency. Constants are
not asserted uniform as q tends to 0 or 1. The logarithm in S16 tracks the
number of possible sufficiently massive anchor locations; using only p or
only 1/alpha would lose this refinement.

## 7. Scope and next decisive question

This is a sharper analysis of the already specified estimator, uniform in
shrinking beta in the two-word regime and in S3. Concentration itself is
classical. A matching unknown-anchor lower bound is needed to decide whether
sqrt(L) is a statistical price or still a proof loss. The earlier fixed-beta
anchor-search lower constructions are relevant antecedents and must be
distinguished from a uniform weak-beta lower bound. No general all-N sharp
anchor logarithm or new publication-priority conclusion is asserted here.
