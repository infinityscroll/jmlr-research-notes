# A concrete reduction of adaptive topic recovery to classical SPA

27 October 2026. New derivation for independent review, not a claim that this preprocessing appeared in the cited paper. No frozen source was changed.

Bound sources:

- Penalized successive projection: `../adaptive_greedy_recovery_20261027/penalized_successive_projection_theorem.md`, SHA256 `93a8dcf921f94cc594ef08f01b7620ff8427be8c686fbc90704771165b36b7a7`.
- Adaptive statistical theorem: `../adaptive_anchor_oracle_20261027/adaptive_estimator_and_constrained_frontier.md`, SHA256 `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`.
- Empirical-frequency lemma: `../adaptive_anchor_oracle_20261027/empirical_frequency_maximum_lemma.md`, SHA256 `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8`.
- Known-strength source: `../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256 `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`.

## 1. What is reduced, and what is not

An elementary row contraction, using the existing frequent core and the same empirical-frequency penalties, reduces the adaptive **statistical rate and anchor-stage operation count** to Gillis–Vavasis's classical uniform-noise SPA theorem. This gives a different estimator from the penalized-score recursion. It therefore does not prove that the latter recursion was already published, or replace its deterministic Lemma G1 on arbitrary inputs with no reliable interior center.

The consequence for significance is substantial: the adaptive topic upper bound does not require a new general vertex-hunting theorem. Classical SPA plus the preprocessing below suffices once the current topic-specific frequent-core and normalized-error bounds are supplied. The remaining possible contribution is the joint weak-anchor statistical frontier and its assumptions, not the claim that an entirely new SPA principle was necessary.

## 2. The exact published theorem used

Gillis and Vavasis, *Fast and Robust Recursive Algorithms for Separable Nonnegative Matrix Factorization*, Theorem 3, treats M'=WH+N where W has full column rank, H contains the identity and its other columns are nonnegative with sums at most one. For the squared-norm score, sufficiently small uniform column noise epsilon yields recovery of one point near each column of W, with error at most

    epsilon [1+80 K(W)^2/sigma_min(W)^2],

where K(W) is the largest column norm. The algorithm is ordinary successive orthogonal projection. [Primary manuscript, Algorithm 1 and Theorem 3](https://optimization-online.org/wp-content/uploads/2012/08/3557.pdf), printed pp.4 and12–14; later published in IEEE TPAMI36(4),698–714(2014). The retrieved PDF and text are pinned in `primary_sources/manifest.json`.

In our row convention W=V'. Let every row of V have norm at most one and sigma_min(V)>=nu. Set

    G_nu=1+80/nu^2,
    e_GV=nu/(8K G_nu).                                    (R1)

For K>=2, e_GV is strictly below the displayed sufficient noise threshold in the retrieved theorem. Its conclusion gives per-row error at most G_nu epsilon, hence Frobenius error at most sqrt(K)G_nu epsilon. In particular epsilon<=e_GV also ensures an empirical inverse guard at nu/2. These deliberately conservative constants avoid needing any sharpened modern SPA bound.

## 3. A general contraction lemma

Let S=conv(0,v_1,...,v_K), where sigma_min(V)>=nu>0. Suppose an analysis-only center c obeys B(c,r) subset S for a known positive radius r. The estimator has a center chat with error xi=||chat-c||. Let ideal rows y_j lie in S, empirical rows yhat_j and chat have norm at most one, and row penalties p_j>=0 satisfy

    ||yhat_j-y_j||<=p_j+Z, for all j.                     (R2)

Designated indices a(k) have y_(a(k))=v_k. The unknown Z is used only in the proof. Define the observable transformed rows

    a_j=r/(r+p_j),
    ytilde_j=a_j yhat_j+(1-a_j)chat.                       (R3)

**Lemma R.** There are ideal rows ystar_j in S, with ystar_(a(k))=v_k exactly, such that

    max_j ||ytilde_j-ystar_j||
       <= (1+2/r) max_k p_(a(k))+Z+xi
       <= (1+2/r) P_T+Z+xi =: e,                         (R4)

where P_T is the sum of designated anchor penalties. Thus the transformed matrix satisfies the hypotheses of the published theorem whenever e<=e_GV.

**Proof.** Write e_j=yhat_j-y_j=e_j^0+e_j^1 with ||e_j^0||<=p_j and ||e_j^1||<=Z; radial truncation supplies this decomposition. For p_j>0, the vector

    z_j=a_j y_j+(1-a_j)[c+(r/p_j)e_j^0]                   (R5)

belongs to S by the interior-ball premise and convexity. Since a_j p_j=(1-a_j)r,

    ytilde_j-z_j=a_j e_j^1+(1-a_j)(chat-c),

so its norm is at most Z+xi. For p_j=0, take z_j=y_j; the same conclusion holds. For non-designated rows set ystar_j=z_j. At a designated anchor instead set ystar_(a(k))=v_k. Directly from R3 and the unit norm bounds,

    ||ytilde_(a(k))-v_k||
       <=a_j(p_j+Z)+(1-a_j)||chat-v_k||
       <=p_j+Z+2p_j/(r+p_j)
       <=(1+2/r)p_j+Z.                                   (R6)

These ideal assignments are analysis devices only; neither S, V nor anchor identities are computed. Every ystar has nonnegative substochastic coordinates in the basis V, and the designated rows give an identity submatrix. This proves R4 and the exact match to the classical separable-NMF theorem. No extra zero vertex is requested from SPA: zero is represented by the allowed all-zero coefficient column. ∎

The empirical row errors themselves may be order one. The contraction transforms them into a uniformly small perturbation of *some* points in S. It changes the ideal coefficients of nonanchors, which is allowed because only V is to be recovered. This reassignment is the step missed by a direct max-noise comparison on the unprocessed rows.

## 4. The frequent core supplies an observable center and a fixed radius

Work on the same E_core as the bound sources, with the same selected K-row core R. Let

    V=diag(mu)^(-1) Sigma A_R',
    B_R=diag(d_R)^(-1) A_R diag(mu),
    Y_R=B_R V.                                           (R7)

The source proves sigma_min(A_R)>=sqrt(v_0/2), mu_k>=c_*, and d_j<=1. Hence, with nu=nu_0=c_*sqrt(v_0/2),

    sigma_min(V)>=nu,
    sigma_min(B_R)>=nu.                                  (R8)

Here c_* denotes the class's mixture lower bound, not an additional parameter. B_R is nonnegative and row stochastic. Each column has Euclidean norm at least nu, so its coordinate sum is at least nu. Define

    c=(1/(K+1)) sum_(j in R)Y_j,
    chat=(1/(K+1)) sum_(j in R)Yhat_j,
    r=nu^2/[2K(K+1)].                                    (R9)

Both centers have norm at most one. The barycentric vector b_c of c in the basis V has

    (b_c)_k>=nu/(K+1),   sum_k(b_c)_k=K/(K+1).            (R10)

For any perturbation u with ||u||<=r, its coefficient vector t=u V^(-1) obeys ||t||<=r/nu. Therefore

    (b_c+t)_k>=nu/(K+1)-r/nu>=0,
    sum_k(b_c+t)_k<=K/(K+1)+sqrt(K)r/nu<=1.               (R11)

We used nu<=1, which follows from the unit vertex-row bounds. Consequently B(c,r) subset S. The radius is known from the fixed class conditioning; it has no alpha, q, p, n or N dependence. The estimator computes only chat, not c or its barycentric coordinates.

The center error has the required expectation:

    E[1_(E_core) xi]<=C/sqrt(m).                          (R12)

To verify it without assuming independence of R, every possible selected row r lies in the deterministic fixed-size set D_*={j:d_j>=tau_*}, and its empirical denominator is at least 2tau_* because R subset H. On E_core,

    ||Yhat_j-Y_j||_2
       <=[||C_hat_(j,R)-C_(j,R)||_2+|d_hat_j-d_j|]/(2tau_*)

for each j in R. Sum over the whole D_* by D_* array and its frequencies. Each term has expected absolute error at most C/sqrt(m) by the source's pair-moment/frequency bounds, valid for every N>=2. The size of D_* and tau_* are fixed class constants. This proves R12. No conditioning on a selected R was used.

## 5. Explicit alternative estimator and statistical consequence

Retain the original frequent-core construction and its guards. Form every Yhat_j and the original empirical-frequency penalty p_j. Compute chat and r from R9. Transform all rows by R3. Apply ordinary squared-norm SPA for K selections to the transformed rows. Call the selected **transformed** matrix Vhat; it is not the matrix of original Yhat rows. Apply the same nu/2 inverse guard, then reconstruct

    Fhat_j=C_hat_(j,R) Vhat^(-1),

clip negatives and normalize columns, with the same bounded stochastic fallback.

The existing expected-excess lemma gives E[1_Ecore Z]<=C/sqrt(m), while the selected true anchors satisfy E P_T<=C rho(alpha), with

    rho(alpha)=min{1,sqrt(log(2+1/alpha)/(m alpha))}.

R4 and R12 imply E[1_Ecore e]<=C rho(alpha). On E_core intersect {e<=e_GV}, the published SPA theorem and the inverse perturbation argument give vertex and full-vocabulary error of the same order as in G21–G22. Markov's inequality bounds the complement by C rho(alpha), since e_GV is fixed; E_core^c costs C p exp(-c m). The final result is

    sup_(C_q(alpha)) E d_topic(Ahat,A)
       <=C min{1,sqrt(log(2+1/alpha)/(m alpha))+tau_q(m,p)}. (R13)

This is the same statistical guarantee as the penalized greedy source. It holds with no alpha or q input. Computing chat and transformed rows costs O(pK+K^2); SPA costs O(pK^2), plus the O(K^3) guard/inversion. The existing frequent-core enumeration remains. This supplies the same anchor-stage asymptotic operation count without the penalized successive-projection proof.

## 6. Precise novelty implication

R13 is a theorem-to-theorem reduction with an explicit new-to-this-note preprocessing argument. It is stronger evidence of classical overlap than merely observing that both methods use a simplex. It **does not** say an older paper states R13: the empirical-frequency maximum lemma, reliable frequent core, all-N document-pair concentration, reconstruction, and constrained-risk construction remain inputs from the current topic package. Nor does it prove literal equivalence of the selected indices or estimates from R3 and penalized score G2.

The standalone claim that the statistical rate requires a novel SPA robustness theory should be dropped. A compact topic paper could present this classical-SPA route and credit its geometric engine directly. Whether the resulting unknown-strength frontier is a substantive new statistical contribution still depends on the quantitative topic/contamination prior-art comparison and independent proof review. No priority clearance follows from this reduction or from searches not finding an exact title.
