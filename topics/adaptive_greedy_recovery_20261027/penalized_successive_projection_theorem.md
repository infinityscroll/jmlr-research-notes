# Adaptive anchor recovery by penalized successive projection

27 October 2026. New source for independent mathematical review. This replaces the vocabulary-wide anchor-tuple enumeration in the adaptive estimator. It does not replace the bounded frequent-core enumeration, establish numerical stability of a floating-point implementation, or claim historical novelty of successive projection.

Read-only dependencies:

- `../adaptive_anchor_oracle_20261027/adaptive_estimator_and_constrained_frontier.md`, SHA256 `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2` (adaptive class, penalty, empirical maximum bound, reconstruction and constrained lower theorem).
- `../adaptive_anchor_oracle_20261027/empirical_frequency_maximum_lemma.md`, SHA256 `82e5a1c0db59497f1ea9e402e07a4b6ea6694d3084b1481c8c8035ee2d977ce8` (expected normalized-row excess error, uniformly over rare rows).
- `../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256 `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4` (experiment, class, frequent core, pair moments and weak-sparsity tail).

All vector norms below are Euclidean; matrix norms are operator or Frobenius as marked. A subprobability vector is nonnegative with coordinate sum at most one. In particular its Euclidean norm is at most one. Algorithms and complexity claims in this note concern exact real arithmetic.

## 1. The changed step and resulting risk theorem

Keep the exact count moments, fixed frequent set, determinant-selected frequent core R, and its guards from the dependencies. Set Yhat_j=C_hat_(j,R)/d_hat_j when d_hat_j>0, and Yhat_j=0 otherwise. Keep the same penalty

    pen(x)=min{2,A_*[sqrt(log(2+1/x)/(mx))
                         +log(2+1/x)/(mx)]}, x>0,
    pen(0)=2.                                               (G1)

Here A_* is the fixed class-dependent constant in A2 of the adaptive dependency. In particular it is not estimated from anchor strength.

Replace only its anchor-tuple selection A3 by this procedure:

1. Start with no selected rows, and Qhat_0=I_K.
2. At t=0,...,K-1 choose an unused row j maximizing

       ||Qhat_t Yhat_j||_2^2 - 4 pen(d_hat_j),                (G2)

   using deterministic smallest-index tie-breaking. Vectors in G2 are understood as columns when a projector acts on them.
3. Append the original empirical row Yhat_j to the selected matrix. Qhat_(t+1) is the orthogonal projector onto the complement of the span of all selected empirical rows. If the newly selected row has zero residual, return the fixed stochastic-column fallback.
4. Let Vhat be the K selected original rows in selection order. Apply the same guard sigma_min(Vhat)>=nu_0/2, then the same full-vocabulary reconstruction, clipping, column normalization, and zero/nonfinite fallback as in the adaptive dependency.

The zero-residual guard is not needed to define an orthogonal projector but makes the recursive implementation unambiguous. It never fires on the small-error event proved below. No oracle labels, W, alpha or q are supplied.

**Theorem G.** On exactly the class and parameter ranges of adaptive Theorem A, this changed estimator satisfies

    sup_(C_q(alpha)) E d_topic(Ahat,A)
       <= C min{1,sqrt(log(2+1/alpha)/(m alpha))+tau_q(m,p)}.  (G3)

Constants and the starting m depend only on fixed class parameters K,q,D and the common conditioning bounds, not on alpha,n,N,p. This includes every N>=2 and sequences of vanishing alpha. Given the already formed p-by-K normalized moment rows and penalties, the anchor-selection stage uses O(p K^2+K^3) arithmetic operations and O(p K+K^2) storage. A simpler dense-projector implementation uses O(p K^3). These are anchor-stage operation counts, not runtime measurements or a claim of polynomial dependence on K for the whole estimator.

## 2. Deterministic heteroscedastic selection lemma

Let V have K subprobability rows v_1,...,v_K and sigma_min(V)>=nu, where 0<nu<=1. Let ideal rows be

    y_j=b_j V,  b_j>=0, sum_k b_jk<=1,                     (G4)

and suppose a distinct index a(k) has b_(a(k))=e_k for every k. Let all empirical rows yhat_j be subprobability vectors. Allow arbitrary nonnegative penalties p_j. Define

    Z=max_j (||yhat_j-y_j||_2-p_j)_+,
    P_T=sum_(k=1)^K p_(a(k)), epsilon=P_T+Z.                (G5)

Run G2 with p_j in place of pen(d_hat_j). Define explicit constants

    C_nu=4/nu^2+1/2,
    L_0=0,
    L_(t+1)=(1+8 C_nu/nu)L_t+6 C_nu+1,
    epsilon_0=min{nu/(2L_K),
                  nu^2/[8(6+8L_K/nu)]}.                  (G6)

**Lemma G1.** If epsilon<=epsilon_0, every selection has nonzero residual, the K selected rows match K distinct vertices, and some permutation Pi satisfies

    ||Vhat-Pi V||_F <= L_K epsilon,
    sigma_min(Vhat)>=nu/2.                                 (G7)

The lemma does not assume max_j||yhat_j-y_j|| is small. Rows with large error can have large penalties; their penalties are charged when selected. Nor does it require a gap between anchors and nearly pure nonanchors.

### 2.1 Projector perturbation and separated projected vertices

Suppose t selected empirical rows have already been matched, in order, to distinct rows indexed by I_t of V. Let A_t be these true rows, B_t the selected empirical rows, E_t=||B_t-A_t||_F, and let Q_t,Qhat_t be the corresponding complementary orthogonal projectors. Every true-row subset has minimum row singular value at least nu: extend any coefficient vector by zeros to use sigma_min(V)>=nu. If E_t<=nu/2, then B_t has full row rank and

    h_t=||Qhat_t-Q_t||_op <=4E_t/nu.                       (G8)

For completeness, let Pi_A and Pi_B be the row-span projectors. A unit vector in span(B_t) has coefficient norm at most 1/(nu-E_t), so its distance to span(A_t) is at most E_t/(nu-E_t). Interchanging the roles, the distance of a unit vector in span(A_t) to span(B_t) is at most E_t/nu. The identity

    Pi_A-Pi_B=Pi_A(I-Pi_B)-(I-Pi_A)Pi_B

therefore bounds their difference by 3E_t/nu, which implies G8. At t=0 set E_0=h_0=0.

Write x_k=Q_t v_k for unselected true vertices and x_0=0. For k,l outside I_t and k!=l,

    ||x_k||>=nu,  ||x_k-x_l||>=sqrt(2)nu.                  (G9)

Indeed the residual is the infimum over linear combinations of selected true rows. The coefficient of v_k remains one (and that of v_l remains minus one for a difference), so the full coefficient norm is at least one (respectively sqrt(2)). Multiplication by V then gives G9. Selected true vertices project to zero. Put

    M_t^2=max_(k outside I_t)||x_k||^2>=nu^2.               (G10)

Every ideal row is a convex combination of the remaining x_k and zero after projection, so ||Q_t y_j||^2<=M_t^2.

### 2.2 The score pays for the selected row's own penalty

For every j, the unit row-norm bound gives

    | ||Qhat_t yhat_j||^2-||Q_t y_j||^2 |
       <=2||yhat_j-y_j||+h_t
       <=2(p_j+Z)+h_t.                                    (G11)

The first term follows by factoring a difference of squared norms; the second projector term is the quadratic form y_j'(Qhat_t-Q_t)y_j. Let a(k_*) be an unused anchor attaining M_t. Its availability is justified in the induction below. Comparing its score with that of the selected row j_t yields

    M_t^2-||Q_t y_(j_t)||^2+2p_(j_t)
       <=6p_(a(k_*))+4Z+2h_t
       <=6P_T+4Z+2h_t=:delta_t
       <=6epsilon+8E_t/nu.                               (G12)

Both the first term on the left and the selected penalty are nonnegative. In particular each is controlled separately. This is the reason for the coefficient four in the score.

### 2.3 Linear, rather than square-root, vertex proximity

For the selected row b=b_(j_t), put w_k=b_k on remaining vertices and

    w_0=1-sum_(k outside I_t)b_k.

This combines the mass on previously selected vertices and the missing substochastic mass into the zero atom. The weights are nonnegative and sum to one. The exact variance identity is

    M_t^2-||sum_i w_i x_i||^2
       =sum_i w_i(M_t^2-||x_i||^2)
          +sum_(i<j) w_i w_j ||x_i-x_j||^2.                (G13)

The first sum is nonnegative and includes w_0 M_t^2. All distinct atom distances are at least nu by G9. Since the left side is at most delta_t, it follows that

    w_0<=delta_t/nu^2,
    1-max_i w_i <=1-sum_i w_i^2<=2delta_t/nu^2.            (G14)

When delta_t<=nu^2/8, the maximum weight is at least 3/4 whereas w_0<=1/8. Thus some NEW vertex k_t satisfies

    b_(k_t)>=1-2delta_t/nu^2,
    ||y_(j_t)-v_(k_t)||<=2(1-b_(k_t))<=4delta_t/nu^2.      (G15)

The unprojected bound uses the norm bound on every v_k and sum b_k<=1. It does not attempt to recover a vector by taking a square root of a norm deficit. Also G12 gives p_(j_t)<=delta_t/2. Consequently

    ||yhat_(j_t)-v_(k_t)||
       <=C_nu delta_t+Z.                                  (G16)

### 2.4 Closing the induction, including excluded anchor indices

At t=0 no anchor index is excluded. If a selected row j_t equals one of the designated anchor indices a(l), then its barycentric vector is exactly e_l. G15 therefore forces k_t=l. Thus selecting an anchor representative never removes the representative of a different, still-unmatched vertex. This proves the availability premise in G12 at each step. The same conclusion holds if there are other duplicate anchor rows; only one representative per vertex is needed.

Stacking the new matched row and using the triangle inequality gives

    E_(t+1)<=E_t+C_nu(6epsilon+8E_t/nu)+Z
            <=(1+8C_nu/nu)E_t+(6C_nu+1)epsilon.            (G17)

Inductively E_t<=L_t epsilon. The chosen epsilon_0 simultaneously ensures E_t<=nu/2 and delta_t<=nu^2/8 for all t<K. Hence G8 and G15 remain applicable, without assuming the conclusion of a later step. After the new matching is established, E_(t+1)<=nu/2 implies sigma_min(B_(t+1))>=nu/2. In particular the newly selected empirical row cannot lie in the previous empirical span, and the zero-residual guard cannot fire. After K steps this proves G7. All constants depend only on K,nu.

## 3. Statistical transfer without an anchor-strength input

On the unchanged good-core event E_core, R lies inside the deterministic set D_*={j:d_j>=tau_*}, whose size is at most r_*. The population vertex matrix V_R has sigma_min(V_R)>=nu_0, subprobability rows, and

    Y_j=B_j V_R for d_j>0;
    Y_j=B_j=0 for d_j=0.                                  (G18)

Take one true anchor per topic of mass at least alpha. The empirical-frequency lemma, applied on the entire deterministic coordinate set D_* before restriction to the selected R, gives exactly the bound A6 of the adaptive dependency:

    E[1_(E_core) Z]<=C/sqrt(m).                            (G19)

There is no conditional-independence claim about R. Both count-normalized empirical and population rows are subprobability vectors. A zero observed frequency uses pen(0)=2, so cannot add positive excess error to Z. The unchanged anchor-penalty calculation A7 gives

    E P_T<=C min{1,sqrt(log(2+1/alpha)/(m alpha))}
             =C rho(alpha).                              (G20)

On E_core intersect {P_T+Z<=epsilon_0}, Lemma G1 with nu=nu_0 proves stable empirical recovery of all vertices. The original reconstruction identity and its inverse perturbation argument therefore give

    ||Fhat-F Pi'||_1
       <=C sum_j sum_(r in D_*)|C_hat_jr-C_jr|
           +C(P_T+Z),   F=A diag(mu).                     (G21)

This uses a fixed, alpha-independent inverse bound; sum_(j,r in R)C_jr<=1 prevents a vocabulary factor in the vertex-error term. The permutation is common across all rows. Clipping and column normalization have the same bounded-loss guards as before and use mu_k>=c.

Within E_core, Markov's inequality bounds failure of P_T+Z<=epsilon_0 by C E[1_(E_core)(P_T+Z)]. Outside E_core, its probability bound costs C p exp(-c_*m). Every fallback has stochastic columns and hence loss at most 2K. The same pair-moment expected L1 bound used in A9–A10 then yields

    E d_topic(Ahat,A)
       <=C[rho(alpha)+sum_j min{h_j,sqrt(h_j/m)}
                          +p exp(-c_*m)].                 (G22)

The weak-q sum and polynomial-vocabulary absorption are unchanged, proving G3. Thus all N>=2, shrinking-alpha and critical q=1/2 qualifications of Theorem A are retained. The fixed-vocabulary constrained lower Theorem B applies to this estimator because it is one alpha-independent estimator satisfying the same strong-class bound. This note proves no new lower bound.

## 4. Operation counts and limits

Given the formed p-by-K Yhat and p penalties, maintain all residual rows r_j=Qhat_t yhat_j. At a selection with nonzero residual, form its unit direction u and replace each residual by r_j-(r_j dot u)u. By orthogonality, this is exactly projection onto the complement of the enlarged selected span. One iteration costs O(pK), plus an O(p) score scan; K iterations cost O(pK^2). The final singular-value guard and inverse cost O(K^3). Storing the rows, residuals and an orthogonal basis costs O(pK+K^2). Zero residuals trigger the stated fallback. This is an exact-arithmetic implementation argument; uncontrolled floating-point rank decisions are not a theorem.

A dense projector recomputation and application gives the looser O(pK^3) bound. Either removes the vocabulary-wide enumeration of K-tuples. The frequent-core search still enumerates K-subsets of H. Because each member of H has empirical frequency at least 2tau_* and total empirical frequency is one, |H|<=1/(2tau_*), a bound independent of p but potentially extremely large in K and conditioning constants. Moment formation also has its own cost. Therefore G3 supplies an anchor-selection improvement, not an end-to-end practical efficiency result or a polynomial-in-K claim.

## 5. Primary antecedent and scope of the contribution

Successive projection itself is classical. Gillis and Vavasis, *Fast and Robust Recursive Algorithms for Separable Nonnegative Matrix Factorization*, Algorithm 1, repeatedly selects a residual column by a strongly convex score and projects it away; squared Euclidean norm is treated in Section 4.1. Their Theorem 3 proves robustness under a uniformly small maximum column perturbation. These are direct antecedents for the geometry and recursion here. [Primary manuscript](https://optimization-online.org/wp-content/uploads/2012/08/3557.pdf), pp.4–5,12–14,19.

The present proof uses a row-dependent empirical-frequency penalty and bounds the oracle quantity P_T+max_j(error_j-p_j)_+, rather than requiring the maximum raw row error to be small. This is the seam needed to retain the adaptive shrinking-anchor rate while scanning all vocabulary rows. The penalty also bounds the selected row's own error, and the zero-atom variance identity supplies linear vertex error. This comparison does not establish that penalized or heteroscedastic variants are historically new; the broader novelty assessment remains the separate adaptive-frontier comparison. The concrete result here is removal of the p-choose-K anchor search with the stated statistical guarantee and remaining frequent-core limitation.
