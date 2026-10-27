# Selected-path margin failure from coupled original queries

28 October 2026. New analytic candidate for hostile review. This is a two-layer, unmasked identity-value **self-attention** model: upper queries, keys and values all evolve with the lower layer. Both unrestricted direct matrices train simultaneously under the released unnormalized p=2 mirror update. The conclusion concerns the actual lower selected-query token SVM, not an all-query surrogate. The proof uses a finite late-entry open basin; it does not certify the separate 50,000-step diagnostic initialization or arbitrary small/random starts.

## 1. Fixed problem, open basin and result

Fix the two input tokens and head

    x1=(1,0)',  x2=(1/2,1)',  d=x1−x2=(1/2,−1)',
    D=1/2,     c_d=||d||²=5/4,    w=e1.

Use the positive example with these token rows and label +1, together with its negative copy with label −1, equal loss weights. For each example,

    H1=softmax_rows(H0 W1 H0') H0,
    H2=softmax_rows(H1 W2 H1') H1,
    prediction=w' H2[1,:]'.                                  (S1)

The loss is the mean logistic loss of the two signed predictions. Their signed predictions and gradients agree exactly. Every coordinate of both 2-by-2 real matrices is trainable. For any fixed eta>0 the simultaneous update is

    W_l(t+1)=W_l(t)−eta grad_(W_l) L(t),  l=1,2.             (S2)

This is precisely p=2 of the authors' power-mirror optimizer with normalize=False. There are no residuals, masks, detached/frozen memories, added value projections, trainable head, or parameter-coordinate restrictions.

Define relevant initial coordinates, and thereafter their current values, by

    l_r=x_r' W1 d,     a=sigmoid(l1), b=sigmoid(l2),
    k=W2 d=(z,k2)',    x=z−l1,     v=z b,
    x*=1/2+log(5/4),   v*=1/2,
    e=(x−x*,v−v*)',
    P=[[41/70,26/35],[26/35,48/25]],  r=1/1000.             (S3)

**Theorem.** There is a finite R0=R0(eta) such that every finite initialization satisfying

    z(0)>R0,    |k2(0)|<1,    e(0)'P e(0)<r²              (S4)

has the following limits under the exact discrete updates S2:

    H1[1,:]' -> x1,     H1[2,:]' -> x2,
    W1(t)/log t -> Theta_bad=(1,−1/2)'d'/c_d,
    W2(t)/log t -> Theta_top=x1 d'/c_d.                    (S5)

The memories stay distinct in the limit, at distance sqrt(5)/2. The upper designated query selects key1 and that selected lower query selects original key1. The actual lower selected-path global p=2 token-SVM is

    minimize ||W||_F²/2 subject to x1' W d>=1,
    Theta_path=x1 d'/c_d.                                 (S6)

Its optimal unit-norm margin is sqrt(5)/2. The trained lower normalized margin tends to 1, so the fraction of the actual global optimum tends to

    2/sqrt(5)<1.                                          (S7)

The normalized p=2 Bregman discrepancy tends to `1−2/sqrt(5)>0`. The upper actual checkpoint token-SVM margin fraction tends to one and its optimal unit-norm margin tends to sqrt(5)/2>0. Thus S7 is a selected-path failure with a nonvanishing comparator scale, not token consensus, factorization mismatch or unused-query starvation.

The set S4 is nonempty and open in all eight initial matrix coordinates. For example, choose any z>R0, set `k2=0`, `l1=z−x*` and `l2=log[(1/(2z))/(1−1/(2z))]`, and take minimum-norm matrices giving those projections. Arbitrary sufficiently small perturbations preserve S4. Components orthogonal to d on the right can be arbitrary finite values. The proof supplies a finite existence threshold R0; it does not give a numerically certified threshold or claim that z=4 meets it.

## 2. Exact full-matrix gradient reduction

The first-layer memory columns are

    h1=x2+a d,       h2=x2+b d.

Write

    m=(a−b)h1'k,     pi=sigmoid(m),
    f=D+(D)[b+pi(a−b)],      Q=(1+exp(f))^(-1).            (S8)

Here f is the common signed prediction and lies between 1/2 and 1. More generally the constant term in f is the first coordinate of x2, which equals D for this fixture. Let c=b+pi(a−b). Differentiating both the upper query and key/value dependencies gives

    c_a=pi+pi(1−pi)[m+(a−b)^2 d'k],
    c_b=(1−pi)(1−pi m),
    A=a(1−a)c_a,       B=b(1−b)c_b,
    grad_(W1) f=D(A x1+B x2)d',
    grad_(W2) f=D(a−b)^2 pi(1−pi)h1 d'.                   (S9)

No downstream derivative has been dropped. In particular B is negative at sufficiently large m; its upper-key derivative opposes the direct value gradient. The native query Gram matrix couples that negative contribution back into the selected-query parameters.

With `rho=eta Q D c_d`, S2 and S9 give the exact simultaneous recurrences

    Delta l1=rho(A+B/2),
    Delta l2=rho(A/2+5B/4),
    Delta k=rho(a−b)^2 pi(1−pi)h1.                       (S10)

They also imply the exact identities

    Delta(l1−2l2/5)=4rho A/5,
    Delta(l2−l1/2)=rho B.                                (S11)

S11 does not assert that either l1 or l2 is individually monotone. Their coupling is the central difference from the previously proved one-hot, independent-row model.

Since every matrix increment in S9 has right factor d', each matrix has the exact decomposition

    W_l(t)=[W_l(t)d]d'/c_d+G_l,
    G_l d=0,     G_l constant in t.                      (S12)

All G_l entries are still trainable parameters. The architecture's exact gradient is zero in these comparison-irrelevant directions. The full comparator has the same irrelevant directions and minimizes them to zero, so S12 introduces no restricted-space comparator mismatch.

## 3. An exact discrete slow-clock expansion

Work temporarily in the closed region

    z>=R,    |k2|<=2,    e'P e<=r².                       (S13)

All O constants below are uniform in this region for sufficiently large R; eta is fixed. The eigenvalues of P lie between 1/5 and 3, so S13 confines x and v to fixed compact intervals with v bounded strictly above zero. From the definitions,

    1−a=e^(−z+x)[1+O(e^(−z))],   b=v/z,
    h1=(1−D(1−a),1−a)',
    m=z−v+O(z e^(−z)).                                   (S14)

The errors are uniform, including either sign of k2. Consequently

    A=e^(−z+x)[1+O(z e^(−z))],
    B=−v e^(−z+v)[1+O(1/z)],
    Delta z=rho e^(−z+v)[1+O(1/z)],
    Delta k2/Delta z=(1−a)/[1−D(1−a)].                   (S15)

In particular `c_eta e^(−z)<=Delta z<=C_eta e^(−z)`, and `|Delta l1|+|Delta l2|<=C Delta z`. There is no continuous-time replacement in these identities or estimates.

For completeness the rescaling of the second coordinate must include its discrete product term. Since `v=z sigmoid(l2)`,

    Delta v=b Delta z+z b(1−b)Delta l2
                   +O(z b(Delta l2)^2+b|Delta z Delta l2|).

The logistic second derivative on the intervening interval is at most Cb because `Delta l2=O(Delta z)` and Delta z is small. Dividing by Delta z, using S10 and S15, gives

    (Delta x,Delta v)'=Delta z [F(x,v)+epsilon_t],
    F1=1−exp(x−v)+v/2,
    F2=v[exp(x−v)/2−5v/4],
    ||epsilon_t||<=C(1/z+Delta z).                       (S16)

For example `A/[Delta z/rho]=exp(x−v)+O(1/z)` and `B/[Delta z/rho]=−v+O(1/z)`. The omitted `b Delta z` term in a formal differential argument contributes O(1/z), and is explicitly retained here. By increasing R, the last bound in S16 is at most C'/z.

## 4. A finite open invariant basin

F vanishes at `(x*,v*)`. Its Jacobian there is exactly

    J=[[-5/4,7/4],[5/16,−15/16]],
    J'P+PJ=−I.                                          (S17)

The displayed rational P is positive definite: `P−I/5` is positive definite and `trace(P)<3`. On the Euclidean ball `||e||<=1/100`, direct differentiation of the two components of F bounds the Taylor remainder by

    ||F((x*,v*)+e)−Je||<=10||e||².

Indeed `exp(x−v)<=5/2` and `1/4<=v<=3/4` on this ball; the entries of the two Hessians give this conservative bound. Since S13 implies `||e||<=sqrt(5)/1000`, S17 gives

    2e'P F((x*,v*)+e)<=−||e||²/2.                       (S18)

Let V=e'Pe and h=Delta z. Exact expansion of this quadratic along S16 yields

    V^+−V=2h e'P(F+epsilon)+h²(F+epsilon)'P(F+epsilon).

Uniform compact bounds and S18 show, for sufficiently large R,

    V^+−V<=−c h||e||²+C h||e||/z+C h²/z².              (S19)

The h²||e||² term has been absorbed because h<=C_eta e^(−z). This estimate proves forward invariance without pretending that a continuous-time inward vector field is enough. On the annulus `r²/4<=V<=r²`, choose R so large that the positive terms in S19 are smaller than its negative term; then V decreases. Inside `V<r²/4`, the uniform bound `||Delta e||<=C h` and sufficiently small h make `sqrt(V^+)<=sqrt(V)+||Delta e||_P<r`. Thus no step leaves the ellipsoid, including an attempted finite overshoot from its interior.

The other stopped boundary closes independently. From the last identity in S15,

    0<=Delta k2<=C e^(−z) Delta z.

Choose R so that Delta z<=1. For positive h<=1, `e^(−z)h<=e integral_z^(z+h) e^(−u)du`. Hence along any prefix in S13,

    sum Delta k2<=C e^(−z(0))<1                         (S20)

after increasing R. With `|k2(0)|<1`, this prevents escape from `|k2|<=2`. It does not assert that the smaller interval |k2|<1 remains invariant. Finally z increases, so it cannot cross its lower boundary.

These estimates use only fixed compact constants, eta, and inequalities achieved by increasing a finite R. Choosing one such R0 proves that every initialization S4 stays in S13 forever. The strict inequalities defining S4 and the surjective linear map from the full matrices to `(l1,l2,k1,k2)` establish openness in all eight parameter coordinates. No asymptotic statement was assumed in closing the basin.

## 5. Convergence and logarithmic scales

Within the invariant region, if z were bounded the lower bound `Delta z>=c_eta e^(−z)` would force it to diverge. Thus z tends to infinity. In particular h tends to zero and `sum h=infinity`. By Young's inequality, S19 gives constants c,C>0 with

    V^+<=(1−c h)V+C h/z²                                (S21)

on a sufficiently late tail. The standard scalar contraction iteration, with vanishing forcing 1/z² and infinite total clock, proves V->0. Explicitly, once C/z²<=c epsilon, every value above epsilon contracts towards epsilon; unrolling the recursion kills the finite-prefix term since `product(1−c h)=0`. Let epsilon decrease to zero. Therefore x->x* and v->1/2. Equation S20 also gives a finite limit for k2.

The upper signed prediction tends to one. Put

    rho*=eta D c_d/(1+exp(1))=5eta/[8(1+exp(1))].

By S15 and convergence of v,

    e^z Delta z -> rho* exp(1/2).

Since Delta z->0, the exact mean-value expansion of `exp(z^+)−exp(z)` and Cesaro averaging imply

    e^(z(t))/t -> rho* exp(1/2),
    z(t)=log t+log(rho*)+1/2+o(1),
    l1(t)=log t+log(4rho*/5)+o(1),
    l2(t)=−log log t−log 2+o(1).                         (S22)

The last line follows directly from `b=v/z` and `l2=log[b/(1−b)]`; it is not inferred from a guessed gradient flow. Thus a->1 and b->0. Solving the two linear logit equations gives

    W1d=(l1,l2−l1/2)',    W2d=(z,k2)'.

Together with S12 and S22, this proves every assertion in S5.

The lower unselected path has a small probability but a leading cumulative gradient. In S15, `B/[Delta z/rho]->−1/2`, while `A/[Delta z/rho]->5/4`. Their combination cancels the leading l2 update but not the full W1 update. This is why pointwise vanishing upper attention does not justify discarding the cross-path effect.

## 6. Comparator and metric are parameterization matched

For the positive example, the lower query selected by the upper attention is h1, which originates from input query x1. Its relevant original-token margin is exactly `x1'W1(x1−x2)=l1`. The negative example gives the identical matrix normal because both tokens and query change sign. Hence S6 is the authors' selected-index attention-SVM applied to the actual lower selected path, with one distinct normal `C=x1d'`.

Cauchy–Schwarz gives the unique global solution `C/||C||_F²=x1d'/c_d`. The limiting trained direction is `Theta_bad/||Theta_bad||_F`. Here `||Theta_bad||_F=1`, `<C,Theta_bad>=1`, and `||C||_F=sqrt(5)/2`. This proves the fraction 2/sqrt(5). For unit matrices, the p=2 Bregman discrepancy is one minus their inner product; both argument orders therefore give the stated strictly positive discrepancy.

At the upper checkpoint the normal is `C_top(t)=h1(t)(h1(t)−h2(t))'`. It tends to C, and S5 gives the same limiting trained upper direction as C. Both its normalized margin fraction and its normalized Bregman discrepancy therefore converge to their optimal values. Its optimal margin has a positive limit, so no vanishing-feature normalization is used.

All logits eventually select key1 at the two comparisons on the prediction path; the other lower query selects key2. The fixed-head loss approaches its bounded-score infimum `log(1+exp(−1))`, not zero. The result concerns token routing and matrix direction, not generalization or classification failure.

## 7. Exact source mapping and limits

[Julistiono, Ataee Tarzanagh and Azizan, *Optimizing Attention with Mirror Descent*, Definition 5 and Theorem 10](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf) study the one-layer direct-matrix token-SVM and power-mirror update. Their released `synthetic-data/tools/att_svm.py` constrains `(x_selected−x_other)'W z>=1`; our row-query convention transposes W, preserving its Frobenius norm, p=2 update and normalized Bregman distance. The held released optimizer SHA256 is `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`.

This is a counterexample to the natural **layerwise selected-path** extension, not to the published one-layer theorem. The data are a fixed two-token paired-sign design; values and head are fixed; p=2 is the Euclidean member of the paper's mirror family. The open basin is at large but finite favorable initialization, with an existence threshold rather than a practical initialization prescription. No generic input-neighborhood, trainable-value/head, non-Euclidean, or arbitrary-initialization claim is included.

The proof is not the old all-query starvation statement: the lower selected-path comparator itself fails. It is not the old token-consensus example: both limiting memories and both relevant optimal margins stay separated. It is not the fixed-memory cross-attention example: the query, keys and values entering layer2 are exactly H1. Nevertheless nonlinear gradient competition and timescale separation are known broad mechanisms. No historical novelty or newsworthiness is asserted by this mathematical source; independent analytic review and primary comparison remain required.
