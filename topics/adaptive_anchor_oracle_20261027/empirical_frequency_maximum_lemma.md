# Empirical-frequency penalties control the maximum normalized pair-moment error

27 October 2026. New analytic lemma for independent audit. This file establishes the stochastic error step only. It does not prove an adaptive topic estimator, a penalized-simplex oracle inequality, C1/C2, or historical novelty. No frozen sources are changed.

## 1. Experiment and statement

For documents i=1,...,n, let the N>=2 tokens Z_it be independent categorical variables with probability vector p_i, identical within each document but allowed to differ across documents. All tokens in different documents are independent. Write m=nN and let the finite vocabulary size p be arbitrary. Define

    d_j = n^(-1) sum_i p_ij,
    C_jr = n^(-1) sum_i p_ij p_ir,
    d_hat_j = (nN)^(-1) sum_i X_ij,
    C_hat_jr = n^(-1) sum_i X_ij(X_ir-1_(j=r))/[N(N-1)].       (1)

Here X_i is the observed count vector. Fix any deterministic core R of size r>=1. For d_j>0 define the row vector Y_j=C_jR/d_j. For d_hat_j>0 define Y_hat_j=C_hat_jR/d_hat_j. Rows with d_hat_j=0 are excluded. A row with d_j=0 has d_hat_j=0 almost surely and contributes nothing.

Use Euclidean row norm, and set

    ell(x)=log(2+1/x),              0<x<=1,
    H=6(sqrt(r)+1), A=12H,
    pen_m(x)=min{2, A[sqrt(ell(x)/(mx))+ell(x)/(mx)]}.       (2)

The constants are deliberately conservative. Neither anchor strength, anchor identities, nor sparsity q enters the penalty.

**Lemma.** There is a finite constant C_r depending only on r such that

    E max_(j:d_hat_j>0) (||Y_hat_j-Y_j||_2-pen_m(d_hat_j))_+
        <= C_r/sqrt(m).                                    (3)

The maximum of an empty set is zero. The result is uniform over all n, N>=2, finite p, and all document probability vectors p_i. In particular it needs no restriction p<=m^D.

A more explicit tail bound is available. Put c_r=1/(64H^2), B_r=2(r+1)+2, and K_r=4 B_r exp(-2)/c_r^2. For 0<t<2,

    P(max_j (||Y_hat_j-Y_j||_2-pen_m(d_hat_j))_+ > t)
        <= min{1, K_r/(m^2 t^4)}.                          (4)

Thus one may use C_r=(4/3)K_r^(1/4). These constants are not intended for practical tuning.

## 2. Exact pair concentration and deterministic boundedness

Both normalized rows are nonnegative subprobability vectors. Indeed, C_jr>=0 and sum_(r in R) C_jr<=d_j. In the sample, for each document,

    sum_(r in R) X_ij(X_ir-1_(j=r)) <= X_ij(N-1).

Consequently sum_(r in R) C_hat_jr<=d_hat_j, and both row Euclidean norms are at most one. In particular

    Z_j:=||Y_hat_j-Y_j||_2 <= 2.                            (5)

This deterministic bound is essential when an extremely rare row appears by chance.

For every u>0, the following joint deviation event has probability at least 1-2(r+1)e^(-u):

    |d_hat_j-d_j| <= sqrt(6d_j u/m)+2u/m,
    max_(r in R)|C_hat_jr-C_jr| <= sqrt(6d_j u/m)+2u/m.      (6)

Here is a direct justification without treating the within-document pairs as independent. Randomly permute each document and form floor(N/2) disjoint unordered pairs. For one pair use

    H_jr(Z,Z')=[1_(Z=j,Z'=r)+1_(Z'=j,Z=r)]/2.

It lies in [0,1], has expectation p_ij p_ir, and variance at most its expectation, hence at most p_ij. There are M=n floor(N/2)>=m/3 independent pair kernels for any fixed choice of permutations. Each document contributes the same number of pairs, so their mean has expectation C_jr and total variance at most M d_j. Ordinary bounded-variable Bernstein therefore gives the bound

    sqrt(2d_j u/M)+2u/(3M)
        <= sqrt(6d_j u/m)+2u/m.

The average over all such permutations is exactly the factorial estimator C_hat_jr, including for odd N and for j=r. Jensen's inequality transfers the centered exponential-moment bound from the disjoint-pair average to C_hat_jr. It therefore transfers the same two-sided Bernstein bound; it does not assert that all overlapping pairs are independent. The empirical frequency averages m independent Bernoulli variables with total variance at most m d_j and obeys an even tighter bound. A union bound over r pair coordinates and one frequency gives (6).

The bounded-variable inequality used here follows from

    log E exp(lambda(S-ES))
      <= lambda^2 V/[2(1-|lambda|/3)],  |lambda|<3,

for a sum of independent centered variables bounded in absolute value by one, with summed variance V. Exponential Markov and a standard optimization give the displayed conservative threshold sqrt(2Vu)+2u/3. Jensen preserves this mgf inequality for the averaged pairing estimator.

## 3. Balanced empirical frequencies

Write d=d_j and x=d_hat_j. On d/2<=x<=2d, (6) and ||Y_j||_2<=1 give

    Z_j = ||(C_hat_jR-C_jR)-Y_j(x-d)||_2/x
        <= H[sqrt(u/(md))+u/(md)].                         (7)

This uses 2(sqrt(r)+1)sqrt(6)<=H and 4(sqrt(r)+1)<=H.

Fix 0<t<2 and use

    u=3ell(d)+c_r md t^2,       c_r=1/(64H^2).              (8)

By sqrt(a+b)<=sqrt(a)+sqrt(b), the right side of (7) is at most

    H[sqrt(3ell(d)/(md))+3ell(d)/(md)]
      +H sqrt(c_r)t+H c_r t^2.                             (9)

The last two terms are at most t/8+t/(32H)<t. Also ell(x)/x is decreasing. Since x<=2d,

    ell(x)/x >= ell(2d)/(2d) >= ell(d)/(4d),               (10)

where the formula ell is extended to positive arguments in this comparison only. The last inequality uses ell(d)<=2ell(2d), valid for all d>0 because 2+1/d<=(2+1/(2d))^2. Hence the **uncapped** penalty in (2) is at least

    A[0.5 sqrt(ell(d)/(md))+0.25ell(d)/(md)],

which dominates the first bracket in (9) because A=12H. If the penalty is capped at two, the excess event is impossible by (5). Otherwise, on the event (6), Z_j<pen_m(x)+t. We conclude

    P(Z_j>pen_m(x)+t, d/2<=x<=2d)
      <=2(r+1)d^3 exp(-c_r md t^2),                        (11)

since exp(-3ell(d))=(2+1/d)^(-3)<=d^3.

## 4. False rare rows and other frequency imbalances

The proof cannot discard x>2d at probability exp(-c md) without accounting for very small d. The following active-penalty threshold supplies the missing factor d^3.

If Z_j>pen_m(x)+t, then pen_m(x)<2. The square-root part of (2) alone implies

    mx > K ell(x),       K=A^2/4>=96.                      (12)

If m<=K log 3, (12) is impossible for every 0<x<=1 and the entire excess maximum is zero. Otherwise, let s in (0,1) be the unique root ms=K ell(s). Since mx-K ell(x) is strictly increasing, (12) requires x>s.

**Underestimation x<d/2.** If this occurs with an active penalty, d>2s, and

    md>2K ell(s)>=2K ell(d).

For X=m d_hat_j, the Poisson-binomial lower Chernoff bound is

    P(X<md/2)<=exp(-md/8).

Because K>=96, md/16>=3ell(d) in this case, so

    P(Z_j>pen_m(x)+t, x<d/2)
      <=d^3 exp(-md/16).                                  (13)

If d<=2s the event is empty, and the same upper bound is still valid.

**Overestimation x>2d.** Together with (12), this implies X>m u, where u=max{2d,s}. If u>=1 the event is empty. Otherwise u in (0,1), k=mu, and z=d/u<=1/2. The Poisson-binomial upper Chernoff bound, obtained from E exp(lambda X)<=exp(md(e^lambda-1)), gives

    P(X>=k)<=exp{-k[log(1/z)-1+z]}.                        (14)

For 0<z<=1/2, let g(z)=log(1/z)-1+z. Elementary calculus gives

    g(z)>=1/4 log(1/z),       g(z)>=1/8,
    hence g(z)>=1/8 log(1/z)+1/16.                         (15)

For the first inequality, (3/4)log(1/z)-1+z decreases up to z=1/2 and is nonnegative there because log 2>=2/3. For the second, g is decreasing on (0,1) and g(1/2)=log 2-1/2>=1/6>1/8.

Since u>=s, k=mu>=K ell(u), so k/8>=3 and k/32>=3log(1/u). Applying (15) and splitting k/16 into two copies of k/32 yields

    k g(z) >= (k/8)log(u/d)+k/32+k/32
            >= 3log(u/d)+3log(1/u)+k/32
            >= 3log(1/d)+md/16.                           (16)

The last inequality uses u>=2d. This is uniform even when d is arbitrarily smaller than 1/m. Consequently

    P(Z_j>pen_m(x)+t, x>2d)
      <=d^3 exp(-md/16).                                  (17)

For t<2, both (13) and (17) are bounded by d^3 exp(-c_r md t^2), since c_r<=1/64. The imbalanced-frequency analysis uses only independent token indicators, not the pair estimator.

## 5. Maximum and expectation

Combining (11), (13), and (17), for each row d_j>0,

    P(Z_j>pen_m(d_hat_j)+t, d_hat_j>0)
       <=B_r d_j^3 exp(-c_r m d_j t^2),
    B_r=2(r+1)+2.                                        (18)

Because sum_j d_j=1,

    sum_j d_j^3 exp(-L d_j)
      <=[sup_(x>0) x^2 exp(-Lx)] sum_j d_j
      =4 exp(-2)/L^2.                                    (19)

A union bound proves (4). Integrating the minimum of one and K_r/(m^2 t^4) over t>0 gives exactly

    integral_0^infinity min{1,K_r/(m^2 t^4)} dt
        =(4/3)K_r^(1/4)/sqrt(m),                          (20)

which proves (3). Extending the integral beyond two is harmless because the actual excess is bounded by two. No high-probability event with an uncontrolled contribution to expected risk has been suppressed.

## 6. A data-selected core inside a deterministic frequent set

Let C_* be a deterministic set with cardinality at most r_* and let the data-selected core R_hat be any subset of C_* (including selection based on the same counts). Apply the lemma to the full coordinate vector C_* and use constants H,A based on r_* rather than the realized core size. Restricting a vector to R_hat cannot increase its Euclidean norm. Therefore (3) also bounds

    max_j (||Y_hat_j,R_hat-Y_j,R_hat||_2
             -pen_m,r_*(d_hat_j))_+.

No independence between core selection and count errors is needed. If R_hat subset C_* only on an event G, the same expectation bound holds on G; on G^c, (5) costs at most 2P(G^c). This is the standard deterministic-set device, stated explicitly rather than treating a random core as fixed.

The lemma controls normalized pair-moment rows. It does not by itself control a random core inverse, select a simplex, or show that a low-frequency spurious vertex cannot improve a penalized determinant objective. Those remain separate deterministic/oracle steps.
