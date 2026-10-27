# A noncentral limit for the original cheap bootstrap near the lower gain-exponent boundary

28 October2026. New analytic candidate for hostile review. This concerns the fixed moderate-curvature objective and the ORIGINAL offline Algorithm1. It does not turn the retained million-step experiment into a deterministic finite-sample coverage theorem. A primary-theorem novelty comparison remains separate.

## 1. Fixed model, varying tuning exponent, and conclusion

Keep the objective and data law fixed:

    g(x)=x+(1/4)log cosh(2x),
    Z_i iid uniform on {-4,+4}, X_0=0, eta=47/50.

For the run of length n use one exponent alpha_n throughout that run:

    gamma_(n,t)=eta*t^(-alpha_n),
    X_(n,t)=X_(n,t-1)-gamma_(n,t)[g(X_(n,t-1))-Z_t],
    F_n=(1/n)sum_(t=1)^n X_(n,t).                       (T1)

Assume 1/2<alpha_n<=3/5 eventually. For each of a fixed B>=1 reruns, draw n observations independently with replacement from the original n observations, restart at zero, use the same gains and post-update averaging, and obtain F_n^{*b}. Define exactly as in the source Algorithm1

    R_n^2=(1/B)sum_b(F_n^{*b}-F_n)^2,
    I_n=[F_n-qR_n,F_n+qR_n], q=t_(B,1-gamma/2).          (T2)

The fixed model has strong convexity1/2, smoothness3/2, Hessian-Lipschitz constant1, bounded noise magnitude4 and fourth moment256. Its population root is zero. The original source Assumptions1–5 hold for each exponent in (1/2,3/5]; the exact mapping is in `../moderate_curvature_gate_20261028/moderate_curvature_bias_proposition.md`, SHA256 `863d6b4751e273442d32e65aa720ee90f79d0737f390b67d880dd030152af9b3`.

**Theorem.** If

    (alpha_n-1/2)log n -> c in [0,infinity),
    kappa_c=(47/25)exp(-c),                             (T3)

then, for independent standard normal U,V_1,...,V_B,

    (sqrt(n)F_n/4,
       sqrt(n)(F_n^{*1}-F_n)/4,...,
       sqrt(n)(F_n^{*B}-F_n)/4)
          => (U-kappa_c,V_1,...,V_B).                  (T4)

Conditional on the complete original dataset, the B-vector of centered reruns in T4 converges in bounded-Lipschitz distance, in probability, to N(0,I_B). The original first coordinate is not part of that conditional claim.

Consequently the original Student pivot has the noncentral limit

    F_n/R_n => (U-kappa_c)/sqrt((1/B)sum_b V_b^2),      (T5)

and its coverage converges to

    C_B(q,kappa_c)
      =P{|U-kappa_c|<=q sqrt((1/B)sum_b V_b^2)}
      <1-gamma.                                       (T6)

If instead (alpha_n-1/2)log n->infinity, with alpha_n<=3/5 eventually, the same conclusions hold with kappa=0 and nominal limiting coverage. In particular this is consistent with the published pointwise fixed-alpha theorem.

**Explicit consequence.** Take alpha_n=1/2+1/(8log n) for n>=4, B=3 and gamma=.05. Then

    lim P(0 in I_n) <111/125=.888.                     (T7)

This is a failure of UNIFORM validity over the allowed exponents on a single fixed smooth bounded-noise problem. It is not a contradiction of a theorem that fixes alpha before sending n to infinity. It also does not prove coverage below.888 at any named finite n. The older portfolio crossover results concern harmonic gains eta_n/t with eta_n*g'(0) near1/2; they do not concern the exponent alpha_n in T1.

## 2. A uniform linearization with the nonvanishing quadratic term retained

We prove a uniform statement that also applies to the empirical bootstrap. For u in [-1,1], let P_u put probability(4+u)/8 on+4 and the remaining probability on-4. Define

    theta(u)=g^(-1)(u), H(u)=g'(theta(u)), J(u)=g''(theta(u)),
    sigma_u^2=16-u^2.

Let X_t be the same zero-start recursion under iid P_u and gains gamma_t=eta*t^(-alpha), with any alpha in [1/2,3/5]. Put e_t=X_t-theta(u) and xi_t=Z_t-u. All constants below are uniform in this compact u/alpha family.

We establish

    sqrt(n)(F_n-theta(u))
      = [1/(H(u)sqrt(n))]sum_(t=1)^n xi_t
        -b_n(u,alpha)+r_n(u,alpha),                    (T8)

    b_n(u,alpha)
      = eta*J(u)*sigma_u^2/[4H(u)^2(1-alpha)]
                                       *n^(1/2-alpha),
    sup_(u,alpha) E|r_n(u,alpha)| ->0.                 (T9)

The proof in fact bounds the final supremum by C n^(-1/5), after changing C to cover small n. No usable finite numerical value of C is asserted.

### 2.1 Uniform contraction and moment bounds

All sample values remain in {-4,+4}. The first iterate is eta Z1 exactly. Every later transition map is increasing with derivative at most1-gamma_t/2: eta*(3/2)/sqrt2<1 already at alpha=1/2. The same maps preserve [-8,8]. The roots theta(u), u in [-1,1], lie in a fixed compact interval. In centered coordinates the noiseless map fixes zero and contracts absolute value by at most1-gamma_t/2.

For later reference, the following elementary kernel estimates are uniform in alpha in [1/2,3/5]. If

    P_(i,t)=product_(k=i+1)^t(1-c gamma_k),

with fixed c>0 and all factors in a sufficiently late tail positive, then

    sum_(t=i)^infinity P_(i,t) <= C/gamma_i,
    sum_(i=2)^t P_(i,t) gamma_i^(r+1) <= C gamma_t^r,
    sum_(i=2)^t P_(i,t) gamma_i/i <= C/t.              (T10)

The second assertion is needed only for r in a fixed compact subset of positive numbers. To verify the last two, split i>=t/2 and i<t/2. In the recent part, gamma_i is within a fixed factor of gamma_t and the products sum to at most C/gamma_t. The older part contains at least t/2 gains of size at least gamma_t and is bounded by a polynomial times exp(-c' t gamma_t), smaller than any needed power uniformly because t gamma_t>=eta t^(2/5). For the first assertion, t<=2i is a geometric sum with gain at least a fixed multiple of gamma_i; for t>2i the products are bounded by exp(-c't^(2/5)), whose total sum is finite. Finitely many initial terms are absorbed in C.

The centered noise is uniformly bounded and has mean zero. The second-moment contraction recursion and T10 give

    E e_t^2<=C gamma_t.

Expanding the fourth power conditionally on the past, bounding the cubic-noise term by C gamma_t^3 E|e_(t-1)| and using the second-moment estimate, gives

    E e_t^4 <= (1-c gamma_t)E e_(t-1)^4+C gamma_t^3,

on a tail. T10 then gives

    E e_t^4<=C gamma_t^2,
    E|e_t|^3<=C gamma_t^(3/2).                         (T11)

This does not assume symmetric bootstrap noise; P_u is allowed to have u!=0. Initial moments are uniformly bounded and are covered by the same constants.

### 2.2 The leading second moment

Write

    g(theta+e)-g(theta)=H e+R_theta(e),
    |R_theta(e)|<=C e^2,
    R_theta(e)=(J/2)e^2+O(|e|^3),                      (T12)

uniformly. The global second and third derivatives of g are bounded, so these Taylor bounds hold on the whole relevant interval. Conditional square expansion and T11 yield, for s_t=E e_t^2,

    s_t=(1-H gamma_t)^2 s_(t-1)+sigma_u^2 gamma_t^2
                                             +O(gamma_t^(5/2)).

Subtract sigma_u^2 gamma_t/(2H). Since gamma_(t-1)-gamma_t=O(gamma_t/t), the remainder obeys a contracting recursion with forcing bounded by C[gamma_t^(5/2)+gamma_t/t]. Applying T10 proves

    E e_t^2 =sigma_u^2 gamma_t/(2H)
                              +O(gamma_t^(3/2)+1/t).  (T13)

All constants are uniform in u and alpha. In particular the leading coefficient is the local Hessian H, not the global strong-convexity lower bound.

### 2.3 Concentration of the accumulated squares

Let S_n=sum_(t=0)^(n-1) e_t^2. Replace the ith observation by an independent P_u copy and denote the resulting trajectory by e_t^(i). Exact contraction gives

    |e_t-e_t^(i)|<=8 gamma_i P_(i,t), t>=i,

with c=1/2. Both trajectories have the same marginal second-moment bound. Minkowski's inequality therefore gives

    ||S_n-S_n^(i)||_2
      <=C gamma_i sum_(t=i)^(n-1)P_(i,t) sqrt(gamma_t)
      <=C sqrt(gamma_i),                              (T14)

where gamma_t<=gamma_i and T10 were used. The product-measure Efron–Stein inequality then gives

    Var(S_n)<=C sum_(i=1)^n gamma_i<=C sqrt(n),
    ||(S_n-E S_n)/sqrt(n)||_2<=C n^(-1/4).             (T15)

This is a concentration bound on the actual nonlinear trajectory; no independence between its iterates is assumed. The deterministic initial error contributes no variance.

### 2.4 Summation by parts and the retained bias

The recursion implies exactly

    H sum_(t=1)^n e_(t-1)
      =sum_t xi_t-sum_t R_theta(e_(t-1))-D_n,
    D_n=e_n/gamma_n-e_0/gamma_1
               +sum_(t=1)^(n-1)e_t(1/gamma_t-1/gamma_(t+1)).

By T11 and |1/gamma_(t+1)-1/gamma_t|<=C t^(alpha-1),

    ||D_n||_2<=C n^(alpha/2),
    ||D_n/sqrt(n)||_2<=C n^(-1/5).                    (T16)

Changing the pre-update average to the post-update average adds(e_n-e_0)/n, negligible at sqrt(n) scale. Equations T11–T15 give

    (1/sqrt(n))sum_t R_theta(e_(t-1))
      = [J*sigma_u^2/(4H sqrt(n))]sum_t gamma_t+o_(L1)(1),

uniformly; the cubic Taylor remainder and the T13 remainder contribute O(n^(-1/4)+log(n)/sqrt(n)). Finally integral comparison, uniformly in alpha in [1/2,3/5], gives

    (1/sqrt(n))sum_(t=1)^n gamma_t
      =eta*n^(1/2-alpha)/(1-alpha)+O(n^(-1/2)).         (T17)

The omission or inclusion of the fixed first index changes only O(n^(-1/2)). Dividing the preceding identities by H proves T8–T9.

## 3. The conditional empirical-bootstrap calculation

For the original model u=0, H=J=1 and sigma^2=16. Let u_n=n^(-1)sum_i Z_i. Equation T8 is

    sqrt(n)F_n=sqrt(n)u_n-b_n(0,alpha_n)+o_P(1).        (T18)

The original empirical distribution is EXACTLY P_(u_n), not merely close to that family. Conditional on the full original dataset, each rerun is an independent iid P_(u_n) recursion with zero start and the same alpha_n. Also P(|u_n|>1)->0. On |u_n|<=1 the uniform L1 remainder in T9 applies conditionally, so for each fixed rerun

    sqrt(n)(F_n^{*b}-theta(u_n))
      = [1/(H(u_n)sqrt(n))]sum_i(Z_i^{*b}-u_n)
                              -b_n(u_n,alpha_n)+o_(P^*)(1),

where conditional remainder probabilities tend to zero in probability. This follows directly from the uniform expectation bound and Markov's inequality; no almost-sure conditional claim is made.

Since u_n=O_P(n^(-1/2)), theta(u_n)=u_n+O(u_n^2), H(u_n)->1, and

    b_n(u_n,alpha_n)-b_n(0,alpha_n)=o_P(1),             (T19)

because the coefficient in T9 is smooth in u and n^(1/2-alpha_n)<=1. Subtracting T18 cancels the shared nonvanishing bias:

    sqrt(n)(F_n^{*b}-F_n)
      = [1/(H(u_n)sqrt(n))]sum_i(Z_i^{*b}-u_n)+o_(P^*)(1),
                                                               (T20)

with the remaining original-data-measurable shift o_P(1). The distinction matters: conditional on the data, F_n is fixed and may depend on their order, but its shift from theta(u_n)-b_n(u_n,alpha_n)/sqrt(n) is asymptotically negligible by T18–T19.

The centered summands in T20 are bounded, with conditional variance16-u_n^2. The elementary iid bounded-variable CLT is uniform for u in [-1,1] (for example its characteristic-function Taylor remainder is uniformly O(|t|^3/sqrt(n))). With u_n->0, it proves the stated conditional Gaussian limit. Conditional independence of the B reruns gives the product limit. Conditional characteristic functions converge in probability to a deterministic limit and are bounded, so integrating them against the original first-coordinate characteristic function proves joint asymptotic independence in T4.

Under T3, b_n(0,alpha_n)/4->(47/25)exp(-c). Under the infinite-c alternative it tends to zero because 1-alpha_n stays bounded away from zero. This completes T4. The Gaussian limiting denominator is strictly positive almost surely, so continuous mapping proves T5. The boundary of the interval event has limiting probability zero, proving T6's coverage formula.

For every positive radius r and nonzero kappa, P(|U-kappa|<=r)<P(|U|<=r): the centered normal interval of a fixed length has maximal probability at zero. Conditioning on the independent positive Gaussian radius proves the strict inequality in T6 for every fixed B and every nominal level in (0,1).

## 4. A rational upper bound for a concrete B=3 limit

Set c=1/8. Since exp(-1/8)>7/8,

    kappa_c=(47/25)exp(-1/8)>329/200>8/5.              (T21)

We use the elementary bound t_(3,.975)<16/5, also proved by rational arctangent inequalities in the held original-interval certificate. A separate new rational checker verifies that bound and all numeric inequalities below.

The square of U-kappa is a Poisson mixture of chi-square variables with1+2J degrees of freedom, J~Poisson(kappa^2/2). This follows directly by expanding its Laplace transform:

    E exp(-s(U-kappa)^2)
      =exp(-kappa^2/2)sum_(j>=0)(kappa^2/2)^j/j!
                                      *(1+2s)^(-j-1/2).

The denominator sum V_b^2 is an independent chi-square3 variable. Conditional on J=j, acceptance at critical value16/5 is the event that a Beta(j+1/2,3/2) variable is at most

    t=256/331.

For every j>=1 its probability is at most I_t(3/2,3/2), since adding independent positive chi-square mass to the numerator increases the ratio. Writing x=2t-1=181/331,

    I_t(3/2,3/2)=1/2+[arcsin(x)+x sqrt(1-x^2)]/pi<21/25.

One purely rational verification uses x<y=11/20, monotonicity of x sqrt(1-x^2) below1/sqrt2, sqrt(1-y^2)<21/25, pi>157/50, and

    arcsin(y)<=y+y^3/6+3y^5/40+y^7/(1-y^2).

The last inequality bounds the remaining positive arcsine-series coefficients by one. These rational bounds give the displayed strict21/25 upper bound.

By T21, the Poisson mean is greater than32/25, so

    P(J=0)<3/10,

because the cubic lower Taylor polynomial of exp(32/25) already exceeds10/3. Bounding the J=0 acceptance probability by one gives

    C_3(t_(3,.975),kappa_c)
       <3/10+(7/10)*(21/25)=111/125=.888,

which proves T7. This bound is deliberately conservative; no numerical quadrature, Monte Carlo output or fitted noncentrality determines it.

## 5. Exact scope of the advance

The objective, data distribution, initialization, curvature constants, B and algorithm are fixed. Only the tuning exponent varies with horizon, while remaining strictly inside the paper's permitted range. The conclusion is a distribution/coverage theorem explaining loss of uniformity near that boundary, not a fixed-alpha asymptotic contradiction or a finite-n certification of79.1%.

The bootstrap differences correctly recover the centered noise scale but cancel the optimization bias shared by the original and rerun trajectories. The resulting normal shift and noncentral Student law are classical distributional mechanisms. The extra proof here is the uniform nonlinear trajectory expansion, quadratic-functional concentration, and exact empirical-bootstrap transfer at the alpha boundary. Whether an earlier primary theorem already supplies this combination remains to be checked before any novelty claim.
