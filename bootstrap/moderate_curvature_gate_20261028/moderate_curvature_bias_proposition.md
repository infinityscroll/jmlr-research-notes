# A finite-horizon bias bound with Hessian-Lipschitz constant one

28 October 2026. New analytic proposition. The numerical mean bound is certified separately by outward integer arithmetic. This is a negative-mean theorem, not a coverage theorem for the bootstrap interval.

## 1. Model and exact source mapping

Use the original offline Algorithm1 of [Lam–Wang, JMLR27,25-0008](https://jmlr.org/papers/volume27/25-0008/25-0008.pdf), with its post-update average, common initialization, empirical resampling, original-centered RMS divisorB, and t_B critical value. The source copy inspected is `../subcritical_repair_finishline_20261027/primary_sources/lam_wang_jmlr_2026.txt`, Algorithm1 on printed p.5 and Assumptions1–5 on pp.7–8. Set

    g(x)=x+h(x), h(x)=(1/4)log cosh(2x),
    Z_t iid uniform on {-4,+4}, X_0=0,
    eta_t=(47/50)t^(-51/100),
    X_t=X_(t-1)-eta_t[g(X_(t-1))-Z_t],
    F_n=(1/n)sum_(t=1)^n X_t.                         (M1)

The population minimizer is zero. A sample objective is the integral of g minus Zx. It is smooth, with

    g'(x)=1+(1/2)tanh(2x) in [1/2,3/2],
    g''(x)=sech(2x)^2 in [0,1].                      (M2)

Thus strong convexity is1/2, smoothness3/2, and the global Hessian-Lipschitz constant is1. The noise is a martingale difference, variance16, fourth moment256, L4 norm4. Initialization is exactly the target. The SAA root lies in [-9,9] for every sample. On that compact set the objective discrepancy is -x times the sample mean of Z, and sample Hessians are deterministic functions of x. Therefore the compact uniform convergence and Hessian Glivenko–Cantelli assumptions are immediate. The gain exponent.51 is strictly inside the stated interval(.5,1]. These facts verify the source's assumptions, while leaving its asymptotic theorem intact.

Although eta_1*(3/2)>1, X_1=eta_1 Z_1 exactly. For t>=2, eta_t*(3/2)<1 because (141/100)^2<2 and 2^(1.02)>2. The drift map f_t(x)=x-eta_t g(x) is then increasing and contracts absolute value by at most c_t=1-eta_t/2. Every iterate lies in [-8,8]: X_1 does, g(-8)<-4 and g(8)>4, and the increasing update maps preserve this interval. The first step is treated exactly throughout.

## 2. Opposite-noise pairing removes the adverse cubic term

**Lemma.** For t>=1,

    E[X_t h(X_t)]<=0.                                (M3)

**Proof.** Pair each finite noise sequence z with -z. Their first iterates sum to zero. If a+b<=0, monotonicity of f_t and evenness/nonnegativity of h give

    f_t(a)+f_t(b)<=f_t(a)+f_t(-a)=-2 eta_t h(a)<=0.

The paired innovations cancel, so induction proves X_t(z)+X_t(-z)<=0. The function psi(x)=x h(x) is odd and increasing, since psi'(x)=h(x)+x h'(x)>=0 on the whole line. Hence psi(X_t(z))+psi(X_t(-z))<=0. The two sequences have equal probability, proving M3. No normal approximation or symmetry of X_t itself is assumed.

Expanding the square of f_t(X_(t-1))+eta_t Z_t and using M3 yields

    E X_t^2 >= (1-eta_t)^2 E X_(t-1)^2+16 eta_t^2.     (M4)

The term eta_t^2 E h(X_(t-1))^2 is nonnegative; the cross term is -2 eta_t(1-eta_t)E[X_(t-1)h(X_(t-1))]>=0. Since eta_t<1, its sign is correct. This gives the slope-one linear variance floor, rather than the weaker slope3/2 floor.

## 3. Deterministic moment recursion

Initialize

    v_1=u_1=16 eta_1^2, w_1=256 eta_1^4,
    b_1=0.

For t>=2 define

    H_(t-1)=max(0,v_(t-1)/2-w_(t-1)/3),
    b_t=(1-eta_t)b_(t-1)+eta_t H_(t-1),
    v_t=(1-eta_t)^2 v_(t-1)+16 eta_t^2,
    u_t=c_t^2 u_(t-1)+16 eta_t^2,
    w_t=c_t^4 w_(t-1)+96 eta_t^2 c_t^2 u_(t-1)
                                      +256 eta_t^4.  (M5)

Then, simultaneously for all t,

    v_t<=E X_t^2<=u_t, E X_t^4<=w_t, -E X_t>=b_t.

The second-moment lower bound is M4. Upper second and fourth moments follow from |f_t(x)|<=c_t|x| and the exact symmetric-noise fourth-moment expansion; odd noise terms vanish. For the mean bound, use

    h(x)>=x^2/2-x^4/3, h(x)>=0.                      (M6)

To prove M6 globally, for z>=0 the derivative of tanh(z)-z+z^3/3 is z^2-tanh(z)^2>=0. Integrating twice, and using evenness, gives log cosh(z)>=z^2/2-z^4/12. Substituting z=2x proves M6. Finally

    -E X_t=(1-eta_t)(-E X_(t-1))+eta_t E h(X_(t-1))

and M5 follows by induction.

**Proposition.** For every n,

    -E F_n >= (1/n)sum_(t=1)^n b_t.                  (M7)

At n=1,000,000 the separate exact recurrence certificate establishes

    -E F_n > 0.00524
             =1.31*(4/sqrt(n)).                     (M8)

The scale4/sqrt(n) is the usual linear asymptotic standard-error scale, not an assertion that the nonlinear statistic is Gaussian or that its actual variance equals16/n.

## 4. What the certificate does and does not establish

`certify_moderate_bias.py` uses Q=2^44 and encloses every gain by k/Q and (k+1)/Q, checking exactly

    50^100 t^51 k^100 <= (47Q)^100
                       <50^100 t^51(k+1)^100.

All nonnegative products and sums in M5 are rounded outward. The H lower bound uses the lower endpoint of v and upper endpoint of w. A floating-point gain is only a root guess; the integer inequalities certify its interval. M8 uses the final rational lower endpoint. No random numbers or SGD trajectories enter this calculation.

This proposition proves finite-horizon optimization bias with moderate curvature and bounded noise. The separate paired probe measures the original bootstrap interval's coverage. The mean bound alone does not certify that coverage, and no deterministic finite-coverage theorem is claimed here. The mechanism of nonlinear stochastic-approximation bias is classical; priority and a broader novelty claim are not established.
