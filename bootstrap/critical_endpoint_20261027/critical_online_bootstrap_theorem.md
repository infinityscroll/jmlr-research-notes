# Positive validity at the critical harmonic step

27 October 2026. New theorem candidate; independent audit pending. This is a repair for the scalar quadratic model, not a claim that the full nonlinear endpoint theorem is valid or that the argument is historically new.

## 1. Exact procedure and statement

Let Z_t be iid with mean zero, variance sigma^2>0, and finite fourth moment. Minimize h(x,Z)=(x-Z)^2/2. For a fixed deterministic x_0, run

    X_t = (1-1/(2t)) X_(t-1) + Z_t/(2t),
    X_t^b = (1-W_t^b/(2t)) X_(t-1)^b + W_t^b Z_t/(2t),
    X_0^b = x_0,

where all W_t^b are independent Exp(1) variables, independent of the data. Fix any finite B>=1. Average iterates t=1,...,n and set

    R_n^2 = (1/B) sum_b (bar X_n^b - bar X_n)^2.

**Theorem candidate.** With v_n=sqrt(n/log n),

    v_n (bar X_n, bar X_n^1-bar X_n, ..., bar X_n^B-bar X_n)
        -> Normal(0, sigma^2 I_(B+1)).

Consequently bar X_n/R_n converges in distribution to Student t_B, and the original cheap online interval with divisor B and cutoff t_(B,1-gamma/2) has limiting coverage 1-gamma for every gamma in (0,1). No change in the implemented interval or number of reruns is required. Its standard error is of order sqrt(log n/n), not n^(-1/2).

This is the harmonic exponent alpha=1 with coefficient eta=1/2, exactly the critical drift value for the unit-Hessian quadratic. The previously preserved failure at smaller harmonic coefficients remains valid. This result does not give a finite-sample coverage error bound, uniformity over x_0 or noise distributions, or a nonlinear/multivariate theorem.

## 2. An exact common martingale representation

Write D_t^b=X_t^b-X_t and let F_(t-1) contain all data and multipliers before time t. Direct subtraction gives

    D_t^b = (1-1/(2t)) D_(t-1)^b + M_t^b/(2t),
    M_t^b = (W_t^b-1)(Z_t-X_(t-1)^b).

Set M_t^0=Z_t. The vector M_t has conditional mean zero. Independence of the current multipliers gives the **exact** conditional covariance

    E[M_t M_t^T | F_(t-1)]
      = diag(sigma^2, sigma^2+(X_(t-1)^1)^2, ..., sigma^2+(X_(t-1)^B)^2).

In particular, common observations do not create an off-diagonal covariance between the bootstrap differences. For distinct b,c the factor E[(W_t^b-1)(W_t^c-1)] is zero; for b versus coordinate zero the factor E[W_t^b-1] is zero. This calculation is for the centered differences, not the perturbed iterates themselves.

Define

    p_t = product_(j=1)^t (1-1/(2j)) = binom(2t,t)/4^t,
    q_n = (1/n) sum_(j=1)^n p_j,
    w_(n,t) = [1/(2nt p_t)] sum_(j=t)^n p_j.

Solving the deterministic-drift recursions and averaging yields exactly

    (bar X_n, bar D_n^1, ..., bar D_n^B)
      = (q_n x_0,0,...,0) + sum_(t=1)^n w_(n,t) M_t.

The representation has deterministic weights even though the original bootstrap recursion has random coefficients. The random-coefficient remainder is retained inside the martingale differences and their conditional variances.

## 3. Exact weights and their normalization

The central-binomial product satisfies

    sum_(j=0)^n p_j = (2n+1)p_n,
    (2t-1)p_(t-1)=2t p_t.

Put A_n=(2n+1)p_n/(2n). Then

    q_n = ((2n+1)p_n-1)/n,
    w_(n,t) = A_n/(t p_t) - 1/n.

Also

    1/p_t - 1/p_(t-1) = 1/(2t p_t),
    sum_(t=1)^n 1/(t p_t) = 2(1/p_n-1).

It follows that

    sum_t w_(n,t)^2
      = A_n^2 sum_t 1/(t^2 p_t^2)
        - (4A_n/n)(1/p_n-1) + 1/n.

Stirling's formula gives p_t=(pi t)^(-1/2)(1+O(1/t)). Therefore

    sum_t 1/(t^2 p_t^2)=pi log n+O(1),
    sum_t w_(n,t)^2=(log n+O(1))/n,
    0<=w_(n,t)<=C/sqrt(nt),
    q_n=2/sqrt(pi n)+O(1/n).

For a_(n,t)=v_n w_(n,t), these imply

    sum_t a_(n,t)^2 -> 1,
    max_t a_(n,t)^2 <= C/log n -> 0,
    v_n q_n x_0 -> 0.

The slow disappearance of the last term is one reason this asymptotic result does not imply good finite-sample coverage for an arbitrary initialization.

## 4. Moment bounds for the genuinely random-coefficient recursion

Let u_t=E[(X_t^b)^2]. Since E W=1 and E W^2=2, independence of Z_t and its zero mean give

    u_t = (1-1/t+1/(2t^2)) u_(t-1) + sigma^2/(2t^2).

Thus u_t=O(log(e t)/t). One direct proof multiplies the recursion by t: its leading coefficient on (t-1)u_(t-1) is 1+O(1/t^2), whose products are bounded, and its forcing is O(1/t). Finite early t are absorbed into the constant. In particular u_t is bounded and tends to zero.

A uniform fourth moment also holds. For U_t=E[(X_t^b)^4], expand the fourth power. The coefficient on U_(t-1) is exactly

    E(1-W/(2t))^4
      = 1-2/t+3/t^2-3/t^3+3/(2t^4).

The term containing E Z_t is zero. The quadratic mixed term is O(u_(t-1)/t^2); the cubic-noise mixed term is O(|E X_(t-1)^b|/t^3), whether or not E Z^3 is zero; the fourth-noise term is O(1/t^4). Bounded second moments therefore give, at all sufficiently large t,

    U_t <= (1-1/t) U_(t-1) + C/t^2.

Together with the finite initial moments this proves sup_t U_t<infinity. Consequently sup_t E||M_t||^4<infinity for fixed B. Constants may depend on x_0, B and the fourth noise moment.

## 5. Joint central limit theorem and the original Student ratio

For any fixed vector z in R^(B+1), the triangular array a_(n,t) z^T M_t is a martingale-difference array. Its sum of conditional variances equals

    sigma^2 ||z||^2 sum_t a_(n,t)^2
       + sum_b z_b^2 sum_t a_(n,t)^2 (X_(t-1)^b)^2.

The expected value of the second term tends to zero. More explicitly, using the weight bound and the second-moment bound, it is at most a constant times

    [u_0 + sum_(t=2)^infinity log(e t)/t^2]/log n,

which tends to zero. Thus conditional variance converges in probability to sigma^2||z||^2.

For every epsilon>0, the expectation of the conditional Lindeberg sum is bounded by

    epsilon^(-2) sum_t a_(n,t)^4 E|z^T M_t|^4
       <= C max_t a_(n,t)^2 sum_t a_(n,t)^2 -> 0.

Markov's inequality makes the conditional Lindeberg sum tend to zero in probability. The martingale triangular-array CLT, followed by Cramer-Wold, yields the asserted joint Gaussian limit. The vanishing deterministic initialization term was checked above.

The limit has independent equal-variance coordinates. The continuous mapping theorem gives

    bar X_n/R_n -> G_0 / sqrt((1/B) sum_(b=1)^B G_b^2),

where the G_b are independent standard normals. The denominator is positive almost surely and this is t_B. Continuity of its distribution at the finite Student cutoff proves the two-sided coverage assertion. Any arbitrary definition on R_n=0 has no effect on the limit.

## 6. Primary-source boundary and originality limits

The algorithm and Student divisor are those of Lam and Wang's cheap online procedure. The reference [arXiv v2](https://arxiv.org/html/2310.11065v2) includes alpha=1 in its averaged-SGD step assumption; the earlier source-bound endpoint notes isolate why unrestricted harmonic coefficients fail.

[Fang, Xu and Yang (JMLR 2018)](https://www.jmlr.org/papers/volume19/17-370/17-370.pdf), Assumption A5, uses alpha strictly between 0.5 and 1. Its general online-bootstrap result therefore does not directly establish this alpha=1 critical case. The probabilistic ingredient used here is classical martingale central limit theory, not a new CLT: see Brown (1971), *Martingale Central Limit Theorems*, DOI [10.1214/aoms/1177693494](https://doi.org/10.1214/aoms/1177693494), and the triangular-array formulation in Hall and Heyde (1980), Chapter 3.

This comparison is not an exhaustive novelty review. The critical stochastic-approximation normalization and persistent initialization mechanism are classical. The potential contribution is a precise positive repair for this finite-rerun Student procedure, complementary to the exact negative endpoint examples; its independent significance and prior publication status remain unresolved.
