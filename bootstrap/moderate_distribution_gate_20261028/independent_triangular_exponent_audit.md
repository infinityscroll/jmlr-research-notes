# Independent hostile audit of the gain-exponent coverage boundary

28 October 2026. Source-bound mathematical review by the independent HCM/attention agent. No producer file was modified, no trajectory was run, and no numerical coverage estimate was used.

**Bound source:** `triangular_exponent_coverage_theorem.md`, SHA256 `59ce6000f9c72fb8fc575c8d45c562ae4caf146b11353a8363d065a554aa8e9c`.

**Verdict:** no blocking mathematical error found in the claimed triangular-array limit, conditional offline-bootstrap transfer, or strict limiting coverage bound, within the exact stated scope. This is not a primary-novelty review, a fixed-alpha contradiction, or a finite-n coverage certificate.

## 1. Uniform contraction is valid after the exceptional first step

For g(x)=x+(1/4)log cosh(2x), g' is in [1/2,3/2], g''=sech²(2x), and g''' is globally bounded. At t>=2, gamma_t<=.94/sqrt(2), so gamma_t*(3/2)<1. Hence the sample transition is increasing, and the centered noiseless map contracts by at most 1−gamma_t/2. The t=1 map need not be increasing, but X0=0 implies X1=.94 Z1 and a bounded first error uniformly over u in [-1,1]. The proof correctly absorbs that finite initial step.

The interval [-8,8] is invariant from t>=2: g(−8)<−4 and g(8)>4, and the transition is increasing. Theta(u) stays in a fixed compact set. All noise moments and initialization errors are therefore uniformly bounded.

I reconstructed the convolution estimates T10. For i>=t/2, gains differ from gamma_t by at most 2^(3/5); a geometric tail contributes O(1/gamma_t). The old part has an exponential factor exp(−c t gamma_t), where t gamma_t is at least .94 t^(2/5), uniformly in alpha. This controls each polynomial remainder. For the forward sum over t>=i, the part t<=2i is O(1/gamma_i); the remaining stretched-exponential sum is uniformly finite. These estimates justify the stated uniform constants, rather than merely pointwise constants depending on alpha.

## 2. The quadratic bias coefficient and its stochastic concentration

Second-moment contraction gives E e_t²=O(gamma_t). In the fourth-moment expansion, the leading noise term is O(gamma_t² E e_(t−1)²)=O(gamma_t³). The possibly asymmetric third noise moment contributes O(gamma_t³ E|e_(t−1)|), which is smaller. Thus T11 holds uniformly for the empirical-law family as well as the symmetric original law.

In the exact second-moment expansion around H=g'(theta), the term −2gamma E[e R_theta(e)] is O(gamma^(5/2)); the R² term is O(gamma^4). Subtracting sigma_u² gamma_t/(2H) leaves forcing O(gamma_t^(5/2)+gamma_t/t). T10 therefore gives T13 with error O(gamma_t^(3/2)+1/t). In particular the coefficient uses the local H, not the global convexity constant.

The Efron–Stein step is sound on the actual nonlinear trajectory. Replacing Z_i by an independent copy changes e_t by at most 8gamma_i P_(i,t). Each replaced trajectory has the same marginal moment bounds as the original. Consequently

    ||e_t²−(e_t^(i))²||_2 <= C gamma_i P_(i,t) sqrt(gamma_t).

Minkowski plus the forward convolution gives ||S_n−S_n^(i)||_2<=C sqrt(gamma_i). Efron–Stein then yields Var(S_n)<=C sum_i gamma_i<=C sqrt(n). No false independence assumption on successive iterates is used.

The summation-by-parts sign in T16 is correct. The terminal term en/gamma_n has L2 norm O(n^(alpha/2)); the weighted interior sum has the same order because its summands have norms O(t^(alpha/2−1)). After division by sqrt(n), the worst uniform order on alpha<=3/5 is n^(−1/5). Cubic Taylor and second-moment remainders have orders at most n^(−1/4)+log(n)/sqrt(n), and the square-functional fluctuation is O_L2(n^(−1/4)). The fixed initial term and pre/post averaging change are smaller. These reconstruct T8–T9, including the uniform L1 remainder and its displayed bias coefficient.

At u=0, H=J=1 and sigma²=16, so b_n/4=eta n^(1/2−alpha)/(1−alpha). This tends to (47/25)e^(−c), exactly as stated. The negative shift has the correct sign: g is locally convex, so the quadratic term lowers the averaged iterate.

## 3. Conditional bootstrap transfer and joint independence

The empirical law is exactly P_(u_n), where u_n is the original sample mean. It is not an approximation to that family. Since u_n=O_P(n^(−1/2)), the event |u_n|<=1 has probability tending to one; on that event, uniform T9 gives a conditional remainder bound by Markov's inequality.

The possible nonvanishing bias in each rerun is b_n(u_n,alpha_n), while the original bias is b_n(0,alpha_n). Their difference is o_P(1) at the scaled level because its coefficient is uniformly smooth and n^(1/2−alpha_n)<=1. Also sqrt(n)[theta(u_n)−u_n]=o_P(1). The remaining original-order-dependent residual is original-data-measurable and o_P(1); it need not be conditionally random. The source explicitly retains this distinction. Thus subtracting F_n cancels the common optimization bias without pretending that the original estimator is unbiased.

Bounded centered bootstrap draws have conditional variance 16−u_n² and a uniformly bounded third moment on u in [-1,1]. Their characteristic-function expansion gives the needed conditional CLT uniformly. Fixed B independent reruns give the product limit. Convergence in probability of the bounded conditional characteristic functions to a deterministic Gaussian characteristic function implies joint independence from the original limiting first coordinate. This is sufficient for T4, including the bounded-Lipschitz conditional statement.

The denominator in T5 is positive almost surely for every fixed B>=1. The interval-event boundary has zero limiting probability. Conditioning on its positive independent radius shows strictly smaller coverage at every nonzero shift, because a centered normal interval of fixed length maximizes normal mass.

## 4. Explicit .888 bound

I read `check_noncentral_limit_bound.py` and its saved certificate, and independently reconstructed the analytic inequalities. The Student-3 two-sided tail is 2[atan(x)−x/(1+x²)]/pi for x=sqrt(3)/q; the function is increasing in x. The checker uses a rational upper bound for sqrt(3), an alternating upper bound for atan, and a valid Machin lower bound for pi, giving a tail below .05 at q=16/5.

The noncentral chi-square Poisson expansion is correct. Conditional on J>=1, the beta acceptance is bounded by I_(256/331)(3/2,3/2). Its elementary arcsine expression, and the conservative rational series bound, give less than 21/25. The lower noncentrality kappa>8/5 implies a Poisson mean greater than 32/25, whose zero probability is less than 3/10. Therefore the mixture bound is strictly below 3/10+(7/10)(21/25)=111/125. The checker concerns only this limiting law; it does not certify a finite-n error probability.

## 5. Remaining scope

The changing quantity is the horizon-dependent tuning exponent, not the objective, curvature, noise law, initialization, B, or algorithm. Each exponent is permitted, but a pointwise theorem fixing alpha need not be uniform over such a triangular array. The proof does not give a usable finite constant for the n^(−1/5) remainder and does not establish coverage below .888 at the earlier experiment's n. It uses the ORIGINAL offline resampling Algorithm 1, not the online multiplier algorithm. These restrictions are material and correctly retained. The statistical mechanisms of nonlinear SGD bias, bootstrap bias cancellation, and noncentral Student limits are classical; this audit does not establish novelty of their particular uniform composition.
