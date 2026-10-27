# Moderate curvature preserves the finite-horizon coverage problem

28 October2026. The new fixed probe gives **405/512 coverage (79.10%)** for the original nominal95% offline B=3 interval at n=1,000,000. Its exact-binomial95% Monte Carlo confidence interval, rounded outward, is **[75.318730%,82.544433%]**. The paired quadratic control and the same-data nonlinear SAA control each cover486/512=94.92%. This is empirical coverage evidence, not a deterministic finite-coverage theorem.

The model is fixed:

    g(x)=x+(1/4)log cosh(2x), Z iid uniform on {-4,+4},
    eta_t=.94*t^(-.51), X0=0, n=1,000,000, B=3.

Its strong-convexity constant is1/2, smoothness constant3/2, and **global Hessian-Lipschitz constant1**, with noise variance16 and fourth moment256. Thus this gate removes the old example's Hessian-Lipschitz5000 restriction without changing the originally proposed noise or tuning after results. The near-endpoint gain exponent.51, relatively large initial step, fixed finite horizon, and constructed asymmetric objective remain material restrictions.

| Statistic used with original-centered B=3 RMS | Covered /512 | Coverage | Monte Carlo95% interval |
|---|---:|---:|---:|
| Original nonlinear ASGD |405|79.10%|75.32%–82.54%|
| Paired quadratic ASGD |486|94.92%|92.65%–96.66%|
| Nonlinear SAA control on the same samples |486|94.92%|92.65%–96.66%|
| Sample-mean / quadratic SAA control |486|94.92%|92.65%–96.66%|

All512 repetitions and all four original/resampled averages per objective are retained. Equality of aggregate control counts does not assert equality of their coverage masks. The nonlinear original mean is -.0066068854, with empirical standard deviation.0039788246. Its mean bootstrap displacement is+.0000436606. Thus the reruns reproduce the optimization bias closely enough that centering their differences at the original output does not reveal that bias in the interval center.

## A separate rigorous statement about bias

`moderate_curvature_bias_proposition.md` proves an opposite-noise pairing inequality, then a finite second/fourth-moment recursion. `certify_moderate_bias.py` evaluates that recursion using exact integer gain enclosures and outward arithmetic. At the same n it certifies

    -E F_n >= 46163488495523193/8796093022208000000
             > .00524 =1.31*(4/sqrt(n)).

There are no random draws in this certificate. It proves negative mean, not the empirical79.1% coverage result and not a Gaussian approximation. The previous slice-Poincare coverage proof is not silently imported: its mean/second-moment event inequality is not enough to certify this moderate example at its much smaller standardized bias. A new joint distribution or small-radius argument remains necessary for a deterministic coverage theorem.

## Exact algorithm and assumption mapping

The procedure matches [Lam–Wang Algorithm1](https://jmlr.org/papers/volume27/25-0008/25-0008.pdf): average iterates1..n, rerun from the same zero initialization using independent empirical resampling, original-centered RMS with divisor3, and t_(3,.975)=3.182446305284263. SAA is a labeled diagnostic control, never substituted for the target statistic. There is no burn-in, fitted center, B-1 correction or restart.

The sample objective is an antiderivative of g minus Zx. Assumptions1–5 hold by the global derivative bounds, bounded additive noise, compact uniform convergence, deterministic Hessian class and allowed gain exponent. These checks are spelled out in the bias proposition. A finite-n failure does not contradict the source's asymptotic coverage theorem; no claim is made that its stated Berry–Esseen bound promises95% coverage at these constants.

## Execution and retained checks

`PROTOCOL.md` was saved before the run. The one fixed seed was202610281911, the local CPU budget300seconds, and the completed run took59.14seconds. Both objectives used paired data and resampling draws. There was no search over seeds or parameters, paid job, author contact or publication. An initial import failure revealed that SciPy was absent before any random draw or output; the unused dependency was replaced by a standard-library binomial-tail calculation, with the scientific protocol unchanged.

The count-first data generator is mathematically equivalent to iid Rademacher data: draw its binomial plus count, generate a uniformly random order conditional on that count, then resample with plus probability K/n. This avoids storing the full512-million-entry dataset. The seed and code reproduce the complete draw stream; terminal statistics, sample means, original counts, masks and five planned checkpoints are retained. Pre-terminal checkpoints use the full-n empirical law and are not presented as standalone short-horizon coverage experiments.

`check_retained_probe.py` independently reconstructs every terminal radius/mask, checks the nonlinear SAA roots with a different formula, and validates the confidence-interval endpoints by exact integer binomial inequalities. It also checks64 complete small joint-data/bootstrap probabilities against ordinary empirical resampling. This is saved-output and source-equation verification, not a second independent million-step replication. The bias proposition and its numeric certificate have not yet received a fresh hostile audit at the time this report is written.

The useful conclusion is specific: **substantial empirical undercoverage survives with Hessian-Lipschitz constant1**, and finite optimization bias is separately certified. Nonlinear stochastic-approximation bias is classical. External novelty, typical-practice prevalence, a repair, and newsworthiness are not established by this package.
