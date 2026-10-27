# Rank 100 ASkotch finite runs and an exact fixed step repair

27 October 2026. The unchanged released optimizer converged in the retained float64 stress runs when supplied with an algebraically equivalent structured kernel model. This does not reproduce practical divergence. Separately, fixing its relative step at one restores a proved expected-error bound throughout the exact family where the original random-power step has an expected-error instability certificate. The two conclusions concern different objects: observed finite trajectories and expectation over all random trajectories.

## Complete finite comparison

The protocol fixed n=10000, b=r=100, lambda=10^-8, nominal delta=10^-10, two seeds and 20000 steps before any random draws. All six float64 cases completed. The relative error is ||w-u||_A^2/||u||_A^2, with deterministic alternating-sign u, response Au and zero initialization.

| Update | Seed 2026102701 final error | Seed 2026102702 final error |
|---|---:|---:|
| Released gradient and ten-step power estimate | 2.71136e-8 | 2.41403e-6 |
| Corrected gradient and ten-step power estimate | 2.04105e-8 | 3.67302e-6 |
| Corrected gradient and fixed eta=1 | 7.81034e-9 | 1.94136e-7 |

The three float64 cases for each seed used identical sampled blocks, Nyström sketches and power starts, verified by the retained random-property digests. The fixed-step case retained the otherwise unnecessary power computation for this matching. No hyperparameter was selected from these outcomes. The two float32 cases both stopped on native Nyström Cholesky errors, after 368 and 1434 completed updates. Their represented RBF delta was zero, and the native spectral-floor rule is different; they are not trajectories in the exact float64 theorem's model.

The eight cases consumed approximately 340 local CPU seconds in total. No paid job was launched. All protocol settings, exceptions, checkpoints and source hashes are retained. `check_saved_results.py` independently recomputes the energy of all 72 saved states; its largest scaled discrepancy is 2.55e-15. This is a saved-state check, not an independent replay of every update.

## What ran unchanged and what was adapted

The official checkout at commit `61cdb69cb11adea48ecb13c823ad654d46dc15df` was not modified. The experiments call its actual ASkotchV2, Nyström construction, ten-step power routine, uniform block sampler and acceleration. The gradient-repair and eta=1 controls are explicitly labeled changes.

The model supplies K=delta I+(1-delta)11' through a structured operator instead of generating all high-dimensional RBF pairs through KeOps. Its block matrix is dense and passed to the unchanged preconditioner; its full selected gradient uses the analytic equicorrelation sum. This is the same real-arithmetic kernel, but it changes floating-point reduction order. Therefore the experiment is **not an untouched n=10000 FullKRR pipeline reproduction**.

An additional bounded n=120, b=r=100 comparison did use the actual FullKRR/KeOps model. Native kernel columns had diagonal one, identical off-diagonal entries 0.9999999999, and exactly the same rounded delta as the adapter. Four one-step comparisons covered zero and nonzero states and both gradient variants. Gradient discrepancies were at most 1.36e-16. Different reduction orders in the extremely ill-conditioned preconditioner produced scaled full-state discrepancies up to 1.04e-6; bit identity is not asserted. The actual observations are retained in `full_model_interface_results.json`.

## Expectation instability does not establish typical failure

The preceding [rank-100 theorem](../rank100_default_gate_20261027/theorem.md) lower-bounds an expectation by .001(1.000001)^(t-1). At 20000 steps that lower bound is about .00102. Two individual trajectories may lie below it without contradiction. An independently reviewed six-coordinate covariance calculation also concerns expectation, not a prediction for each realization.

The saved runs show error concentrating in relatively few coordinates. At step 2500 of the first released run, one coordinate carries about 65.3% of squared coefficient error; later that run converges. This is consistent with a rare-trajectory explanation of the difference, but establishes neither a tail theorem nor almost-sure convergence. No failing seed was searched for after seeing these results. The [independent driver review](independent_driver_review.md) found no obvious interface mismatch and retains this distinction.

## Exact repair on the same family

The [fixed-step theorem](eta1_repair_theorem.md) proves, for every delta in [5e-11,2e-10], both stale and corrected gradients, the same uniform blocks and acceleration, and fixed eta=1,

    E ||w_t-u||_A^2 / ||u||_A^2 <= 4(0.999999)^t.

Its exact rational certificate covers 64 parameter/gradient boxes and 320 Bernstein PSD matrices. Positive covariance comparison supplies the all-time conclusion, rather than the observed convergence or floating eigenvalues. The general Lyapunov method is classical. The result identifies a sufficient modification on this explicit family; it gives no general-kernel guarantee or competitive wall-clock claim.

The research claim is now sharper: the practical random-power recipe can be unstable in mean square in an exact, highly ill-conditioned family, and a fixed step restores stability there. The retained finite double-precision runs do not establish a practically visible breakdown. This remains a technical correction candidate, not evidence of broad solver inferiority or a refutation of JMLR Theorem 17.
