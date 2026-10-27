# Primary theorem comparison: the power-exponent boundary

28 October 2026. Bounded comparison of actual primary statements, not a priority search or novelty clearance. The held candidate is `triangular_exponent_coverage_theorem.md`, SHA256 `59ce6000f9c72fb8fc575c8d45c562ae4caf146b11353a8363d065a554aa8e9c`.

## Result being compared

For the fixed scalar model with gradient `g(x)=x+(1/4)log cosh(2x)`, bounded noise `Z=±4`, zero initialization and gain `(.94)t^(-alpha_n)`, the candidate proves a joint original/offline-bootstrap law when `(alpha_n-1/2)log n -> c`. The original standardized average tends to `U-(47/25)e^(-c)`; each original-centered rerun tends conditionally to an independent standard normal. Original Algorithm 1 with any fixed B therefore has a noncentral Student limit. At `c=1/8`, its nominal-95%, B=3 limiting coverage is strictly below `111/125=.888`.

This is a precise failure of uniform-in-exponent calibration on one objective and noise law. It does not contradict fixed-exponent consistency, establish finite-horizon coverage at n=10^6, or discover the general fact that bootstrap centering can miss estimator bias. The new work requiring verification is the uniform nonlinear expansion and its conditional empirical-law transfer, not the final normal/Student calculation.

## 1. The target theorem is pointwise in the exponent

Lam and Wang, [JMLR 27, 25-0008](https://jmlr.org/papers/volume27/25-0008/25-0008.pdf), printed pp.8–9, Assumption 5 and Theorem 1, fix a power exponent in `(1/2,1]` before taking the sample-size limit. Algorithm 1 uses the empirical distribution, original-centered RMS with divisor B, and the t_B critical value. There is no displayed supremum over exponents. Appendix A.4, equations (20)–(21), has the nonlinear remainder `n^(1/2-alpha)` and a constant allowed to depend on alpha.

Our sequence keeps each finite-horizon exponent strictly inside their interval while approaching its lower boundary. That distinguishes nonuniformity from a counterexample to their pointwise theorem. Their Appendix already warns quantitatively through a remainder that need not vanish along this sequence; it does not give its signed limiting coefficient or the resulting fixed-B coverage law.

Local primary PDF/text inspected: `../subcritical_repair_finishline_20261027/primary_sources/lam_wang_jmlr_2026.{pdf,txt}`. This comparison does not rely on the separate previously recorded endpoint or Borel-set metric corrections.

## 2. The nonlinear error scale is established prior work

Shao and Zhang, [arXiv:2102.04923v2](https://arxiv.org/pdf/2102.04923v2), Theorems 3.4–3.5, printed pp.10–11, bound Gaussian approximation over convex sets by a term containing `n^(1/2-alpha)`, for fixed `alpha in (1/2,1)`. The constant explicitly depends on alpha. Their proof, pp.28–29, isolates the accumulated quadratic Taylor remainder of the drift.

This directly anticipates the scale on which our boundary becomes relevant. It is not an exact shifted-normal limit: an upper error bound cannot identify a nonzero signed shift, prove concentration of that shift, or establish cancellation of its empirical counterpart from original-centered reruns. The candidate supplies those model-specific steps. It would be inaccurate to present the existence of nonlinear averaging bias or the power `1/2-alpha` as new.

Local primary read: `../harmonic_endpoint_boundary_20261027/primary_sources/shao_zhang_2021v2.pdf`.

## 3. General stochastic-approximation bias results

Lauand and Meyn, [Revisiting Step-Size Assumptions in Stochastic Approximation, v3](https://arxiv.org/html/2405.17834v3), Theorem 2.2, prove moment/convergence and averaged-error bounds for nonlinear SA at each fixed power exponent in `(0,1)`. Their explicit parameter-bias expansions in Theorems 2.3–2.4 concern **linear** SA. In the additive-noise linear case the corresponding bias vanishes; their nonzero linear coefficient arises from the broader noise setting. The nonlinear average-*target*-bias identity (15) concerns the mean drift averaged along the path, not the average parameter itself.

Our nonlinear additive-noise curvature term is therefore not obtained by inserting this scalar model into their displayed linear coefficient. The paper nevertheless establishes the larger phenomenon of bias competing with averaged stochastic error and treats the half-power boundary as meaningful. Its fixed-exponent constants are not an automatic uniform triangular-array theorem. This is a concrete mismatch, not proof that no other result subsumes our expansion.

## 4. Bootstrap bias mismatch is explicitly known

Cavaliere, Gonçalves, Nielsen and Zanelli, [Bootstrap Inference in the Presence of Bias, v3](https://arxiv.org/html/2208.02028v3), Section 3.1 and especially **Remark 3.1**, explicitly treat an original limit `B+xi` with a centered bootstrap limit. Our mapping is `B=-(47/25)e^(-c)`, `xi=N(0,1)`, and implicit bootstrap bias tending to zero. Remark 3.1 gives the resulting nonuniform p-value law. The centered-xi_2 condition of their Theorem 3.1 is not satisfied by the nonzero deterministic difference, and the authors explicitly separate that case in the remark.

Thus the general inference failure is an instance of their established bias-mismatch phenomenon. Their result does not prove the nonlinear-SGD expansion needed to verify this mapping, and their full conditional-CDF p-value is different from the fixed-B RMS Student interval. Once our joint Gaussian law is known, however, its finite-B noncentral-Student consequence is elementary rather than a new bootstrap principle.

## 5. A recent diminishing-step comparison

Suvroikova, Dvinskikh, Dorn and Gasnikov, [When Momentum Helps Polyak–Ruppert Averaging, v2](https://arxiv.org/html/2610.27990v2), Theorem G.5 and Proposition G.7, provide a diminishing-step Abel transfer and verified SGD moment bounds. With a Lipschitz Hessian, their Taylor-remainder estimate again has size `n^(1/2-gamma_step)`. Theorem G.5 assumes a fixed exponent strictly above one half; it bounds that term instead of resolving its leading random/deterministic decomposition. Corollary G.6 treats triangular **batch sizes** under uniform moment premises, not the original cheap empirical bootstrap with a moving power exponent.

The Abel decomposition and stability strategy are therefore strongly overlapping classical ingredients. The actual theorem statements inspected do not supply the coefficient `(47/25)e^(-c)`, original-centered empirical-bootstrap cancellation, or fixed-B coverage conclusion for this model. No claim about the paper's other calibration results follows from that limited comparison.

## Verdict and defensible contribution

The strongest defensible candidate is a **fully specified uniformity boundary for the original cheap-bootstrap procedure**, with moderate curvature and bounded noise, supported by a uniform nonlinear expansion rather than a heuristic normal approximation. It connects the known nonlinear-SA remainder to an exact noncentral-Student coverage law. The underlying bias and bootstrap-mismatch mechanisms are established; the original paper's fixed-alpha theorem remains intact.

This could support a focused robustness/boundary note if the analytic audits pass. These comparisons do not justify calling it a new general bootstrap method, a refutation of fixed-exponent asymptotic validity, or a newsworthy discovery by themselves. Historical priority of the exact triangular-exponent statement remains unresolved.

The arithmetic certificate checks only the displayed limiting bound: `noncentral_limit_bound_certificate.json` binds checker SHA256 `2ef577c4988fb0505c0c2502e7f3cb182c0837626a9f542519867c54d3e0261f`. No simulations or finite-n coverage claims were added for this comparison.
