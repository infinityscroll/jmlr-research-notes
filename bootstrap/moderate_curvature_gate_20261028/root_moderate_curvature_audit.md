# Independent review of the moderate-curvature bootstrap result

28 October 2026. Root review of the producer's model, proof, simulation source
and retained statistics. Bound analytic source:
`moderate_curvature_bias_proposition.md`, SHA256
`863d6b4751e273442d32e65aa720ee90f79d0737f390b67d880dd030152af9b3`.
Bound empirical report: `RESULTS.md`, SHA256
`1c3966680584815a2366803936dc676c723f48a28cfa5db93b505b60cffaf789`.

**Verdict:** the moderate-curvature assumption mapping and negative-mean
proposition pass this internal analytic review. Independent exact recomputation
of all one million recurrence steps confirms the mean bound. The saved probe
supports empirical undercoverage, with Monte Carlo uncertainty; it does not
prove a deterministic finite-sample coverage bound or contradict the source's
asymptotic theorem. No novelty clearance is supplied here.

## Source procedure and assumptions

I read the retained complete Lam--Wang primary text at Algorithm 1 and
Assumptions 1--5. The simulation uses the stated post-update ASGD average,
same zero initialization for the original and each rerun, independent empirical
resampling, B=3, original-centered sum of squares divided by B, and the t3
critical value. There is no SAA substitution for the target statistic.

The gradient g=x+(1/4)log cosh(2x) has derivative in [1/2,3/2] and second
derivative sech(2x)^2<=1. Additive Rademacher noise of magnitude four supplies
the bounded fourth moment, nonzero variance and martingale difference. The
empirical optimizer lies in a fixed compact interval; objective deviations
there are the sample mean times x, and the Hessian class is deterministic.
The primary Assumption 5 imposes no additional upper bound on eta=.94, and
alpha=.51 is in its interior. These verify the source assumptions without
claiming a useful finite-n value for its Berry--Esseen bound.

The first step has eta_1*L>1, but is treated exactly. From step two onward
the drift is increasing and a contraction. The interval [-8,8] is invariant:
g(-8)<-4 and g(8)>4, and the update maps are increasing. No global first-step
contraction is used in the proof or certificate.

## Analytic bias argument

Opposite noise paths have sums at most zero by induction because h is even,
nonnegative and the later drift maps are increasing. The function x*h(x) is
odd and increasing, so the mixed moment E[Xh(X)] is nonpositive. With eta<1,
the cross term in the second-moment expansion has the favorable sign. This
justifies the stronger slope-one variance lower recursion.

The second and fourth upper recursions follow from |f_t(x)|<=c_t|x| and
the symmetric bounded-noise moment expansion. The factor96 is exactly
6*16. The global lower bound h(x)>=x^2/2-x^4/3 follows by integrating
tanh(z)-z+z^3/3, whose derivative is z^2-tanh(z)^2>=0 for z>=0, and using
evenness. Combining its positive part with the variance lower and fourth
upper produces a valid lower bound on the negative mean at every step.

I independently implemented `root_check_bias.py` without importing the
producer's interval functions. It uses Q=2^42 rather than Q=2^44 and fuses
each recurrence into a one-sided rational polynomial before directed integer
rounding. Every gain enclosure is proved by its integer 100th-power
inequality. All one million steps were recomputed. The resulting lower bound is

    23081750376873377/4398046511104000000
      > .00524818 > .00524 = 1.31*(4/sqrt(1,000,000)).

The finer producer interval encloses a different conservatively rounded
recursion; the independent lower endpoint need not lie below its lower
endpoint. Both are valid bounds on the exact analytic recurrence. No
simulation or normal approximation enters either certificate.

## Empirical result and its verification limits

The count-first generator is exactly the iid Rademacher experiment: its
binomial count followed by uniform ordering assigns probability2^-n to each
original sequence. Conditional empirical resampling depends only on that
count, and uses separate random draws. Repetitions are independent under the
simulation law. The four methods share data and resampling to provide paired
controls; they are not four independent studies. The source's log1p/sinh
formula is algebraically log cosh(2x), and remains finite on the invariant
iterate range.

I loaded the bound `probe_outputs.npz`, SHA256
`83a9cdf7df452b6594bdcd6d215725d2ab3a0bfa00ec39740b2cd142e69653ed`,
and independently reconstructed all terminal events using squared intervals.
The counts are 405,486,486,486 out of512, with every retained mask matching.
The t3 CDF was checked with its elementary arctangent formula, and nonlinear
SAA roots were checked by a separate logaddexp expression. The producer's
saved-output checker also verifies outward Clopper--Pearson endpoints through
exact integer binomial inequalities; I reviewed that code and inequality
directions. Its confidence interval bounds Monte Carlo sampling uncertainty,
not implementation or model uncertainty.

I did NOT rerun the million-step stochastic trajectories with an independent
implementation, and do not describe the result as independently replicated
coverage. The independent million-step calculation is specifically the
deterministic bias recurrence. The fixed protocol, all512 outcomes and both
controls are retained. No tuning or new random experiment was performed in
this review.

The evidence removes the previous example's Hessian-Lipschitz5000 restriction:
the new constant is one. It retains a constructed asymmetric objective,
bounded noise of magnitude four, near-endpoint alpha and the specified finite
horizon. The mean theorem alone is insufficient to prove 79.1% coverage, and
classical nonlinear SGD bias remains an important prior-art boundary.
