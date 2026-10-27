# Cheap-bootstrap endpoint and calibration notes

This package studies the original cheap confidence intervals in
[Lam and Wang, JMLR 27(93), 2026](https://www.jmlr.org/papers/volume27/25-0008/25-0008.pdf).
It contains a proposed correction to the closed harmonic endpoint, a controlled
finite-sample experiment, and an analytic nonuniformity boundary near the
lower allowed gain exponent. These are research drafts, not accepted errata.

**Review status:** the mathematical reviews in this package were performed by
separate AI agents, with human-directed scope. They are internal checks, not
external expert review, author agreement, formal verification, or evidence of
historical priority. Read the assumptions and claim boundaries below before
using a result.

| Result | Established within the supplied work | What it does not establish |
|---|---|---|
| Harmonic endpoint correction | A bounded quadratic example has nominal-95% offline interval coverage at most approximately **0.100858% for every n** | No contradiction for a fixed exponent strictly between 1/2 and 1; no new method |
| Moderate-curvature fixed probe | **405/512 = 79.10%** empirical coverage at n=1,000,000; a separate deterministic negative-mean bound | The empirical coverage is not a finite-n coverage theorem |
| Triangular exponent boundary | A fixed smooth problem has a noncentral Student limit when the tuning exponent approaches 1/2 at logarithmic speed | No contradiction of pointwise fixed-exponent asymptotic validity |
| Nonlinear harmonic online regime | A conditional/joint Gaussian limit under a local spectral condition, including critical logarithmic scaling | No offline-bootstrap repair or finite-sample coverage bound; substantial classical antecedents |

## Start with the endpoint correction

[Full manuscript (LaTeX)](author_correction_v2/main.tex) gives a self-contained
proof and checks the published assumptions. The model is

\[
h(x,Z)=\tfrac12(x-Z)^2,\quad Z=\pm0.01\text{ equiprobably},\quad
x_0=1,\quad\eta_t=1/(4t).
\]

For the paper's offline averaged-SGD Algorithm 1, B=3 and nominal 95%,

\[
\Pr(0\in I_n)\le(1+\sqrt2\,t_{3,.975})^2/30000
\approx0.00100857488,\qquad n\ge1.
\]

The exact expression is a probability; its percentage is about 0.100858%.
The proof uses the persistent initialization contribution at the harmonic
endpoint. That phenomenon is classical; the proposed correction concerns its
inclusion in the printed coverage statement. The observations, initialization
and fourth moment are bounded. This is not a claim that arbitrary small-gain
SGD is a good practical choice.

The [rational verifier](author_correction_v2/bootstrap_exact_cleanroom.py)
checks finite identities and a conservative quantile-free bound. The analytic
proof supplies the all-n conclusion. All retained simulations and negative
controls remain in [endpoint_results.json](author_correction_v2/endpoint_results.json).
The [source map](author_correction_v2/source_map.json) pins the original paper
and code commit. The published Algorithm 1 and the pinned repository helper
use different centering/divisor formulas; the manuscript explains this
distinction. We test the printed algorithm, without attributing the helper
variant to every published experiment.

## A separate finite-horizon experiment with moderate curvature

The [report](moderate_curvature_gate_20261028/RESULTS.md),
[prespecified protocol](moderate_curvature_gate_20261028/PROTOCOL.md), and
[all retained outputs](moderate_curvature_gate_20261028/probe_outputs.npz)
use the fixed gradient

\[
g(x)=x+\tfrac14\log\cosh(2x),\quad Z=\pm4,\quad
\eta_t=.94t^{-.51},\quad x_0=0.
\]

Strong convexity is 1/2, smoothness is 3/2, the global Hessian-Lipschitz
constant is **1**, noise variance is 16, and its fourth moment is 256.
At n=1,000,000, B=3 and the original-centered RMS, the nonlinear interval
covers 405/512 repetitions. The outward Monte Carlo 95% confidence interval
is [75.318730%, 82.544433%]. The paired quadratic SGD and two same-data SAA
controls each cover 486/512. SAA is a diagnostic control, not a replacement
for the target estimator. All outcomes, including the controls, are retained.

A [separate proof](moderate_curvature_gate_20261028/moderate_curvature_bias_proposition.md)
and two independently implemented integer recurrences certify
`-E[F_n] > .00524` at the same horizon. This does **not** prove the 79.10%
coverage probability. The saved-output checks reconstruct every interval and
confidence endpoint, but are not an independent stochastic replication.
The near-boundary exponent, asymmetric objective and fixed horizon remain
material limitations. No practical prevalence or novelty claim follows.

## Exact boundary for a horizon-dependent exponent

The [triangular-array theorem](moderate_distribution_gate_20261028/triangular_exponent_coverage_theorem.md)
keeps that objective, noise, initialization, gain coefficient and algorithm
fixed. In a run of length n, use one exponent alpha_n throughout. If
`(alpha_n - 1/2) log n -> c >= 0`, then

\[
\left(\sqrt n F_n/4,\ \sqrt n(F_n^{*b}-F_n)/4\right)_{b=1}^B
\Rightarrow (U-\kappa_c,V_1,\ldots,V_B),\qquad
\kappa_c=(47/25)e^{-c},
\]

with independent standard normals. Each rerun is centered at the original
estimate, so the common optimization bias cancels from the radius and remains
in the center. For `alpha_n=1/2+1/(8 log n)`, B=3, the limiting nominal-95%
coverage is strictly below **111/125 = 88.8%**.

This is an asymptotic nonuniformity result over allowed exponents on one fixed
model. It does not certify that bound at n=1,000,000. The
[primary comparison](moderate_distribution_gate_20261028/primary_scope_comparison.md)
credits the established nonlinear-SA remainder and bootstrap-bias mismatch;
the specific uniform expansion and conditional empirical-bootstrap transfer
are the candidate contribution.

## Secondary positive theory: the unchanged online multiplier procedure

[Nonlinear harmonic theorem](nonlinear_harmonic_repair_20261027/nonlinear_critical_bootstrap_theorem.md),
[mean-square-continuity extension](nonlinear_harmonic_repair_20261027/mean_square_continuity_extension.md),
and [conditional consistency](nonlinear_harmonic_repair_20261027/conditional_bootstrap_consistency.md)
concern the **online** Exp(1) gradient multipliers, not offline resampling.
With globally strongly convex mean drift, appropriate global sample-gradient
regularity, a locally Holder Hessian, finite second-moment root noise, and
`eta lambda_min(H) >= 1/2`, the proof gives mixed sqrt(n/log n) and sqrt(n)
scales and the unchanged fixed-B Student pivot. The precise assumptions of
each extension are in its statement; they are not interchangeable.

The [critical scalar](critical_endpoint_20261027/critical_online_bootstrap_theorem.md)
and [SPD-spectrum](critical_endpoint_20261027/spd_critical_spectrum_bootstrap_theorem_20261027.md)
proof dependencies are included. Classical stochastic approximation,
localization and multiplier-bootstrap methods are credited in the
[comparison](nonlinear_harmonic_repair_20261027/primary_scope_comparison.md).
Conditional consistency was added after that historical comparison; its final
sentence about this point being unproved is superseded by the included
conditional-consistency note and audit. No finite-sample error bound is added.

## Bounded verification

Requires Python 3.10+ and NumPy. From the repository root:

```sh
python3 -m pip install -r bootstrap/requirements.txt
python3 bootstrap/verify.py
```

The default command checks release hashes, exact endpoint identities, the
saved 512-repetition probe, exact Monte Carlo confidence endpoints, the
limiting .888 inequality, and critical averaging identities. It also checks
the bindings and rational conclusions of the two retained million-step bias
certificates. It **does not recompute those million steps**, rerun Monte Carlo,
prove the CLTs, or establish novelty. Each subprocess has a time limit, and
all generated files go to a temporary directory.

To recompute both deterministic million-step bias certificates explicitly:

```sh
python3 bootstrap/verify.py --full-bias
```

This optional check is slower and still uses no random trajectories. The
original simulation scripts are included for transparency; do not run their
main programs to perform the bounded checks. The endpoint simulation script
would overwrite its result file, and the moderate probe intentionally refuses
to overwrite an existing run.

`main.tex` can be compiled with a standard LaTeX installation using its listed
packages. Compilation is not part of the Python verification.

## Provenance and review limits

[Copy provenance](copy_provenance.json) records original and release hashes.
All 43 curated source/result files are byte-for-byte copies; the portable
runner and this front page are new. [Packaging notes](PACKAGING_NOTES.md)
explain historical headers and omitted material. Primary PDFs, upstream code,
outreach drafts, credentials and machine-specific paths are not distributed.

Every file called an “independent audit” is an **AI-agent internal audit**.
Computational checks support finite identities and retained data; they do not
replace the mathematical arguments. Neither an author endorsement nor an
admissions, publication, or newsworthiness outcome is claimed.
