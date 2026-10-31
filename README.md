# Research proofs and reproducible notes

Substantial results and reproducible experiments through 31 October 2026.
These are research notes with explicit assumptions and limitations,
not accepted papers or claims of author endorsement.

## New results — 31 October

| Result | Scope | Review status |
| --- | --- | --- |
| [Negative Plurality and Gaussian simplex stability](frontier/negative-voting-simplex/PUBLICATION_NOTE.txt) | Exact negative-voting-range simplex optimality without mass constraints for every sufficiently large number of parts; negative Plurality is Stablest and the exact Frieze–Jerrum MAX-m-CUT threshold under UGC. | Complete internally audited proof candidate: 20-page manuscript, 34-source dependency companion, separate proof/content reviews. Existential m0; external verification and exhaustive priority clearance remain outstanding. |
| [Gaussian covariance concavity and simplex optimality](frontier/gaussian-simplex/README.md) | A covariance theorem for every finite-dimensional target with finite second moment; balanced first-moment optimality for every cell count, both-sign near-zero noise results, and a separately audited quadratic Gaussian-bubble stability consequence. | Complete manuscript, three internal analytic audits, assembly audits and two exact checkers. The full positive range and the remaining cases outside the new large-m negative-voting result remain open. |
| [Gaussian quantization landscape](frontier/gaussian-simplex/supplements/quantization-landscape/README.md) | For arbitrary prescribed positive masses and `N >= m - 1`, every local minimum is global; every distinct nonglobal stationary configuration is a strict saddle. | Audited corollary of covariance concavity, with an exact lower-dimensional counterexample. No Lloyd convergence or empirical-data claim. |
| [Marcus inequality for three blocks](frontier/marcus-three-blocks/README.md) | Every block size and every complex PSD Gram rank. | Complete proof, independent derivation and exact checks. The arbitrary-block conjecture remains open. |
| [Coupled cactus causal models](frontier/causal-cactus/README.md) | Exact generic real-fiber count for the declared coherent cactus class, including cross-component error correlations. | Scoped technical note with audited proof and exact checks. Earlier-literature overlap remains unresolved. |
| [Gaussian polynomial independence](frontier/gaussian-polynomial-independence/README.md) | A compact extremal critical-fiber obstruction allowing arbitrary degeneracy. | Scoped analytic lemma and root audit. The full U-conjecture remains open. |

The new negative-voting candidate is available as a [20-page manuscript](frontier/negative-voting-simplex/output/pdf/negative_gaussian_simplex_stability_v2.pdf) and a [complete review archive](archives/negative-voting-simplex-review-2026-10-31.zip).

A [1 November supplement](frontier/negative-voting-simplex/supplements/endpoint-and-foundation-20261101/README.txt) credits the known FJ endpoint formula and supplies an exact covariance-Hessian remainder. The theorem remains a candidate for sufficiently large alphabets; the full named conjectures are not claimed solved.

The Gaussian covariance, negative-voting simplex, and Marcus packages include readable PDFs and preserve
their frozen manuscripts, proof sources, audit records and checksums. Downloadable archives
are in [archives/](archives/).
All independent internal reviews are **AI-agent reviews**, not external expert
endorsement. Publication records the work; it does not settle its novelty or
newsworthiness.

## Original six-project release — 28 October

| Project | Main result | What it establishes |
| --- | --- | --- |
| [Attention](attention/README.md) | A selected-token margin obstruction at depth two for every fixed \(p>1\) | Exact discrete mirror-descent dynamics on an open input class and a finite open initialization basin; both layers train and memories remain distinct. A separate \(p=2\) example satisfies the source's initial layerwise cones. |
| [Hierarchical causal models](hierarchical/README.md) | Supported-policy identification completeness on specified subclasses, including separated terminal receivers | Positive nonparametric identification arguments and counterpairs. The general shared-latent receiver problem remains open. |
| [Cheap bootstrap](bootstrap/README.md) | Harmonic-endpoint correction, finite nonlinear bias, and a tuning-exponent boundary | Exact coverage obstructions and their assumptions, separated from retained finite simulations and previously known stochastic-approximation phenomena. |
| [Sparse topics](topics/README.md) | Joint adaptation to weak anchors and topic diversity, with a computable selector and constrained lower bound | Short-document rates under exact-anchor and strong-geometry assumptions; a restricted connection to a published 2020 open question. |
| [ASkotch / kernels](kernel/README.md) | A complete regime map and an exact mean-square instability/repair mechanism | Matched available search budgets; a separate highly ill-conditioned default-recipe construction. Finite float64 stress runs converged. |
| [Video diffusion](video/README.md) | A completed 512-rollout study with an inconclusive primary comparison | Preserves the negative result and reproduces its feature-level statistics. No scheduler-ranking success or theorem counterexample is claimed. |

The attention result concerns a **natural extension** of a one-layer theorem.
It does not refute that published theorem. The extra lower-layer constraint
arises from a token path whose attention vanishes but whose accumulated
gradient still changes the trained direction. The notes distinguish the
actual selected-query comparator from stronger auxiliary margin definitions.

## Verification

Python 3.11 or later is recommended. Install the small CPU dependencies:

```sh
python -m pip install -r requirements.txt
python verify_release.py
```

The default checks cover both the original six projects and the new theorem
packages, using saved evidence and bounded exact/numerical algebra.
They do not launch cloud jobs, retrain a video model, rerun a benchmark, or
overwrite released results. Optional native PyTorch interface checks and
training reproduction are documented in the attention package.

Passing these checks is **not** formal verification of the analytic proofs.
Each project states what is checked, what is assumed, and what remains open.
The release manifest binds every published file; source-provenance records
distinguish unchanged research artifacts from portable release wrappers.

## Research status and attribution

This work was developed with AI assistance. The saved independent internal
reviews were performed by separate AI-agent runs; they are not external
expert review. Historical novelty remains provisional. Classical ingredients,
prior related results and failed approaches are credited in the comparisons.
The notes do not claim that any cited author has reviewed or endorsed them.

Third-party papers, model weights, dependency installations and bulk upstream
repositories are not redistributed here. Pinned source URLs and hashes identify
the implementations used. Generated scientific figures, retained numerical
artifacts and our proof/checking code are included where needed.

The earlier [Isolation Forest ranking-reversal release](https://github.com/infinityscroll/iforest-depth-rank-reversal)
is a separate repository and remains a narrowly scoped verified counterexample.

The research program is ongoing. This release records the substantial work
without treating an artifact count, an internal audit or a favorable benchmark
as evidence of a newsworthy breakthrough.
