# Research proofs and reproducible notes

Substantial results and reproducible experiments through 2 November 2026.
These are research notes with explicit assumptions and limitations,
not accepted papers or claims of author endorsement.

## Preprint and partial Lean formalization

[The integrated preprint](preprints/negative-voting-simplex/output/pdf/negative_voting_simplex_preprint.pdf), by Jitendra Prajapati ([ORCID](https://orcid.org/0009-0008-7493-0311)), consolidates the large-alphabet negative-voting argument and its credited dependencies. [LaTeX sources and submission notes](preprints/negative-voting-simplex/README.txt) and a [upload bundle with proof companions](archives/negative-voting-simplex-arxiv-source-2026-11-02.tar.gz) include the supporting analytic proof files. This is a GitHub preprint package; it has not been submitted to arXiv.

[The Lean project](formalization/negative-voting/README.md) proves the actual Gaussian noise expansion, its mass/centroid/quadratic terms, regular-reference identities, the exact affine-reference comparison, prescribed Gaussian fan masses and their actual offset Jacobian, quantitative polyhedral covariance bounds, and Gaussian trace/facet estimates. Its attributed dependencies now also include OpenAI's smooth Ehrhard proof and Tau Ceti's singular Schur-complement calculus; the [reuse ledger](formalization/negative-voting/REUSE_SEARCH_20261102.json) records the source revisions and exact scope. CI rebuilds the pinned project and audits every compiled first-party theorem by source module, including generated helpers. **The complete negative-voting theorem remains unproved in Lean.** The remaining obligations concern Gaussian covariance/offset geometry, quantitative trace and cap assembly, and uniform localization. See the [coverage ledger](formalization/negative-voting/COVERAGE.md) and [standalone source archive](archives/negative-voting-lean-2026-11-02.tar.gz).

## 2 November — integrated negative-voting proof

[The integrated manuscript](frontier/negative-voting-simplex/supplements/integrated-full-voting-proof-20261102/MAIN_THEOREM_INTEGRATED_PROOF_20261102.txt) presents a proposed proof of regular-simplex optimality throughout the negative voting interval for every sufficiently large alphabet, in every finite ambient dimension N >= m-1, allowing fractional rules and unequal masses. Its consequence is negative Plurality Is Stablest and the **exact fixed-alphabet Frieze–Jerrum MAX-m-CUT threshold**, with UGC retained for hardness.

[Current proof reconstructions](frontier/negative-voting-simplex/supplements/integrated-full-voting-proof-20261102/README.txt) cover localization, both noise branches, singular covariance limits, equality and the single uniform alphabet threshold. The mass-envelope proof still uses the explicitly reconstructed cycle-refined Ehrhard estimate; the Hodge proof does not replace that stronger input. This is a complete internally audited proof manuscript. **External expert review remains pending.** The threshold is existential, and the full all-alphabet conjecture is not claimed solved.

## Immutable release snapshots

[The release workflow](RELEASING.txt) publishes verified source snapshots, the main manuscript PDF, checksums and signed build provenance after trusted main-branch verification. Published release assets and their tags are immutable. The public Sigstore record and GitHub publication time establish artifact identity and publication history; they do not establish mathematical validity or exclusive research priority.

## 2 November — Gaussian stability beyond the voting range

[The new candidate theorem](frontier/negative-voting-simplex/supplements/beyond-voting-range-20261102/README.txt) extends the negative Gaussian interval to magnitude at most m^(-7/8)/(1+log m)^2 for every sufficiently large alphabet. This eventually exceeds the voting cutoff 1/(m-1) by a factor tending to infinity. It retains a quantitative bound on Gaussian-L1 distance to the regular simplex and allows arbitrary measurable fractional rules and unequal masses.

[Final proof](frontier/negative-voting-simplex/supplements/beyond-voting-range-20261102/QUANTITATIVE_NEGATIVE_SIMPLEX_BEYOND_THE_VOTING_INTERVAL_V2_20261102.txt) · [Mass review](frontier/negative-voting-simplex/supplements/beyond-voting-range-20261102/mass/WIDER_V2_FINAL_MASS_ASSEMBLY_REVIEW_20261102.txt) · [Proxy/exterior review](frontier/negative-voting-simplex/supplements/beyond-voting-range-20261102/proxy/WHOLE_WIDER_RANGE_V2_REVIEW_AND_SIGN_CORRECTION_20261102.txt) · [Local/L1 review](frontier/negative-voting-simplex/supplements/beyond-voting-range-20261102/local/FINAL_V2_WIDER_RANGE_LOCAL_SCOPE_AND_L1_REVIEW_20261102.txt)

[An independent hazard certificate](frontier/negative-voting-simplex/supplements/independent-hazard-certificate-20261102/README.txt) now reconstructs the central structured derivative estimate directly from Gaussian integrals, including the moving offsets and all threshold tails. It covers a larger variance box and mixed perturbations; the original proof sources remain unchanged.

[The independent Hodge proof now uses established regularity inputs](frontier/negative-voting-simplex/supplements/classical-hodge-normal-strain-20261102/README.txt) and also proves the quantitative finite-simplex curvature bound needed by the negative-voting argument. A reciprocal-coordinate reduction removes its earlier September 2026 preprint dependency. The new facet-measure and barrier proofs have independent internal audits; the prior Hodge checker retains its 1,603 exact algebra checks. An accompanying endpoint-only transfer note makes the fixed-alphabet UGC consequence and error choices explicit.

Three internal reviews support the revised assembly. Its new ingredients handle empty labels, construct the equal-row comparison without individual row lower bounds, and extend the local proof to the larger range. **External mathematical validation and priority remain open.** The threshold is existential, the full conjecture remains open, and the discrete voting channel retains its original cutoff.

## 1 November — global stability for large alphabets

[A quantitative stability supplement](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/README.txt) strengthens the negative-voting candidate: for every sufficiently large alphabet, a nearly optimal measurable rule must be close to a regular simplex, with constants independent of ambient dimension. The proof permits unequal winning probabilities and fractional rules.

[Sharper theorem and proof](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/linear_threshold/LINEAR_NOISE_THRESHOLD_GLOBAL_STABILITY_SUCCESSOR_20261101.txt) · [Full earlier derivation](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/GLOBAL_QUANTITATIVE_NEGATIVE_VOTING_STABILITY_20261101.txt) · [Mass/slack review](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/linear_threshold/LINEAR_SUCCESSOR_FINAL_MASS_REVIEW_20261101.txt) · [Covariance review](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/linear_threshold/COVARIANCE_PROXY_EXTERIOR_REVIEW_20261101.txt) · [Full stability review](frontier/negative-voting-simplex/supplements/global-quantitative-stability-20261101/linear_threshold/LINEAR_THRESHOLD_LOCAL_CAP_AND_L1_INDEPENDENT_REVIEW_20261101.txt)

The fourth-power Gaussian-L1 bound, including its sharper threshold linear in the noise magnitude, has passed three internal reconstructions and inherits the main proof's dependencies. Its alphabet threshold is existential. **External mathematical validation and priority remain open.** The original manuscript and archive are preserved; the supplement includes two proof clarifications and an explicit obstruction to removing the row cap.

## 1 November — tetrahedral local stability

[The tetrahedral endpoint package](frontier/negative-voting-simplex/local-stability-four-candidates/NONLINEAR_LOCAL_THEOREM_READING_GUIDE_20261101.txt) proves **local Gaussian-L1 quadratic stability for arbitrary measurable matched-mass pairs in every fixed finite dimension N >= 3**. At correlation -1/3, the objective exceeds the tetrahedral value by at least the squared distance to its common orthogonal orbit divided by 1000, in a sufficiently small neighborhood. The common mass vector may vary. Reflection gives the equivalent correlation 1/3 statement near opposite tetrahedral partitions.

[Measurable proof in R3](frontier/negative-voting-simplex/local-stability-four-candidates/ARBITRARY_MEASURABLE_LOCAL_STABILITY_VIA_TRANSFER_COMPACTNESS_R3_20261101.txt) · [All finite dimensions](frontier/negative-voting-simplex/local-stability-four-candidates/ARBITRARY_MEASURABLE_LOCAL_STABILITY_ALL_FINITE_DIMENSIONS_SUCCESSOR_20261101.txt) · [Certified Hessian input](frontier/negative-voting-simplex/local-stability-four-candidates/THEOREM_AND_PROOF_ACCEPTED_20261101.txt)

The proof combines the certified Hessian gap of 8/25 with an analytic transfer-compactness argument. It imposes no smoothness or stationarity assumption on competitors. The neighborhood may depend on dimension; its numerical radius is not supplied. **Global four-label optimality remains open.** Reviews are internal; novelty and external verification remain open.

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

Python 3.12 is used for reproducible verification. Install the CPU dependencies:

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
