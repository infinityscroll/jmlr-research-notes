# Complete-grid audit and interpretation

26 October 2026. **PASS for the complete descriptive grid, with the protocol-role correction and timing/numerical-stop qualifications below.** Use this version's [report](REGIME_REPORT.md), [released-primary grid](regime_grid_official_vs_inducing.pdf) and [all paired seeds](paired_seed_effects_official_vs_inducing.pdf). These are standalone scientific PNG/PDF artifacts, not a webpage.

## Completeness and independent verification

All fifteen shard audits passed before outcome processing. The historical independent source auditor, which imports neither the aggregator, shard auditor nor visualization code, verified the complete raw summaries for **270 selected models and 3,240 candidate trials**. It independently checked all 270 selected weight-file hashes, eligible validation minima, candidate order, saved selections, selection-before-test timestamps and source pins. Every aggregate seed-level test MSE, selected lambda and capacity agreed with the corresponding raw source model. The full raw weight/trial archive and that historical auditor are not included in this curated release; [the public verification runner](../../verify.py) recomputes the retained aggregate arithmetic and the separately released exact certificates and finite states.

The [saved audit](complete_source_and_timing_audit.json) recomputes paired means, sample standard errors and t4 intervals from the raw-source MSEs. Its largest difference from the independent visualization summary is 7.11×10^-15. Every one of the 18 regimes and all five seeds is retained. The [selected-model table](selected_model_hyperparameters.csv) records all 270 methods/regimes/seeds, their test MSEs and selected hyperparameters; 94 models selected a lambda endpoint.

The source confirms disjoint train/validation/test RNG streams shared across methods. Training sizes are nested within a seed. The same seed is also reused across kernels and noise settings, so regimes should not be treated as 18 independent replications or pooled into a winner score. The test stream is constructed after validation selection; source order, weight hashes and saved timestamp ordering support this claim, without constituting an independently trusted event logger.

## Protocol-role correction and preserved provenance

The frozen experimental [PROTOCOL](../../regime_replicates/PROTOCOL.md) makes **released ASkotchV2 versus inducing** primary and the corrected arm diagnostic. Version 1 followed an incorrect preparation instruction and reversed those labels. Version 2 restores the pre-existing protocol. No seed, test MSE, selection, hyperparameter, interval or comparison estimate changes: all 54 keyed comparison records, including every seed effect, compare exactly equal between the two summaries.

The [correction record](../protocol_role_correction.json) preserves the v1 renderer/freeze and original report hashes. The old report carries a prominent supersession notice and an exact original backup remains available. The v1 freeze's `actual_outcomes_read_before_freeze=false` refers only to the renderer author's inspection. The root had inspected the completed aggregate around 07:17 UTC, before the 07:19 renderer freeze; this was **not a globally blinded visualization preregistration**. The experiment and aggregation were frozen earlier. Version 2 is an explicitly post-outcome protocol-role and reporting correction.

The method called inducing PCG/Falkon is `InducingKRR` with `PCG(..., {'type':'falkon'})` from the same pinned `fast_krr` repository. It is not a claim that the separate official Falkon package was run. Both released and corrected full solvers use the same declared acceleration safeguard. The corrected arm changes the block-gradient regularizer evaluation; differences between its timed selected models and the released arm cannot be attributed solely to that code change because iteration counts and selections can also differ.

## What the primary grid shows

Released ASkotchV2 has lower mean selected-model test MSE in 13 of the 18 displayed regimes; inducing has lower means in five. These counts are descriptive, not a universal winner declaration. Of the 18 paired t4 intervals, 12 lie below zero, four above zero and two include zero. The intervals containing zero are n=2048, noise SD=0.3, for Matérn ν=2.5 and RBF. In particular, the released-primary RBF/high-noise/n=2048 interval crosses zero; the corrected diagnostic's corresponding interval does not, so those roles must not be interchanged.

The most stable observed pattern is lower released-method MSE in all six rough Matérn ν=0.5 regimes, with all five paired seeds favoring it in each. The inducing method has lower means in RBF at n=2048 and n=8192, and in low-noise Matérn ν=2.5 at n=8192. Noise and sample size matter, and some intervals are wide. The released-minus-corrected diagnostic has intervals containing zero in all 18 regimes; this does not establish absence of a correction effect, nor a systematic practical benefit. The separately established implementation defect is not inferred from these experiments.

Each interval is descriptive mean ± t_(4,.975)×sample-SD/√5, with only five paired replications. Relative effects are the mean of 100(L−R)/R across seeds, not the percentage difference of mean MSEs. There is no multiplicity adjustment, certified continuous crossover boundary, universal superiority theorem or publication-novelty conclusion. A lambda endpoint is unresolved tuning, not evidence that extending the grid would preserve the ranking.

## Nonfinite stops and unequal consumed time

The aggregate's empty `numerical_failure_outcomes` list covers candidate exceptions and absent eligible checkpoints. It does **not** mean there were no numerical stops. The independent raw audit finds eight inducing candidates stopping after a nonfinite iterate. Every one retained at least one earlier eligible finite checkpoint, and **none of the eight was selected**. All are n=8192, RBF, large inducing capacity:

| Seed | Noise SD | Lambda | Eligible checkpoints | Selected? |
|---:|---:|---:|---:|:---:|
| 11 | 0.05 | 1e-6 | 4 | No |
| 11 | 0.3 | 1e-6 | 2 | No |
| 23 | 0.05 | 1e-8 | 3 | No |
| 23 | 0.05 | 1e-6 | 3 | No |
| 23 | 0.3 | 1e-8 | 5 | No |
| 47 | 0.05 | 1e-6 | 4 | No |
| 47 | 0.3 | 1e-6 | 1 | No |
| 131 | 0.05 | 1e-8 | 3 | No |

| Method | Candidate trials | Stop counts | Mean measured seconds |
|---|---:|---|---:|
| Released ASkotchV2 | 1080 | 1080 budget | 4.007410 |
| Corrected ASkotchV2 | 1080 | 1080 budget | 4.007306 |
| Inducing PCG/Falkon | 1080 | 1020 residual tolerance, 52 budget, 8 nonfinite | 0.306008 |

The protocol equalizes **available four-second caps and twelve candidates**, not consumed wall time. Inducing left approximately 3.694087 seconds per candidate unused on average. Warmup is discarded and reported separately. Its stopping criterion uses the recursively maintained PCG residual; the audit does not replace that with a direct residual or certify numerical optimality. These facts constrain any runtime interpretation and were not used to retune or rerun the experiment.

## Visual verification

The full primary PNG grid and the PDF rasterization of its all-seed companion were visually inspected after the role correction. Labels, signs, units, all 18 regimes, all five seed points and uncertainty bars are readable. The secondary released-versus-corrected PNG was also inspected. Relative color/axis scales are explicitly symmetric-logarithmic, linear within ±1 percentage point; values and intervals remain printed numerically. No outcomes are removed because of their sign or uncertainty. Tight figure bounds and a pre-save layout draw are presentation-only changes in v2.

The final artifact hashes are recorded in [artifact_manifest.json](artifact_manifest.json). The input aggregate SHA-256 is `fdf88eddc2ef1dd92973306c4e58a327b198142fb640432deb58259ed33ee4a1`; the v2 renderer SHA-256 is `8ca8e8e45e993af25f9143251ab3acac9f9a028539c8477f3323061cd2121598`.
