# Complete replicated kernel regime grid — protocol-primary revision

**Version 2 correction:** the frozen [PROTOCOL](../../regime_replicates/PROTOCOL.md) designates released ASkotchV2 versus inducing as primary and corrected ASkotchV2 as diagnostic. Version 1 followed an incorrect preparation instruction that reversed those roles. This version restores the protocol roles; no MSE, seed, interval, selected model, hyperparameter or comparison estimate changes. The old renderer, freeze and figures are preserved. See the [correction record](../protocol_role_correction.json).

Implementation names: the inducing comparator is the same pinned fast_krr repository’s InducingKRR and PCG with its Falkon preconditioner, not a claim to execute the separate official Falkon package. The released and corrected full solvers use the same frozen acceleration safeguard; the corrected arm changes the stale block-regularizer evaluation. Figure labels identify these frozen code paths.

All 15 shard audits passed before this analysis read the aggregate: 18 regimes × five seeds = 90 seed-specific cells, with three selected models per cell (270 models). All regimes and seeds are retained in protocol order.

The protocol-primary contrast is released ASkotchV2 minus inducing PCG/Falkon on selected-model test MSE. For each seed, d=L−R and r=100(L−R)/R. The displayed relative effect is the mean of the five seedwise percentages, not a ratio of mean MSEs. Negative values mean lower MSE for the left method.

Each interval is mean ± 2.7764451051977987 × sample-SD/√5, calculated separately for d and r. These are descriptive paired-t₄ intervals with only five replicates; their nominal interpretation needs appropriate independence and distributional assumptions. There is no multiplicity correction across the 18 regimes, no interpolated crossover boundary, and no universal superiority claim. Comparisons within a seed use paired test streams; different regimes are not pooled into a winner score.

Each method was offered the same frozen search: 12 candidates with 4 synchronized seconds per candidate, including fresh measured construction and selection work. Symmetric discarded warmup was recorded separately. This is warmed implementation performance, not cold end-to-end timing. A method may stop early and leave available time unused. Selected models were frozen before test creation according to the shard audits; those audits qualify the timestamp/source-order evidence.

## Primary comparison: every regime

| n | Kernel | Noise SD | Mean ΔMSE [t₄ interval] | Mean relative % [t₄ interval] | Left smaller / 5 |
|---:|---|---:|---:|---:|---:|
| 512 | Matérn ν=0.5 | 0.05 | -5.7131e-02 [-6.606e-02, -4.820e-02] | -25.128% [-29.476, -20.780] | 5 |
| 512 | Matérn ν=0.5 | 0.3 | -5.0981e-02 [-5.731e-02, -4.465e-02] | -15.578% [-17.566, -13.589] | 5 |
| 512 | Matérn ν=2.5 | 0.05 | -3.3718e-02 [-4.004e-02, -2.740e-02] | -27.803% [-32.846, -22.760] | 5 |
| 512 | Matérn ν=2.5 | 0.3 | -1.9701e-02 [-2.853e-02, -1.088e-02] | -7.929% [-11.561, -4.297] | 5 |
| 512 | RBF | 0.05 | -1.6428e-02 [-2.191e-02, -1.094e-02] | -15.776% [-20.712, -10.839] | 5 |
| 512 | RBF | 0.3 | -3.4990e-03 [-6.219e-03, -7.794e-04] | -1.550% [-2.753, -0.347] | 5 |
| 2048 | Matérn ν=0.5 | 0.05 | -2.4998e-02 [-3.089e-02, -1.911e-02] | -28.323% [-32.925, -23.720] | 5 |
| 2048 | Matérn ν=0.5 | 0.3 | -1.7586e-02 [-2.171e-02, -1.347e-02] | -9.420% [-11.313, -7.526] | 5 |
| 2048 | Matérn ν=2.5 | 0.05 | -3.0947e-03 [-4.393e-03, -1.796e-03] | -7.322% [-9.863, -4.782] | 5 |
| 2048 | Matérn ν=2.5 | 0.3 | -1.3633e-03 [-5.451e-03, +2.724e-03] | -0.829% [-3.411, +1.753] | 3 |
| 2048 | RBF | 0.05 | +1.5288e-02 [+9.224e-03, +2.135e-02] | +38.677% [+23.442, +53.913] | 0 |
| 2048 | RBF | 0.3 | +3.1961e-03 [-3.190e-03, +9.582e-03] | +1.880% [-1.948, +5.709] | 1 |
| 8192 | Matérn ν=0.5 | 0.05 | -9.4024e-03 [-1.028e-02, -8.527e-03] | -26.982% [-28.813, -25.151] | 5 |
| 8192 | Matérn ν=0.5 | 0.3 | -4.6988e-03 [-5.367e-03, -4.031e-03] | -3.553% [-4.049, -3.058] | 5 |
| 8192 | Matérn ν=2.5 | 0.05 | +3.8576e-03 [+2.785e-03, +4.930e-03] | +25.970% [+18.033, +33.907] | 0 |
| 8192 | Matérn ν=2.5 | 0.3 | -3.3254e-03 [-5.572e-03, -1.078e-03] | -2.609% [-4.364, -0.854] | 5 |
| 8192 | RBF | 0.05 | +9.7349e-03 [+1.869e-04, +1.928e-02] | +38.546% [+0.770, +76.322] | 1 |
| 8192 | RBF | 0.3 | +1.0612e-02 [+3.668e-03, +1.756e-02] | +8.381% [+2.961, +13.802] | 0 |

[Primary regime grid](regime_grid_official_vs_inducing.pdf) · [All paired seeds](paired_seed_effects_official_vs_inducing.pdf)

## Separate implementation diagnostics

The [corrected-minus-inducing grid](regime_grid_corrected_vs_inducing.pdf) and [released-minus-corrected grid](regime_grid_official_vs_corrected.pdf) retain the same 18 regimes and five paired seeds. They describe the frozen implementations. Their differences cannot be attributed solely to the block-gradient correction because timed iteration counts and selected settings may also differ. They do not establish a theorem about either algorithm, and the correction's theoretical projection bounds are not certified by this benchmark. Color scales are shared within each figure/metric, not across different comparison figures.

The aggregate records 0 candidate-exception or missing-eligible-checkpoint records. This narrow field does not count nonfinite iteration stops: the complete raw-source audit found eight inducing trials that stopped on a nonfinite iterate; every one retained an earlier eligible checkpoint, and none of the eight candidates was selected. All eight were n=8192, RBF, large capacity, at lambda 1e-8 or 1e-6. They remain in the raw results. Across all 270 selected models, 94 selected a lambda endpoint, which remains unresolved tuning.

The raw timing audit records 1,020 inducing residual-tolerance stops, 52 budget stops and eight nonfinite stops. Mean measured candidate time was 0.306008 seconds for inducing, 4.007410 seconds for released ASkotchV2 and 4.007306 seconds for corrected ASkotchV2. Thus the experiment equalizes available four-second caps and candidate counts, not consumed wall time. Inducing left about 3.694087 seconds per candidate unused on average. Warmup is separate. Residual-tolerance stopping uses the recursively maintained PCG residual, not an independent direct residual or optimality certificate. [Full stop/timing audit](../complete_source_and_timing_audit.json).

## Reproducibility

[Complete aggregate](../aggregate.json) · [Independent summary](regime_summary.json) · [All 54 comparison rows](regime_summary.csv) · [All 270 paired seed effects](paired_seed_effects.csv)

Aggregate SHA-256: `fdf88eddc2ef1dd92973306c4e58a327b198142fb640432deb58259ed33ee4a1`.

Analysis source SHA-256: `8ca8e8e45e993af25f9143251ab3acac9f9a028539c8477f3323061cd2121598`.

The independent summary recomputes differences and t intervals from aggregate.raw_seeds and checks them against the aggregator. It also checks cross-comparison MSE/selection consistency, all 270 model identities, and all 15 passed shard-audit metadata records. No partial cell/trial outcome file is used.
