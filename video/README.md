# Video scheduler study: the prespecified result is inconclusive

128 held-out prompts, four selected schedules, 512 rollouts and 128 reference
clips were analyzed under the frozen protocol. The sole primary contrast,
descending minus ascending in late-minus-early KVD, is **-14.5996**, with an
approximate paired 95% percentile interval **[-76.2714,184.9560]**.

This establishes neither a successful no-rollout ranking rule nor a ranking
counterexample. The measured denoising proxies and KVD are not the paper's
KL error quantities. Secondary FVD and exploratory comparisons do not replace
the prespecified result. Six windows of a video are repeated observations,
not additional independent prompts.

## Reproduce the statistical result

This public package releases the complete extracted feature arrays, all
reported metrics, the pre-outcome protocol and schedule selection, and the
frozen count-weighted KVD implementation. It does not redistribute the
multi-gigabyte generated clips, model weights or source dataset. Their
original hashes remain in the retained provenance; this is a feature-level
reproduction package, not a new end-to-end generation run.

```sh
python video/verify.py
```

Requires Python 3.11+ and NumPy. NumPy 2.3.5 was used for the original analysis.
The command verifies feature/protocol/metric hashes and recomputes all 24
KVD point estimates, the primary contrast and all paired intervals using
the original 2,000 draws and seed. It neither launches GPU work nor chooses
schedules from held-out outcomes. Secondary FVD is retained as descriptive;
this bounded check does not recompute its eigendecompositions.

The intervals use shared prompt resamples across schedules/windows and an
independent shared reference resample. Repeated bootstrap indices are retained
correctly in the unbiased cubic-kernel U-statistic. There is no clipping,
multiple-comparison correction or claim that percentile intervals are exact.
The model ran the pre-outcome FP16 serial revision, not official-default FP32.

See [metrics](final_analysis/completed_study/metrics.json),
[protocol](final_analysis/completed_study/evidence/protocol.json), and
[selection](final_analysis/completed_study/evidence/selection.json).
This is a preserved negative/inconclusive study, not a claimed breakthrough.
