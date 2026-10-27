# Statistical and computational proof closure

All links below are included research sources. Review files are internal AI reviews. Exact finite checks support algebraic seams, not universal probabilistic conclusions.

## Main results

| Claim | Source and review |
|---|---|
| Adaptive upper, unknown anchor strength and mixture diversity | [Theorem A](joint_adaptation_gate_20261028/joint_adaptive_upper.md); [internal root review](joint_adaptation_gate_20261028/root_adaptive_upper_audit.md) |
| Matching fixed-vocabulary constrained adaptation lower | [Paired-sign lower](joint_adaptation_gate_20261028/paired_sign_constrained_lower.md); [internal review](joint_adaptation_gate_20261028/independent_paired_sign_lower_audit.md) |
| Computational replacement of maximum-volume enumeration | [Selector theorem](efficient_joint_adaptation_gate_20261028/design_compression_selector_theorem.md); [internal review](efficient_joint_adaptation_gate_20261028/independent_design_compression_audit.md) |
| Known-strength common-class minimax law for every N | [Matched frontier](anchor_selection_frontier_20261028/MATCHED_ALL_N_FRONTIER.md), with bound upper/lower sources listed there |

## Upper-bound chain

1. [General-K spectral factorization and affine geometry](multitopic_frontier_gate_20261027/general_k_upper.md).
2. [Dimension-uniform Hilbert moment proof](multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md) and its [internal audit](multitopic_frontier_gate_20261027/independent_root_growing_vocabulary_upper_audit.md).
3. [Sparse output reconstruction](weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_upper.md) and [observable diversity threshold](weak_sparsity_frontier_gate_20261028/observable_conditioning_threshold.md), with [joint internal audit](weak_sparsity_frontier_gate_20261028/independent_sparse_upper_and_observable_threshold_audit.md).
4. [Localized short-document argument](anchor_selection_frontier_20261028/short_document_sharp_log_upper.md), upgraded by [the all-N Bernstein theorem](anchor_selection_frontier_20261028/all_document_lengths_bernstein_upper.md) and its [internal audit](anchor_selection_frontier_20261028/independent_all_document_lengths_upper_audit.md).
5. The earlier [empirical-frequency maximum lemma](adaptive_anchor_oracle_20261027/empirical_frequency_maximum_lemma.md), [adaptive geometry](adaptive_anchor_oracle_20261027/adaptive_estimator_and_constrained_frontier.md), and [known-strength core proof](anchor_strength_continuum_20261027/known_strength_minimax.md) supply the explicitly identified geometric and probability ingredients. The latest adaptive theorem supplies the weak-diversity/all-N composition; it is not obtained by silently substituting parameters into these older fixed-conditioning statements.
6. [Penalized greedy recovery](adaptive_greedy_recovery_20261027/penalized_successive_projection_theorem.md) and its [classical SPA reduction](greedy_decisive_prior_gate_20261027/classical_spa_contraction_reduction.md) explain the algorithmic antecedent. The latest [selector theorem](efficient_joint_adaptation_gate_20261028/design_compression_selector_theorem.md) supplies the new exact-arithmetic guarantee using observable coordinates.

## Lower-bound chain

- [General-K full-document information](multitopic_frontier_gate_20261027/general_k_lower.md) and [growing-vocabulary family](multitopic_frontier_gate_20261027/growing_vocabulary_lower.md).
- [Weak-sparsity tail construction](weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_lower.md), including its [internal audit](weak_sparsity_frontier_gate_20261028/independent_weak_sparsity_lower_audit.md).
- [Unknown-anchor location family](anchor_selection_frontier_20261028/unknown_anchor_short_document_lower.md), [all-N short-information proof](anchor_selection_frontier_20261028/unknown_anchor_short_regime_all_N_lower.md), and [long-information proof](anchor_selection_frontier_20261028/unknown_anchor_long_document_lower.md). Their common-class combination is stated explicitly in the matched frontier.
- The latest [paired-sign constrained lower](joint_adaptation_gate_20261028/paired_sign_constrained_lower.md) uses a distinct prior for which every deterministic nuisance matrix is admissible. It is a lower bound on adaptation under a uniform strong-anchor risk requirement, not the unrestricted known-alpha minimax theorem.

## What is not claimed by the package

The reproducibility suite does not execute the full statistical estimator or estimate its practical sample complexity. It verifies exact finite identities used in the manuscripts. Primary sources are linked, not redistributed. Earlier manuscripts' references to other historical portfolio branches are comparisons unless listed above as proof imports; those branches are not additional public claims here.
