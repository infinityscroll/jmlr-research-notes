# Proof dependencies and reading order

The top-level claims are the no-feedback completeness statement and its separated-terminal-receiver extension. None of the finite certificates substitutes for a proof below. All included review documents are internal AI reviews.

| Step | Source | What is imported |
|---|---|---|
| 1 | [Positive multimode hedge](binary_selected/general_positive/multimode_hedge/theorem.md), Sections 1–4 | Positive flat observationally equivalent models and selected-outcome separation, including directed re-entry. |
| 2 | [Joint target corollary](binary_selected/general_positive/multimode_hedge/joint_target_corollary.md) and [capacity construction](binary_selected/general_positive/hidden_capacity_attack/capacity_compression_v2.md) | Selected joint outcomes and finite hidden-state realization. |
| 3 | [Private-switch completeness](prescribed_unit_structure_gate_20261028/private_switch_completeness.md) | Lift to a prescribed original HCM unit graph, actual policy support, and complete observational-law equality. |
| 4 | [Multiple policies](multiple_private_switch_gate_20261028/multiple_policy_completeness.md) | Independent local switches for simultaneous unconditional product policies. |
| 5 | [Positive alphabet refinement](alphabet_refinement_gate_20261028/positive_finite_alphabet_refinement.md) | Arbitrary prescribed finite observed alphabets, preservation of the complete queried table and selected event. |
| 6 | [Integrated no-feedback theorem](alphabet_refinement_gate_20261028/COMPLETENESS_FRONTIER.md) | Exact combined class, quantifiers, and exclusions. |
| 7 | [Separated terminal receivers](terminal_receiver_completeness_gate_20261028/separated_receiver_completeness.md) | Support transport and receiver-by-receiver necessity for an actual unit-outcome distribution. |

The terminal [exact controls and boundary](terminal_receiver_completeness_gate_20261028/exact_controls_and_boundary.md) distinguish a nontrivial identifiable receiver, nonidentification, separate received marginals, and failure once a hidden cause spans the upstream and downstream blocks.

## Internal reviews

- [Single switch](prescribed_unit_structure_gate_20261028/independent_private_switch_audit.md).
- [Multiple policies](multiple_private_switch_gate_20261028/independent_multiple_policy_audit.md).
- [Finite alphabets](alphabet_refinement_gate_20261028/independent_finite_alphabet_refinement_audit.md).
- [Terminal receiver theorem](terminal_receiver_completeness_gate_20261028/independent_separated_receiver_audit.md).

These reports bind exact source hashes and describe what their reviewers checked. “Independent” means a different AI agent, not an external mathematical referee.

## Historical references outside the claim closure

The multimode manuscript's Section 5 points to older fixed-policy encoding and continuous-lift manuscripts, and to an earlier routing-obstruction note. The current private-switch theorem explicitly imports only Sections 1–4, and supplies its own HCM lift. Those older links are archival references, not missing premises of this package; the historical HCM claim in Section 5 is not promoted here. Likewise the terminal manuscript lists older reset and finite-codebook criteria as comparisons, not dependencies.

The public package keeps the source text and its original hashes intact instead of silently rewriting that history. All proof dependencies used in Steps 1–7 are present. Primary publications are cited by links in the manuscripts, not redistributed.
