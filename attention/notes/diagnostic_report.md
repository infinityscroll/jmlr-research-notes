# Fixed diagnostic and retained-state verification

28 October 2026. These runs preceded the complete invariant-basin proof. They are diagnostics, not numerical proof of the asymptotic theorem or a certified instance of its initialization basin.

The working derivation and `diagnostic_protocol.json` fixed both cases before execution: query tokens `(1,0),(delta,1)` for delta=0 and delta=1/2, identity values, two unmasked self-attention layers, fixed head e1, paired positive/negative examples, full direct matrices, released SMD with p=2 and step .1, 50,000 simultaneous steps. Both start with logits `(4,-4)` and upper projection `(4,0)`, choosing their minimum-norm matrices. No randomization, seed selection, discarded cases, or outcome-dependent tuning was used. The two cases are independent batched problems, not two examples sharing the same trained matrices.

The optimizer file was imported unchanged from the official repository, SHA256 `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`. The run's maximum discrepancy between the full native autograd gradients/prediction and the independently written reduced expressions was `2.220446049250313e-16`. All 173 retained checkpoints include both full matrices for both cases in `diagnostic_states.npz`.

| Case | Final lower selected-margin fraction | Final upper selected-margin fraction | Memory distance | Lower logits |
|---|---:|---:|---:|---|
| delta=0 | 0.8788055689754964 | 0.999998172891994 | 1.3949086812881986 | (7.932462197155288, -4.307224040517468) |
| delta=1/2 | 0.7227174727898438 | 0.9999990165713967 | 1.0669965740983893 | (6.7233863295506495, -3.06796365599095) |

The delta=0 control's finite lower fraction is also below one. Finite time therefore does not distinguish the proposed asymptotic mechanisms by itself. Neither row is advertised as already reaching a theoretical limit. In particular the delta=1/2 theorem predicts `2/sqrt(5)` for its proved late basin, not the displayed finite number. The proof supplies an existence threshold R0 and does not establish that the diagnostic z=4 meets it.

`check_algebra_and_retained_states.py` performs no training and imports no producer functions. It independently recomputes the complete two-layer predictions, actual SVM margin fractions, memory geometry, signed-copy identity and conserved irrelevant matrix components from the saved matrices. All 4,844 scalar comparisons passed, maximum discrepancy `2.6645352591003757e-15`; conserved-gauge error was at most `5.773159728050814e-15`. The checker also verifies the rational Lyapunov identity, positivity bounds on P, exact coupled-update combinations and exact fixed-theorem margin algebra using `Fraction`.

Its certificate binds the proof, protocol, producer, released optimizer, result file and saved states. These checks substantiate the implementation/interface and retained data. They do not certify the uniform remainder estimates, invariant basin or infinite-time theorem, which require separate analytic review. No further trajectories were run after inspecting these outcomes.
