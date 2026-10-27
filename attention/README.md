# Selected-path margin failure in two-layer attention

This research note gives an analytic counterexample to a natural layerwise extension of *Optimizing Attention with Mirror Descent*: for every fixed **p > 1**, two jointly trained self-attention layers can select the intended tokens while the lower layer's direction remains strictly below its **selected-query global ℓp token-SVM optimum**. The intermediate tokens converge to distinct limits, and the optimal margin scales remain positive.

Both full direct attention matrices train under the authors' unnormalized power-mirror update. The upper queries, keys and values are the learned lower outputs. This is not a counterexample to the published **one-layer** theorem.

## Main result and scope

The architecture is

```
H0 = X
H1 = softmax_rows(H0 W1 H0ᵀ) H0
H2 = softmax_rows(H1 W2 H1ᵀ) H1
f  = wᵀ H2[row 1]
Jp(Wℓ⁺) = Jp(Wℓ) − η ∇Wℓ L,   Jp(z) = sign(z)|z|^(p−1).
```

The data are the paired examples `(X,+1), (−X,−1)`, with two tokens. Values are identity maps, the head is fixed, and there are no residuals or normalization. At each fixed p, the theorem covers an **open input class and an open set of finite full-matrix initializations** at a sufficiently large scale. The pair structure is retained; independently perturbing the positive and negative examples is not covered.

Let `q*` minimize `||q||p^p/p` subject to `x1ᵀq ≥ 1` and `x2ᵀq ≤ 0`. The main theorem assumes independent token rows, nonzero coordinates of `x1`, `x1−x2`, and `q*`, and strictly positive multipliers for both active constraints. These strict conditions give the open class and avoid differentiability claims at vanishing dual coordinates. They are substantive hypotheses, not genericity conclusions for every dataset.

The lower selected-query margin fraction tends to

```
R = 1 / (||q*||p ||x1||p′) < 1,       p′ = p/(p−1).
```

For example, `x1=(1,1)`, `x2=(2,1/2)`, `w=(−1/3,4/3)` is admissible for every fixed p; here `q*=(−1/3,4/3)` and `R=3/[2^(1−1/p)(1+4^p)^(1/p)]`. The upper layer reaches its actual checkpoint token-SVM direction. The ignored lower query supplies a leading cumulative gradient and acts as an extra zero-margin constraint.

This is a directional characterization, **not an accuracy or generalization improvement/failure**. No random-initialization guarantee, trainable-head/value theorem, practical basin threshold, or novelty clearance is claimed. The discrete orbit is proved in the notes; finite tests do not establish its infinite-time behavior.

## Read the results

| Note | Role | Review status |
|---|---|---|
| [Every fixed p > 1](proofs/generic_p_open_input_theorem.md) | Main open-input result | Separate internal analytic review passed |
| [Concrete p = 3/2](proofs/p_three_halves_dynamics.md) | Explicit non-Euclidean construction and constants | Separate internal analytic review passed |
| [Concrete p = 2](proofs/selected_path_noncollapse_theorem.md) | Explicit discrete basin and margin deficit | Separate internal analytic review passed |
| [General p = 2 geometry](proofs/positive_gram_extension.md) | Margin fraction equals the sine of the query angle | Separate internal analytic review passed |
| [Printed one-layer cone comparison](proofs/printed_single_layer_cone_compatibility.md) | A separate p = 2 family starts inside the stated one-layer sufficient cones | Separate internal source/analytic review passed |

The last row does not promote the printed-cone conclusion to every p. Reviews in [audits/](audits/) were performed by separate **AI agents in the same research workflow**. They are not external expert review, Lean/formal verification, or proof of priority.

[Primary comparisons](notes/primary_scope_comparison.md) identify concrete distinctions from generalized SVM interpretations, gradient starvation, JoMA, trained-embedding attention, and other multilayer results. That archived comparison was written for the p = 2 result; its restrictions are superseded only by the explicit later proofs above. [The targeted subsumption test](notes/TARGETED_SUBSUMPTION_TEST.md) additionally checks lexicographic/quasi-homogeneous results and proves why a proposed excess-loss reduction fails its near-homogeneity premise. [Non-Euclidean source mapping](notes/source_mapping_and_scope.md) checks the optimizer and the released Bregman **argument order**. For p ≠ 2, reversing that order changes the reported gap.

## Verify without training

Use Python 3.11+ with the pinned NumPy dependency. From this directory:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py
```

This needs only NumPy and performs no downloads or training. It checks archival hashes, exact rational identities, all retained checkpoints, the metric orientation, and finite generic-p KKT/clock fixtures. Use `--output NEW_FILE.json` to retain a new report; existing reports are never overwritten.

For full autograd and the pinned released SMD implementation:

```sh
python -m pip install -r requirements-native.txt
python fetch_optimizer.py
python verify.py --native
```

The fetch is explicit, downloads only one small upstream file, and verifies its commit-bound SHA256 before execution. It is not vendored in this repository; see [THIRD_PARTY.md](THIRD_PARTY.md). The native check runs 48 one-step cases, not training trajectories.

The release checks passed with Python 3.12.14, NumPy 2.3.5 (default checks), and NumPy 2.5.4 / PyTorch 2.14.1 (native checks). [The retained release check](provenance/release_verification.json) records the exact outcomes. The dependency ranges are installation requirements, not a claim that every version was tested.

## Retained diagnostics and optional reproduction

Both prespecified 50,000-step p = 2 trajectories, including the `δ=0` control, are retained: [protocol](data/diagnostic_protocol.json), [results](data/diagnostic_results.json), [states](data/diagnostic_states.npz), [interpretation](notes/diagnostic_report.md). The control also has a finite-time margin deficit. **Those runs do not distinguish the asymptotic theorem by themselves**, and their modest initialization was not certified to lie in the proved large-scale basin. No p = 3/2 or generic-p training run is being implied.

To reproduce the same two fixed diagnostics on CPU, after the native setup:

```sh
python run_diagnostic.py --output-dir runs/reproduction-01
```

This explicitly performs training. It has no tuning/seed/step overrides, retains every scheduled checkpoint, and requires a new output directory. It was ported without changing the training loop; only bounded verification was executed while preparing this release.

## Provenance

The five proof files, five reviews, four notes, and retained data/provenance artifacts are byte-identical archival copies. [Source manifest](provenance/source_manifest.json) records their hashes and original relative paths. Some archived prose refers to historical filenames or review states; [portable changes](provenance/PORTABLE_CHANGES.md) maps the public entrypoints and documents the changed script hashes. Downloaded papers, third-party repository bulk, credentials and machine-specific runtime paths are excluded.
