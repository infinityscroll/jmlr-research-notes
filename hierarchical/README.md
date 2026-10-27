# Supported policies and separated receivers in hierarchical causal models

This is a research manuscript package, with proofs and exact finite checks. It is **not externally peer reviewed or Lean-verified**. Files called “independent” or “root” audits are reviews by separate AI agents in the same research workflow; they are not independent human validation or evidence of novelty.

Start with [the terminal receiver theorem](terminal_receiver_completeness_gate_20261028/separated_receiver_completeness.md) and [the no-feedback completeness statement](alphabet_refinement_gate_20261028/COMPLETENESS_FRONTIER.md). The [proof map](PROOF_MAP.md) identifies every substantive imported result.

## What the manuscript establishes

For the stated no-feedback class, ordinary within-unit flat ID characterizes whether a selected subunit policy distribution is identifiable from the distribution of the observed within-unit laws. The result permits a prescribed upstream unit DAG, observed unit covariates, finite observed subunit alphabets, hidden subunit confounding, and a specified strictly positive unconditional product policy on finitely many treated subunits.

The necessity argument constructs two positive hierarchical models with identical complete observations—including every finite observed subunit record—but different policy distributions. Independent private treatment switches make the actual queried policy tables naturally supported. A universal hidden unit selector is not required. The finite-alphabet refinement preserves the entire policy table, rather than merely its marginal treatment probabilities.

The terminal receiver theorem adds genuine subunit-to-unit arrows. A receiver can respond nonlinearly to the joint within-unit law of its subunit parents. For a terminal unit outcome, identification holds exactly when flat ID recovers every ancestral receiver's required policy input. Its identifying formula learns the downstream response from the observed law and transports it to the identified policy inputs. The proof establishes the necessary support inclusion; it does not evaluate a conditional distribution at an unsupported input.

## Restrictions that matter

- In the no-feedback theorem, there are no subunit-to-unit arrows. The terminal extension permits them only in a downstream receiver block separated from upstream hidden unit and hidden subunit causes, conditional on observed context. Confounding inside that downstream block is allowed.
- Hidden subunit confounders are semi-Markovian pairwise roots with sufficiently large prescribed finite state spaces. This is not completeness for every small hidden alphabet.
- Policies are strictly positive, unconditional, and products across simultaneously treated subunits. The **whole policy table** must have positive natural probability conditional on its allowed unit parents. Positive physical treatment probabilities alone do not imply this condition.
- The conclusions concern graph-class identification of distributions. Nonidentification of a distribution does not imply nonidentification of every preassigned scalar ATE.
- No faithfulness assumption is imposed; ignored graph arrows are allowed. Neither the general shared-latent receiver problem nor arbitrary feedback is solved.

These are restricted completeness results and a support-preserving converse, not a counterexample to the original paper's soundness theorem or a proof that every permitted augmentation sequence fails. The receiver's sufficient formula is classical conditional transport; the scope of the converse is the substantive issue.

## Reproduce the finite checks

From the repository root, using Python 3.10 or later and its standard library:

```sh
python3 hierarchical/reproduce.py
```

The runner checks the publication manifest, copies this section to a temporary directory, executes the five included checks, and compares their JSON output with the saved certificates. It leaves this checkout unchanged and needs no network or GPU. Use `--only NAME` to run one named check, or `--list` to list them.

The checks cover the positive multimode witness, hidden-capacity construction, single and multiple private switches, and terminal receiver controls. They verify finite algebra and fixtures. They do not mechanically verify the universal analytical proofs.

## Sources and status

The primary comparison is [the prescribed-unit scope note](prescribed_unit_structure_gate_20261028/primary_scope_gate.md), supplemented by [the terminal receiver comparison](terminal_receiver_completeness_gate_20261028/primary_scope_comparison.md). The closest foundations are ordinary ID/hedge completeness and the original hierarchical causal model definitions. The package does not claim a new do-calculus, external author endorsement, or historical priority.

Research sources are copied byte for byte; their dated headers preserve the state in which each source was first written. Subsequent internal reviews are included separately. [PROVENANCE.json](PROVENANCE.json) records source and staged hashes. The old multimode source is imported only for its flat-model Sections 1–4; its historical Section 5 is not used to support the current HCM claims.
