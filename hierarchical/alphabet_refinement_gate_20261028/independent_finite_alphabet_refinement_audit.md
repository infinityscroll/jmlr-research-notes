# Independent audit: positive finite-alphabet refinement

28 October 2026. Source-level adversarial review by the separate hcm_adversarial_boundary agent. No producer file was changed.

## Bound sources and verdict

Reviewed the entire `positive_finite_alphabet_refinement.md`, SHA256 **4364d97a03288717303da9e21732b92683c0ffe587cf89ab67d2723d846c6fb1**, against the held single-action source **274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755**. Also reread the primary HCM Definition 1, Definition 2, and Assumptions 2–3 in the saved paper text.

**No mathematical blocker or requested repair found in the stated refinement implication.** The single-action conclusion inherits the held binary theorem; Section 5 correctly makes its multi-action consequence conditional on the separately reviewed binary theorem. This audit proves neither the binary theorem anew nor historical novelty.

## Exact seams checked

**1. Legal local kernels and positivity.** Every prescribed observed alphabet has at least two states, so each surjection exists. For fixed fine-parent values and hidden-root states, summing R6 over a fiber returns the corresponding binary cell, and summing both fibers returns one. Each actual fine cell uses a strictly positive fiber probability; zeros outside a fiber are not zero physical cells. A finite positive binary floor times the minimum positive fiber mass is a valid fine floor. The factorization reads only allowed observed-parent groups and unchanged hidden parents. The within-fiber draw can use the node's existing fresh subunit noise under Definition 1; it needs neither a new common cause nor a larger hidden-root alphabet.

**2. Whole-policy support, including all fine-parent configurations.** For the fixed fine policy, R9 gives two positive coarse masses and R10 gives normalized positive fibers. A constant binary policy table then maps to the exact fine table pi at *every* allowed parent assignment. Conversely, summing a fine table over its outcome fibers recovers the binary table. Surjectivity of the parent group maps makes this converse cover every binary parent assignment, including assignments not singled out by a particular observation. Thus the two policy-table events are identical, and a non-policy table cannot become the policy after refinement. This is stronger than matching a marginal treatment frequency.

The held counterexample's only varying subunit-associated unit disturbance is the independent treatment switch; all other subunit tables are constant across units. Hence conditioning on actual allowed collapsed parents does not reveal that switch, and the policy probability remains one half. Refinement preserves unit variables and is invertible by coarsening on each table image, so it introduces no extra distinction among unit states. This checks the actual Assumption 3 intervention support; no Cartesian support for arbitrary tuples of auxiliary tables is being imposed.

**3. Full observed law and finite records.** Multiplying the refined local kernels pulls exactly one factor r_v(x_v|g_v(x_v)) per observed node outside the hidden-root summation. This proves R7 pointwise in unit state and private unit disturbances, even when the binary observed joint law has arbitrary dependence. It implies equality of Law(C,Q_O) after the common deterministic refinement map. Applying the same identity to each subunit record proves R8; conditional independence of fresh subunit draws supplies the tensor product. Equality persists for every finite number of units and records. The observation argument does not replace the full joint law by its marginal cells.

**4. Interventions and selected events.** Replacing the fine treated kernel by pi is exactly refinement of replacing the binary kernel by its coarse pi. No-feedback preserves the unit state. The identity commutes with marginalization, and group summation is a left inverse, so differences cannot disappear. In particular, the fine parity event R12 has exactly the binary parity probability, not merely a lower bound on its discrepancy. Linearity also preserves the discrepancy of expected selected laws. The explicit three-state/four-state illustration has coarse treatment masses (1/2,1/2), and its outcome group event retains risks 17/32 and 15/32.

**5. Counterexample submodel versus universal sufficiency.** The failure construction deliberately makes children ignore distinctions within a group. This is allowed in the unrestricted nonparametric class and suffices to disprove uniform identification there. It would not justify assuming all models possess this grouping. The source avoids that error: on ID success it conditions an arbitrary fine-alphabet HCM on its unit state and uses ordinary flat ID on the actual fine alphabets, then averages against the prescribed policy and pushes forward jointly with C. This establishes sufficiency for the full stated class.

**6. Multiple actions.** With fixed unconditional product policies, each action has its own compatible fiber kernel, and simultaneous replacement commutes with refinement. Group summation gives equivalence of the entire queried-table tuple event, preserving the binary joint-support probability and selected-event gap. Nothing here proves that marginal policy-table support generally implies joint support, or handles correlated intervention draws. The independently reviewed binary source is the required additional input; the refinement needs no further hidden capacity.

## Scope and evidence limits

This is an elementary exact lifting argument. It removes the prescribed finite observed-alphabet restriction, provided every observed node has at least two states. It does not remove the no-feedback, sufficiently rich hidden-root, or strictly positive unconditional-policy restrictions. It does not prove a discrepancy for every preassigned numerical outcome contrast, a common witness for multiple different policies at one node, or general completeness of the paper's augmentation search.

The checks above are analytical. No numerical checker was substituted for the proof or rerun for this audit. Primary semantics: [Weinstein and Blei, Hierarchical Causal Models, Definitions 1–2 and Assumptions 2–3](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf).

