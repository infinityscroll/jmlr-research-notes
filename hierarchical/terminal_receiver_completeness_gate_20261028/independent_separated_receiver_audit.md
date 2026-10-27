# Independent audit of separated terminal-receiver completeness

28 October 2026. Source-level analytic audit; no producer files were edited and no new computational experiment was run.

**Verdict: no blocking mathematical issue found in the stated class.** The result identifies the actual unit-outcome law, not merely an encoding of an upstream table. Its essential restriction is independence, conditional on C, between the upstream mechanism state and the entire terminal unit-noise block. The proof does not extend to a hidden common cause crossing that boundary.

## Exact source binding

| Item | SHA256 |
| --- | --- |
| `separated_receiver_completeness.md` | `9b6d81b482c7fbf5b63e703d20e5e6af4a12bea865ac48341b3b4d7c7f15f2ce` |
| `../multiple_private_switch_gate_20261028/multiple_policy_completeness.md` | `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf` |
| `../alphabet_refinement_gate_20261028/positive_finite_alphabet_refinement.md` | `4364d97a03288717303da9e21732b92683c0ffe587cf89ab67d2723d846c6fb1` |

I read both dependencies, the complete receiver proof, and the retained primary HCM definitions. This audit imports the held private-switch construction; it is not another independent derivation of its full Fourier/hidden-capacity proof.

## 1. Individual support survives the required conditioning

The potentially dangerous step is conditioning on all other mechanisms, not multiplying unconditional policy probabilities. Let theta contain the realized C,U and every non-action subunit mechanism's associated unit disturbance. Each action table is a function of its own private unit disturbance and allowed unit parents in C,U. The table indexes subunit-parent assignments; its generation does not depend on their realized subunit values. Since there is no subunit-to-U or D-to-upstream feedback, theta does not contain an action-noise descendant. The private action disturbances remain independent of theta and of one another after conditioning on C,U.

Consequently, individual actual-table probabilities `e_a(C,U)>0` imply

    P(all queried tables occur | theta)=product_a e_a(C,U)>0

almost surely. This is valid for the full tables even with hidden subunit parents. It does not follow from positive treatment-state probabilities, and the source does not make that substitution. Nor does it claim that the event is observable from Q_O.

The policy-received tuple S^pi is a function of theta alone. On the joint table event, the natural received tuple equals that policy tuple. If a measurable set N has zero natural (C,S) probability, then

    E[e(C,U) 1{(C,S^pi(theta)) in N}]=0.

Strict positivity implies that its indicator is zero almost surely. This establishes domination of the **whole tuple** `(C,S^pi)` by `(C,S)`. No uniform propensity floor, inverse-propensity integrability, or finite mechanism codebook is needed. Conditioning only on separate receiver inputs would not establish the required joint support; T5 does establish it.

The [original HCM Definition 1 and equation (14)](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf) distinguish private unit noise, private subunit noise, and the conditional generation of whole Q tables from unit parents. Assumption 3 imposes positive probability of the queried collapsed-variable value conditional on its parents. The source's use of these semantics matches this argument. Its graph separation is stronger than merely having a positive observational distribution.

## 2. Terminal transport, including hidden receivers

In the limiting model, collect every private random input of the retained terminal unit DAG into eta. Given C, eta is independent of theta. All subunit-parent dependence of that DAG enters through the tuple of true joint laws `S_r=Q_(B_r)`. The DAG, including hidden vertices and internal common causes, therefore induces one conditional response kernel L_Y(y|c,s).

Natural Y given C,S has that kernel because eta remains independent of S after C. Intervention changes neither eta nor C. Hence the same kernel applies to S^pi. The domination proved above makes any observational regular-conditional version equal to L_Y at the counterfactual input almost surely. T4 is therefore well defined from observations and invariant to null-set versions.

This step allows hidden receivers and internal confounding because no D mechanism is intervened on. It would fail if a hidden parent jointly influenced an upstream mechanism and terminal response. Knowing S^pi alone does not repair that failure. The source states this boundary explicitly.

## 3. Separate flat queries suffice for the joint random input

For a fixed actual unit state, condition on every unit variable and associated mechanism disturbance. The remaining subunit model has the stipulated semi-Markovian graph, positive cells, and its actual observed joint q. Successful ordinary ID thus returns each hard-action T_r law from q. Averaging with the fixed independent product policies gives T2, including the treated coordinates retained in B_r. It does not incorrectly replace their dependence on untreated coordinates by a product of marginal laws.

Every successful receiver law is a deterministic functional F_r of the **same** q. The joint law across all receiver tables is therefore the simultaneous pushforward F(Q_O), available from the complete observed random table. Flat ID of the within-subunit union of those outcomes would be a different and unnecessarily strong demand. Likewise, knowing only the separate distributions of the random tables would be insufficient; the actual experiment observes their coupling through Q_O.

## 4. Necessity concerns the actual original experiment

On one failed receiver query, the held multi-policy theorem supplies two upstream models with the same unit law, the same full natural random-table law, and identical natural records for every finite replication. Their non-action mechanisms ignore allowed unit parents. After replacement of all action tables, the selected target distribution is deterministic within each model and differs on a fixed group event. Thus averaging over C,U cannot cancel that discrepancy. The finite-alphabet refinement preserves all those properties and actual full-table support.

The receiver response T9 reads a linear probability of that event from its permitted B_r marginal and ignores other allowed arguments. Marginalizing treated B_r coordinates recovers precisely the failed T_r target. Arbitrary ignored arrows are legal in the nonparametric graph class. Positive noisy copies along a directed unit path to Y attenuate, but cannot erase, the discrepancy. Hidden path vertices require no observation or extra intervention. Their finite alphabets permit the stated positive two-group channel.

For natural finite records, T9 is implemented using the empirical **joint** B_r distribution. Given the entire observed upstream record and C, every appended D variable is generated by the same channel in both models. This proves equality jointly with all observed D variables, not just the selected outcome. At the limit the event-probability functional is continuous and all constructed response cells have a positive fixed floor (after prescribed finite fiber refinement). The empirical laws converge and KL is bounded, which verifies the original mechanism-convergence requirement. Under intervention the success gap at the selected y is exactly the upstream event-probability gap times `2^(-(l+1))`.

This supplies two admissible full HCMs with equal complete observations and different unit-outcome distributions. It proves nonidentification of that distribution, not just failure of an encoding or a chosen collapse calculation. The converse depends on unrestricted permitted mechanisms, sufficient hidden-subunit capacity, and graph-class identification rather than identification at every exceptional observed law.

## 5. Scope of this verdict

The exact original observations, hidden-subunit confounding, prescribed finite alphabets, positive actual unconditional product-policy support, and finite-record/limit distinction were checked. No premise requiring full-joint flat ID slipped into the selected-input criterion. The independently reconstructible front-door illustration is consistent with the theorem, but no fixture or checker was used as a substitute for the proof.

This is a supported completeness extension through a causally separated terminal block. Its positive part is classical conditional transport; its converse composes the held private-switch witness with a common positive response channel. This audit does not establish novelty, complete the unrestricted HCM augmentation procedure, allow feedback or shared hidden causes across the separation, or give a theorem for arbitrary preassigned numerical contrasts. Internal analytic review is not external mathematical validation.
