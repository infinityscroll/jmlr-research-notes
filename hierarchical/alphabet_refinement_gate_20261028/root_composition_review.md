# Root review of the multiple-policy and finite-alphabet composition

28 October 2026. This review binds the multiple-policy source
`../multiple_private_switch_gate_20261028/multiple_policy_completeness.md`
at SHA256 `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf`
and `positive_finite_alphabet_refinement.md` at SHA256
`4364d97a03288717303da9e21732b92683c0ffe587cf89ab67d2723d846c6fb1`.
Both sources were read in full. The single-policy dependency was previously
reconstructed in `../prescribed_unit_structure_gate_20261028/root_private_switch_review.md`.

**No blocking error found in the composition as stated in
`COMPLETENESS_FRONTIER.md`.** This is internal mathematical review.

I checked the multiple-action seam. The inner hedge avoids every action,
and the selected outcome route avoids the whole action set. Hence no treatment
receives an inner perturbation, and replacing every queried table leaves the
inner selected-outcome discrepancy intact. Every surviving outer label must
occupy its entire connected tree. Its coefficient contains exactly the product
of the private action flags. Independent unequal Bernoulli probabilities
(k+j-1)/(k+j) make this product equal one with probability one half. The
all-zero probability is exactly k!/(2k)!. The treatment coefficient signs
remain the same between models because all model signs are at an inner node.
The resulting full treatment-table distributions, not merely their marginals,
agree between models. The capacity count h+k<=d-1 is valid because the route
avoids every action and the inner hedge is nonempty.

I also summed the displayed three-node original kernels. Their hidden-root
contraction is [1+sigma(1-2t1t2)y/64]/8. The four independent flag probabilities
are 1/12,1/4,1/6,1/2, so the two natural table laws agree exactly. Replacing
both treatment tables gives policy success probabilities 65/128 and 63/128.
The local lower bound 31/128 is positive. The checker is a supplement to the
general contraction argument, not its proof.

For finite refinement, R6 reads only the allowed fine parent states through
their fixed groups. Summing a fiber normalizes each physical kernel. Its
strictly positive within-fiber factor multiplies a positive binary cell, so
no actual physical fine-state cell vanishes. At an observed assignment the
product of all refinement factors is independent of the hidden roots and unit
state. It factors out of the hidden-root sum, yielding the exact full table
map L_O. Summing groups is its left inverse and commutes with marginalization.
These identities also give equality of all finite record laws after mixing
over the original unit states.

At each treatment the refinement factor is the queried pi conditioned on its
group. Thus the binary queried table maps to exactly pi on every fine observed
and hidden parent assignment. Conversely, coarsening any full fine table
equal to pi recovers the binary queried table. Surjectivity covers every
binary parent configuration. Alternative tables stay distinct, and the whole
joint policy-table event has exactly the same probability before and after
refinement. No new shared noise or hidden-root states are introduced; a single
fresh local categorical draw implements each refined kernel.

The selected group-parity event has the same policy probability as in the
binary model, including after expectation. Sufficiency for arbitrary fine
models is applied directly through ordinary ID; it does not assume every fine
model factors through groups. The grouped submodel is used only to produce
failure witnesses for the larger unrestricted class.

Finally, the individual-support formulation is a valid quantifier extension.
Success holds pointwise for every model in that larger class. The failure
witnesses lie in the smaller joint-supported class, so they also disprove
identification in the larger class. This does not claim that marginal support
implies joint support in an arbitrary model. All other positivity, graph,
hidden-capacity and no-feedback assumptions are held fixed.

The integrated result does not remove feedback, impose informative variation,
or cover conditional/correlated policies. It is not a formal proof-assistant
certificate, external expert review, or a historical-novelty finding.
