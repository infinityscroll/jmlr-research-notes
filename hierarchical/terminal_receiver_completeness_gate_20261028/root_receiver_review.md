# Root review of separated terminal receiver completeness

28 October 2026. Bound source `separated_receiver_completeness.md`, SHA256
`9b6d81b482c7fbf5b63e703d20e5e6af4a12bea865ac48341b3b4d7c7f15f2ce`.
The root read the entire source and reconstructed both directions. This is
internal analytic review, not novelty clearance or external validation.

**No blocking error found in the stated separated-block theorem.**

The key support assertion concerns the joint tuple of received subunit laws.
Conditioning on the upstream unit state and all other mechanism disturbances
leaves action-node private disturbances mutually independent. There is no
upstream subunit-to-unit feedback in this block, so that conditioning does
not absorb an action disturbance through a descendant. Individual actual
whole-policy table probabilities therefore multiply to a strictly positive
conditional probability. On their joint event the natural within-unit law
equals its intervened law for the remaining state. Weighting a null-set
indicator by this strictly positive probability proves absolute continuity
of the entire counterfactual received tuple with respect to its natural law.
It does not assume the event or its propensity is observed.

Given observed context C, the whole downstream receiver-noise block is
independent of upstream mechanisms. Marginalizing its latent vertices yields
one unchanged response kernel of the complete received tuple. This is the
precise reason the observed conditional response can be transported. A
hidden cause spanning both blocks would invalidate that identity. Hidden
causes wholly within the downstream DAG do not invalidate it, because no
downstream mechanism is intervened on.

Successful flat ID of each input marginal supplies each received-table
coordinate as a deterministic function of the same observed q. Their joint
law is then identified by simultaneous pushforward; separate identification
does not mean separately estimating unrelated marginal laws and guessing
their dependence. If received sets contain treatment coordinates, the
displayed formula properly retains those coordinates through the known
product policy and sums only the remaining action assignments.

On failure the held private-switch construction gives identical complete
observations and a deterministic policy discrepancy in the relevant input.
The common positive receiver channel converts that discrepancy into an
actual selected unit-outcome probability gap. An allowed unit-only path
propagates the gap with a nonzero attenuation. At finite replication the
channel reads the empirical joint of its actual subunit parents, so equality
of finite upstream records is preserved for all observed downstream nodes,
including paths through hidden receivers. The channel is continuous and
uniformly positive, making its limiting convergence compatible with the
original HCM. This is an identification witness, not merely an encoding map.

The front-door example's intervened input is 3/8+3U/64, which is nonconstant;
the effect is not obtained by resetting every receiver input to a known
constant. The exact checker supplements the analytic construction. The
positive result's conditional transport principle is classical, and the
converse inherits the earlier positive hedge machinery. This is a useful
closure under a separated terminal block, not resolution of the general
shared-latent receiver/aggregation problem.
