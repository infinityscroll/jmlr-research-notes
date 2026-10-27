# Supported subunit policies on prescribed hierarchical graphs

28 October 2026. Integrated statement of the new private-switch construction,
its multiple-action extension and its positive alphabet refinement. This is a
restricted nonparametric completeness theorem. It is not general HCM
completeness, an external correctness certification or a claim of priority.

## The class and the criterion

Fix a finite acyclic hierarchical graph with no subunit-to-unit arrows. The
unit DAG, its observed and hidden nodes, and its unit-to-subunit arrows are
prescribed. Unit-node alphabets are finite. There are d observed subunit nodes,
each with a prescribed finite alphabet of size at least two. Hidden subunit
causes are independent pairwise roots, conditional on the complete unit state.
Their existing prescribed alphabets have sufficient capacity: at least
2^(d-1)+2 states per root, with unrestricted positive laws, is sufficient.
The unit graph can be empty. No additional shared unit selector is assumed.

Mechanisms may be any functions of their allowed parents and the original
independent private disturbances; allowed arrows need not have a nonzero
effect. Physical subunit kernels are strictly positive. Let C denote observed
unit variables and Q_O the complete observed within-unit subunit distribution.
The observed experiment is Law(C,Q_O).

Choose a nonempty set B of subunit treatments and a nonempty selected outcome
set Y disjoint from B. Fix a positive unconditional distribution pi_a on each
treated alphabet. The intervention replaces the B tables simultaneously and
draws independently from these distributions. Assume the actual queried
whole tables have the natural support required by the source model. Individual
table support suffices for the theorem below; it also holds on the smaller
class requiring joint tuple support.

**Completeness theorem.** Ordinary flat ID for P(Y | do(B=b)) in the subunit
graph succeeds if and only if the selected policy targets

    Law(C,Q_Y^pi)  and  E Q_Y^pi

are identifiable uniformly over this hierarchical model class.

On success, the functional is the measurable pushforward by

    (c,q) -> (c, F_pi(q)),
    F_pi(q) = sum_b [product_(a in B) pi_a(b_a)] ID_b(q).

On failure, two models on the exact prescribed graph have the same unit law,
hidden subunit-root laws, and full joint distribution of treatment tables.
Their full observed law and every finite natural observational record law
agree, yet their selected policy distributions and pooled probability vectors
differ. For a failure hedge containing k treated nodes, the queried *joint*
table tuple has natural probability k!/(2k)! conditional on every allowed
unit-parent assignment. With r=|B| this is at least r!/(2r)!>0. Thus the
failure does not exploit zero support for the actual intervention.

## Why the theorem follows

The three proof sources, in dependency order, are:

1. [Private-switch construction](../prescribed_unit_structure_gate_20261028/private_switch_completeness.md),
   SHA256 `274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`.
2. [Independent switches for multiple treatments](../multiple_private_switch_gate_20261028/multiple_policy_completeness.md),
   SHA256 `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf`.
3. [Positive refinement to prescribed finite alphabets](positive_finite_alphabet_refinement.md),
   SHA256 `4364d97a03288717303da9e21732b92683c0ffe587cf89ab67d2723d846c6fb1`.

For success, fix the complete unit state and private unit disturbances. Flat
ID identifies the policy distribution from the within-unit observed law,
pointwise. The intervention does not change that unit state because there is
no feedback from subunits. Pushforward gives the law jointly with C. This
argument applies to arbitrary mechanisms in the class, with no binary-group
restriction and no need to infer joint support from individual support.

For failure, the binary construction superposes nested positive hedge modes.
Only the outer mode depends on the treatment switches, and it survives exactly
when all k independent switches are on. Choosing on-probabilities

    (k+j-1)/(k+j), j=1,...,k,

makes that event have probability one half. The two models therefore swap the
labels of the same two observed table atoms. The actual policy turns all
switches off; its natural probability is k!/(2k)!, and the two resulting
selected laws differ. Every private switch belongs to its own treatment
mechanism; no cross-node private noise is shared.

For a prescribed fine alphabet choose a surjection g_v onto two groups. Refine
the binary kernel by multiplying by a fixed positive probability within each
group. At a treatment, use the queried pi_a conditioned on the group. The
binary queried table then refines to exactly the prescribed full pi_a table.
The refinement has coarsening as a left inverse, so it preserves observation
equality, policy-table event probabilities and the selected distribution gap.
Every physical fine cell is positive. It uses only local fresh subunit noise
and does not enlarge the hidden roots. This proves the failure direction on
the prescribed alphabets. Since these witnesses have joint tuple support,
they also prove failure in the larger class with individual support only.

## A small exact example

Three binary observed nodes A1,A2,Y and two binary hidden subunit roots suffice
for a two-treatment example. There are no endogenous unit nodes. The two
queried treatment tables are naturally present together with probability
1/12. Every finite natural record has the same law in both models, but under
the simultaneous policy

    P_+(Y=1)=65/128,   P_-(Y=1)=63/128.

The local physical probabilities are strictly positive. The multiple-action
source gives all original kernels, and its exact checker sums them directly.
The general theorem is proved analytically rather than extrapolated from this
example. Positive refinement gives corresponding examples with larger
prescribed alphabets and nonuniform policies.

## What has and has not been resolved

The earlier portfolio composition required a universal shared hidden unit
variable and was stated for a single policy with binary observed subunits.
This construction removes those requirements. It establishes an exact
criterion for the stated no-feedback, hidden-subunit class, even when the
entire distribution of within-unit observed laws is available.

This is uniform graph-class identification. It does not say that informative
environment changes can never identify an effect in a particular distribution.
The witnesses intentionally use constant non-treatment mechanisms and may
ignore allowed unit arrows. Faithfulness and guaranteed informative variation
are not assumptions of this theorem.

The theorem does not cover subunit-to-unit feedback or unit-level outcomes,
parent-dependent policies, correlated simultaneous interventions, fixed small
hidden alphabets, or every preassigned numerical outcome contrast. It also
does not identify one counterpair that defeats all policies at once: each
positive policy is fixed before constructing its witnesses. The source
paper's full receiver/aggregation completeness question remains open here.

The [primary comparison](../prescribed_unit_structure_gate_20261028/primary_scope_gate.md)
places the result against HCM and causal/Do-Finetti statements. The relevant
HCM hidden-subunit limitation appears in [Section 8.1](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf),
while its broader completeness question remains outside the no-feedback
class. Existing hedge theory, orthogonal perturbations and elementary alphabet
refinement are credited ingredients. Whether this composition is historically
new and substantial requires specialist comparison; no inspected source
directly supplied the complete criterion, but that is not priority clearance.
