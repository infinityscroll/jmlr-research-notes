# Positive refinement to prescribed finite observed alphabets

28 October 2026. Standalone exact transfer lemma and a single-action completeness corollary. The multi-action corollary is explicitly conditional on the separate binary multi-action theorem. No held source is changed. This is an elementary alphabet-extension argument, not a new identification algorithm or a priority claim.

## 1. Bound class and result

The held single-action source is

`../prescribed_unit_structure_gate_20261028/private_switch_completeness.md`,
SHA256 `274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`.

Its independent analytic audit is

`../prescribed_unit_structure_gate_20261028/independent_private_switch_audit.md`,
SHA256 `58f2ba02acccb89f810cc8a776aed911e58d0ec7cf46caa7123abae5b3d672fb`.

Keep that source's prescribed acyclic hierarchical graph, arbitrary finite unit-node alphabets and observed unit vector C, **no subunit-to-unit arrows**, semi-Markovian subunit graph, and independent private disturbances. The existing hidden subunit roots have free positive laws and sufficiently large prescribed finite alphabets. Permitted arrows need not be functionally active. The observation remains Law(C,Q_O), with Q_O the complete within-unit observed subunit joint law.

Now prescribe, before choosing either witness, any finite alphabet X_v with |X_v|>=2 for every observed subunit v in O. Write d=|O|. All actual physical subunit kernels remain strictly positive. Fix one treatment A, a nonempty selected set Y subset O minus {A}, and one strictly positive unconditional policy pi_A on X_A. As in the held theorem, its *whole mechanism table* must occur naturally with positive probability conditional on the allowed collapsed unit parents.

**Corollary R1, single action.** Ordinary flat ID for P(Y|do(A=a)) in the subunit graph is complete for Law(C,Q_Y^pi) and E Q_Y^pi in this finite-alphabet HCM class. In the failure direction, the two models use these same prescribed observed alphabets, the same prescribed unit graph and unit law, the same hidden-root alphabets and laws, and the same natural treatment-table distribution. The actual pi_A table has conditional natural probability one half. All finite observational record laws agree, but the selected policy distributions differ.

The sufficient graph-wide hidden-root capacity remains **2^(d-1)+2 states per existing pairwise root**. It does not depend on the observed alphabet sizes. There are no added endogenous variables or shared private disturbances. This conclusion is about an outcome distribution and some probability determined by it, not every preassigned numerical contrast on X_Y.

## 2. Positive refinement lemma

For each observed v choose any fixed surjection

    g_v : X_v -> {−1,+1}.                                  (R1)

For each b in {−1,+1}, choose a probability r_v(·|b) strictly positive on the fiber g_v^(-1)(b), and zero outside that fiber. These g_v and r_v are common to both models and to every unit. Their zero values outside the fiber do not create zero physical cells: an actual state x_v always uses r_v(x_v|g_v(x_v))>0.

For a finite set D of observed vertices, define the linear refinement map

    (L_D q)(x_D)=q(g_D(x_D)) product_(v in D) r_v(x_v|g_v(x_v)). (R2)

It takes probability vectors to probability vectors. Define its coarsening left inverse by

    (C_D qtilde)(b_D)=sum_(x_D:g_D(x_D)=b_D) qtilde(x_D).    (R3)

Then C_D L_D is the identity. Thus L_D is injective, and it cannot erase any difference in a binary D-distribution. Marginalization commutes with refinement:

    marginal_D (L_O q) = L_D (marginal_D q).                (R4)

Both facts follow by summing each normalized fiber probability, without any independence assumption on q.

Let a binary HCM on the held graph have local observed-subunit kernels

    k_v(b_v | b_paO(v), h_paH(v), theta),                    (R5)

where theta denotes the fixed unit state and private unit disturbances for the within-unit experiment; h denotes hidden subunit root states. Refine only the observed-node mechanisms to

    ktilde_v(x_v | x_paO(v), h_paH(v), theta)
      = k_v(g_v(x_v) | g_paO(v)(x_paO(v)),h_paH(v),theta)
          r_v(x_v | g_v(x_v)).                             (R6)

Leave all unit mechanisms and hidden subunit-root mechanisms unchanged.

Equation R6 is a legal kernel on precisely the prescribed parent set: it reads only existing parent states, using the groups of observed parents. It is normalized because summing over a fiber gives the corresponding binary probability. Every physical cell is strictly positive. For a finite witness with uniform binary cell floor epsilon, the fine floor is at least epsilon times min_(v,x_v) r_v(x_v|g_v(x_v))>0. A uniform floor independent of alphabet size or pi is not asserted.

The extra draw within a fiber uses only fresh noise at that same subunit node. It can be generated jointly with the binary draw by a single private categorical sampler for R6, so no new graph node, cross-node common noise, or enlarged hidden-root alphabet is needed. Children depend on the drawn parent only through its group. This is a valid unrestricted-mechanism submodel; it is not a faithfulness assertion.

Conditional on theta and a complete hidden-root assignment, multiply R6 over observed nodes. All r_v factors depend only on the displayed observed assignment, not on theta or the hidden roots. They therefore factor outside the hidden-root sum. The exact within-unit identity is

    Qtilde_O = L_O Q_O                                    (R7)

for every unit state, not just after averaging over units. Consequently equal binary observations Law(C,Q_O) imply equal fine observations Law(C,Qtilde_O). Conversely, within this refined submodel coarsening the fine Q recovers the binary Q. The refinement adds no information about a hidden switch label.

For a finite within-unit record of length m, R7 similarly yields

    Qtilde_O^(tensor m)(x^(1),...,x^(m))
       = Q_O^(tensor m)(g(x^(1)),...,g(x^(m)))
            product_(i=1)^m product_v r_v(x_v^(i)|g_v(x_v^(i))). (R8)

Thus equality of the binary record laws, jointly with the unit variables, lifts exactly for every m and every number of units. This does not require an infinite-subunit limit.

## 3. Commutation with the actual prescribed policy

Fix the fine policy pi_A and define its binary pushforward

    pi_A,g(b)=sum_(x:g_A(x)=b) pi_A(x)>0.                   (R9)

At the treated node choose the refinement law specifically as

    r_A(x|b)=pi_A(x)/pi_A,g(b) for g_A(x)=b.                (R10)

The binary constant table pi_A,g then refines to the *entire* constant table pi_A, independent of every observed and hidden parent assignment. It is not merely a marginal treatment distribution.

For any binary A table, refinement of that table equals pi_A if and only if the binary table equals pi_A,g on every parent assignment. The forward implication follows by summing fine states over each fiber. Surjectivity of every observed-parent g ensures that every binary observed-parent assignment has a fine representative, and the hidden-parent domains are unchanged. The reverse implication is R10. In particular, a distinct alternative binary A table stays distinct after refinement.

Therefore the binary event that the actual whole A table equals pi_A,g is exactly the fine event that its whole table equals pi_A. In the held witnesses its conditional probability is one half. Unit variables are unchanged. If collapsed parent coordinates include other mechanism tables, their fixed refinement maps have coarsening left inverses as well; they do not create an additional distinction between unit states. In the concrete witnesses all non-A subunit mechanisms are already constant across units, so the policy-support calculation also follows directly from A's independent fair switch.

Replacing A by pi_A in the fine model is exactly the refinement of replacing its binary mechanism by pi_A,g. All other kernels remain R6. Since there is no feedback to units, the unit state and its distribution are unchanged. Hence, pointwise and for every selected outcome set,

    Qtilde_O^pi_A = L_O Q_O^(pi_A,g),
    Qtilde_Y^pi_A = L_Y Q_Y^(pi_A,g).                      (R11)

The fine policy is fixed first. The resulting refinement laws and binary witness may depend on that fixed query. This does not construct one pair of models that works simultaneously for every possible fine policy.

## 4. Proof of single-action completeness

On flat-ID failure, apply the held binary theorem using pi_A,g from R9. It gives positive binary witnesses with a common unit law, common hidden-root laws, common A-table distribution, whole-policy support one half, identical full natural observations, and a selected outcome discrepancy. Apply the same R1/R6/R10 refinement to both witnesses. Sections 2–3 verify every fine-class requirement and preserve the full observation equality and actual policy support.

If the binary selected discrepancy is witnessed by a parity chi_T(b_T), T subset Y, use the fine event

    E_T={x_Y : product_(v in T) g_v(x_v)=+1}.              (R12)

Its probability in the refined model is exactly the corresponding binary parity probability. Thus the positive gap from the held theorem survives with the **same size**. More generally, injectivity of L_Y alone preserves any difference of binary selected distributions. The same holds after expectation because L_Y is linear. The joint law with C also differs in the held witnesses, where the selected policy probability vector is deterministic within each model.

This proves nonidentification in the full fine-alphabet model class, even though the counterexamples belong to the restricted group-dependent submodel. A counterexample submodel suffices for that direction.

For flat-ID success, do **not** assume that an arbitrary fine-alphabet HCM factors through the groups. Condition directly on its unit variables and private unit disturbances. The remaining experiment is a positive flat semi-Markovian model with the actual prescribed fine alphabets. Successful ordinary ID therefore returns its fine selected hard-action law. Averaging that formula with pi_A and pushing forward jointly with C identifies the requested fine targets. No-feedback ensures that the intervention changes no conditioning unit state. This is the same sufficiency argument as the held theorem, applied to arbitrary fine mechanisms. It completes Corollary R1.

## 5. Several simultaneous unconditional policies: conditional corollary

For each a in a nonempty action set B, fix a positive unconditional pi_a on X_a and define pi_a,g and r_a by R9–R10. Use arbitrary positive fiber laws at all remaining observed nodes. If the binary intervention draws independently from the product of the pi_a,g, then the refined intervention draws independently from the product of the pi_a. The kernel identity R11 holds with all B tables replaced simultaneously. The event that the *joint tuple* of binary queried tables occurs naturally is exactly the corresponding event for the fine queried tuple.

**Conditional Corollary R2.** If the binary multiple-policy theorem

`../multiple_private_switch_gate_20261028/multiple_policy_completeness.md`,
SHA256 `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf`,

holds in its stated class, then all its completeness and observation-equality conclusions hold for the arbitrary prescribed finite observed alphabets above. The existing hidden-root capacity remains 2^(d-1)+2. Its joint whole-policy support probability k!/(2k)! for k treatments in the chosen hedge is preserved exactly, as is the selected parity-event gap.

The mathematical refinement implication is proved here. At the time this addendum was prepared, the separate general binary multiple-policy source was undergoing independent review; this note does not substitute for that review or silently promote its proof status. Its single-action conclusion depends only on the held single-action theorem and audit.

## 6. Explicit three-state treatment / four-state outcome illustration

Start with the held two-node binary fixture, whose policy is fair on A and whose policy group-success probability for Y is 17/32 or 15/32. Set

    X_A={0,1,2},  g_A(0)=−1, g_A(1)=g_A(2)=+1,
    pi_A=(1/2,1/6,1/3).

Its coarsened policy is fair, and the positive A-fiber laws are r_A(0|−)=1 and r_A((1,2)|+)=(1/3,2/3). Set

    X_Y={0,1,2,3}, g_Y(0)=g_Y(1)=−1, g_Y(2)=g_Y(3)=+1,
    r_Y((0,1)|−)=(1/4,3/4), r_Y((2,3)|+)=(2/5,3/5).

Every physical A and Y cell is positive after R6. The fine observed table law is the same common mixture of L_(A,Y)q_+ and L_(A,Y)q_-. The whole three-state policy pi_A appears with conditional probability one half in both models. Under that policy, the event Y in {2,3} has probability 17/32 versus 15/32, so the gap remains 1/16. This illustrates exact full-table support and selected-event preservation; it is not an argument by numerical extrapolation.

## 7. Boundaries and significance

The transfer fails as stated if an observed alphabet has only one state, because a surjection to two groups does not exist and fixed deterministic observed states can change the identification problem. Strictly positive policies are assumed; this note does not supply positive whole-table witnesses for a policy assigning zero probability to fine states. Conditional policies, correlated simultaneous interventions, feedback to unit variables, and externally fixed incompatible hidden-root laws require separate arguments. For two different queried policies at the same node, one fixed fiber law need not be compatible with both; no such simultaneous-query claim is made.

There is no assertion that all fine states play distinct causal roles. The unrestricted class permits children to ignore distinctions within a group. There is also no claim for each preassigned numeric mean or contrast on the enlarged alphabet: the guaranteed difference is in the selected distribution, witnessed by the group event R12.

The original [HCM Definitions 1–2 and Assumptions 1–3](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf) provide the mechanism, intervention, observation and support semantics used here. This extension removes a finite observed-alphabet restriction from the held no-feedback result by an exact positive refinement. The hidden-subunit/no-feedback scope, capacity assumptions and unresolved historical novelty of the held completeness construction remain unchanged.
