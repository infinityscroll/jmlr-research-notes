# Independent audit: prescribed-unit private-switch completeness

28 October 2026. Analytic, source-bound internal review. No producer source was edited, and no external mathematical or novelty validation is claimed.

## Verdict and bindings

**No blocking issue found in the stated class.** The construction removes the extra universal endogenous unit selector used by the earlier composition, while preserving exact equality of the full observed experiment and positive support for the actual policy table. Its conclusion concerns a selected outcome distribution (and a constructed parity-event probability), not every prescribed scalar effect. It retains no subunit-to-unit feedback, semi-Markovian subunit confounding, and sufficient finite hidden-root capacity.

Reviewed source:

- `private_switch_completeness.md`: SHA256 `274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`.

Reviewed mathematical dependencies:

- `../binary_selected/general_positive/multimode_hedge/theorem.md`, Sections 1–4: `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147`.
- `../binary_selected/general_positive/multimode_hedge/joint_target_corollary.md`: `8119664d55ca00547478e336784a0143a359d20c47fe3623e877b590dac282bf`.
- `../binary_selected/general_positive/hidden_capacity_attack/capacity_compression_v2.md`, finite orthogonal-label construction: `1dfc788b295bf9dc30202bfa7315f5eb44f98b662b04c6794b543ef84cd7d6af`.

The review independently reconstructs the new simultaneous-mode contraction, original-HCM switch, selected-outcome discrepancy, and capacity count. It does not treat a finite checker as proof of the general statement. The producer's subsequently supplied checker/certificate were not executed for this verdict.

## 1. Original model and the observed experiment

The relevant primary definitions were checked in [Weinstein and Blei, *Hierarchical Causal Models*](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf): Definitions 1–2 on printed page 10 and Assumptions 1–3 on printed page 27. Each subunit node has its own unit-shared private disturbance as well as fresh subunit noise. The stated intervention replaces that node's conditional mechanism. The limiting observation is the distribution of observed unit variables and the observed within-unit joint law; it does not reveal the mechanism conditional on hidden subunit parents.

This distinction makes the private switch legal even when the endogenous unit graph is empty. A's own unit-shared disturbance may select between two complete A tables. It is not shared with another endogenous mechanism, and it is not an added endogenous unit variable. The source's revised wording correctly allows ordinary randomness in endogenous unit variables while saying that only A's *subunit-associated* private unit disturbance is used nontrivially.

For the negative witness, all subunit mechanisms may ignore their prescribed unit parents and all unit mechanisms may ignore permitted unit arrows. These are permitted submodels absent faithfulness or a minimum-effect condition. Choosing one common compatible unit law, independent of A's private switch, gives equality jointly with every observed unit covariate. This proves the stated graph-class result; it is not a claim for mechanisms constrained to make every permitted arrow active or to follow externally fixed, incompatible hidden-root laws.

Positive local subunit kernels and positive hidden-root masses ensure positivity of all finite physical parent configurations. More specifically, the actual queried whole A table equals pi with probability exactly one half, conditional on every allowed unit-parent configuration. This addresses mechanism-table support, not merely positive probabilities for realized treatment values.

## 2. Simultaneous nested-tree contraction

Let I be the inner hedge and F the outer hedge, with A in F minus I. The bidirected spanning tree on I can be extended to one on F. The coefficient identity

    c_F = chi_(F minus I) c_I product_(v in F minus I) p_v

is an allowed-parent function: the compatible directed forest gives each outer-only vertex an outgoing edge to another F vertex, so its own variable occurs in the union of F's parent arguments. The inherited Fourier allocation assigns each character to a child for which it is an actual parent. No local kernel reads its own outcome through that allocation.

The new step is to place all outer Fourier labels and one additional inner label into the same local kernels. At a complete observed assignment the product expansion chooses one additive term or the baseline at each vertex. If any vertex chooses outer label j, connectedness of the outer tree forces every F vertex to choose that same label: on the first boundary edge, its mean-zero label is paired either with a constant or a different orthogonal label, and the term vanishes. This argument includes boundaries adjoining an inner-labelled vertex, including an edge absent from the inner tree. If there is no outer label, the same argument on the inner tree allows only an all-I inner term or the baseline. Because I is nonempty, an all-F outer term and an all-I inner term cannot coexist in one product term.

Thus only the baseline, the complete inner perturbation, and the complete outer Fourier modes remain. Their physical hidden-root contractions yield exactly

    q_(sigma,t) = p_0 + sigma lambda Psi - 2 sigma lambda t Psi.

Putting every model sign and Fourier-coefficient sign at a fixed vertex of I keeps all A coefficients common between the two models. Multiplying only A's outer terms by t changes the entire outer contribution and no non-A kernel. At t=0, A is its baseline pi with no residual hidden-parent or observed-parent dependence. At t=1 the alternative table is the same in both models. It is distinct from pi: at A there is a nonzero outer mode on an incident tree edge, and distinct orthogonal mode products cannot cancel identically.

All added local terms sum to zero over their own binary outcome. For fixed finite labels and coefficients, their absolute sums tend uniformly to zero with lambda. The claimed common positive lower bound follows by choosing lambda small enough relative to the minimum baseline cell. This is positivity of the actual physical kernels, not positivity added to an already marginalised distribution. Singleton I causes no exceptional failure: its inner term is a direct local perturbation and requires no inner edge.

## 3. Exact natural equality and policy inequality

Let q_+=p_0+lambda Psi and q_-=p_0-lambda Psi. With the common fair private switch, the two models have the same observed table law

    (delta_(q_+) + delta_(q_-))/2.

They differ only in which unobserved switch label produces each observed table. Both models also have the same natural two-table A-mechanism distribution. Observed unit covariates are independent of this switch in the witnesses. Therefore the full observation Law(C,Q_O) agrees, not just a collection of marginals or moments.

The intervention replaces A's mechanism by pi, which is exactly the t=0 setting. It removes the switch dependence at that node and yields q_sigma for every unit. For m subunits per unit, the original finite record law is exactly

    (q_+^(tensor m) + q_-^(tensor m))/2

in either model. The same compatible unit law and independent units then give agreement for every finite observational dataset. No limiting approximation is used in this equality.

I independently checked the selected-outcome transfer. In the directed route forest K avoiding A, each nonsink has one selected child and the sinks form a nonempty T subset of Y. Write

    L_v = x_v product_(u in J_v) x_u.

Acyclicity makes x_K to L_K a triangular bijection. The product of all L_v equals the sink parity chi_T. The baseline factors and the monomial c_I therefore give

    sum_x chi_T(x) Psi(x) = 2^(-|K minus I|) > 0.

This calculation permits paths merging, re-entering the outer hedge, or passing through another inner vertex; those are already encoded by the selected-parent factors. A is outside K, so its independent baseline pi sums to one. Hence the selected parity expectation differs by 2 lambda times this positive constant, and the positive-parity event differs by lambda times the constant. This proves a distribution discrepancy at the *same fixed soft policy* for every positive pi, without requiring a treatment-value contrast or relying on cancellation between hard-action arms.

The small two-node fixture also checks directly: under A's alternative table, E[H|A=a]=a/2 and the displayed outcome mean changes from sigma/16 to -sigma/16. Its natural observed table mixture agrees and the policy success probabilities are 17/32 versus 15/32. This is a useful scope illustration, not the justification for the general theorem.

## 4. Sufficiency and conditioning

Condition on all unit variables and private unit disturbances. The remaining per-subunit experiment has fixed local kernels and independent subunit disturbances, including independent semi-Markovian hidden roots conditional on those unit quantities. Its observed joint is Q_O. A successful ordinary ID expression holds for every such flat model and returns the selected policy law pointwise by averaging the hard-action ID formula against pi.

No subunit-to-unit feedback is essential here: replacing A does not change the conditioning unit state or another chosen subunit mechanism. Consequently Q_Y^pi=F_pi(Q_O) pointwise, and the measurable pushforward of Law(C,Q_O) identifies both the requested joint law with C and its expectation. This argument uses selected-outcome ID directly; it does not silently require successful identification of the full observed interventional joint.

## 5. Capacity and exact quantifiers

The baseline expansion contributes at most 2^(h+1) outer Fourier modes, where h=|(F minus I) intersect K|. Since K avoids A and I is nonempty, h is at most d-2. There is one additional inner label. Thus at most 2^(d-1)+1 nonconstant mutually orthogonal functions are required, alongside the constant function.

On 2^(d-1)+2 equally likely states, the stated Helmert construction supplies those functions. Pairwise orthogonality suffices: each independent hidden root enters only its two endpoint kernels, so the contraction never requires joint independence of the different labels on a single root. Each mode's positive norm factors can be corrected separately in its coefficient product; the inner tree having fewer edges is harmless. The capacity can be fixed from d before choosing either model, the policy, or the selected outcome. Larger prescribed alphabets with free positive masses can be partitioned into equally weighted groups as stated.

The construction therefore does not establish the general conclusion for fixed binary hidden roots or for an externally prescribed incompatible hidden-root distribution. It makes no uniform positive lower bound on the size of the policy discrepancy. Its whole-policy support probability remains one half even if the admissible lambda becomes small.

## 6. What this review establishes

Within the source's precise no-feedback class, the private-switch converse is a substantive extension of the older universal-unit-root composition: arbitrary prescribed unit graph structure no longer needs to contain that selector. The proof preserves the original observation experiment, the queried whole-table support, and positive physical kernels while keeping observed subunits binary.

This does not resolve general feedback/receiver constraints in HCMs, give completeness for every numerical scalar contrast, or establish publication priority. Ordinary hedge completeness, the held positive Fourier constructions, and mixture-label ambiguity remain explicit dependencies. A separate primary-literature comparison is still required before presenting the extension as a novel contribution.
