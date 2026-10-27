# Independent audit: simultaneous policies with private switches

28 October 2026. Full analytic review of the new multi-policy extension, its bound single-policy construction, the earlier finite-mode realization/routing argument, and the relevant original-model definitions. No producer source was edited. The producer's finite checker was not rerun or used as a substitute for the arbitrary-graph proof.

**Bound source:** `multiple_policy_completeness.md`, SHA256 `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf`.

**Dependencies inspected:** the prescribed-unit single-policy source `274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`; flat multimode theorem `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147`; selected-joint corollary `8119664d55ca00547478e336784a0143a359d20c47fe3623e877b590dac282bf`; and the orthogonal hidden-label compression source `1dfc788b295bf9dc30202bfa7315f5eb44f98b662b04c6794b543ef84cd7d6af`.

**Verdict:** no blocking mathematical error found within the stated binary-observed, sufficiently rich finite-hidden, no-feedback, unconditional product-policy class. The independent-switch construction genuinely supplies joint natural policy support and equality of the complete observed experiment. No repair is requested. The same graphical iff also extends to the larger class imposing only individual actual-policy support, by the separate quantifier argument in Section 7 below. Neither statement is unrestricted HCM completeness or a publication-priority verdict.

## 1. The hedge must concern the complete action set

I checked the actual-query version in [Shpitser, *When does the ID algorithm fail?*, Proposition 1(1)](https://arxiv.org/html/2307.03750v1). Failure for `P(Y|do(B=b))` supplies a hedge whose inner set I is disjoint from **all** B, whose outer set F intersects B, and whose common roots reach Y along paths avoiding B. The older criterion phrased using arbitrary treatment subsets is not used; the cited note explicitly explains why that formulation is incorrect.

Every inner vertex reaches a common root within the inner directed forest, hence reaches Y without B. Choosing edges that decrease shortest distance to Y produces the required route forest K, with every nonsink having one selected child and with sinks T contained in Y. This is valid for a selected joint outcome; no common single sink is required. The inner set is nonempty, so `1<=k=|F intersect B|<=|F minus I|<=d−1`.

## 2. All switch operations remain local and legal

The matching coefficient

    c_F=chi_(F minus I) c_I product_(v in F minus I) p_v

is a function of allowed F-parent arguments. Each outer-only vertex is not a common root and therefore has a selected directed child in F. Its own variable belongs to the union of F parent sets. The Fourier allocation sends each such character to an actual child; it never lets a local kernel read its own output.

Because I avoids B, no treated vertex has an inner perturbation. Multiplying every outer summand at treatment a_j by its own flag t_j makes its t_j=0 table exactly its baseline pi_a, with no leftover hidden-parent or observed-parent argument. Put all model-sign and Fourier-coefficient signs at one vertex of I. Then **every treated table**, not just its marginal distribution, is the same in the two models. A treated vertex's alternative table is genuinely different from pi: it has a nonzero outer mode on an incident outer-tree edge, and distinct orthogonal mode products cannot cancel identically.

The original [HCM Definition 1 and Definition 2](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf), printed p.10, give each subunit mechanism its own private unit disturbance and allow simultaneous replacement of a set of subunit tables. Thus independent Bernoulli flags at separate treatments are legal, including when there is no endogenous unit variable. No node reads another node's flag, and no new latent cause or graph edge is being inserted. Unconditional product policies are exactly within this intervention language; the note does not silently establish parent-dependent or correlated policy completeness.

## 3. Nested-mode contraction gives the exact AND coefficient

At a complete observed assignment, expanding the product of local kernels chooses one additive mode or baseline at each vertex. If any vertex chooses an outer label, a nonconstant mean-zero factor appears at a tree boundary unless every F vertex chooses that same outer label. Pairwise orthogonality also kills boundaries against a different inner/outer label. Without an outer label, the same argument on the inner tree leaves only an all-I inner term or the baseline. An all-I term and an all-F term cannot coexist in one product term, since I is nonempty.

Consequently the only possible outer contribution collects one factor t_j from each treated outer vertex, giving exactly

    q_(sigma,t)=p_0+sigma lambda Psi
                       −2 sigma lambda (product_j t_j) Psi.

This is an AND, not a parity operation. It does not require coordination between private disturbances. Every local summand sums to zero over its own binary outcome. The finite perturbation sums tend uniformly to zero as lambda decreases; choosing lambda small relative to the fixed positive baseline cells preserves strict positivity in both signs and every flag state.

The contraction uses only independence across existing pairwise roots and orthogonality of labels on each root. It does not require independent labels on the same root. The inner tree being a proper subtree causes no additional mixed term: at an outer boundary absent from the inner tree, the unmatched outer label simply has mean zero.

## 4. Exact support and complete observational equality

For independent flags with `P(t_j=1)=(k+j−1)/(k+j)`,

    P(all ones)=product_(j=1)^k (k+j−1)/(k+j)=1/2,
    P(all zeros)=product_(j=1)^k 1/(k+j)=k!/(2k)!.

Every flag configuration has positive probability. The complete table law is therefore the same equal mixture of q_+ and q_- in the two model signs, despite the different number of flag states producing each atom. A literal policy replacement sets all affected tables to their zero-flag baseline; it is not conditioning on the natural all-zero event. It yields q_sigma deterministically.

Each switch is independent of all prescribed unit parents in these witnesses. Hence the joint policy atom has the displayed probability conditional on every allowed unit-parent configuration. The individual support probabilities are also positive; actions outside F are always at their policy. This verifies support of entire conditional mechanism tables, not merely positive sampled treatment-value probabilities.

One common compatible unit-variable law is used in both models. Subunit mechanisms may ignore permitted unit parents because the class has no faithfulness or minimum-effect requirement. Thus equality holds jointly with observed unit covariates C. Given the flag vector, subunit records are iid from q_(sigma,t). For any m the complete natural record law is precisely

    (q_+^(tensor m)+q_-^(tensor m))/2.

Independent units then give equality for every finite original observational dataset. This is stronger than equality of pooled means or selected marginal moments. Positive physical kernels and hidden-root masses also satisfy the source's subunit-level positivity requirement; no unsupported auxiliary table intervention is used.

## 5. The selected discrepancy survives every prescribed product policy

The route K excludes every treatment. Consequently its noisy-parity baseline kernels and inner coefficient involve no treatment value. In the exact signed kernel, every action contributes only its independent baseline factor pi_a, each summing to one. On K, the triangular sign transformation

    L_v=x_v product_(u in J_v) x_u

is a bijection, and the product of all its coordinates equals chi_T because each nonsink appears once as its own sign and once at its selected child. Fourier orthogonality gives

    sum_x chi_T(x) Psi(x)=2^(−|K minus I|)>0.

Thus the selected parity expectations at the same simultaneous policy differ by `2lambda 2^(−|K minus I|)`. There is no cancellation over hard-action assignments, including nonuniform or fair policies. Re-entry into F or I is already handled by the parent characters and does not overwrite a base equation.

Conversely, on flat-ID success condition on all unit variables and all private unit disturbances. The per-subunit model then has fixed positive kernels and independent subunit disturbances. No feedback implies that the simultaneous action changes none of those unit quantities and no untreated selected kernel. Summing the pointwise flat-ID formula against the product pi_B gives M7 in every realized unit. Its measurable pushforward jointly with C, and its expectation, therefore identify the stated hierarchical targets.

## 6. Hidden capacity and fixture arithmetic

Write `h=|(F minus I) intersect K|`. The route factors contribute at most 2^h outer Fourier modes and the k action baselines at most 2^k. These two vertex sets are disjoint because K avoids B. Hence `h+k<=|F minus I|<=d−1`. Multiplication by the remaining fixed monomial does not increase the count. There is one additional inner label and one constant function, so `2^(d−1)+2` root states suffice for the orthogonal-label realization. Larger prescribed alphabets with a freely chosen positive law can implement the required effective labels by grouping. This is not a claim for arbitrary fixed binary hidden roots or a separately fixed incompatible root law.

The small fixture checks directly without a numerical calculation. Averaging the product of M8 over its two fair hidden bits leaves the baseline `1/8+sigma y/512` and the sole outer contraction `−sigma t1 t2 y/256`. This equals M9. The four flag probabilities are `1/12,1/4,1/6,1/2`; the smallest Y cell is `31/128`; and the policy risks are `65/128` and `63/128`. The fixture is consistent with the theorem but is not used to establish arbitrary-graph completeness.

## 7. Valid extension to individual-support-only models

Fix every other assumption. Let C_joint be the source's class requiring positive natural probability of the whole queried table tuple, and C_ind the larger class requiring only the original individual-action support conditions. Joint positivity is **not** inferred from individual positivity.

If flat ID succeeds, the pointwise identity M7 holds for every model in C_ind; it does not use the natural probability of the joint table tuple. Therefore the effect is identified throughout C_ind. If flat ID fails, the displayed pair belongs to C_joint, hence also to C_ind, and has equal observations with different targets. Therefore the same uniform graphical iff is valid in C_ind, with witnesses satisfying the stronger joint support property.

This is a quantifier consequence of the already proved two directions, not a new construction. It preserves the no-feedback graph, positive physical kernels, finite-capacity and unconditional-product-policy qualifications. It does not establish data-specific nonidentification at every observed law, a preassigned scalar ATE discrepancy, or a general feedback/receiver result.

## 8. Research scope

The inspected primary HCM definitions permit the construction. Ordinary ID, the actual-query hedge theorem, positive Fourier modes, and deterministic route cancellation remain established or held ingredients. This addendum closes the additional multiple-private-switch and joint-support seam. It does not prove incompleteness of the authors' augmentation toolbox and does not settle their receiver-induced numerical-constraint problem. Its historical novelty and significance require a separate specialist comparison; this internal audit is a correctness assessment only.
