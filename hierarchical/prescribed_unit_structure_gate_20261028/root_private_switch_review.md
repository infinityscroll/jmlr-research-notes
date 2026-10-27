# Root review of completeness on prescribed unit graphs

28 October 2026. Final source `private_switch_completeness.md`, SHA256
`274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`.
The root read the full construction and the imported positive multimode hedge,
selected-target, capacity, and earlier supported-lift arguments. The final
source clarifies two scope phrases about subunit-associated private unit
disturbances; those changes do not alter the construction. This is internal
analytic review, not formal verification or external validation.

**Verdict: no blocking error found in the precise stated class.**

The important change is the original-HCM implementation of the observational
label swap. It uses A's own allowed unit-shared private disturbance. It does
not introduce an extra common unit variable or let another mechanism read
that disturbance. Thus the construction remains available when the prescribed
endogenous unit graph is empty. Unit variables may have a common strictly
positive law and mechanisms may ignore allowed arrows in this unrestricted
nonparametric class. A faithfulness or informative-variation requirement would
be a different model.

I checked simultaneous inner and outer modes on nested spanning trees. Any
nonzero outer mode must occupy the entire outer tree: its first boundary edge
otherwise has zero expectation by mean zero or orthogonality. With no outer
mode, the inner mode must occupy the entire inner tree. These two full modes
cannot occur in the same product term because their vertex sets overlap.
Putting all model signs at an inner vertex leaves the treatment table common
to both models. Multiplying only its outer modes by the private binary switch
therefore gives exactly

    q_(sigma,t)=p0+sigma lambda Psi-2 sigma lambda t Psi.

The fair switch produces the identical two-atom law of the complete observed
within-unit distribution in both models. This implies equality of every
finite observational record, not only pooled marginals. At switch zero the
actual whole A table is the queried positive policy pi. Setting that table
by intervention yields q_sigma in every unit. Its natural conditional support
probability is exactly one half in both models; treatment-value positivity
alone is not substituted for policy-table support.

Positive local kernels are obtained by choosing lambda small before
marginalization. The alternative treatment table differs from pi because its
nonzero orthogonal modes cannot cancel identically. The directed route-forest
calculation transfers the perturbation to a nonempty parity of the requested
outcomes: its coefficient is 2^(-|K minus I|)>0. This proves a selected-vector
discrepancy for the same fixed positive policy, while making no claim about
every preselected scalar contrast or a uniform lower bound on effect size.

The converse uses at most 2^(d-1)+1 nonconstant orthogonal labels. Each hidden
root enters two endpoint kernels, so pairwise orthogonality suffices; the
labels need not be independent on that root. A positive finite distribution
on 2^(d-1)+2 states supplies enough labels. This is a sufficient capacity
bound and does not cover an arbitrarily prescribed binary hidden-root model.

For sufficiency, fixing the complete unit state and private disturbances gives
the ordinary flat subunit model. Successful selected-target ID yields the
policy law pointwise from the observed within-unit law. The absence of any
subunit-to-unit arrow ensures that replacing A changes neither this unit state
nor another subunit mechanism. Pushing the observational law through that
functional identifies the joint law with observed unit covariates and its
pooled expectation. This is the exact place where feedback remains excluded.

The independent audit agrees on these steps. Finite exact fixtures include
overlapping trees and nonuniform policies; they supplement rather than prove
the general graph argument. The result removes the universal common-unit-root
assumption of the earlier portfolio theorem. It remains a restricted
completeness result, not a resolution of general receiver/aggregation
completeness in the source paper. Primary comparisons have not established
historical novelty or external significance.
