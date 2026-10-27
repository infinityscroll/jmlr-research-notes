# Root review of the polynomial selector

28 October 2026. This records the root agent's reconstruction of the complete
new proof, followed by inspection of the independent review. It is an internal
mathematical review, not external expert validation or formal verification.

The final source is `design_compression_selector_theorem.md`, SHA256
`188c39bfbe31e11b668bddd7d31d251a56ba4d179b72fb7d23fbfb6339b70a16`.
The full reconstruction preceded the sole final change from `p-J` compression
eliminations to `max{p-J,0}`. That clarification changes no algorithm or bound.
The imported statistical source is `../joint_adaptation_gate_20261028/joint_adaptive_upper.md`,
SHA256 `7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd`.

**Verdict: no blocking error found in the stated exact-real-arithmetic theorem.**

The log-determinant progress bound is uniform even when the current maximum
leverage is huge: monotonicity permits replacement by K+delta *before* applying
the elementary logarithm inequalities. Concavity gives the stopping certificate,
and M <= p M0 bounds the entire objective gap by K log p. This avoids an
unstated minimum-eigenvalue or unknown-coordinate input to the iteration count.

Constructive compression preserves total weight and the covariance, which are
exactly the objects needed later. The deterministic estimates must be applied
again to the compressed weights; retaining an earlier atomwise error bound
would not suffice. The proof does reapply them. Near-optimal determinant and
the trace upper bound give a fixed covariance condition bound. The stronger
linear estimate follows instead from the weighted trace deficit and the
substochastic simplex inequality

    ||B-e_argmax B||_1 <= 2(1-||B||_2^2).

Thus there is no illicit inference that near-optimal determinant makes the
ellipsoid O(error)-close in every direction. After compression, the number of
atoms is bounded by J; deleting weights below 1/(8KJ) preserves at least one
representative of each vertex and bounds every retained row's error linearly.

I checked the whitening orientation: with x=vT and L'ML=I, the transformed
vertices have row matrix R=T^(-1)L and RR'=(T'MT)^(-1). The unknown, possibly
ill-conditioned T cancels. Greedy row pivots have a constant residual gap
between an already selected vertex and an unselected one, including the
perturbation of the previously selected span. The selected *raw* rows therefore
have the same bounded inverse and linear selection error as the former
exhaustive selector.

The statistical transfer uses the existing spectral event, truncated maximum
row excess, and expected designated-anchor penalties. It does not assume an
untruncated excess is integrable. Observable optimization tolerance contributes
only delta times row mass; summing those masses gives delta, controlled by the
same effective noise level. Bad selection events use the bounded fallback and
Markov's inequality on truncated excess. The existing same-data cutoff then
applies unchanged. No independence from the selected rows is assumed.

The exact finite certificate (777 assertions on eight fixtures) checks useful
algebra but is not evidence for the general statistical or complexity theorem.
The independent analytic review also found no blocker and correctly separates
those roles. The arithmetic count is polynomial in p, K and the token count;
it does not prove finite-bit numerical stability, a strongly polynomial bound,
or faster practical training. Exact anchors, fixed K and the inherited strong
topic geometry remain. Classical optimal-design, compression and simplex
selection ingredients are not new; priority of this statistical composition
requires a separate literature judgment.
