# Independent analytic audit: generic-p selected-path obstruction

28 October 2026. Reviewer: `/root/status_claim_check`, independently of the
root author and the separate concrete-p=3/2 producer/auditor.

**Verdict:** no mathematical blocker found in the stated theorem. No source
repair requested. This is an internal analytic review, not external validation,
formal proof checking, a novelty finding, or a numerical demonstration.

Bound source: `generic_p_open_input_theorem.md`, SHA256
`db10a99b365cb9de1c422d9ded8e4839c703f9656dfd11aae5684613660d4551`.
I read the entire source and reconstructed its update, row-map estimates,
inversion, discrete basin, asymptotic clock, and full-matrix comparators. I did
not use the separate p=3/2 result as a proof of this extension.

## 1. Exact native gradient and unrestricted dual invariants

Let `f/D` denote the nonconstant score coefficient `b+pi(a-b)`, where
`m=(a-b)h1'k` and `h1=x2+a d0`. Differentiation gives

    partial_a m=h1'k+(a-b)d0'k,
    partial_b m=-h1'k,
    partial_a(f/D)=pi+pi(1-pi)[m+(a-b)^2 d0'k],
    partial_b(f/D)=(1-pi)(1-pi m).

These yield the source's A, B and U and equation (6), including the path
through the moving upper query. The signed negative example gives the same
score and derivative, so averaging the pair introduces no extra factor.

The lower affine space is the image of `span{x1,x2}` under `r -> r d0'`.
Its orthogonal complement is exactly represented by the conserved G1 with
`G1 d0` perpendicular to that span. The upper decomposition has conserved
`G2 d0=0` and a varying coefficient split along x1 and its orthogonal
complement. Thus these decompositions allow all full-matrix initial states;
they are not rank or zero-offset assumptions.

## 2. Row-map constants, inverses, and uniformity

Writing `j=J_(p')`, the derivative of each row map is

    F_i'(r_i)=sum_j d0_j^2 |r_i d0_j+G_ij|^((2-p)/(p-1))/(p-1).

In the asserted nonzero leading cone, the expansion is uniform over bounded
offsets. Its leading value is
`c |r_i|^((2-p)/(p-1))/(p-1)`; substituting
`|F_i| ~ c |r_i|^(1/(p-1))` gives precisely
`C_p=c^(p-1)/(p-1)`. The second derivative has size
`O(s^(3-2p))`. Every dual entry is separated from zero at a scale comparable
to `s^(p-1)`. No smoothness at zero is being imported for p>2 or p<2.

For the lower inverse, the two coefficient derivatives of the limiting
logit map form a positive scalar multiple of M. Its quadratic form is
`sum_a |q*_a|^(2-p)(z1 x1_a+z2 x2_a)^2`, strictly positive for nonzero
(z1,z2). The uniform local inverse therefore exists. For global uniqueness,
two solutions satisfy
`(r-r')'[F_G(r)-F_G(r')]=0`; strict coordinate monotonicity makes every
summand nonnegative and at least one strictly positive unless r=r'. This
rules out an additional branch without assuming the trajectory's limit.

The target logits differ from (s,0) by O(log s). Rescaled offsets have size
O(s^(1-p)); hence the source's
`q/s=q*+O(log(s)/s+s^(1-p))` follows. The upper projection is likewise a
strictly increasing scalar function of t, tending to both infinities, and
has the asserted positive-t inverse and direction k*. In particular, the
slow offset decay when p is close to one is real but harmless for this
fixed-p asymptotic statement. No bound uniform in p is proved.

## 3. The effective metric and stable discrete field

The softmax expansions use exact `b=v/s`, `l1=s-x` and
`h1'k=s-(1-a)d0'k`. Since k=O(s), this gives
`m=s-v+O(s exp(-s))` independently of the slower row-offset error.
The lower row derivatives contribute M; the upper projection contributes
the strictly positive `a_top`. A dual increment O(exp(-s)) has a physical
Taylor remainder `O(s^(3-2p) exp(-2s))`. Dividing by the leading clock
`s^(2-p) exp(-s)` gives exactly the vanishing relative bound in the source.

The KKT equation gives
`q*=diag(|q*|^(2-p))(lambda x1-mu x2)` and therefore
`lambda M12=mu M22`. The stipulated positive multipliers force M12>0.
This verifies the positive equilibrium, rather than assuming positive
Euclidean query correlation suffices for every p.

I independently differentiated (13). The Jacobian is (14), with negative
trace and determinant `u* v* det(g)>0`. It is Hurwitz for every fixed
admissible instance. The finite product/Taylor expansion for
`v=s sigmoid(l2)` contributes O(1/s) and O(h) forcing, both covered by
`E(s)+h`. It does not replace the discrete algorithm by gradient flow.

## 4. First-exit closure and the clock

Equation (15) follows from the quadratic expansion and local coercivity.
One implicit absorption is valid: for sufficiently large s and fixed eta,
`h=O(s^(2-p) exp(-s)) <= E(s)`. Thus the O(h) component of the field error
is absorbed into O(E(s)), leaving the stated `h^2 E(s)^2` term. On the
outer annulus the negative term dominates; inside the smaller ellipsoid the
increment is uniformly too small to cross the full boundary.

The transverse dual increment is exactly proportional to `(1-a)U`.
Dividing by the physical clock yields `O(exp(-s)s^(p-2))`. This positive
envelope is eventually decreasing, has bounded logarithmic derivative, and
is integrable. Its discrete sum against h is bounded by a constant times
its integral when h<=1. Taking R0 sufficiently large prevents transverse
escape on every stopped prefix. This estimate and the ellipsoid estimate
close simultaneously; neither assumes convergence in advance.

The local inverse constructs a finite center with zero offsets; strict
inequalities then give an open preimage in every primal matrix coordinate
because the entrywise mirror map is a homeomorphism. The stationary offsets
are bounded on open balls in their complementary spaces, not fixed to zero.

A bounded clock would have a positive minimum increment, which is
impossible. Hence sum h diverges while h vanishes. The scalar contraction
with forcing `E(s)^2 -> 0` proves V->0 without any summability assertion for
E. Finally, for `T(s)=exp(s)s^(p-2)`, the mean-value theorem gives
`Delta T -> C*`. Inverting `T(s_n)/n -> C*` gives the exact signs and
coefficients in (16), including `(2-p) loglog n` in s and coefficient -1
in the second logit.

## 5. Global comparators and actual released metric

The rowwise Holder problem has unique solution
`W=q J_(p')(d0)'/c`, with norm `||q||_p/c^(1/p')`.
The isolated selected-query problem is unrestricted and has q=k*. Thus
the claimed fraction is `||k*||_p/||q*||_p`. It is strictly below one because
the positive second multiplier and independent normals preclude q*=k*.
This check does not restrict the comparison to the trajectory's affine dual
space. At the upper layer the actual moving normal converges to x1 d0',
which has nonzero optimal margin; continuity of the unique lp optimizer
gives the upper conclusion.

I also read the held released implementation. `SMD.step` with normalize=False
implements precisely the stated simultaneous native update (using gradients
computed at the common old state). `correlation_calculation.py` passes the
optimal matrix first and trained matrix second. The metric is therefore
`D_psi(optimal_unit,trained_unit)`. Both unit-norm potential terms combine to
one. Factoring the common right unit vector out of the dual pairing gives
exactly (5), not `1-R` for general p. Transposing both matrices to match the
paper's query/key convention preserves the entrywise norm and this pairing.

The explicit two-dimensional family has head scores 1 and 0, q*=(-1/3,4/3),
k*=(1/2,1/2), and the stated positive multipliers. Substitution confirms
(17), including its p=2 and p=3/2 specializations. Nonzero coordinates and
the nonsingular bordered KKT system justify the asserted local input
openness at each fixed p.

## Scope retained

The review supports the stated late-basin theorem for every fixed p>1 on
the stipulated open input class. It does not establish practical entry,
random or small initialization, all-p printed-cone compatibility, independent
perturbations of the paired examples, training of values/head, a zero limiting
loss, worse test accuracy, or a contradiction of the published one-layer
theorem. Nor does this audit settle the historical significance of the result.

Released-code bindings, under `attention/source/official/synthetic-data/`:

* `tools/optimizers.py`: `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`.
* `tools/bregman_div.py`: `c478f9ec5dd0eeadc8c766e3d9686d9d1366c07ca66af860b467012950c22a6c`.
* `correlation_calculation.py`: `a9e7a0d7665ea0731fcb4582c4fc2e1d4ac171326038041e2493fb6b6a2f1e9c`.

No experiments or source edits were needed for this review.
