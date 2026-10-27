# Independent hostile audit of the vocabulary-explicit upper bound

27 October 2026. Reviewer: `/root/hcm_adversarial_boundary`.

Bound theorem: `root_growing_vocabulary_upper.md`, SHA256
`de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`.
Bound estimator/geometric dependency: `general_k_upper.md`, SHA256
`56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`.
Both sources were read directly and left unchanged. The concentration route
was independently reconstructed before receipt of the final theorem.

**Verdict:** no blocking mathematical error found in the stated upper bound.
The constants can be independent of p under the stated fixed K, prevalence
floor and unnormalized topic singular-value floor. The balanced-half argument
retains the full document-length variance scale; no independence of all token
pairs is assumed. This is a mathematical audit, not formal verification,
external expert review, computational validation, or novelty clearance.

## 1. Hilbert concentration and exact pair identities

I checked the self-contained Hilbert Bernstein derivation rather than importing
an iid scalar inequality. The radial Hessian eigenvalue of
`cosh(lambda ||x||)` is `lambda^2 cosh(lambda ||x||)`; its transverse eigenvalues
are smaller by `tanh(t)<=t`. The bound extends to zero by continuity. Taylor's
remainder, centering and successive conditioning give the stated exponential
bound with the sum of second moments. The power-series estimate and tail
integration yield U2 for real q>=2, with a numerical constant independent of
the Hilbert-space dimension. Nonidentical documents and conditional fixed
coefficients are allowed. The zero-variance case is correctly separated.

For the full factorial-pair statistic, expansion of the centered token products
gives U3 exactly, including diagonal subtraction. For a fixed row j, only an
ordered token pair matching itself or its reversal contributes to its squared
norm expectation. Their respective contributions are

    Gamma_jj tr(Gamma),     ||Gamma_j:||^2.

Thus U5 is a vector-row identity, not a sum of p separately bounded coordinates.
Summing the identity gives `[(tr Gamma)^2+tr(Gamma^2)]/[N(N-1)]<=2/[N(N-1)]`.
Independent centered documents then give both dimension-free Qbar bounds.

The first-order factor E also has dimension-free second moments. The pointwise
prevalence bound `pi_ij<=d_j/mu0` and exact identity
`sum_i w_i' Sigma^(-1) w_i=nK` prove U4. The nN summands for E_j have norm at
most `1/(nN sqrt(beta))`, so U6 includes the necessary linear Bernstein term.
The scalar frequency estimate U7 is valid for the nonidentical token indicators.
Zero-mass rows vanish almost surely; no division by such rows is required.

## 2. The balanced-half proof preserves the N-squared scale

For any N>=2, let L=floor(N/2) and H=N-L. A uniform split puts any ordered
pair of distinct token positions in its first and second groups with probability
`LH/[N(N-1)]`. Averaging either cross-product over that split therefore recovers
the full ordered-pair statistic, and symmetrizing preserves it. This verifies
U8 for even and odd N. Conditional Jensen for the convex norm power, followed
by Minkowski, legitimately transfers the split-statistic bounds to Qbar.

For `S_j=n^(-1) sum_i a_ij b_i`, condition on the first halves. The remaining
summands have norm at most `2/(nH)` and total conditional variance at most
`sum_i a_ij^2/(n^2 H)`. The scalar-coordinate vector `(a_1j,...,a_nj)` is itself
a sum of nL independent centered vectors in R^n, with variance sum at most
`n d_j/L` and increment norm at most `1/L`. Applying U2 to this stacked vector
and then to the conditional second-half sum gives precisely

    C [q sqrt(d_j)/sqrt(nLH)
                    + q^(3/2)/(nL sqrt(H)) + q/(nH)].

The transposed row is `n^(-1) sum_i b_ij a_i`; exchanging L and H supplies
the same argument. Since both group sizes are at least N/3, the last two
terms are bounded by `C q^2/(nN)`. This proves U9 with no hidden p factor.
It does not approximate the full U-statistic by n*floor(N/2) independent pairs.

## 3. Spectral event and affine reconstruction

On G0, the stated constants give

    sigma_min(M)^2 >= 9 kappa0^2 beta/16,
    ||R||_op <= kappa0^2 beta/32 + kappa0^2 beta/16
              = 3 kappa0^2 beta/32.

Consequently the Kth selected eigenvalue is positive and
`H0'H0 >= 3 kappa0^2 beta I/8`. The analysis-only coordinate map is invertible.
Direct multiplication of `Chat=MM'+R` establishes the exact transformed identity
in U10. In particular,

    ||(EE')_j|| <= ||E_j|| ||E||_op

absorbs the EE' contribution into `C||E_j||/sqrt(beta)` on G0. This is a
pathwise estimate and requires neither independence of E_j and the eigenspace
nor an additional inverse-beta factor. The resulting delta_j is defined on all
outcomes; its unconditional mean is bounded by `C sqrt(d_j) a_n`.

One implicit but valid detail in U12 is worth spelling out. Markov applied to
the global second moments first gives a bound of the form
`min(1,C a_n^2)`. This is at most `C' a_n`: use `a_n^2<=a_n` when a_n<=1,
and probability at most one otherwise. Thus the displayed U12 bound holds
uniformly without an extra sample-size assumption.

The coordinate transformation does not change the observable estimator.
Every candidate determinant is multiplied by the same nonzero determinant,
and the right transformation cancels from reconstruction. This remains true
when the transform depends on the data and the unknown population parameters;
it is a pathwise analysis identity, not an oracle implementation.

## 4. Screening and the maximum normalized row error

For q=2+log(p), the maximum Lq inequality contributes at most the universal
factor `p^(1/q)<=e`. Inserting U6, U7 and U9 into the definition of Z gives
the two terms in U13. I checked the linear terms explicitly: the largest is
`C q^2/(nN beta alpha)`. It is retained; no rare-row denominator is silently
bounded by a constant. The inequalities for `sqrt(d)/(d+alpha)` and
`1/(d+alpha)` are uniform, including d tending to zero. Also beta<=1 follows
from the stochastic-column constraint and `trace(Sigma)<=1`.

On small Z, an anchor with d_j>=alpha has empirical mass at least
`(1-2Z)d_j`, so remains in the screen. A row with d_j<alpha/4 has empirical
mass below `alpha/4+5Z alpha/4`, hence cannot enter. Every retained row then
satisfies `d_j>=alpha/4`, `d_j+alpha<=5d_j` and `dhat_j>=d_j/2`.
These inequalities prove U14 simultaneously for the entire retained set,
including its data-selected members. No conditional-on-selection concentration
statement is needed.

The dependency's maximum-volume lemma has constants depending only on K.
Its proof uses determinant perturbations of K-by-K matrices, stochastic row
norms and a row-collision argument; the number of available candidate rows
does not enter. All K exact coordinate vertices remain available through the
retained anchors. It therefore applies with error 10Z even when p grows.

## 5. L1 recovery, bad events and the final rate

On the good event, transformed reconstruction is
`(A diag(mu)+D) Bhat^(-1)` with Bhat close to a permutation and bounded inverse.
The signal matrix A diag(mu) has total mass one. Hence its mixing error costs
`C Z`, while its additive row error costs `C sum_j delta_j`, independently of p.
Clipping cannot increase distance to nonnegative target columns; normalization
costs at most `2/mu0`, including the zero-column fallback. This proves U15.

Taking unconditional expectations of the nonnegative error envelopes avoids
any unjustified conditioning on the good event. Cauchy--Schwarz gives
`sum_j sqrt(d_j)<=sqrt(p)`, producing the explicit vocabulary term. The
complement costs at most 2K times its probability, bounded using U12 and
Markov for Z. Finally, with r as in Section 8,

    log^2(2p)/(nN alpha beta) <= r^2.

For r<=1 this is absorbed into r. For r>1 the deterministic loss bound applies.
Thus the claimed truncated risk bound follows with constants independent of
p,n,N,alpha,beta. There is no hidden assumption that N grows, that p is fixed,
or that a spectral or active-anchor gap beyond the stated hypotheses exists.

## 6. Scope of the verdict

The theorem is an upper bound for known alpha, fixed K and fixed positive
mu0,kappa0, using exact pure anchors and potentially expensive maximum-volume
search. Strong *unnormalized* topic geometry is material; fully diffuse columns
with entries uniformly of order 1/p generally leave this class. The theorem is
not itself an adaptive-alpha or weak-lq sparsity theorem.

The separately proved growing-vocabulary lower bound can support a
near-minimax comparison on its overlapping parameter class and stated
vocabulary/sample domains. This audit does not enlarge that lower-bound
domain or remove the logarithmic gap in the anchor-search term. The Hilbert
inequality, U-statistic conditioning, affine anchor geometry and max-volume
method are classical components. Correct composition and a source-bound
audit alone do not establish publication priority or newsworthiness.
