# Independent audit: selected-path noncollapse theorem

28 October 2026. Analytic source-level review. No producer files were edited, no trajectory was rerun, and no finite diagnostic output was used to establish the asymptotic claim.

**Verdict: no blocking mathematical issue found in the fixed two-token, p=2 theorem as stated.** The proof supplies a finite open late-entry basin for the actual simultaneous full-matrix updates. In that basin the lower selected-path margin fraction tends to 2/sqrt(5), while the upper checkpoint comparator is attained and both memories remain separated.

## Source binding

`selected_path_noncollapse_theorem.md`:
SHA256 `46db3f866ad368b39f1bf600e730133a2f52570b6f4a24464aebb39e57187ae7`.

I read the entire source, the held released optimizer, `att_svm.py`, `bregman_div.py`, and the primary paper's Definition 5 and Theorem 10. The released optimizer SHA256 asserted by the source is `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`. This audit does not cover the separately proposed general-Gram extension.

## 1. Full gradient and signed-example reduction

Negating every input token leaves both attention score matrices unchanged and negates every value/output vector. Multiplying by the negated label restores the same signed score and parameter gradient. Thus the equal-weight two-example logistic loss produces exactly the single common signed-score update, with no missing factor two.

Writing `c=b+pi(a-b)` and `m=(a-b)h1'k`, independent differentiation gives

    m_a=h1'k+(a-b)d'k,    m_b=-h1'k,
    c_a=pi+pi(1-pi)[m+(a-b)^2 d'k],
    c_b=(1-pi)(1-pi m).

These retain the evolving upper query, both keys, and both values. With `A=a(1-a)c_a` and `B=b(1-b)c_b`, their matrix gradients are exactly S9. The query Gram entries are 1,1/2,5/4, giving S10 and both exact linear identities S11. In particular the negative B term is a genuine upper-key derivative, not an imposed sign or detached-memory approximation.

Every increment has right factor d'. The fixed right-null components in S12 are a consequence of the exact architecture, not a parameter constraint imposed by the proof. They have no effect on either row-softmax gap. They remain arbitrary finite initial coordinates and vanish after division by log t.

## 2. Uniform discrete clock expansion

On S13, the P bounds imply compact intervals for x and v, with v bounded away from zero, while |k2|<=2. Put t_a=1-a. Then

    t_a=exp(-z+x)(1+O(exp(-z))),
    h1'k=z+t_a(k2-z/2),
    (a-b)h1'k=z-v+O(z exp(-z)).

All constants can be chosen independently of the position in the stopped region. Therefore `pi(1-pi)=exp(-z+v)(1+O(z exp(-z)))`. Substitution gives

    A=exp(-z+x)(1+O(z exp(-z))),
    B=-v exp(-z+v)(1+O(1/z)),
    h=Delta z=rho exp(-z+v)(1+O(1/z)).

Here rho is bounded above and below by positive constants depending on fixed eta because the score lies in [1/2,1]. The exact ratio `Delta k2/h=t_a/(1-t_a/2)` is nonnegative. No derivative of rho or continuous-time approximation is required: the same positive factor cancels from the needed update ratios.

The discrete rescaling of v is consequential. Expanding `(z+h)sigmoid(l2+Delta l2)` gives the `b h`, `z b(1-b)Delta l2`, and product/Taylor terms shown in the source. Since `Delta l2=O(h)`, the logistic second derivative on the finite intervening interval is O(b), uniformly. After division by h, the omitted product terms are O(h), while `b h/h` and the `(1-b)` correction contribute O(1/z). This verifies S16 with uniform error O(1/z+h). In particular, its non-summable O(1/z) forcing is treated by contraction, not incorrectly discarded as a summable perturbation.

## 3. Finite invariant ellipsoid and other boundaries

The equilibrium equations give `v*=1/2` and `exp(x*-v*)=5/4`. Differentiating F yields exactly

    J=[[-5/4,7/4],[5/16,-15/16]].

Direct rational multiplication verifies `J'P+PJ=-I`. The symmetric matrix P has P-I/5 positive definite and trace(P)<3. On the stated small Euclidean ball, the two Hessians give a Taylor remainder smaller than the conservative `10||e||^2` bound. Hence the cubic term in `2e'PF` is at most `60||e||^3`; since the stopped ellipsoid implies `||e||<=sqrt(5)/1000`, S18 follows with room to spare.

The exact quadratic increment is used before any first-exit conclusion. The second-order term is at most `C h^2(||e||^2+z^-2)`; its first part is absorbed into the negative drift once R is large. This establishes S19. On the outer annulus, `||e||` has a fixed positive lower bound, so the O(1/z) perturbation cannot defeat the inward drift for sufficiently large R. Inside the smaller ellipsoid, the separate O(h) displacement bound prevents a discrete jump beyond the outer boundary. Thus an inward continuous vector field is not being used as a substitute for discrete invariance.

Independently, `Delta k2<=C exp(-z)h`. Because z is increasing and h<=1, the integral comparison in S20 bounds its entire possible accumulated increase by C exp(-z0). Choosing this below one closes |k2|<=2 from every |k2(0)|<1. The lower z boundary cannot be crossed. Constants depend only on eta and the fixed compact region; increasing one finite R closes all three boundaries without assuming the eventual limits.

The map from the eight matrix entries to `(l1,l2,z,k2)` is surjective because x1,x2 are linearly independent and d is nonzero. The strict initial inequalities therefore define a nonempty open subset of the full parameter space. The source does not claim that the diagnostic z=4 satisfies the existential threshold R0.

## 4. Divergent clock and matrix limits

If z were bounded inside the invariant set, the lower bound `h>=c_eta exp(-z)` would prevent convergence to a finite value. Thus z->infinity, h->0, and sum h=infinity. Young's inequality applied to S19 yields S21 with nonnegative contraction coefficient on a sufficiently late tail. Unrolling it eliminates the finite prefix and drives V to zero because its forcing coefficient z^-2 vanishes. This proves x->x*, v->1/2; it does not presuppose either limit in the clock-divergence argument.

The converged score gives the asserted rho*. Then `exp(z)Delta z -> rho*exp(1/2)`. The exact exponential increment differs by a relative O(h), so Cesaro averaging proves S22. In particular `l2=-log log t-log 2+o(1)` follows from the exact identity b=v/z. Solving the original query equations yields

    W1 d=(l1,l2-l1/2)',    W2 d=(z,k2)',

and S12 supplies the stated complete-matrix limits. The two memory limits are x1 and x2, not a common token; their distance is sqrt(5)/2.

## 5. Global selected-path comparator and source metric

At the prediction path, the upper attention eventually selects h1, originating from the lower query x1, and that lower query selects key1. The negative example gives the same constraint normal after both signs cancel. The lower comparator therefore has the single distinct full-matrix constraint `<C,W>>=1`, with `C=x1 d'`.

Cauchy–Schwarz over all real 2-by-2 matrices gives the unique optimum `C/||C||_F^2`; no gradient-invariant subspace or diagonal restriction is imposed on the comparator. The limiting lower matrix has norm one and margin one, while `||C||_F=sqrt(5)/2`. Hence its normalized margin fraction is exactly 2/sqrt(5), and the unit-normalized quadratic Bregman discrepancy is exactly `1-2/sqrt(5)`.

The upper checkpoint normal `h1(h1-h2)'` converges to C. The upper trained direction converges to C/||C||, so both its margin fraction and Bregman metric attain their optimum with a nonzero comparator scale. This distinguishes the result from an unused-query-only measurement or a collapsing-memory normalization.

The [paper's Definition 5](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf) and released `att_svm.py` use `(x_selected-x_other)'W z`. Transposing W gives the source's row-query convention and preserves the Frobenius objective. The released unnormalized SMD update at p=2 is exactly ordinary gradient descent; its Bregman utility normalizes both flattened arrays. At p=2 both argument orders yield the same half-squared Euclidean distance. This verifies the metric mapping without importing a factorized or constrained comparator.

## 6. What this verdict does not establish

The counterexample addresses an unrestricted layerwise selected-path directional claim in this two-layer direct-matrix self-attention architecture. Its late basin approaches a direction whose cosine to the selected-path optimum is 2/sqrt(5). It does **not** refute every possible depth-two theorem with a sufficiently narrow initialization cone around each comparator. The published one-layer theorem and its stated initialization hypotheses remain intact.

The source proves no arbitrary-small/random initialization result, certified numerical entry threshold, trainable-head/value result, generic input-neighborhood result, non-Euclidean p result, or generalization claim. Its fixed-head score approaches one and the loss approaches log(1+exp(-1)), not zero, consistently with the bounded output range. No historical priority or newsworthiness conclusion follows from this internal proof audit.
