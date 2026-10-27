# Selected-path attention: a targeted implicit-bias subsumption test

28 October 2026. New primary-source comparison and a direct test of a proposed
reduction. This note does not certify historical novelty or external validation.
It does not change any held theorem.

## Result being compared

The held positive-Gram theorem proves an open finite late-initialization basin
for constant-step GD on two simultaneously trained, unrestricted direct
self-attention matrices. The lower matrix has limiting direction proportional
to `q_* d'`, where `d=x1-x2`,

    q_*=(||x2||² x1-(x1'x2)x2)
             /(||x1||²||x2||²-(x1'x2)²),
    x1'q_*=1, x2'q_*=0.

It therefore solves the quadratic problem with constraints `x1'Wd>=1` and
`x2'Wd<=0`, while the actual selected-path comparator has only the first
constraint. Both lower memories remain distinct; the second lower logit is
`-log log n+O(1)`. The upper comparator succeeds. Head and values are fixed,
the loss has a positive infimum, and there is no accuracy or generalization
failure claim. The separate printed-cone result shows that checking the two
isolated one-layer initialization conditions does not prevent this limit.

Bound sources, relative to the portfolio root:

* `attention/selected_query_coupling_gate_20261028/positive_gram_extension.md`,
  SHA256 `29c18514bf16ab7282b227e46bafcee71e677332644c92af8d2ff78ccd97fc36`.
* `attention/selected_query_coupling_gate_20261028/printed_single_layer_cone_compatibility.md`,
  SHA256 `bcd9d2fbb6270cf036b4daf27d87f9a59200f2e3ab7db1de78dd33abd08a4ec5`.
* Starting comparison: `attention/selected_query_coupling_gate_20261028/primary_scope_comparison.md`,
  SHA256 `f1f16e5539c703560c633ef2313c4fdd5c9ed444275d2a024561223794b0618f`.

The earlier comparison already inspects attention-SVM, JoMA, trained embeddings,
stagewise two-layer causal-learning, and the generic near-homogeneous theorem.
The comparisons below add new candidates and test a stronger proposed import.

## 1. A genuinely close general candidate: lexicographic margins

Nacson, Gunasekar, Lee, Srebro and Soudry (ICML 2019) distinguish constrained
minimizers from GD iterates. Their Section 3.2, equation (10), assumes a finite
sum of positive-homogeneous submodels on parameter blocks; Theorem 1 concerns
the constrained path. Section 4 restricts to homogeneous predictors. Its GD
Theorem 2 assumes smoothness, vanishing exponential loss, existence of the
parameter and normalized-loss directions, and LICQ. Theorem 4's lexicographic
conclusion is again about constrained minimizers. These statements do not
supply the coupled softmax trajectory or its convergence. The selected-query
system is neither the stipulated homogeneous predictor nor the finite
blockwise homogeneous sum. This is a failure of theorem premises, not a claim
that their techniques cannot be adapted. [Primary paper, Sections 3.2–4,
printed pp. 6–8](https://proceedings.mlr.press/v97/nacson19a/nacson19a.pdf).

In particular, giving the extra zero-margin inequality to an optimization
theorem after deriving it is not a derivation of that inequality from GD.
Computing its unique KKT solution is elementary. The substantive question is
why the unselected branch supplies a persistent negative gradient and develops
the log-log scale under the exact coupled update.

## 2. Quasi-homogeneous models do not rescue the direct import

Kunin, Yamamura, Ma and Ganguli (ICLR 2023), Definition 3.1, require an exact
scaling `f(exp(t Lambda)theta)=exp(t)f(theta)`. Theorem 4.1 assumes this scaling,
gradient flow, exponential loss, separability, normalized convergence, and
conditional separability, and concludes a KKT condition for an asymmetric
parameter seminorm. The original fixed-head attention score is bounded and
nonzero, so it cannot obey that exact unbounded-output scaling. Adding a
trainable homogeneous head would change both the model and update; choosing
zero scaling weights for attention would also make the theorem's penalized
coordinates the head rather than the lower attention block. Neither move
proves the held fixed-head result. [Primary paper, Definition 3.1 and
Theorem 4.1, printed pp. 3–5](https://arxiv.org/pdf/2210.03820).

## 3. The stronger excess-loss shortcut fails a concrete premise

Merely observing a positive loss infimum is insufficient to reject a generic
exponential-loss theorem: subtracting a constant preserves GD. Here is an
explicit check of this stronger reduction.

Use the held theorem's inputs and fixed head, with `c=w'(x1-x2)>0`,
`f1=w'x1`, `ell(f)=log(1+exp(-f))`, and `L_inf=ell(f1)`. Write

    a=sigmoid(x1'q), b=sigmoid(x2'q),
    h1=x2+a d, m=(a-b)h1'k, pi=sigmoid(m),
    f=w'x2+c[b+pi(a-b)],
    E(q,k)=ell(f)-ell(f1)>0, Psi(q,k)=-log E(q,k).       (N1)

The matrix realization is `W1=q d'/||d||²`, `W2=k d'/||d||²`.
Equation (N1) is smooth at all finite matrices. Because `exp(-Psi)=L-L_inf`,
GD on this exponential loss is exactly the original GD, with the same step.
The paired examples have identical signed scores, so no averaging issue arises.

**Lemma (discontinuous radial effective score).** Put
`k0=x1/||x1||²`. For each epsilon>=0, choose q_epsilon continuously in epsilon
with `x1'q_epsilon=1`, `x2'q_epsilon=-epsilon`; independence of x1,x2 permits
this choice, and q_0=q_*. Then

    lim_(R->infinity) Psi(R q_0,R k0)/R = 1/2,
    lim_(R->infinity) Psi(R q_epsilon,R k0)/R = 1
                    for every fixed epsilon>0.           (N2)

**Proof.** The exact deficit is

    f1-f=c[(1-a)+(1-pi)(a-b)].                            (N3)

In both ray cases a>b for sufficiently large R, so both terms are nonnegative.
The logistic derivative is bounded above and bounded away from zero on the
fixed token-score interval, making E comparable to f1-f with fixed constants.
On the boundary ray, `1-a=exp(-R)(1+o(1))`, `b=1/2`, and
`h1'R k0=R+O(R exp(-R))`. Thus
`m=R/2+O(R exp(-R))`, and (N3) has logarithmic decay rate 1/2.
For fixed epsilon>0, `b=exp(-epsilon R)(1+o(1))`,
`a-b->1`, and `m/R->1`. Both terms in (N3) have logarithmic decay rate 1;
their positive sum does too. This proves (N2). The associated full matrix
directions converge continuously as epsilon decreases to zero. QED.

Cai et al. (ICML 2025), Proposition 5.1, imply a continuous radial homogenization
with a uniform lower-order error from their near-homogeneity assumption.
For degree one that error is bounded. Their GD conclusions in Theorem 6.2
retain the near-homogeneity requirement. Equation (N2) directly contradicts
the required continuity for Psi. Thus subtracting the limiting loss and
relabeling it as an exponential loss does not make their theorem applicable.
[Primary source, Proposition 5.1 and Theorem 6.2](https://arxiv.org/html/2502.16075v2).

Nor does increasing the homogeneous degree solve this particular reduction.
Since the output coefficient is a convex combination of a and b,

    f1-f >= c min(1-a,1-b)
         >= (c/2) exp[-max(0,x1'q,x2'q)].

Consequently Psi is bounded below and is at most `C+C||q||` globally, for
constants depending on the fixed problem. Every higher-degree radial
homogenization is therefore zero, providing no separating leading model.

This is a local obstruction at the actual limiting direction to a specific
general-theorem shortcut. It is not a proof that every possible implicit-bias
framework is inapplicable. A theorem for discontinuous radial limits with
boundary-layer corrections could be relevant; no such theorem is asserted here.

## 4. A recent attention candidate explicitly leaves trajectory selection open

Singh, Mishra and Raut (July 2026) study rotary/absolute positional retrieval.
Their Lemma 2 concerns the selected geometry under assumptions, and Section 5.2
contains a two-layer multi-head empirical transfer. Section 7 explicitly
separates selected-solution characterization from trajectory selection and
leaves the latter open; its stated theoretical scope is one layer. Thus this
recent implicit-bias account supplies neither the present direction nor a
two-layer convergence theorem. [Primary source, Sections 4, 5.2 and 7](https://arxiv.org/html/2607.18759v1).

## 5. What this resolves, and what it does not

This bounded challenge found no direct derivation of the held selected-path
limit from the inspected theorems. It adds two serious generic candidates to
the existing comparison and rules out the tempting excess-loss import by an
explicit calculation. The constrained quadratic program itself, KKT algebra,
and the possibility of gradient competition are classical. They should not be
sold as new concepts.

The potentially substantive statement remains the exact discrete coupled
attention limit, its open finite basin, distinct surviving memories, the
log-log loser, and failure of the actual one-layer selected-path comparator
even when the isolated printed cones can both be satisfied. Priority and
research significance still require specialist judgment. This note provides
no evidence of practical transformer failure or a generalization gap.

Further broad keyword searches are unlikely to improve this bounded decision.
A useful next prior-art challenge needs a specific theorem handling nested
saturating softmax, a continuously moving feature map, or the discontinuous
effective-score recession function above. Lack of such a match in this search
is not evidence that none exists.

## Reproducibility

The new `primary_sources/retrieval.json` records retrieved URLs, PDF hashes,
text hashes and page counts. The supplied papers were read at the statements
identified above; search snippets were used only as locators. The inherited
Cai PDF was also read directly and is dependency-bound in `manifest.json`.
No simulation, paid computation, contact, or publication was performed.
