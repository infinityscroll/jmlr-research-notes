# Compatibility with the printed sufficient one-layer cones

28 October 2026. Separate scope-strengthening corollary, conditional on the held general positive-Gram theorem. It does not change either held dynamical proof. The published theorem still concerns one layer and is not contradicted.

## 1. Claim

For the fixed, well-conditioned inputs

    x1=(1,0)', x2=(epsilon,1)', epsilon=1/100, w=e1,

there are finite initial matrices in the general theorem's nonempty open bad basin that also satisfy the **printed sufficient one-layer initialization cones** for both actual selected-query problems at initialization, with a common sufficiently small fixed step. The lower limiting margin fraction is nevertheless `1/sqrt(1+epsilon²)<1` under simultaneous two-layer training.

The deficit is small: approximately `0.00004999625`. This corollary strengthens the initialization comparison, not the size of the effect. The fixed epsilon=1/2 source has a larger deficit but does not meet this particular explicit cone bound.

## 2. Exact constants in the primary source

The primary source is [Julistiono, Ataee Tarzanagh and Azizan, JMLR 27, 25-0549](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf), held PDF SHA256 `984c74508677a57e0a24e8f8dcf4564510ccf73ea111cfb53e2872e82c6f0c9e`. Appendix A.1, equations (6)–(8), printed page 26, defines

    delta_paper=min(1/4,delta'),
    A=max(1, ||Wmm||_F max_(i,t)||x_it z_i'||_F),
    mu0=(1/2)(delta_paper/(8A))²                 [p=2].

It explicitly sets delta'=infinity when there are no nonsupport competitors. Lemma 28, printed pages 42–43, selects `mu'=mu/3`; Lemma 29 uses it with `mu=mu0`. Appendix D derives Theorem 10 through that sufficient construction. We use these displayed sufficient choices, not an unspecified conjectured uniform cone width.

Both paired examples give the same sole constraint, and the unique competing token is a support token. Thus delta_paper=1/4. In the lower selected-query problem, `z=x1`, `d=x1-x2`, and

    A'=max(||x1||,||x2||)/||d||
      =sqrt(1+epsilon²)/sqrt((1-epsilon)²+1)<1.

Hence

    A=1, mu0=1/2048, mu'=1/6144.                        (C1)

This computation is uniform for `0<epsilon<=1/2` (strict A'<1 for epsilon<1/2). The fixed-head score gap is 1-epsilon>0, so the selected token is globally, and therefore locally, optimal under the paper's definition.

## 3. Lower initial cone

The general theorem has, for these inputs, `v*=epsilon`, `u*=1+epsilon²`, and `x*=epsilon+log(1+epsilon²)`. At a basin center choose

    s=R, k=R e1,
    l1=R-x*, l2=log[(epsilon/R)/(1-epsilon/R)],
    q=(l1,l2-epsilon*l1)',
    W1=q d'/||d||², W2=R e1 d'/||d||².                 (C2)

These are finite for R>epsilon. Their lower normalized direction converges as R grows to the bad direction proportional to `(1,-epsilon)'d'`. Its Bregman discrepancy from the normalized selected-only SVM is

    b_epsilon=1-1/sqrt(1+epsilon²)
              <=epsilon²/2=1/20000<1/6144.              (C3)

The elementary inequality follows by integrating the derivative of `(1+x)^(-1/2)` on `[0,epsilon²]`. Continuity gives strict membership of C2's lower matrix in the printed angular cone for all sufficiently large finite R. Its norm tends to infinity. Strict membership persists in a sufficiently small open neighborhood contained in the dynamical basin; it is not an equality-initialized orbit only.

## 4. Upper actual-checkpoint cone

At initialization `h1=x2+a d`, `h2=x2+b d` with `a=sigmoid(l1)`, `b=sigmoid(l2)`. The selected upper query is h1, its selected token is h1, and its comparator normal is

    C_top=h1(h1-h2)'=(a-b)h1 d'.

As R grows, a->1, b->0, h1->x1, h2->x2, and

    A'_top=max(||h1||,||h2||)/||h1-h2||
           ->sqrt(1+epsilon²)/||d||<1.                  (C4)

Thus the upper frozen-checkpoint dataset also has `A=1`, delta_paper=1/4, and the same printed angular allowance C1. The angle between W2 in C2 and C_top is exactly the angle between e1 and h1, which tends to zero. Upper norm tends to infinity, and the upper signed head gap tends to 1-epsilon>0. Therefore its angular condition also holds strictly for large finite R.

## 5. Radius and step-size conditions are not silently discarded

The lower single-layer dataset is fixed. Its radius threshold in Lemmas 20, 21, 28 and 29 is therefore finite. The upper frozen-checkpoint datasets converge to that fixed dataset. Along a sufficiently late neighborhood: A=1; the only support score gap is bounded below, for example by .9; token/query norms and SVM norms are bounded; logistic derivatives on their bounded score intervals have positive finite lower/upper bounds; and there are no nonsupport competitors. The printed radius estimates use only these bounded quantities and fixed positive mu0, mu', and an auxiliary `pi<mu0/3`. Their denominators remain bounded away from zero. Consequently one may choose a finite common upper radius bound over this neighborhood. Both matrix norms in C2 eventually exceed the respective radius bounds. This is uniformity on one compact neighborhood with a fixed support pattern, not a blanket assertion that arbitrary data-dependent thresholds are continuous.

There is also a direct global step-size bound for each standalone one-layer loss here. With its sole scalar logit m, write `f(m)=v0+D sigmoid(m)`, where `0<D<=1`. For logistic loss ell,

    |(ell composed with f)''(m)|
       <=D²/64+D/4<=17/64.

The Hessian in W has operator norm at most `(17/64)||C||_F²`. At every initialization in C2, the original and intermediate token rows are convex combinations of x1,x2, so

    ||C||_F²<=2(1+epsilon²)<2.001.

Thus this Hessian norm is below one, and any fixed `0<eta<=1`, including eta=.1, makes `psi-eta L` convex for each isolated p=2 problem. This satisfies the sufficient-step convention in the paper's Remark 9 without a circular choice of an initialization-dependent step. The general dynamical theorem independently supplies a sufficiently large finite basin threshold for eta=.1. Increase R to meet all finite requirements together.

The argument does not assert convexity of the **joint two-layer** loss, which is not a hypothesis of the single-layer theorem being compared.

## 6. Exact meaning

This improves on arbitrary angular closeness: the simultaneous two-layer failure can begin inside actual sufficient single-layer cones extracted from the primary proof, for both initial layerwise datasets. It shows that those per-layer initialization checks alone do not justify applying the one-layer conclusion independently to a jointly trained stack.

It does not refute the published fixed-input, fixed-head one-layer theorem. Nor does it exclude a depth-two theorem with additional restrictions on query correlation, cross-path gradients, smaller data-dependent neighborhoods, or other architecture-specific conditions. The data remain a paired-sign two-token design, p=2, fixed values/head, and a large finite basin. A specialist novelty assessment remains separate.
