# Independent audit of printed one-layer cone compatibility

28 October 2026. Source-level comparison with the actual primary proof. No held theorem or diagnostic was edited or rerun.

**Verdict: no blocking issue found.** For epsilon=1/100, a finite open subset of the general theorem's bad basin satisfies the printed sufficient angular cones, finite radius requirements and a common fixed sufficient step size for both initial isolated layerwise problems. This is stronger than saying the bad direction can be made arbitrarily close to an optimum. It still compares initial frozen layerwise problems with a jointly trained stack; it does not refute the published fixed-input one-layer theorem.

## Binding and dependencies

| Source | SHA256 |
| --- | --- |
| `printed_single_layer_cone_compatibility.md` | `bcd9d2fbb6270cf036b4daf27d87f9a59200f2e3ab7db1de78dd33abd08a4ec5` |
| `positive_gram_extension.md` | `29c18514bf16ab7282b227e46bafcee71e677332644c92af8d2ff78ccd97fc36` |
| `independent_positive_gram_audit.md` | `517d13f3069eeffb557fa48f4c7a4fc07d24ee943137657c00ff95654b1f1588` |
| `../source/paper.pdf` | `984c74508677a57e0a24e8f8dcf4564510ccf73ea111cfb53e2872e82c6f0c9e` |

I read the complete compatibility corollary, general-Gram theorem and its independent audit. For the primary comparison I inspected Definitions 3, 5 and 7; Remark 9; Appendix A.1 equations (6)–(10); the proof bounds of Lemmas 20–21; Lemmas 28–29; and Appendices D–E. The previously completed independent fixed-fixture audit is not being silently extended to an arbitrary-input theorem; the general dynamics are a separately bound dependency here.

## 1. The actual printed angular allowance

The [primary Appendix A.1](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf) sets delta' to infinity if all nonsupport sets are empty, then delta=min(1/4,delta'). Its A is max(1,A'), where at p=2, A' is the SVM norm times the largest token-query outer-product Frobenius norm. Equation (8) gives mu0=(1/2)(delta/(8A))^2. Lemma 28 explicitly permits mu'=mu/3; Lemma 29 uses the construction at mu=mu0, and Theorems 10–11 depend on it.

The two signed examples have the same single constraint normal. The only competing token is a support token, so their nonsupport sets are empty. For x1=e1, x2=(epsilon,1), d=x1-x2,

    ||Wmm||=1/||d||,
    A'=max(||x1||,||x2||)/||d||
      =sqrt(1+epsilon^2)/sqrt(2-2epsilon+epsilon^2).

This is strictly below one for epsilon<1/2. At epsilon=1/100 the exact printed choices therefore are

    delta=1/4, A=1, mu0=1/2048, mu'=1/6144.

The signed head gap is 1-epsilon>0. Thus the selected token is globally optimal and satisfies the paper's local-optimality definition. Neither a nonsupport margin nor a token-score gap is being sent to zero to obtain the angular allowance.

## 2. Finite initial directions, not only their limiting angle

For this input, the general-Gram quantities are r=epsilon, t=1+epsilon^2, v*=epsilon and u*=1+epsilon^2. The proposed initialization has exactly x=x*, v=v*, and k_perp=0, so it is the center of the dynamical ellipsoid at every sufficiently large finite scale R. The lower coordinate ratio is

    q2/q1=-epsilon+l2/(R-x*),
    l2=log[(epsilon/R)/(1-epsilon/R)].

It converges to -epsilon. Therefore the lower unit-matrix cosine to the isolated selected-query optimum converges to 1/sqrt(1+epsilon^2). For quadratic Bregman divergence the limit is

    1-1/sqrt(1+epsilon^2) <=epsilon^2/2=1/20000<1/6144.

The strict numerical slack is decisive. It gives actual angular-cone membership for all sufficiently large finite R, even though the finite-R discrepancy approaches its limit from above. The lower matrix norm grows linearly in R.

For the upper frozen-checkpoint problem the query is h1 and the normal is h1(h1-h2)'. The SVM norm is `1/(||h1|| ||h1-h2||)`, so the query norm cancels out of A'_top. Its limit is the same A'<1. Thus A_top=1 eventually. Its competing token remains the sole support token and its head-score gap tends to .99. The initial W2 direction is e1 d'; the comparator direction tends to that direction, so the upper discrepancy tends to zero and its norm also diverges. All these inequalities are strict eventually and survive a small full-coordinate perturbation inside the dynamical basin.

## 3. The changing upper dataset does not make the radius circular

The upper initial dataset depends on R, so merely asserting a finite radius for each R would be insufficient. The corollary instead uses the explicit quantities in the primary proofs. These can indeed be bounded uniformly on one sufficiently late neighborhood of the limiting dataset.

Here is an independent conservative bound making that argument concrete. On such a neighborhood choose

    ||Wmm||<=2, gamma_gap>=.9, Gamma<=1,
    A=1, T=2, number_of_examples=2, Lbar<=4,
    delta=1/4, auxiliary pi=mu0/6=1/12288.

The score is confined to [.01,1] for the two isolated problems. Hence its logistic derivative is bounded away from zero and infinity, and Lbar in equation (18) is uniformly bounded (the paired structure actually gives the sharper value two). The displayed sufficient logarithmic bound in the Lemma 20 proof, even retaining its extra example-count factor conservatively, is at most

    8 log(384/.7875)<50.

The displayed Lemma 21 sufficient bound is at most

    (2/pi) log(290/(.9 pi)) < 10^6.                      (A1)

Empty subsets in that proof need no negative contribution; replacing any present score-gap maximum by one only enlarges the bound. Thus one can choose a common radius at least 10^6 for the two late isolated datasets. Lemma 28's remaining radius condition is `eta*(loss drop)/R_mu^2 <=mu0/3`. At eta=.1 and loss drop below one this holds already for `R_mu^2>=.1*6144`, much smaller than the conservative radius above. Lemma 29 adds only the maximum with the preceding radius and one.

These deliberately loose bounds are not a certified practical initialization recommendation. They demonstrate that the printed sufficient radius construction stays bounded as the frozen upper dataset varies with R. Both initialized matrix norms tend to infinity, so eventually they exceed this common bound. The general dynamical theorem supplies its own finite R0 for the same already-fixed eta. Increasing R beyond all these finite requirements is legitimate; neither the step nor the paper's cone width is adjusted after seeing a trajectory.

## 4. The common step meets the primary sufficient convention

For an isolated two-token problem, with signed score `f(m)=v0+D sigmoid(m)` and 0<D<=1,

    |(ell composed with f)''|
      <=(1/4)(D/4)^2+1*(D/4)
      =D^2/64+D/4 <=17/64.

The first term uses ell''<=1/4; the second uses |ell'|<=1 and |sigmoid''|<=1/4. Since m is a linear Frobenius functional with normal C, its full Hessian operator norm is at most `(17/64)||C||_F^2`. The input and intermediate tokens are convex combinations of the fixed pair, giving `||C||_F^2<=2(1+epsilon^2)<2.001`. Hence the Hessian bound is strictly below one globally in W for each frozen isolated problem. For psi=||W||_F^2/2, every eta<=1 makes psi-eta L convex, satisfying the sufficient convention stated in Remark 9. In particular eta=.1 works simultaneously and independently of R.

This is not a claim of joint two-layer convexity. The separate dynamical theorem allows each fixed positive eta after choosing its late-basin threshold.

## 5. Metric, transpose and interpretation

The source's row-query convention transposes the paper's `(x_selected-x_other)'W z` convention. Frobenius norms, quadratic mirror descent, the unique one-normal SVM, and the unit-normalized p=2 Bregman divergence are all invariant under that transpose. No coordinate-restricted or factorized comparator is introduced.

This addendum therefore resolves the earlier objection that its failure might merely start outside the paper's actual sufficient **initial** layerwise cones. The discrepancy is small but strictly positive, about 0.00004999625, for the fixed epsilon=.01 data. The epsilon=.5 larger-gap fixture does not inherit this particular numerical cone comparison.

The logical conclusion is that satisfying those printed one-layer initialization checks separately does not justify applying the one-layer conclusion independently to a simultaneously trained stack. Later lower dynamics contain cross-path gradients, and the upper inputs move. Additional depth-specific hypotheses could still yield a correct theorem. No arbitrary/random initialization, practical entry threshold, non-Euclidean result, empirical generalization, historical priority, or external validation is established by this audit.
