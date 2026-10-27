# Positive binary hedge witnesses using finitely many hidden parity modes

26 October 2026. New proof candidate; all earlier frozen notes remain unchanged. The observed state spaces in this result are exactly binary. Existing independent hidden roots may need a larger finite state space: each selected bidirected edge carries a finite vector of independent fair bits. No observed coordinate, vertex, directed arrow, or bidirected edge is added. This state-capacity qualification is essential.

## Statement

Let H be a finite ADMG interpreted by its semi-Markovian DAG: every bidirected edge is represented by an independent hidden root with its two endpoints as children. Let A be an actual action set and let y be a selected observed vertex outside A. Suppose H has an actual-query hedge I ⊂ F for P(X_y | do(X_A=a)), with a common root set R, as in [Shpitser (2023), Proposition 1, item 1](https://arxiv.org/html/2307.03750v1). All observed variables have the fixed state space {-1,+1}.

Then, provided the existing hidden roots have sufficient finite state capacity, there exist two SCMs on that same DAG such that:

1. Their entire observational distributions on all original observed binary variables are exactly equal.
2. Every observed conditional probability, conditional on every assignment of its observed and explicit hidden parents, is at least 1/8 in both models.
3. For every assignment a to the actual action set A, the selected probabilities P(X_y=+1 | do(X_A=a)) differ by a strictly positive amount.

The construction does not require the earlier routing condition (R), or (D2), or even a singleton action. It proves nonidentification of a selected binary *interventional distribution*. It does not assert that a contrast between two action assignments differs; the displayed construction may give a common, nonzero shift for all action assignments.

The following proof is self-contained apart from the classical actual-query hedge criterion. Its central construction is an elementary finite Fourier expansion and latent-bit cancellation. The use of a hedge and the general strategy of matching observational models while separating their interventions are classical. No priority claim is made for the positive multimode construction.

## 1. Parent notation and a connected-set realization lemma

For a set C of observed vertices, define

\[
P_C=\bigcup_{v\in C}\operatorname{pa}_H(v).
\]

Crucially, this union **includes parents that belong to C**. It is not the external-parent set P_C\C. Write χ_D(x)=∏_{v∈D}x_v, with χ_empty=1.

Fix arbitrary strictly positive binary baseline DAG kernels p_v(x_v | x_pa(v)). Set p_0(x)=∏_v p_v(x_v | x_pa(v)). If C is nonempty and bidirected-connected, then for every real function c on {-1,+1}^{P_C}, and every sufficiently small λ>0, a model on the same graph realizes exactly

\[
p_C^{(\lambda)}(x)
=p_0(x)+\lambda\,\chi_C(x)c(x_{P_C})
                    \prod_{v\notin C}p_v(x_v\mid x_{\operatorname{pa}(v)}).
\tag{1}
\]

Every observed local kernel can be kept arbitrarily close to its baseline kernel, uniformly over all observed and hidden parent assignments. The extra hidden coordinates are independent fair bits in existing roots.

**Proof.** Choose a spanning bidirected tree T_C. Expand the finite table c in the Walsh basis:

\[
c(x_{P_C})=\sum_{S\subseteq P_C}\widehat c_S\chi_S(x),\qquad
\widehat c_S=2^{-|P_C|}\sum_{z\in\{-1,+1\}^{P_C}}c(z)\chi_S(z).
\tag{2}
\]

Keep only the M nonzero coefficients. For each parent variable w∈P_C, choose one child j(w)∈C for which w→j(w) is an allowed edge. For mode S and vertex v∈C put

\[
f_{v,S}(x_{\operatorname{pa}(v)})
=\prod_{w\in S:\ j(w)=v}x_w.
\]

Thus ∏_{v∈C}f_{v,S}=χ_S, and each f_{v,S} uses only allowed observed parents of v, even when w∈C.

For each tree edge e and mode S, let H_{e,S} be an independent fair sign. Its two endpoints are precisely the children of the existing hidden root for e. At v∈C use the binary kernel

\[
k_v(x_v\mid x_{\operatorname{pa}(v)},h)
=p_v(x_v\mid x_{\operatorname{pa}(v)})
 +x_v\sum_S b_{v,S}f_{v,S}(x_{\operatorname{pa}(v)})
                    \prod_{e\ni v}h_{e,S},
\tag{3}
\]

where ∏_{v∈C}b_{v,S}=λ ĉ_S. For example, give every vertex the magnitude (λ|ĉ_S|)^{1/|C|}, and put the coefficient's sign at one designated vertex. Other observed kernels remain p_v. Each summand in (3) sums to zero over x_v, so normalization is exact. If δ is the minimum baseline cell, every cell remains at least δ/2 whenever

\[
\lambda^{1/|C|}\sum_{S:\widehat c_S\ne0}|\widehat c_S|^{1/|C|}
\leq\delta/2.
\tag{4}
\]

Now expand the product of the observed kernels at a fixed complete observed assignment x and average over all hidden signs. For a fixed mode S, each of its edge signs appears at the endpoints whose factors selected that mode. A nonzero expectation requires the selected-vertex set to have no boundary in the connected tree. That set is therefore empty or all of C. A vertex chooses at most one additive term in the product expansion, so two different modes cannot both occupy C. The only surviving terms are the all-baseline term and, for each S, the term where every vertex in C selects S. Their sum is exactly (1).

For |C|=1 no hidden edge is needed: (3) is simply a sum of local parent monomials, and (1) follows directly. If c=0 the baseline itself suffices. This proves the lemma. □

This also specifies hidden capacity: M independent bits suffice per chosen edge of T_C. Two models can use the same roots and a common finite state space by retaining every bit used by either construction and ignoring unused bits. Extra allowed graph edges may be ignored. The claim is not made for prescribed binary hidden roots.

## 2. Matching the full observational law

For the hedge choose compatible directed forests with common roots R. Every vertex of F\I has a directed child in F: it is not a common root, and its selected path to R has positive length. Consequently

\[
F\setminus I\subseteq P_F.
\tag{5}
\]

Also P_I⊂P_F. Take any finite table c_I(x_{P_I}) and define

\[
c_F(x_{P_F})
=\chi_{F\setminus I}(x)c_I(x_{P_I})
  \prod_{v\in F\setminus I}p_v(x_v\mid x_{\operatorname{pa}(v)}).
\tag{6}
\]

This is a legitimate function of P_F. Every x_v with v∈F\I is included by (5); all its parents are included by definition; and every input to c_I is included by P_I⊂P_F. This is the step that allows a treatment to have a directed parent in its district. No vertex gets to read its own value in its local kernel: (2) assigns each occurrence to an allowed child in F.

Let M_F be the connected-set model (1) for C=F,c=c_F, and M_I the model for C=I,c=c_I, using the same λ, small enough for (4) in both models. Their perturbations agree pointwise because

\[
\chi_F c_F\prod_{v\notin F}p_v
=\chi_I c_I\prod_{v\notin I}p_v.
\tag{7}
\]

Thus the complete observational joint law is identical, not merely a marginal or an approximation.

## 3. What the actual intervention does

The hedge has F∩A≠empty and I∩A=empty. Under do(X_A=a), at least one F vertex's kernel is removed. In the hidden-bit expansion of M_F, a mode can survive only if its selected-vertex set has no tree boundary. It cannot be all of F because the removed kernel supplies none of its incident signs. Hence every F mode vanishes. This includes the case that multiple vertices of F are treated. The postintervention law of M_F is exactly the truncated baseline law.

All I kernels remain in M_I. Actions outside I replace only baseline factors, so the same expansion as before gives

\[
p_{I,a}^{(\lambda)}(x_{V\setminus A})-p_{F,a}^{(\lambda)}(x_{V\setminus A})
=\lambda\chi_I(x)c_I(x_{P_I})
     \prod_{v\notin I\cup A}p_v(x_v\mid x_{\operatorname{pa}(v)})\big|_{x_A=a}.
\tag{8}
\]

If F is larger than one vertex, every proper nonempty subset of its spanning tree has a boundary, which proves the disappearance rigorously. A singleton outer F cannot form a hedge with nonempty I⊂F. Action values need no special choice.

## 4. Re-entry-safe routing of the selected binary discrepancy

Every i∈I is an ancestor of y in H\A: follow its inner-forest path to a common root and then a root-to-y path avoiding A. Choose, in H\A, a finite directed subgraph K containing I∪{y} in which every vertex other than y has exactly one outgoing edge and reaches y. One construction chooses a shortest-distance-to-y outgoing edge for each vertex in the union of selected paths and keeps all vertices reached from I. Extra incoming edges of H are ignored. Paths can merge and can pass through any nonroot of F. They may also pass through another vertex of I.

Let J_v be the selected K parents of v. Choose baseline kernels

\[
p_v(x_v\mid x_{\operatorname{pa}(v)})
=\begin{cases}
\tfrac12\{1+\beta_v x_v\prod_{u\in J_v}x_u\},&v\in K\setminus I,\\
\tfrac12,&v\notin K\setminus I,
\end{cases}
\tag{9}
\]

with, for example, β_v=1/2. These are valid allowed-parent kernels with all cells in [1/4,3/4]. Set

\[
c_I(x_{P_I})=2^{-|I|}\prod_{i\in I}\prod_{u\in J_i}x_u.
\tag{10}
\]

Each factor in (10) is an actual parent of an I vertex. In particular, when a route re-enters I, its incoming signal is included in c_I. No route uses an action vertex, so (9)–(10) are independent of action values.

To compute the selected mean difference from (8), first sum the independent fair variables outside K∪A. For v∈K define L_v=x_v∏_{u∈J_v}x_u. The remaining signed kernel is

\[
\lambda 2^{-|K|}
  \left(\prod_{i\in I}L_i\right)
  \prod_{v\in K\setminus I}(1+\beta_vL_v).
\tag{11}
\]

The transformation x_K↦(L_v)_{v∈K} is a bijection on the binary cube: solve for x_v in a topological order. Moreover, because each non-y vertex has exactly one selected child,

\[
\prod_{v\in K}L_v=x_y.
\tag{12}
\]

In the Fourier expansion of (11), the unique term whose sign character is x_y selects every remaining L_v. Orthogonality under the uniform cube then gives

\[
\mathbb E_{M_I}[X_y\mid do(a)]-
\mathbb E_{M_F}[X_y\mid do(a)]
=\lambda\prod_{v\in K\setminus I}\beta_v>0.
\tag{13}
\]

Equivalently, the selected +1 probabilities differ by λ·2^{-|K\I|-1} for β_v=1/2. This is an exact expression. It does not depend on a.

Taking λ sufficiently small for (4) in both models, with δ=1/4, makes every observed local cell at least 1/8. Finite hidden roots are uniform on their bit-vector states, with full support. Equations (7) and (13) finish the stated theorem. □

## 5. Consequence for fixed-policy HCM transfer, and limits

In the semi-Markovian hidden-root HCM class of the frozen fixed-policy manuscript, suppose every actual unit receiver satisfies exact sensitivity (S), all subunit variables are observed with finite alphabets of size at least two, the observed unit variables have their fixed binary alphabets, and the existing hidden roots have the finite state capacities required above. For a selected original unit y and fixed positive subunit policies (and any queried unit assignments), every failure of ordinary collapsed ID now has the positive binary flat witness just proved. The exact finite-codebook theorem for (S) encodes the two flat labels at each subunit mechanism, with the prescribed policy as the action label. Its continuous receiver interpolation lifts the common full flat observational law and the selected unit discrepancy to the HCM limiting mechanism-level observation.

The lift therefore supplies selected-unit nonidentification under the actual policy, with positive label probabilities conditional on all explicit hidden parents and strictly positive codeword tables. The positive interpolation and uniform lower bound supply the expected-KL convergence used by the previously audited lift. This is the same limiting-observation interpretation as the manuscript, not equality at each finite number of subunits. Ordinary unaugmented auxiliary support is covered by the finite full Cartesian support. Additional deterministic augmentation reachability requirements are not asserted.

If the direct collapsed ID procedure succeeds, its usual sound formula still applies under its support assumptions. Thus this is a candidate selected-fixed-binary-unit completeness extension under (S) and sufficiently rich existing independent hidden roots. It does not cover failed (S), fixed small hidden state spaces, selected subunit functionals, or extra restrictions on the structural functions. It does not claim necessity of (S) for causal completeness. The hidden-capacity requirement prevents reading the statement as an all-variables-binary result.

Proof dependencies: the actual-query hedge criterion cited above; [exact fixed-policy separation](../../../fixed_policy_separation/theorem.md); and the positive continuous mechanism lift in [the frozen full-law manuscript](../../../fixed_policy_manuscript/sections/completeness.tex). The new argument replaces the earlier scalar routing witness, not the policy coding or HCM limiting-law theory. The earlier [singleton routing obstruction](../singleton_routing_obstruction.md) remains a correct counterexample to (R); it is now a test case for this alternative construction.
