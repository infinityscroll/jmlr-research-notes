# Hidden-state compression for the positive multimode construction

26 October 2026, revision 2. This revision only makes the rational-baseline qualification explicit; the preserved revision 1 and its independent audit remain valid with that qualification. Separate proved improvement to the frozen multimode witness; no frozen source is changed. The original connected-set proof uses one independent bit per nonzero Fourier mode on each tree edge. That independence is unnecessary: each edge has only two endpoints, so pairwise orthogonality suffices.

**Result.** A connected-set coefficient with M nonzero Fourier modes can be realized with **M+1 states per selected pairwise hidden root**, preserving the observed binary alphabets, graph, exact observed law, intervention cancellation, and a uniform positive local-cell bound. For the hedge routing construction, M_F=2^h and M_I=1, where h counts the outer-only vertices used by the route forest. Thus **2^h+1 states per used root suffice**, instead of 2^(2^h). Binary hidden roots suffice when h=0. This does not prove that binary roots suffice for all actual-query hedges.

The Walsh reuse observation was derived independently here. The root agent suggested the rational unnormalized Helmert basis below; its normalization and all arguments were then checked independently. Orthogonal bases and the rank facts used are standard linear algebra. This note makes no publication-priority claim.

## 1. Compressed connected-set realization

Use the notation and local-parent allocation of [the frozen theorem](../multimode_hedge/theorem.md), SHA `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147`. Let C be nonempty and bidirected-connected, n=|C|, and choose a spanning bidirected tree T_C. Write

\[
c(x_{P_C})=\sum_{j=1}^M a_j\prod_{v\in C}f_{v,j}(x_{pa(v)}),
\qquad a_j\ne0,
\tag{C1}
\]

where the factors are the allowed-parent Walsh monomials from that theorem. Each f has absolute value one. Fix positive baseline kernels p_v with minimum cell delta_0.

Choose an integer K≥M+1. At every selected edge put an independent uniform variable Z_e on {1,...,K}. Its graph children remain the two existing endpoints. Define phi_0=1 and, for 1≤j≤M,

\[
\phi_j(z)=
\begin{cases}
1,&z\le j,\\
-j,&z=j+1,\\
0,&z>j+1.
\end{cases}
\qquad
d_j=E\phi_j^2=\frac{j(j+1)}K.
\tag{C2}
\]

These rational functions have mean zero. For j<l, their product sums to j-j=0 over the first j+1 states and vanishes elsewhere. Therefore

\[
E\phi_j\phi_l=0\quad(j\ne l),\qquad E\phi_j^2=d_j>0.
\tag{C3}
\]

At v∈C set

\[
k_v(x_v\mid x_{pa(v)},z)=p_v(x_v\mid x_{pa(v)})
+x_v\sum_{j=1}^M b_{v,j}f_{v,j}(x_{pa(v)})
                 \prod_{e\ni v}\phi_j(z_e),
\tag{C4}
\]

and require

\[
\prod_{v\in C}b_{v,j}=\frac{\lambda a_j}{d_j^{n-1}}.
\tag{C5}
\]

Every summand still sums to zero over x_v. At a fixed complete observed assignment, label each selected product factor either 0 (baseline) or its mode j. An edge expectation is zero unless the two endpoint labels agree. Independent edge variables therefore force the label to be constant on the connected tree. The all-zero term is the baseline. An all-j term contributes d_j^(n-1), canceled by (C5). Exactly the original joint perturbation results:

\[
p(x)=p_0(x)+\lambda\chi_C(x)c(x_{P_C})\prod_{v\notin C}p_v(x_v\mid x_{pa(v)}).
\tag{C6}
\]

This is a finite exact contraction. Independence across modes is not used; different mode functions intentionally share each edge variable.

For a quantitative positivity choice, give all b coefficients in mode j magnitude (lambda |a_j|/d_j^(n-1))^(1/n), placing the sign of a_j at one vertex. Since |phi_j|≤j, the local perturbation is at most lambda^(1/n) A_v, where

\[
A_v=\sum_{j=1}^M |a_j|^{1/n}d_j^{-(n-1)/n}j^{\deg_{T_C}(v)}.
\]

Thus every cell is at least delta_0/2 if lambda^(1/n) max_v A_v≤delta_0/2. All quantities are finite. The new contrasts can have magnitude greater than one, so this is a new lambda bound; the old explicit bound must not be copied unchanged. For rational baseline kernels and rational coefficients one can instead set lambda=t^n with sufficiently small rational t, set b=t at all but one designated vertex, and set the remaining b=t a_j/d_j^(n-1). This gives entirely rational CPTs and the same limit to the baseline as t decreases.

For n=1 no hidden root is needed and the local parent expansion directly realizes c. For c=0 use the baseline. The state count K=M+1 concerns nontrivial connected sets and nonzero c.

### Bounded Walsh alternative

If preserving the old lambda bound is preferable, take q=ceil(log2(M+1)) bits on each edge and assign modes distinct nonzero Walsh characters of the q-bit vector. Baseline uses the constant character. Orthogonality gives the same equal-label condition, every norm is one, and every character has magnitude one. Thus the original positivity bound applies unchanged. This uses 2^q<2(M+1) states. It is still exponentially smaller than using M independent bits, which uses 2^M states.

## 2. Actual interventions and common hidden state spaces

An intervened vertex supplies no local perturbation. Treat its label as 0. Equal labels along the whole outer tree then force every remaining label to be 0. Consequently the same surgery argument eliminates all outer modes. Inner modes survive when no inner vertex is treated. Observational matching and the selected parity calculation are unchanged.

Two models need not realize their hidden labels simultaneously as independent copies. They can use the same K-state uniform root on every edge, with different response tables. Taking K≥max(M_F,M_I)+1 suffices, including edges used by both spanning trees; unused edges may be ignored. Recompute d_j using that common K.

If an existing root has a prescribed finite domain of size D≥K, partition it into K nonempty cells, assign each cell total mass 1/K, and give every state in a cell positive equal mass. Composing phi with the cell label yields the same law, with positive mass on every existing state. It adds no vertex or edge. This does not handle a prescribed root law that cannot induce the required effective weights, or an additional restriction on its allowed response functions.

## 3. Sharper state count for the actual hedge coefficient

Let I⊂F be the actual-query hedge and K_r the route forest of the scalar theorem or joint-target corollary. To avoid overloading K, write

\[
D=(F\setminus I)\cap K_r,\qquad h=|D|.
\]

The specified baseline is fair except on K_r minus I, where it is (1+beta_v L_v)/2. Therefore the outer coefficient has the exact form

\[
c_F=2^{-|F|}\,\chi_{F\setminus I}
\left(\prod_{i\in I}\prod_{u\in J_i}x_u\right)
\prod_{v\in D}(1+\beta_vL_v).
\tag{C7}
\]

The L_v are independent sign characters: the full map x_{K_r} to (L_v) is triangular and invertible. Thus different subsets of D give distinct Walsh monomials. Multiplying by the fixed prefactor character preserves their distinctness. Every coefficient is nonzero because beta_v>0. Consequently **M_F=2^h exactly**, while c_I is a single monomial and M_I=1.

All these characters are functions of P_F: in particular, each own variable v in F minus I is a parent of some F vertex. The argument does not treat P_F as only the external parents.

It follows that 2^h+1 common states per used pairwise root suffice. Since K_r avoids A,

\[
h\le |F\setminus I|-|F\cap A|\le |F|-2.
\tag{C8}
\]

This is a sufficient bound for the selected route forest, not an optimal graph invariant. Choosing routes with fewer outer-only vertices can improve it; no efficient route-optimization claim is made. When h=0 the construction needs one mode and binary roots suffice. The former no-re-entry routing subclass admits such a choice. When re-entry is necessary, the bound is exponential in the number of used outer-only vertices, rather than doubly exponential.

## 4. Exact three-state fixture on the forced re-entry graph

The separate [checker](check_capacity.py) and [certificate](certificate.json) use the six-node graph from the frozen obstruction: directed U→A→B→Y and R→Z→B, with bidirected tree A–Y–R–U–B. F={U,A,R,B,Y}, I={R,Y}, and the sole action is A. The route R→Z→B→Y has h=1. The two outer modes are

\[
c_F=x_Ux_A/32+x_Ux_Ax_Bx_Z/64,
\qquad c_I=x_B/4.
\]

All four existing hidden roots are independent and uniform on three states. Use the two Helmert modes, whose squared norms are 2/3 and 2. With t=1/16 and lambda=t^5, set b=t for all outer vertices except U and b_{U,j}=t a_j/d_j^4. For the inner model use mode 1 on the R–Y edge, with coefficients t at R and t^4/(4d_1) at Y. Every number is rational.

Direct summation over all 81 hidden configurations verifies all 64 common observational atoms and all 32 interventional atoms for each action value. The exact minimum local cell is 1/8 in the outer model and 1/4 in the inner model. For either actual action, the selected positive-probability gap is 1/8388608. This is the same lambda and gap as the independent earlier signed-kernel certificate, now realized using three states per root instead of four.

Three is not proved necessary for this causal query. It is sufficient for this compressed construction. The earlier graph-specific fiber certificate used four-state roots; neither certificate establishes the minimum state capacity over every possible witness on that graph.

## 5. What cannot be inferred about binary roots

### Lower bound for the orthogonal-label gadget

On a K-state root with positive weights, the function space has dimension K. A nonzero constant baseline and M nonzero mutually orthogonal mode functions require K≥M+1. More generally, if different endpoint encodings are allowed but their cross-expectation matrix is a nonsingular diagonal matrix on M+1 labels, its rank is at most K and the same bound follows. Thus M+1 is optimal for this exact label-matching device. This does not rule out a different witness, cancellation among mixed modes, or a different tensor representation with fewer states.

### A stronger obstruction for a specified universal-realization target

There is also a graph-specific rank obstruction to any binary-root version of the **universal connected-set realization lemma**. Let A and B each be groups of d independent observed binary roots. Let X,Y be binary, with arrows A_j→X and B_j→Y, and one hidden root U→X,Y. No other arrows or hidden causes occur. Put m=2^d and prescribe

\[
P(x,y\mid a,b)=\tfrac14+\lambda xy\,m\,\mathbf1\{a=b\},
\qquad \lambda>0\text{ sufficiently small}.
\tag{C9}
\]

Both conditional marginals are uniform. If U has k states, write f_a(u)=E[X|a,u] and g_b(u)=E[Y|b,u]. Its law mu is independent of A,B by the graph. Uniform marginals give E_mu f_a=E_mu g_b=0. Therefore

\[
C_{ab}=E[XY\mid a,b]=E_\mu[f_a g_b]
\]

is a matrix of inner products in a centered space of dimension at most k−1. Hence rank C≤k−1. But (C9) gives C=4lambda m times the m×m identity, so k≥m+1.

This target is a valid connected-set perturbation: the equality kernel has the Walsh expansion

\[
m\mathbf1\{a=b\}=\sum_{S\subseteq[d]}\chi_S(a)\chi_S(b).
\]

It has exactly m modes. The M+1-state construction realizes it with locally positive kernels for sufficiently small lambda, so the rank lower bound is attained. For d=2 the checker explicitly realizes it with five states and lambda=1/256, verifies every local cell is at least 1/4, and obtains the exact conditional covariance matrix I_4/16. No root with four or fewer states can realize that specified law on that graph.

Thus a universal connected-set representation of arbitrary parent functions cannot have a state bound polynomial in the number of binary parent variables: this family requires 2^d+1 states with 2d observed parent variables. **This is not an impossibility theorem for positive binary-root hedge witnesses.** The displayed graph and prescribed target test expressive capacity, not the minimum capacity needed to witness some failed causal query. A different observational pair may avoid the high-rank target entirely.

## 6. Prior context, scope, and the remaining question

[Kivva et al., UAI 2022, Appendix C, equations (27)–(29) and Lemmas 17–18](https://arxiv.org/html/2206.01081) already give all-binary noisy-parity witnesses in their stated special case: the observed graph has no directed edges and its bidirected edges form a tree, with all available subsets proper. Their local probabilities are positive conditional on hidden parents. That case does not impose the arbitrary parent-dependent coefficient in (C1). It is fully consistent with the one-mode binary case here. This note does not portray binary locally positive witnesses themselves as new.

[Evans (2018), Lemmas 5.6–5.7 and Corollary 5.8](https://arxiv.org/pdf/1501.02103) supply connected-set degenerate perturbations through finite latent functional models. Those are relevant structural precedents. The present state count follows from the explicit two-endpoint contraction, without a tangent-rank or uniform-neighborhood inference. Neither this comparison nor the elementary compression establishes publication priority.

The proved improvement is quantitative and changes the sufficient capacity assumption: exponential rather than doubly exponential root domains, with an explicit routing-dependent bound. The original HCM sensitivity, graph, support, and limiting-observation hypotheses remain. Existing binary roots suffice for h=0; the general h>0 binary-root question remains open here. The universal representation lower bound warns against claiming that a basis change alone resolves it.

## Reproducibility

The local exact checker also verifies 203 Helmert Gram entries, Walsh orthogonality for one through four bits, and all 125 label patterns of a three-vertex tree with four modes. Only the five constant-label patterns survive. It uses `fractions.Fraction`, no numerical rank thresholds, simulation, or cloud service.

- Checker SHA256: `959c73478b307b5ad851929204b637e8857fec2638257867523b9178f8397840`.
- Certificate SHA256: `3f62c07d25d6e01f3c5f7d1d56506bdd2f54b711dcd9cb95025fb320749790b7`.
- Frozen main proof verified unchanged: `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147`.
