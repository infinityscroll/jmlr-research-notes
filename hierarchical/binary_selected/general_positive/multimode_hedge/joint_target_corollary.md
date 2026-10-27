# Joint selected binary outcomes

26 October 2026. Separate corollary to the unchanged [single-outcome theorem](theorem.md), SHA `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147`. The connected-set realization, hidden capacity, observational matching, and local positivity arguments are unchanged.

Let Y be a nonempty set of observed binary variables disjoint from the actual action set A. If ordinary ID fails for P(X_Y | do(X_A=a)), its actual-query hedge I⊂F has roots R⊂An_{H\A}(Y). Every i∈I is therefore also an ancestor of the set Y in H\A. It need not be an ancestor of any one common selected outcome.

For each vertex that can reach Y in H\A, choose an outgoing edge decreasing its shortest distance to Y; vertices in Y have no selected outgoing edge. Keep the vertices and edges reached from I by these choices. The resulting directed forest K has outdegree one at every nonsink, contains all of I, avoids A, and has a nonempty sink set T⊂Y. Routes stop at their first selected outcome. They may merge or pass through other I vertices or nonroot F vertices. Selected outcomes not reached from I are outside K and play no role in the discrepancy.

Write J_v for the selected routing parents of v. Use exactly equations (9)–(10) of the main proof: positive noisy parity baseline channels with β_v=1/2 at v∈K\I, fair baseline channels elsewhere, and

\[
c_I=2^{-|I|}\prod_{i\in I}\prod_{u\in J_i}x_u.
\]

Define c_F by the same equation (6), and take λ positive and small enough for the same local-cell bound 1/8. This gives equal full observational laws and the signed postintervention difference (8). After summing variables outside K∪A, it is

\[
\lambda 2^{-|K|}\prod_{i\in I}L_i
    \prod_{v\in K\setminus I}(1+\beta_vL_v),
\qquad L_v=x_v\prod_{u\in J_v}x_u.
\]

The map x_K↦L_K is a bijection by topological recursion. Each nonsink occurs once as its own sign and once as a selected parent's sign, so

\[
\prod_{v\in K}L_v=\prod_{t\in T}x_t=\chi_T(x).
\]

Fourier orthogonality now gives, for every assignment a,

\[
\mathbb E_{M_I}[\chi_T(X)\mid do(a)]-
\mathbb E_{M_F}[\chi_T(X)\mid do(a)]
=\lambda\prod_{v\in K\setminus I}\beta_v>0.
\]

Equivalently, the selected event {χ_T(X)=+1} has probability difference λ·2^{-|K\I|-1}. Since T⊂Y, the joint selected law on Y differs. The conclusion does **not** imply that every selected one-variable marginal differs; the discrepancy can reside only in a joint parity.

Composing with exact sensitivity (S) and the same positive continuous receiver lift gives completeness for joint laws of selected fixed-binary original unit variables, for arbitrary actual action sets and collapsed graphs in the stated pairwise hidden-root HCM class with sufficient finite hidden state capacity. The observation is the complete limiting mechanism law, and the policies are the actual prescribed positive conditional policies. The assumptions and exclusions of Section 5 of the main theorem apply unchanged. This corollary does not concern selected subunit functionals or contrasts between action assignments.
