# Completeness with a prescribed unit graph: a private policy-switch construction

28 October 2026. New candidate for independent audit. This source removes the universal hidden unit root from the recent support-preserving completeness theorem. It imports the older flat connected-set realization and hedge routing ideas, but uses a different hierarchical witness: only the treatment's own private unit disturbance varies. No frozen source is changed.

## 1. Class, observation, and result

Fix a finite acyclic hierarchical graph with **no subunit-to-unit arrows**. Its unit graph, its observed/hidden unit designation, and all unit-to-subunit parent sets are prescribed arbitrarily. There need not be a shared hidden unit cause; the unit graph may be empty. Unit structural mechanisms are unrestricted on their allowed arguments, with mutually independent private disturbances as in Weinstein and Blei's Definition 1.

The subunit graph is semi-Markovian: observed vertices O, d=|O|>=2, have binary alphabets; hidden subunit vertices are independent pairwise roots in the subunit graph. Such roots may have prescribed unit parents. Their finite alphabets have sufficient capacity as specified in Section 5. Conditional on all unit variables and private unit disturbances, all local subunit kernels are strictly positive. The unit variables can have any prescribed finite nonempty alphabets. Allowed arrows need not be functionally active; there is no faithfulness or minimum-heterogeneity assumption.

Let C be the vector of observed unit variables. The limiting observed experiment is the source's actual Assumption 1 experiment

    O_H=Law(C,Q_O),                                             (P1)

where Q_O is the entire within-unit joint law of the observed subunits. Fix one observed subunit treatment A, a nonempty selected set Y subset O minus {A}, and a known unconditional policy pi with pi(−1),pi(+1)>0. The actual whole A-table pi must have positive natural probability conditional on its collapsed unit parents. This is not merely positivity of sampled A values.

**Theorem.** In this class, ordinary flat ID for P(Y | do(A=a)) in the semi-Markovian subunit graph is complete for

    Law(C,Q_Y^pi)  and  E Q_Y^pi.                              (P2)

On success, the identified functional is the pushforward of (P1) by

    (c,q) -> (c,F_pi(q)),   F_pi(q)=sum_a pi(a) ID_a(q).       (P3)

On failure, there are two HCMs on the **same prescribed hierarchical graph**, with the same unit-variable law, the same hidden subunit-root laws, the same natural distribution of A's two mechanism tables, and conditional pi-table probability exactly 1/2, such that:

* their full observations (P1) agree;
* their natural observations agree for every finite number of units and subunits;
* their selected policy distributions and pooled laws differ.

No shared endogenous unit variable is used in these witnesses. All non-A subunit mechanisms are constant across units. The only subunit-associated private unit disturbance used nontrivially is A's own Bernoulli switch; endogenous unit variables may still have their own random private disturbances. Unit covariates cannot distinguish the two models, because the subunit mechanisms in the witnesses ignore their allowed unit parents. The result concerns a distribution or some selected parity probability, not every preassigned scalar contrast or ATE.

## 2. Bound old ingredients and the new superposition

The flat dependencies are:

| Source | SHA256 |
|---|---|
| `../binary_selected/general_positive/multimode_hedge/theorem.md`, Sections 1–4 | `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147` |
| `../binary_selected/general_positive/multimode_hedge/joint_target_corollary.md` | `8119664d55ca00547478e336784a0143a359d20c47fe3623e877b590dac282bf` |
| `../binary_selected/general_positive/hidden_capacity_attack/capacity_compression_v2.md` | `1dfc788b295bf9dc30202bfa7315f5eb44f98b662b04c6794b543ef84cd7d6af` |

Those sources already prove locally positive binary-observed hedge witnesses, including routes that re-enter the outer hedge. They do not by themselves supply the independent-private-switch HCM pair below. The previous supported binary composition, SHA256 `25ba59f7963f9f26b3834ec089ea1e161fb4bfdc1f3395fd4ced6a059466665a`, instead used a universal hidden unit root and changed its mixing probabilities. That root and its reweighting are not present here.

For a failed actual query, take an inner/outer hedge I subset F with A in F minus I. Choose a bidirected spanning tree T_I on I and extend it to a spanning tree T_F on F. The usual compatible directed forest makes each vertex of F minus I a parent of some F vertex. Put P_D=union of the observed-parent sets of vertices in D; this includes parents lying inside D.

Choose positive baseline subunit kernels p_v, with **p_A=pi exactly**. For a connected set D, the old realization gives the observable perturbation

    Psi_D(x)=chi_D(x)c_D(x_{P_D}) product_{v notin D}p_v(x_v|pa_v),
    chi_D=product_{v in D}x_v.                                (P4)

Choose c_I as in Section 4 below and set

    c_F=chi_{F\I} c_I product_{v in F\I}p_v.                (P5)

This is a function of P_F: every own variable in F minus I is an observed parent of an F vertex, and all other arguments are also in P_F. It does not authorize a local kernel to read its own outcome. The old Fourier allocation assigns each parent character to an allowed child. As in the old proof,

    Psi_F(x)=Psi_I(x)=:Psi(x) pointwise.                       (P6)

**Simultaneous-mode lemma.** On this same graph, one can realize, for every sufficiently small lambda>0 and each sign sigma in {−1,+1}, two A-table settings t in {0,1}, with full observed joint law

    q_{sigma,t}=p_0+sigma lambda Psi−2sigma lambda t Psi,
    p_0=product_v p_v.                                       (P7)

All non-A local kernels are fixed as t varies. At t=0, A's actual complete table is pi. At t=1, A uses one other strictly positive table, the **same table in both sigma models**. Every physical local kernel is bounded below by a common positive constant depending on pi and the finite construction.

Here is a complete contraction argument. Expand c_F into its M nonzero allowed-parent Fourier modes. Use a separate outer mode label for each of them on T_F. Use an additional, distinct inner label on T_I for the one-monomial c_I. At a vertex in I, its kernel is its baseline plus the sum of its inner and outer perturbation terms; at a vertex in F minus I, it has only outer terms. Every term has the form

    x_v b_{v,j} f_{v,j}(x_pa(v)) product_{e incident to v}phi_j(H_e), (P8)

where f uses only allowed observed parents. For an outer label the incident edges are those of T_F; for the inner label they are those of T_I. Every term sums to zero over x_v. On a common edge, label functions have mean zero and are pairwise orthogonal; Section 5 gives explicit finite root distributions.

In the product expansion at a fixed complete observed assignment, a vertex can choose only one additive label or its baseline. If any vertex selects an outer label j, a boundary edge of T_F would pair phi_j either with a constant or with a different orthogonal label, giving zero expectation. Thus a surviving outer label must occupy **all F**, with the same label at every vertex. If no outer label appears, a surviving inner label must occupy **all I**, by the same argument on T_I. Since I is nonempty and contained in F, an all-F outer term and an all-I inner term cannot occur together. The only surviving contributions are the baseline, the all-I inner term, and each all-F outer term. There is no uncontrolled mixed term.

Choose the products of inner coefficients to yield sigma lambda c_I, and of outer coefficients to yield −2sigma lambda c_F, with their orthogonal-label norm corrections included. Put every sign sigma, and every outer Fourier-coefficient sign, at one fixed vertex i0 in I. That vertex is not A. All coefficients at A can therefore be chosen identical in the two models. Multiplying **all A outer terms** by t switches the entire outer contribution between zero and its prescribed value while changing no other local mechanism. At t=0, A's kernel is p_A=pi with no remaining hidden or observed-parent dependence. This proves (P7).

For positivity choose magnitudes of inner coefficients proportional to lambda^(1/|I|), and outer coefficients proportional to lambda^(1/|F|), with fixed finite normalization factors. At each vertex the finite sum of absolute perturbations tends uniformly to zero as lambda decreases to zero. Select lambda so this sum is at most half the minimum baseline cell. This works simultaneously for both sigma signs and both table settings; the factor 2 is included in the outer coefficients. Singleton I uses its direct local perturbation and requires no inner hidden edge. Since F contains both I and A, F has at least two vertices. The alternative A-table differs from pi: it contains a nonzero outer mode on an incident T_F edge, and the distinct orthogonal modes cannot cancel identically as a function of the hidden parents.

## 3. The original-HCM private switch and exact observation equality

Let every unit variable follow any one common distribution compatible with its prescribed unit DAG; for finite alphabets a product of positive marginal distributions, ignoring allowed unit arrows, suffices. Use that law in both models. All subunit mechanisms ignore their allowed unit parents. Hidden subunit roots have the common independent finite laws in Section 5 and ignore all private unit disturbances.

At A only, its own independent unit disturbance chooses t=0 or 1 with probability 1/2 each. All subunit samples in that unit share that choice, and then use fresh independent subunit disturbances. Every other subunit-associated private unit disturbance can be ignored. This is exactly the structure permitted by Definition 1: no disturbance is shared between different endogenous mechanisms.

Define q_+=p_0+lambda Psi and q_−=p_0−lambda Psi. Equation (P7) gives

    Law(Q_O | sigma=+1)=Law(Q_O | sigma=−1)
                       =(delta_{q_+}+delta_{q_−})/2.             (P9)

The common observed unit vector C is independent of this random table in the witnesses, so its joint law with Q_O also agrees. The A-table distribution itself is the same two-table distribution in both models, and the actual queried pi table has probability exactly 1/2 conditional on every allowed unit-parent assignment. Thus the original queried intervention support is verified directly.

The literal policy removes A's unit switch and uses pi, which is precisely t=0. Hence

    Q_O^pi=q_sigma deterministically in model sigma.             (P10)

For each finite m, the natural within-unit record law is exactly

    (q_+^{tensor m}+q_−^{tensor m})/2,                           (P11)

in both models, jointly with the same C law. Independent units give equality for every finite observational dataset, not just equality in the limiting mechanism experiment. The policy record laws differ whenever the selected marginal of q_+ differs from that of q_−, as proved next. All physical subunit kernels and hidden-root masses are strictly positive. No deterministic support violation or extra auxiliary intervention has been introduced.

## 4. A nonzero selected-outcome discrepancy, with arbitrary positive pi

Use the old re-entry-safe directed route forest K in G with A removed, starting at every I vertex and ending at a nonempty sink set T subset Y. Every non-sink has one chosen child. Let J_v be the selected K parents of v. Take

    p_v(x_v|pa_v)=[1+(1/2)x_v product_{u in J_v}x_u]/2
                     for v in K minus I,
    p_A=pi,
    p_v=1/2 otherwise,
    c_I=2^{−|I|} product_{i in I} product_{u in J_i}x_u.          (P12)

There is no conflict in (P12), because K avoids A. All baseline cells are at least delta0=min(1/4,min_a pi(a))>0. The triangular sign transformation L_v=x_v product_{u in J_v}x_u has product over K equal to chi_T. The old orthogonality calculation, now with the independent factor pi(A) summing to one, gives

    sum_x chi_T(x) Psi(x)=2^{−|K\I|}=:b>0.                    (P13)

Variables outside K and A have fair baseline kernels and sum out. Re-entry through F minus I or through another I vertex is already accounted for by the selected-parent factors in (P12). Therefore

    E_{q_+}chi_T−E_{q_−}chi_T=2lambda b>0.                    (P14)

The positive-parity event probabilities differ by lambda b. Thus both the selected distribution and its pooled probability vector differ. For a singleton binary Y this is an ordinary outcome-mean difference. The discrepancy does not depend on a treatment-value contrast; it is a difference between two models at the same actual soft policy.

For the success direction, condition on all unit variables and all private unit disturbances. The remaining per-subunit mechanisms form a positive flat model on the fixed subunit graph. Since there are no subunit-to-unit arrows, the intervention changes no unit variable and no other selected subunit mechanism. Successful flat ID gives Q_Y^pi=F_pi(Q_O) pointwise. Finite positive-table ID expressions are measurable, so pushforward and expectation establish (P3) jointly with C. Combining this with (P9)–(P14) proves the theorem.

## 5. Finite hidden capacity and exact policy support

Unrestricted finite hidden-root alphabets suffice. There is also a graph-wide sufficient fixed bound. With the baseline (P12), the outer coefficient (P5) is, up to a nonzero constant and sign monomial,

    (1+mu x_A) product_{v in D}(1+(1/2)L_v),
    mu=pi(+1)−pi(−1),   D=(F minus I) intersect K.              (P15)

Its number of nonzero Fourier modes is at most 2^{h+1}, h=|D|. Since A is outside K and I is nonempty, h<=d−2. The inner coefficient has one mode. Thus at most M+1 nonconstant labels, M<=2^{d−1}, are required on any common hidden edge.

The old compressed orthogonal-label construction supplies those labels on K0=M+2 equally likely states: use the constant function and M+1 nonconstant mutually orthogonal Helmert contrasts, with their explicit positive squared norms. Apply the norm correction separately to each tree-mode coefficient product. Every root is independent; no cross-root coupling is used. The contraction in Section 2 remains valid even though the inner label uses fewer edges, because T_I is a subtree of T_F and the inner and outer labels are orthogonal on every shared edge.

Consequently **2^{d−1}+2 states per existing pairwise hidden subunit root suffice** uniformly over the graph, selected outcome set, and prescribed positive pi. This is a sufficient bound, not a minimality claim. If a prescribed root has a larger finite alphabet with otherwise free positive law, partition it into K0 nonempty groups and give each group probability 1/K0, distributed positively over its member states. Use the same grouping and law in both witnesses. A separately prescribed incompatible hidden-root law or fixed binary hidden roots are not covered by this general capacity statement. The two-node fixture below needs only one binary hidden root.

The bound lambda in the positivity argument may deteriorate with graph size, pi, or the hidden-label normalization. No quantitative effect-size lower bound uniform over those parameters is claimed. Nevertheless the actual whole-policy support remains exactly 1/2 and does not deteriorate with lambda. Support of unrelated hard mechanism values or a full Cartesian mechanism codebook is neither assumed nor needed.

## 6. Small binary fixture and source-model meaning

Take no endogenous unit variables, observed binary subunits A,Y in signs {−1,+1}, a hidden binary subunit root H with H->A,Y and A->Y, and H fair. For pi(A)=1/2, let A's private unit switch choose equally between

    P(A=a|H=h)=1/2,
    P(A=a|H=h)=(1+(1/2)ah)/2.

In model sigma in {−1,+1}, use

    E[Y|A=a,H=h]=sigma(1/16−(1/4)ah).                       (P16)

Under pi, E[Y|A=a]=sigma/16. Under the second table, E[H|A=a]=a/2, so E[Y|A=a]=−sigma/16. Thus q_±(a,y)=(1±y/16)/4, and the natural complete-table law is the same equal mixture of q_+,q_−. Under do(pi), P(Y=+1) is 17/32 or 15/32, a gap 1/16. Every A cell is at least 1/4, every Y cell at least 11/32, and pi-table support is exactly 1/2. This fixture demonstrates the private switch directly; the general theorem does not rely on extrapolating from it.

The primary [HCM paper](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf), Definition 1 (page 10), assigns each subunit both its own private unit disturbance and its own subunit disturbance. Definition 2 replaces the treatment table and removes the former dependence. Assumption 1 (page 27) observes Law(C,Q_O), not the hidden-parent A table or the private switch label. Assumptions 2–3 are satisfied by the displayed physical positivity and whole-policy atom. No-feedback makes the source's unit-mechanism convergence immediate here.

The paper's Section 8.1 explicitly leaves hidden subunit confounding as a direction to investigate, and Section 8.2 asks for completeness in general HCMs. This theorem answers a restricted no-feedback hidden-subunit-confounding question for arbitrary prescribed unit structure, including an empty unit graph. It does **not** settle the receiver/feedback numerical-constraint obstacle in Section 8.2. Its comparison is with within-unit flat ID, not with the erased-inner-plate graph or a claim that every published augmentation search is complete. Theorem 13 of the source concerns unit treatments and no hidden subunit confounders, a different class.

The older Fourier realization, ordinary hedge completeness, and mixture-label ambiguity are established ingredients. The proposed additional result is the exact support-preserving private-switch converse on a prescribed hierarchical graph, with observed covariates and no shared unit selector. No publication-priority or significance claim follows from this internal construction alone. A separate primary-literature gate remains necessary.
