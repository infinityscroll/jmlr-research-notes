# Completeness through a causally separated terminal receiver block

28 October 2026. New proof for source-level review. No held source is changed. This is an actual unit-outcome identification theorem with hidden subunit confounding and subunit-to-unit arrows. Its sufficient calculation is classical conditional transport. It does not solve the shared-latent receiver constraints in the unrestricted HCM completeness question.

## 1. Exact original-HCM class

Fix the following finite acyclic hierarchical graph.

* C is an observed finite unit-context vector generated upstream of everything below. Its coordinates may have a prescribed observed DAG and a positive joint law.
* U is an arbitrary upstream hidden-unit DAG with parents in C or U. It has no subunit parents. Its mechanisms and all private disturbances are unrestricted and mutually independent in the original structural sense.
* O is the set of observed subunits. Their within-unit graph is semi-Markovian: hidden subunit vertices are independent pairwise roots, with possibly prescribed parents in C,U. Observed subunit mechanisms may depend on C,U and their allowed subunit parents. Every observed subunit has a prescribed finite alphabet of size at least two. All physical kernels are strictly positive.
* D is a terminal DAG of unit vertices, observed or hidden. Its parents can be in C,D,O, but not in U or the hidden subunits. There are no D-to-O, D-to-U or D-to-C arrows. Independent unit noise at hidden D vertices can confound arbitrarily many downstream D vertices. All D alphabets are finite with at least two states and their local probabilities are positive.

Thus the upstream unit/within-unit mechanism noises and the entire downstream unit-noise block are independent conditional on C. This follows from the stated graph, not an inferred observational independence. Shared hidden causes *inside* D are permitted. A hidden cause shared across the upstream and downstream blocks is excluded.

For every r in D let B_r=pa_S(r) subset O be its original subunit-parent set. In the convergent limiting HCM its mechanism can depend arbitrarily on the **joint** received law

    S_r = Q_(B_r),                                         (T1)

as well as its ordinary unit parents and own unit noise. It is not restricted to an affine response, a known response function, a finite codebook, or a separate marginal for each subunit parent. The original HCM convergence requirement is retained. Hidden subunit nodes are not direct parents of a D receiver.

The complete observation is Law(C,Q_O,D_obs). Fix a nonempty observed unit outcome set Y subset D_obs. Keep only D ancestors of Y and Y itself. Let R be the retained D vertices with B_r nonempty. Some of these receivers can be hidden. Other D observations may still be included in the experiment.

Fix a nonempty subunit action set I subset O and strictly positive **unconditional product policies** pi=(pi_a:a in I). At each treated node, the actual whole table pi_a must have positive natural probability conditional on its allowed upstream unit parents. Physical positive treatment probabilities alone do not replace this assumption. There is no uniform positive lower bound requirement across all models.

Hidden subunit roots have the capacity required by the held private-switch theorem: 2^(|O|-1)+2 states per existing pairwise root suffices; larger prescribed domains and arbitrary finite observed alphabets are covered by its refinement. The class is nonparametric and allows ignored arrows. There is no faithfulness condition.

The target is the distribution P_pi(Y), or equivalently its joint distribution with the unchanged observed context C. The theorem is uniform identification over this graph class, not identification at every individual exceptional observed law.

## 2. The criterion

For r in R define T_r=B_r minus I. Let ID_r be ordinary within-unit flat ID for P(T_r|do(I=i)). If T_r is empty, call the query successful. The input law includes the treated coordinates in B_r, so on success define the **entire joint received law**

    F_r(q)(x_(B_r))
      = sum_(i:i_(I intersect B_r)=x_(I intersect B_r))
          [product_(a in I) pi_a(i_a)]
          ID_r(q;i)(x_(T_r)).                             (T2)

When T_r is empty, this reduces to the appropriate product-policy marginal. ID_r acts on the actual fine observed alphabets. Hidden unit states are held fixed within each unit and need not be observed to apply the same graphical ID functional to its q.

**Theorem.** In the stated class,

    P_pi(Y) and P_pi(C,Y) are uniformly identified
       iff every ID_r, r in R, succeeds.                 (T3)

On success set S(q)=(q_(B_r):r in R), F(q)=(F_r(q):r in R). From the observation obtain any regular conditional distribution

    K_Y(y|c,s)=P(Y=y|C=c,S(Q_O)=s).

Then an identifying formula is

    P_pi(C=c,Y=y)
       = E[1{C=c} K_Y(y|C,F(Q_O))].                       (T4)

The receiver response is learned on its naturally observed support; it is not supplied as an oracle. The next lemma proves that (T4) does not evaluate an observational conditional on an unsupported counterfactual set.

## 3. Whole-policy support implies transport support

Let Theta collect all upstream unit variables and all subunit-associated unit disturbances other than the action-node disturbances. Condition also on C. The action disturbances are independent of Theta and of each other. The whole table at action a depends on its allowed unit parents and its own private disturbance, although the table's physical rows also index its subunit parents.

Write e_a(C,U)>0 for the conditional probability that this entire table equals pi_a. Let E_pi be the event that every action table equals its queried word and set

    e(C,U)=product_(a in I) e_a(C,U)>0.

This event need not be observable when a treatment has hidden subunit parents. No formula below conditions the data on it.

On E_pi the within-unit experiment is exactly its pi-intervened experiment for the fixed remaining Theta. For any measurable set N in the space of (C,S), natural measure zero implies

    0 = P((C,S(Q_O)) in N, E_pi)
      = E[e(C,U) 1{(C,S^pi(Theta)) in N}].                (T5)

Since e is strictly positive almost surely, this gives

    Law(C,S^pi) << Law(C,S).                              (T6)

It requires neither a bounded inverse propensity nor observability of that propensity. Independence of action private disturbances gives the displayed product; more generally strict conditional joint whole-table support would suffice.

The same argument proves (T6) without first knowing an ID formula for S^pi. On ID success, S^pi=F(Q_O) pointwise in the actual unit state, so the pushforward law appearing in (T4) is the one dominated in (T6). Consequently any two versions of K_Y agree almost surely at the argument used in (T4). This handles arbitrary, including continuous, distributions of the random tables.

## 4. Proof of sufficiency

Let Eta denote the complete private-noise block of the terminal unit DAG. Conditional on C, Eta is independent of the upstream state and all subunit mechanisms. In the limiting original model the downstream DAG can therefore be written as one stochastic kernel of C and the received tuple S; marginalizing its hidden units leaves K_Y.

The policy does not act on any downstream mechanism or noise distribution and does not change C or upstream U. Hence the same structural kernel generates Y under intervention:

    P_pi(C,Y)=Law(C,S^pi) K_Y.                            (T7)

This identity does not replace a natural conditional by an interventional law under hidden confounding; the required independence is a graph assumption already established. Within each fixed upstream unit state, ordinary flat ID returns (T2), regardless of hidden subunit confounding. Thus S^pi=F(Q_O). Equations (T6)–(T7) prove (T4), with every conditional evaluation supported.

Shared hidden parents and observed arrows inside D do not need their own identification argument: no D node is intervened on, and its entire exogenous response block remains independent of the mechanism inputs conditional on C. Multiple input sets need only be separately identified from the *same* q; their joint random-table law is then the simultaneous pushforward F(q). Requiring flat ID of the union of all B_r would be unnecessarily strong.

## 5. Proof of necessity inside the original graph

Suppose ID_r fails for one retained receiver r. Then T_r is nonempty. Remove the downstream block temporarily and apply the held multi-action private-switch completeness theorem to this upstream graph, selected subunit set T_r and the fixed product policy. If observed subunit alphabets are nonbinary, use the held positive refinement.

It supplies two valid positive upstream HCMs with:

1. the same prescribed unit graph and unit-variable law, including C;
2. exactly equal Law(C,Q_O) and equal full natural finite-record laws;
3. positive actual joint whole-policy support at the hidden-parent level;
4. two different **deterministic** policy-selected distributions Q_(T_r)^pi, with a gap witnessed by a fixed group-parity event E.

The witness ignores allowed upstream unit parents, so its policy-selected table is deterministic within each model; C cannot expose its switch. The treatment coordinates in B_r may be ignored by the following receiver response. The linear continuous functional

    f(s)=s{x_(B_r):x_(T_r) in E}                          (T8)

has different values at the two policy input laws. Give r a common binary-group success probability

    P(r is + | s)=1/4 + f(s)/2,                           (T9)

ignoring its other allowed parents. Use positive fiber probabilities if its prescribed alphabet is larger than two.

Because r is a directed ancestor of at least one selected Y coordinate, choose one unit-only directed path r=v_0 -> v_1 -> ... -> v_l=y. At each later path node use the common positive channel

    P(v_j is + | v_(j-1))=1/4 + 1{v_(j-1) is +}/2.        (T10)

This remains valid if some path vertices are hidden. All other D mechanisms use common positive independent kernels and ignore their allowed arguments. No latent capacity beyond the stipulated finite alphabets is needed in D.

Given the same complete observed subunit record and C, this appended downstream system is a common stochastic channel in both models. Thus equality of the entire natural experiment is preserved, including every observed D vertex. In the limiting model it depends on the common observed q only through its true marginals. At finite replication, apply (T9) to the empirical B_r joint and use (T10); the channel remains common. Its continuous uniformly positive kernels satisfy the original convergence condition by the law of large numbers and bounded-KL dominated convergence.

Under the actual policy the y-success gap is the upstream group-event gap multiplied by 2^(-(l+1)), which is nonzero. The actual policy tables and their conditional support were not changed by appending a block with no arrows back into the upstream graph. This proves nonidentification for the selected unit law and establishes necessity.

This argument is not an encoding lemma: (T9) directly converts an upstream causal discrepancy into a supported, positive, observable original-unit outcome discrepancy. It preserves full observations rather than only a receiver moment.

## 6. A nonreset identified example with hidden subunit confounding

Take observed subunits A -> M -> Z and a hidden fair subunit root H -> A,Z. A hidden upstream unit U is a fair sign and may parent all three subunits. A binary terminal unit Y receives Z alone and has no upstream hidden-unit parent. Its response to s=Q(Z=1) is arbitrary in the class.

Within each unit ordinary front-door identification gives

    F_pi(q)(Z=z)
      = sum_a pi(a) sum_m q(m|a)
            sum_(a') q(z|m,a')q(a').                     (T11)

The theorem identifies the unit effect by integrating the observed response P(Y|Q_Z) at F_pi(q), even though H confounds the subunit treatment and final subunit outcome. Whole-policy support supplies the support of those receiver values.

For a concrete positive instance, write A,M,Z in {0,1}, H,U in {−1,+1}. At A a fair independent private unit flag selects either the actual policy pi(A=1)=1/2 or

    P(A=1|H=h,U=u)=1/2+h/8+u/16.
    P(M=1|A=a,U=u)=1/4+a/2+u/16.
    P(Z=1|M=m,H=h,U=u)=1/4+m/4+h/8+u/32.                (T12)

Choose P(Y=1|s)=1/4+s^2/2 for the illustration only; the theorem does not assume this known response. Every physical cell is positive, and the policy's whole table has conditional probability one half. Under the policy,

    Q_Z^pi(1)=3/8+3U/64,                                 (T13)

which depends on U and is not a constant reset. The actual observed conditional response at these input values supplies (T4). The adjacent exact checker reconstructs (T11) independently from every positive within-unit table and compares it with physical intervention enumeration. This is a source-admissible example, not a claim that front-door identification is new.

## 7. What this closes, and what it does not

This is a closure of the supported private-switch completeness result under a **separated terminal receiver block**. It covers genuine subunit-to-unit arrows, hidden subunit confounding, nonlinear receiver mechanisms, latent receivers, arbitrary internal unit confounding, multiple input sets and simultaneous positive product policies.

Its decisive restriction is separation of downstream exogenous variation from upstream unit mechanisms after C. A shared hidden unit parent of a policy mechanism and a receiver invalidates (T7), even if (T6) and perfect knowledge of S^pi continue to hold. An adjacent exact control reconstructs this ordinary bow obstruction; it is not a new counterexample.

The theorem does not handle alternating unit/subunit feedback, hidden subunit parents received directly by a unit, conditional or correlated policies, arbitrary shared-latent receiver constraints, or general completeness of a search over the paper's augmentations. It neither declares a failed raw collapse calculation a failure of the authors' complete toolbox nor resolves their Section 8.2 open problem. Its positive transport principle is classical; the support-preserving converse is inherited and applied to an actual receiver outcome. The result should be assessed as a scoped technical extension, not a confirmed significant breakthrough.

## Read-only dependencies

* `../multiple_private_switch_gate_20261028/multiple_policy_completeness.md`, SHA256 `acb87f7dfaca473bbc87dba2dfd43cc5f9717ba9d1bef14cd0bed90d3bf9b3cf`.
* `../alphabet_refinement_gate_20261028/positive_finite_alphabet_refinement.md`, SHA256 `4364d97a03288717303da9e21732b92683c0ffe587cf89ab67d2723d846c6fb1`.
* Earlier reset criteria: `../general_bridge_lifting_20261027/arbitrary_dag_positive_reset_completeness.md`; their positive argument is CSI/district recovery, and their inputs exclude hidden subunit confounders.
* Earlier finite-policy receiver encodings: `../generic_policy_completeness/theorem.md` and `../receiver_quotient_characterization/theorem.md`; those results have different finite-support/generic-policy or no-hidden-subunit premises.

Primary model semantics: [Weinstein and Blei, Hierarchical Causal Models](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf), Definitions 1–2 and 5, Theorem 6 and Sections 8.1–8.2. Ordinary flat identification: [Shpitser and Pearl, Complete Identification Methods for the Causal Hierarchy](https://jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf). The new proof imports the held actual-query positive private-switch converse, not an unqualified older subquery-hedge statement.

