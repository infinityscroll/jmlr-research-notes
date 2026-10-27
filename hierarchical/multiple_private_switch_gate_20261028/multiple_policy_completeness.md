# Several supported subunit policies using independent private switches

28 October 2026. Separate extension candidate; the held single-policy source is unchanged. An independent-switch AND event suffices. A shared unit selector or a coordinated parity switch is unnecessary.

## 1. Statement and exact scope

Use the prescribed no-feedback hierarchical graph class of `../prescribed_unit_structure_gate_20261028/private_switch_completeness.md`, SHA256 `274e543e79b4dc24e4ee745a48887f4deb191b60b59cf46d4ffa8723aacac755`. In particular: arbitrary prescribed finite unit DAG and observed unit covariates C; no subunit-to-unit arrows; binary observed subunits O; a semi-Markovian hidden-subunit graph with sufficiently rich existing finite pairwise roots; unrestricted permitted mechanisms and independent private disturbances; locally positive physical subunit kernels. The observation is Law(C,Q_O).

Replace the single action by a nonempty set B subset O and let Y be a nonempty subset of O minus B. Fix a strictly positive **unconditional** policy pi_a for every a in B. The simultaneous action replaces all B mechanisms, drawing independently according to these policies. Its within-subunit action law is the product pi_B=product_a pi_a. The HCM class requires the actual joint tuple of queried tables to have positive natural probability conditional on all their allowed unit parents. This joint requirement is stronger than merely requiring each table separately to appear somewhere.

**Theorem.** Ordinary flat ID for P(Y | do(B=b)) in the subunit graph is complete for Law(C,Q_Y^{pi_B}) and E Q_Y^{pi_B} in this class. If ID fails, witnesses can be chosen with no shared unit selector, with mutually independent private unit switches at the treated subunits, with all non-treatment mechanisms constant across units, and with identical observational laws for every finite number of units and subunits. Their full natural treatment-table distribution is the same in both models, yet their selected simultaneous-policy targets differ.

For a chosen failure hedge F containing k=|F intersect B|>=1 treatments, the witnesses have joint queried-table probability

    s_k=k!/(2k)!>0.                                          (M1)

Every treated vertex outside F always uses its queried policy. Each treated vertex inside F genuinely has two different positive tables. If r=|B|, then s_k>=s_r, so the support bound can also be expressed using the total action count. No lower bound uniform in r is claimed.

This is for simultaneous unconditional product policies. It does not establish a theorem for arbitrary parent-dependent policy tables, correlated stochastic interventions, a prescribed minimum policy-support constant independent of action count, fixed binary hidden roots on all graphs, or subunit-to-unit feedback. It does not assert that every action in a counterexample is necessary for a target discrepancy.

## 2. Exact nested-mode construction

The old multimode flat theorem and joint-target corollary already apply to an arbitrary actual action set B, not merely to a single treatment. Their hashes are respectively `60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147` and `8119664d55ca00547478e336784a0143a359d20c47fe3623e877b590dac282bf`.

A failure supplies a hedge I subset F with I disjoint from B and F intersect B nonempty, and a directed route forest K avoiding all B and ending in a nonempty selected sink set T subset Y. Choose the positive noisy-parity baseline and inner coefficient exactly as in the old route proof, except set p_a=pi_a at **every** a in B. This is consistent because K avoids B. Let

    p_0=product_v p_v,
    c_F=chi_(F minus I)c_I product_(v in F minus I)p_v,
    Psi=chi_I c_I product_(v notin I)p_v.                     (M2)

The outer connected-set perturbation equals the same Psi pointwise. As in the single-policy source, superpose one inner label family on a tree T_I and the outer Fourier labels on an extending tree T_F. Put the coefficient signs at one fixed i0 in I, so all coefficients at every treated vertex are common across the two model signs sigma in {−1,+1}. Choose amplitudes sigma lambda for the inner contribution and −2sigma lambda for the outer contribution, with lambda small enough to keep every physical local cell positive.

At each a_j in F intersect B multiply **all of its local outer terms** by its own flag t_j in {0,1}. It has no inner term, since I avoids B. Its t_j=0 table is exactly pi_(a_j), independently of all hidden and observed parent assignments. Its t_j=1 table is the common positive alternative.

The single-policy source's full contraction remains valid. A surviving outer mode must occupy all F with one common label; otherwise a tree boundary has a mean-zero or orthogonal hidden factor. Its coefficient therefore contains product_j t_j. A surviving inner mode occupies all I and is unaffected by those flags. A surviving term cannot contain both an inner and an outer mode because I intersects F. Thus, at every complete observed assignment,

    q_(sigma,t)=p_0+sigma lambda Psi
                         −2sigma lambda(product_(j=1)^k t_j)Psi. (M3)

This is an exact full-joint identity, not an approximation or a marginal moment matching. If any flag is zero, the law is q_sigma:=p_0+sigma lambda Psi; only the all-one flag vector gives q_(−sigma). No mechanism reads another vertex's private flag.

Use independent Bernoulli flags with

    P(t_j=1)=(k+j−1)/(k+j),       j=1,...,k.                  (M4)

Their all-one probability telescopes to k/(2k)=1/2. Their all-zero probability is product_j 1/(k+j)=k!/(2k)!, proving M1. These probabilities are strictly between zero and one, so every natural flag vector has positive probability. The two HCMs use the same flag distributions and the same treatment tables. All other private unit disturbances associated with subunit mechanisms may be ignored; endogenous unit variables still have the same arbitrary positive common law in both witnesses.

Consequently

    Law(Q_O | sigma=+1)=Law(Q_O | sigma=−1)
                       =(delta_(q_+)+delta_(q_−))/2.           (M5)

The subunit mechanisms ignore permitted unit parents in these witnesses. This preserves the exact prescribed graph and gives equality jointly with observed C. It also makes the joint policy-table probability M1 hold conditional on every allowed unit-parent assignment.

The actual simultaneous intervention sets every treated table to its t_j=0 baseline (and leaves already-baseline actions outside F unchanged). Its selected law is therefore the selected marginal of q_sigma. The route calculation sums all independent product-policy factors and gives

    E_(q_+)chi_T−E_(q_−)chi_T
                         =2lambda 2^(−|K minus I|)>0.         (M6)

For every finite number m of subunits the natural record law is exactly (q_+^{tensor m}+q_−^{tensor m})/2. Independent units and the common C law preserve equality of every finite observational experiment. Local physical positivity, common hidden-root laws, and no-sharing of private unit disturbances hold exactly as in the single-policy source.

On ID success, conditioning on all unit variables and private unit disturbances leaves a positive flat model. With no feedback, the simultaneous intervention changes just the B tables and no unit variable. Hence the identified within-unit functional is

    F_(pi_B)(q)=sum_b [product_(a in B)pi_a(b_a)] ID_b(q).      (M7)

Its pushforward jointly with C and its expectation identify the stated targets. This proves the iff.

## 3. Finite capacity remains bounded by the same graph-wide quantity

Let h=|(F minus I) intersect K|. In the outer coefficient, the noisy route factors contribute at most 2^h Fourier modes. The k unconditional action baselines contribute at most 2^k modes. The route avoids B, so these factors are legitimate parent functions under the old matching identity and

    h+k <= |F minus I| <= d−1.

Thus the outer family has at most 2^(d−1) nonzero labels. The one inner label and constant baseline can be realized using at most 2^(d−1)+2 states on each existing pairwise hidden root, via the old orthogonal-label compression. This is the same conservative graph-wide sufficient bound as the single-policy source. The sign placements do not require new roots or children. Larger prescribed domains with unrestricted positive laws can be partitioned into equally weighted effective labels. A prescribed incompatible hidden law, or a universal binary-hidden claim, remains outside scope.

## 4. A three-observed-node, two-action binary fixture

Take no endogenous unit variable. The observed subunits are A1,A2,Y with directed chain A1->A2->Y. Two independent fair hidden subunit bits H12,H2Y give the pairwise links A1<->A2<->Y. The action set is {A1,A2}; each queried policy is a fair Bernoulli. This is the smallest possible number of observed vertices for two distinct treatments and a nonempty disjoint observed outcome. No minimal hidden-cardinality or intervention-necessity claim is made.

Let t1,t2 be independent private unit flags with probabilities 2/3 and 3/4 of being one. In signs a1,a2,y,h12,h2y in {−1,+1}, use

    P(a1|h12,t1)=1/2+(t1/8)a1 h12,
    P(a2|a1,h12,h2y,t2)=1/2+(t2/8)a1 a2 h12 h2y,
    P_sigma(y|a2,h2y)=1/2+sigma y[1/128−a2 h2y/4].       (M8)

All hidden masses are positive. Every A cell is at least 3/8 and every Y cell at least 31/128. The treatment tables, including their flag laws, are identical in the two models; only the fixed Y table changes with sigma. Direct summation over both hidden bits gives

    q_(sigma,t)(a1,a2,y)
       =[1+sigma(1−2t1t2)y/64]/8.                         (M9)

The four flag probabilities are 1/12,1/4,1/6,1/2 for 00,01,10,11. Therefore each model has the same equal mixture of the two distinct full observed tables. The actual queried table pair has natural probability 1/12. Under the simultaneous policy, P(Y=+1) is 65/128 in model + and 63/128 in model −, a gap 1/64.

This fixture has three binary observed nodes, two binary hidden subunit roots, no shared unit noise, two genuinely varying treatment tables, strict physical positivity, full Cartesian natural support of the four flag states, and exact equality of all finite natural records. It certifies a multi-action example; the arbitrary-graph conclusion rests on Sections 2–3, not on extrapolation from this example.

## 5. What this changes and what it does not

Equal-probability fair switches at every treatment would not give the desired two-atom swap when k>1: the all-one mass would be 2^(−k), rather than 1/2. That is a failure of that particular balanced-switch choice, not of independent switching. The explicit unequal Bernoulli probabilities M4 repair it while keeping the actual joint policy supported. A parity-based dependence between private disturbances is neither needed nor allowed.

The original [HCM Definition 2](https://www.jmlr.org/papers/volume27/25-0899/25-0899.pdf) permits a set of simultaneous subunit-table replacements. This note checks the additional independence and joint-support seam needed to extend the new private-switch converse to that set. It adds no receiver/feedback case and no generic-informative-environment guarantee. Its proof is a short extension of the held nested-mode construction, not a new flat ID theorem or a separate claim of historical novelty.
