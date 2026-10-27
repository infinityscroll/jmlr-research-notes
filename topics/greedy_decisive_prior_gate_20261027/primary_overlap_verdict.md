# Decisive prior-art gate for adaptive greedy topic recovery

27 October 2026. Primary-theorem comparison, with an explicit reduction. No priority clearance, external approval, or publication claim.

The target is `../adaptive_greedy_recovery_20261027/penalized_successive_projection_theorem.md`, SHA256 `93a8dcf921f94cc594ef08f01b7620ff8427be8c686fbc90704771165b36b7a7`. The prior statistical comparison is `../adaptive_frontier_novelty_20261027/primary_novelty_and_significance.md`, SHA256 `3f0a5c1ec6d2ad853dea3bc7c12cc0536f23deef474208b7088fdbc82a3c9f59`.

## Verdict

**The claim of major standalone algorithmic novelty should be demoted.** The companion derivation `classical_spa_contraction_reduction.md`, SHA256 `6f6613f2758ffca32473fea5392a19775be72ee06384ef9a63e711e74335827d`, obtains the same adaptive upper rate and O(pK^2) anchor-stage arithmetic count using classical Gillis–Vavasis SPA after elementary, observable contraction toward the frequent-core center.

This is an actual theorem-to-theorem reduction of the guarantee for an alternative estimator. It is not a claim that the contraction or the new penalized-score algorithm was printed in an earlier paper. The reduction still uses this project's empirical-frequency error bound and frequent-core statistical construction. Thus it does not subsume the complete unknown-anchor-strength statistical frontier into an old topic theorem. It identifies exactly which part of a possible contribution should carry the weight: the joint quantitative statistical analysis, not a new simplex-finding principle.

## 1. Classical SPA now suffices after explicit preprocessing

Gillis–Vavasis Theorem 3 gives recovery error proportional to maximum column noise under full-rank separability and substochastic coefficients. Its Algorithm 1 is ordinary squared-norm successive projection. The companion note constructs a center c and known radius r with B(c,r) inside conv(0,V), using the already selected frequent core. The observable contraction

    ytilde_j = [r/(r+pen_j)] yhat_j
                +[pen_j/(r+pen_j)] chat

produces a separable matrix with uniform noise at most

    (1+2/r) P_T + Z + ||chat-c||,

where P_T sums the true anchors' penalties and Z is the maximum excess of row error over its penalty. The center error has expected order m^(-1/2). The published theorem, followed by the existing reconstruction, gives the same adaptive expected L1 rate. [Gillis–Vavasis, Algorithm 1 and Theorem 3](https://optimization-online.org/wp-content/uploads/2012/08/3557.pdf).

The nonanchor ideal coefficients are reassigned after contraction; only the topic vertices need be preserved. The designated anchors are assigned their original ideal vertices, paying O(P_T). These are proof assignments, not oracle inputs. This is why the transformation avoids needing a uniform bound on the original normalized-row errors. The companion note supplies explicit constants and the selected-core expectation argument.

## 2. What the direct robust-SPA theorems already say

**Jin–Ke–Moryoussef–Tang–Wang, ICLR2024, Theorem 1.** This is a stronger direct antecedent than a maximum-raw-noise theorem. Its error parameter is the maximum of (i) the largest observed distance to the true simplex and (ii) the worst, across true vertices, of the best pure-row approximation error. Thus it already tolerates large perturbations of interior rows. Its Gaussian pp-SPA rate theorems separately impose common isotropic noise and growing pure-point populations; those assumptions do not describe count-normalized topic rows with one rare anchor per topic. [Primary paper, equations (6)–(7), Theorems 1–3](https://proceedings.iclr.cc/paper_files/paper/2024/file/7504142a20a3e1fe9dd7de42f475828c-Paper-Conference.pdf).

The direct substitution fails on a precise deterministic example. Let

    v_1=(7/8,1/8),  v_2=(1/8,7/8),
    y_1=v_1, y_2=v_2, y_3=(1/2,1/2),
    yhat_1=y_1, yhat_2=y_2, yhat_3=(1,0),
    pen_1=pen_2=0, pen_3=1.

Here P_T=Z=0, while the third observation is at distance sqrt(2)/8 from conv(v_1,v_2), and ordinary unprocessed SPA selects it first. The new oracle guarantee is exact on this input, so neither maximum raw error nor the 2024 distance-to-simplex parameter is bounded by P_T+Z. This does not refute the published theorem; its hypothesis parameter is simply different. For the contraction route, nu=3/4 gives r=3/64 and chat=(1/3,1/3). The third transformed row is (73/201,64/201), whose coefficients in V are (149/402,125/402), nonnegative with sum below one. The original two anchors remain exact, so classical substochastic SPA recovers them exactly.

**Gillis2019, Sections 2–3.** Robust SPA changes the candidate-selection rule using residual reconstruction error. Its explanation allows a different strongly convex function at each iteration, but requires that function to be common across candidate columns, nonnegative and zero at its minimum at the origin. The column-dependent functions ||x||^2-4pen_j do not satisfy that stated premise. The paper retains low-uniform-noise robustness; it does not state the present P_T+Z oracle inequality. [Primary paper, Assumptions 1–2 and Algorithms 2–3](https://arxiv.org/pdf/1908.04109v1).

**Barbarino–Gillis2024/2025.** The paper sharpens conditioning factors, proves tightness, and studies translated/lifted variants. Its basic error parameter remains maximum column perturbation. It also explicitly credits the standard O(r nnz(X)) implementation, so our O(pK^2) count for a dense p-by-K input is a classical SPA cost, not a new complexity principle. [Primary preprint, Theorem 1, Remark 1, Sections 2 and9](https://arxiv.org/pdf/2411.16195v1).

These comparisons do not rule out every heterogeneous-noise NMF result. They identify the premises of the closest inspected primary statements and, through Section1, give a valid route that does not require such a statement.

## 3. Frequency-sensitive topic estimation and penalties have substantial antecedents

Arora et al.2013 already combine normalized co-occurrences, automatic anchor selection and full topic recovery. Their main-paper sample guarantee has substantially stronger inverse anchor-strength dependence than the present alpha^(-1) effective-sample scale. This is an antecedent, not a contradiction or a comparison claiming their newer recovery algorithm has only the displayed older rate. [Primary paper, Definition 2.1, Theorem 2.2 and Sections 3–4](https://proceedings.mlr.press/v28/arora13.pdf).

Nguyen–Hu–Boyd-Graber's 2013 workshop paper already studies frequency-filtered anchor candidates, sensitivity to the frequency cutoff, and regularization. Its L2/Beta penalties act in topic reconstruction and are tuned experimentally. It supplies no shrinking-anchor expected-risk oracle theorem. Thus neither filtering unreliable words nor regularizing anchor methods should be advertised as new. [Primary paper, Sections 2–4](https://mimno.infosci.cornell.edu/nips2013ws/nips2013tm_submission_27.pdf).

Bing–Bunea–Wegkamp's JMLR2020 Theorem 2 explicitly assumes condition (24): selected-anchor mean frequency at least c log(n vee p)/N and a maximum-document frequency floor of order log^2(n vee p)/N. Remark4 states the role of rare anchors. Their Bernoulli2020 extension (49) retains these types of floors and explicitly leaves minimax-rate optimality without them open. These hypotheses prevent a direct import in the present N=2, alpha tending to zero regime. Their models also allow growing K and address other complexities, so our restricted theorem does not settle their entire question. [JMLR2020, condition (24), Theorem 2 and Remark4](https://jmlr.org/papers/volume21/20-079/20-079.pdf); [Bernoulli2020, Remark10 and (49)](https://pi.math.cornell.edu/~marten/euclid.bj.1587974523.pdf).

The earlier primary comparison already gives exact reasons the inspected MPE/demixing results do not provide the whole class-uniform guarantee: fixed-distribution support constants, supplied mixture samples, or selection errors remain. It also proves the constrained-risk inequality is a direct Duchi–Ruan specialization. Those conclusions remain unchanged. A rate-sensitive empirical-frequency penalty and shell argument are standard statistical tools; the issue is whether their composition yields a previously established topic theorem under the same quantifiers.

## 4. What remains after the reduction

For a literal prior-art subsumption of the joint statistical result, a published theorem or complete reduction still needs all of these together:

1. Arbitrary unknown deterministic document mixtures satisfying the fixed covariance/overlap conditions, with every N>=2.
2. No input of anchor identities or alpha, and a bound uniform as pure-anchor corpus mass alpha tends to zero while topic geometry stays conditioned.
3. Expected normalized-row control that tolerates arbitrarily rare false candidates, preserving fixed-strength root-m coordinate accuracy without an ambient log m loss.
4. Full-vocabulary weak-q reconstruction and the matching fixed-p constrained-risk separation, rather than only a vertex estimate or a high-probability bound with larger logarithms.

The classical SPA reduction removes vertex hunting from this list of unresolved new proof ingredients. It does not supply items1–4 by itself. The prior comparison supplies the classical lower-inequality reduction but still requires the topic-specific pair and its exact class membership. This is a narrower, more credible contribution than a novel general recovery/adaptation theory.

The fair significance sentence is: **a candidate sharp statistical analysis of weak-anchor topic recovery, with a quantified adaptation cost, implementable through established SPA geometry.** Specialist review of that exact claim is warranted. It is not yet historical priority clearance, a general solution to unrestricted topic recovery, a benchmark result, or a basis for calling the package newsworthy.

## 5. Retrieval and integrity

`primary_sources/manifest.json` records exact source URLs and hashes for the downloaded SPA papers and the two2013 topic papers. The2024/2025 SPA comparison uses arXiv2411.16195v1, not a claim to have read a later revision with identical text. The JMLR and Bernoulli frequency assumptions were freshly read from their primary PDFs; the prior comparison and its source manifests remain unchanged. The decisive contribution of this audit is the explicit contraction reduction, not absence of a search match.
