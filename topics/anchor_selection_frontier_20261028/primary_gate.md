# Primary significance gate: the sharp all-document-length anchor frontier

28 October 2026. Targeted theorem-to-theorem comparison, not a proof audit or
novelty clearance. Primary assumptions and statements were reopened or read
from the retained complete primary text. No producer proof was changed, no
author was contacted, and no paid computation was used.

**Verdict.** No inspected primary theorem directly implies the full proposed
uniform law. The strongest candidate contribution is the joint, log-sharp
expected-risk frontier as anchor mass and document-mixture diversity weaken,
uniformly over every N>=2. The square-root anchor logarithm at fixed diversity,
ordinary sparse-tail envelope, and qualitative demixing geometry were already
covered by older work, including earlier portfolio results. This update must
not be described as a second resolution of the same fixed-conditioning case.

## 1. Exact result being compared

There are n independent count vectors X_i distributed as Multinomial(N,A w_i).
W is unknown and deterministic. K and q in (0,1) are fixed; topic columns have
weak-q radius four and a fixed unnormalized singular-value floor. Mixture
prevalence has a positive floor and lambda_min(WW'/n)>=beta. Exact pure anchors
have corpus probability at least alpha, but their locations are unknown. The
loss is expected entrywise L1 error modulo topic permutation. Define

    a = 1/sqrt(nN beta) + 1/[beta sqrt(nN(N-1))],
    Lambda = log(2+min(p,alpha^(-q))),
    R = min{1, a sqrt(Lambda/alpha) + F_(q,p)(a)},          (P1)

where, in the nontrivial range a<1, up to fixed constants,

    F_(q,p)(a) = a,                                      q<1/2;
                a log(2+min(p,1/a)),                     q=1/2;
                min(a^(2(1-q)),a p^(1-1/(2q))),          q>1/2.

The proposed matching statement is c R <= minimax risk <= C R. Its common
lower/upper domain includes p>=2K+8, n>=128(K-1), alpha<=1/(64K), and
beta<=1/[1024 K^2 max(1,K-2)]. The lower matrices also have interior mixture
coordinates at least 1/(4K), positive topic overlaps, and the stated strong
topic geometry. Constants are uniform in n,p,N,alpha,beta, but may depend on
the fixed class constants and q. Zero vocabulary rows are permitted. The
estimator uses K and alpha, not beta, q, W, or anchor locations. This is not
unknown-alpha adaptation, an assertion for growing K/radius, or a claim about
practical runtime and benchmark dominance.

The exact sources compared are:

| Source | SHA256 |
| --- | --- |
| `all_document_lengths_bernstein_upper.md` | `bd9c774907a8691508d41bf4ea019d4b7b996b99707a0a1e8694aedd74aac2d3` |
| `unknown_anchor_short_regime_all_N_lower.md` | `3b7a7c77c4f46761fd8e1c5708fe9b1709bdebe579f2eccdd3ab27ef28a5c851` |
| `unknown_anchor_long_document_lower.md` | `7390561c70dea239f91c018446504b240f6246631ce4ede711b2d1e78fd6d7ce` |
| N=2 family and class checks, `unknown_anchor_short_document_lower.md` | `a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56` |

The previously held sparse-tail lower is
`../weak_sparsity_frontier_gate_20261028/weak_sparsity_joint_lower.md`, SHA256
`bd43ef4d96e7f7c561bd90b5c90d0a1e32a4e3b4ad527c11bd03380de25f3c09`.
This gate assesses the statement conditional on mathematical verification of
the combined sources; it does not itself certify the newly written lower proof.

## 2. What can actually be said about the TLD open question

[Tran–Liu–Donnat, JMLR 27(59), 2026](https://www.jmlr.org/papers/volume27/23-1344/23-1344.pdf),
Assumptions 1–5, Theorem 19, and Section 5 were reread. Their model fixes
positive conditioning floors for A and WW'/n, requires an anchor above the
J-minus corpus threshold, and permits a varying weak-q radius s. Section 5
leaves the weak-q minimax L1 rate open. Theorem 19 is a high-probability upper
bound; it is not a matching minimax theorem. Their discussion of nonseparable
methods does not remove separability from the assumptions of the proved bound.

The following is our substitution into P1. Put m=nN and L0=log(p vee n).
At their quantitative anchor threshold alpha=C_source sqrt(L0/m), with beta
fixed positive, a is comparable to m^(-1/2), uniformly for N>=2. Then P1 gives

    min{1, sqrt(log(2+min(p,(m/L0)^(q/2))))/(m L0)^(1/4)
                            + F_(q,p)(m^(-1/2))}.          (P2)

For the transparent specialization bounded N and p of order m, this is
(L0/m)^(1/4) for q<=1/2, and

    (L0/m)^(1/4) + m^(q-1),                              q>1/2. (P3)

The anchor term dominates through q=3/4 (including its logarithm at equality);
the sparse tail dominates for fixed q>3/4. This addresses a quantitative
fixed-K, fixed-radius, exact-anchor expected-risk version of the stated
question. It does not settle arbitrary growing s, nonseparable topics,
growing K, or the same confidence level as their upper theorem. Expected risk
only gives fixed-confidence control by Markov without another concentration
argument. Allowing beta to vanish goes beyond their fixed-conditioning
assumption; it is an extension, not an in-assumption counterexample.

Crucially, P2–P3 were already implied by the held
`../anchor_strength_continuum_20261027/known_strength_minimax.md`, SHA256
`196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`.
That source already covers all N>=2 at fixed conditioning, with the same
unknown-location logarithm. The new result removes the extra log factor in
the recent *shrinking-beta* upper bound and matches it uniformly through the
document-length transition. It must not inherit credit for the older
fixed-beta resolution again. The current estimator's knowledge of alpha also
must not be confused with the earlier, separate fixed-beta alpha-adaptation
theorem.

## 3. Closest topic-model theorems: attempted direct substitutions

**Arora–Ge–Moitra.** [Theorem 1.4 and robust-NMF Theorem 2.7](https://arxiv.org/pdf/1204.1956)
already track quantitative anchor mass and mixture conditioning. At fixed K
and prevalence imbalance, the printed document requirement contains
log(p)/(epsilon^2 p_A^6 gamma^2 N), plus a gamma-dependent document floor.
With p_A comparable to alpha and gamma comparable to beta, this gives a
different anchor exponent and does not produce the long-document
beta^(-1/2) improvement. It is an upper guarantee for random document-mixture
sampling, not the matched all-deterministic-W law P1. The anchor geometry and
inverse-conditioning mechanism are established antecedents; sharper analysis
of that algorithm is not ruled out by this failed substitution.

**Bing–Bunea–Wegkamp.** [JMLR 2020, Theorem 2, condition (24), Corollary 3](https://jmlr.org/papers/volume21/20-079/20-079.pdf)
explicitly include lambda_min(WW'/n). Condition (24) requires selected-anchor
mean corpus frequency at least c log(n vee p)/N and a maximum-document floor
of order log²(n vee p)/N. This excludes fixed N with growing n even before
the desired alpha-beta limit. Theorem 2 contains inverse-eigenvalue terms;
Corollary 3 fixes the relevant conditioning scale. Its lower construction
uses pure-document groups and does not vary the interior weak-diversity
nuisance together with rare unknown anchors. Long-document overlaps are
real, but the printed hypotheses and inequalities do not imply P1 uniformly.

**Ke–Jingming Wang.** [2024, Assumptions 1–3 and Theorem 3](https://arxiv.org/html/2405.17806v1)
require a fixed positive mixture-concurrence eigenvalue. Their weakening
beta_n belongs to A'H^(-1)A, not to WW'/n. They also require a word-mass floor
of order K/p and minimum N,p of order log³ n. Our topics remain strongly
separated while mixture diversity weakens; relabeling their beta_n does not
map one problem to the other. Their short-document optimality is not a new
claim of this portfolio and does not supply the rare-anchor weak-beta law.

**Wu–Zhang–Cai.** [Sparse Topic Modeling, Assumptions 2–4 and Theorem 4.1](https://pmc.ncbi.nlm.nih.gov/articles/PMC10530787/)
also fix the mixture-spectrum floor and require topic row masses of order
K/p. Their sparsity counts nonzero entries rather than the present weak-q
decay. These explicit hypotheses block a direct import to weakening beta and
rare heterogeneous words. Their growing-K and inference conclusions are
separate strengths that P1 does not reproduce.

## 4. Classical demixing and weak-mixture theory: the exact remaining seam

The older population reduction still applies. With C=A Sigma A', d=A mu,
and an invertible K-row core R, distributions C[:,r]/d_r are mixtures of
the topic columns with mixing matrix diag(d_R)^(-1) A_R Sigma. Pure anchors
imply joint irreducibility. Thus [Katz-Samuels–Blanchard–Scott, Theorem 2](https://jmlr.org/papers/volume20/17-576/17-576.pdf)
already implies population identification. Their Theorem 5 gives consistency
from iid samples of the mixtures, with distribution-dependent thresholds;
it does not give the uniform shrinking-alpha/beta expected-rate bound.
Disjoint token-pair reduction supplies nonidentical document-specific draws
and discards the variance gain available from all pairs. Simply replacing its
sample size by nN(N-1) would incorrectly declare overlapping pairs independent.
The complete primary text retained locally was read when the current web PDF
request timed out.

[Raim–Neerchal–Morel, Theorem 2 and Remark 1](https://www.ism.ac.jp/editsec/aism/pdf/s10463-015-0542-9.pdf)
already establish that grouped observations reveal a latent mixture component
and observed Fisher information approaches complete-data information. The
printed exponential missing-information bound is at given component
parameters. It is not uniform in shrinking cell probabilities and coalescing
components. Our lower experiment is a grouped multinomial mixture, so the
mechanism is directly relevant, not novel. The theorem does not itself supply
the rare-location cross-likelihood estimate needed for a sharp search cost.

[Wu–Zhou, Theorem 10 and equation (199)](https://arxiv.org/pdf/1908.10935)
give minimax directional rates for symmetric Gaussian mixtures. A proxy with
signal sqrt(N beta) predicts the same weak/strong crossover. It does not
establish a uniformly valid experiment reduction when N alpha can vanish,
nor an estimator for arbitrary deterministic W. For example, the admissible
asymptotic choices N=2, beta=n^(-1/8), alpha=n^(-1/4), and separately
N=n^(1/2), beta=n^(-1/4), alpha=n^(-1), have vanishing expected per-document
anchor counts on opposite sides of the crossover. This does not disprove a
Gaussian reduction; it identifies a uniformity obligation it must meet.

The sharp unknown-location lower bound needs more than a scalar Fisher
calculation. Writing L_j for the per-document likelihood ratio of alternative
anchor location j, the new short-information proof obtains, for N beta<=2,

    E0(L_j-1)^2 <= C alpha theta² N(N-1) beta²,
    |E0(L_j L_k)-1| <= C alpha² theta² N(N-1) beta², j!=k. (P4)

The extra alpha in the second line allows mixing about
min(p,alpha^(-q)) alternatives and yields the square-root logarithm. It is
obtained through posterior covariance and twice centering a smooth function.
Both tools are classical. A theorem giving only the diagonal information
scale, a fixed-parameter limit, or a Gaussian analogue does not imply P4.
The long-information proof instead reveals the sign without revealing W and
has exact orthogonal off-diagonal likelihoods. These are the precise
additional reduction targets for a specialist, not claims of first use.

Nor is substituting an effective sample size into the older known-alpha
theorem a proved reduction. Writing
G_N=N(N-1)beta²/[1+(N-1)beta], a is comparable to (nG_N)^(-1/2), so this
substitution formally predicts P1. Whitening a count matrix does not turn it
into independent multinomial observations with sample size nG_N. The current
upper's variance-sensitive full-pair control and the lower's P4 supply the
missing statistical work; the resemblance of formulas is not an experiment
equivalence.

The recent [de Juan–Mazuelas–Zhu–Scott 2026, Theorem 1](https://arxiv.org/abs/2609.39829)
has an iid selective-classification bound consisting of a selection-bias term
plus the inverse square root of accepted sample count. It assumes a
row-diagonal-dominance margin of the transition matrix and leaves selection
excess risk as a separate term. Our class does not imply that dominance, as
the held exact reduction obstruction already shows. It neither closes P4 nor
supplies the arbitrary-W full-topic reconstruction bound.

## 5. Significance judgment and permitted claim

The full matching law, if the bound proofs stand, is a substantially cleaner
specialist result than the preceding log-gap frontier. It separates three
costs: weak document diversity, searching for rare anchors, and estimating
the weak-q vocabulary tail. At fixed token budget m=nN, the scale is

    a = 1/sqrt(m beta) + 1/[beta sqrt(m(N-1))].

Increasing document length helps the weak-diversity term until N is of order
1/beta; beyond that, the leading token-budget rate saturates. This statement
keeps n inside the theorem's domain and is a theoretical design consequence,
not an empirical recommendation or a new general weak-mixture phenomenon.

A defensible research description is: **a proposed sharp expected-risk law
for separable weakly sparse topic models, jointly uniform in rare-anchor
mass, document-mixture diversity, vocabulary size and every document length,
with unknown deterministic mixtures and no need to know the diversity floor.**
It must retain known alpha, exact anchors, fixed K/q/radius, strong topic
geometry, and the stated parameter domain. It gives a quantitative
fixed-radius specialization of TLD's open question and extends it to weak
mixture conditioning; it does not settle the entire question as posed.

The strongest residual novelty candidate is the full uniform combination,
especially P4 and its matching observable upper, not the individual classical
ingredients. No exact subsuming primary theorem was established in this
targeted review. That is a bounded finding, not proof of novelty. The next
decisive gate is an expert theorem comparison of P4 plus the all-deterministic-W
upper, followed by a coherent manuscript; more certificate counts do not
establish significance. No newsworthy-breakthrough claim is justified by
this literature gate alone.

## 6. Reading record

This note supersedes only the *log-gap description* in
`../weak_sparsity_frontier_gate_20261028/primary_gate.md`; its prior boundaries
and attribution remain applicable. The TLD complete local PDF/text hashes are
`f05b1194ac06c6e69afbd3cbb80ec29fc79d294de5efa39cec09c36fb84b3b5f` and
`912e25c226789e6a3cd8fba9a9e1c7a8e598d3889dd7e03206696dca6077c15c`.
Retained complete primary texts reread here have hashes:

- AGM: `74665c005b1eb63436cc4fd0b3fd917b244e4e20edeacf9f577c727ad1a0e462`.
- BBW2020: `8f98186cefac6bb32be85ea5dacc674d08c36f5bf8d207927e3206b2e71eef41`.
- Katz-Samuels et al.: `eb1a69ef4bdcc8a822983d26a2262907723f98c89de001b9920aaf82587c7eee`.
- de Juan et al.: `74b757553d89fba30a0790a518e6ebd463226a25d4df4a4756a5210351d59f73`.

Raim and Wu–Zhou PDF/text identities are in the unchanged
`../document_length_frontier_gate_20261027/primary_sources/manifest.json`.
Ke–Wang's assumptions and Wu–Zhang–Cai's full primary theorem page were read
online. Search was bounded and used to locate primary statements; no search
snippet or absence of a hit is treated as theorem evidence.

## 7. Dated check for a newer resolution

On **28 October 2026**, a bounded fresh search checked the exact TLD title
with `minimax`, its arXiv identifier `2310.06730`, `Tran Donnat minimax topic
2026`, and the combinations `topic weak sparsity minimax`, `topic models
mixture conditioning minimax`, and `topic anchor strength estimation`.
The latter checks included arXiv, JMLR, Project Euclid and PMLR domain filters
and a two-year recency request. Search engines returned some older papers
despite that request; publication dates were not inferred from crawl dates.

The current [JMLR publication record](https://jmlr.org/papers/v27/23-1344.html)
and complete published PDF were checked, not just the original 2023 abstract.
The PDF's Section 5 still poses the weak-q minimax question. That establishes
what this version of the source says; it does not establish that no subsequent
paper has answered it. The recent de Juan et al. September-2026 primary paper
was also checked at theorem level, with the distinct scope recorded above.

These searches did not yield a newer primary theorem explicitly resolving
the TLD weak-q question or proving P1 with weakening document-mixture
conditioning. This is not an exhaustive citation-index traversal and may
miss differently worded, unindexed, or newly posted work. Accordingly the
permitted statement remains **a candidate sharp joint weak-beta frontier
requiring specialist priority review**. A headline saying simply that the
published open problem has been solved is not supported by this bounded
search, or by our more restricted class and risk quantifiers.
