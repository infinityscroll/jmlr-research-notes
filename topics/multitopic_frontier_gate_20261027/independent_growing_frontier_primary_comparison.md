# Growing vocabulary: what the published topic theorems do and do not imply

27 October 2026. Bounded primary-theorem comparison by `hcm_end_to_end`. No producer proof, frozen source, or experimental result was changed. This is a scope and reduction check, not historical-priority certification.

## 1. The precise result under comparison

The new lower source is `growing_vocabulary_lower.md`, SHA256 `a2f855ed3a2bb1ee5280ba04adce315ee1be07ed877da8c72a7815e729582091`. Its independent analytic audit is `independent_growing_vocabulary_lower_audit.md`, SHA256 `ed5287e0b95f60d44d40b8925f0f15e5cb7920dd332c3092fc74c1cc910161d9`.

At fixed K, for the displayed growing vocabularies p=K+2+2m, m>=4, and the stated ranges of n, alpha and beta, it proves

    R >= c_K min{1, (sqrt(p)+alpha^(-1/2)) a_n},
    a_n = 1/sqrt(nN beta) + 1/[beta sqrt(nN(N-1))], N>=2.       (P1)

The experiment is the full independent multinomial count experiment with unknown deterministic document mixtures W. The loss is expected entrywise L1 error for A modulo topic permutation. The class fixes strong singular-value and overlap floors for A, keeps every mixture weight positive, requires lambda_min(WW'/n)>=beta, and requires an exact anchor of corpus mass at least alpha for every topic. The lower bound even allows revelation of designated anchor identities and their topic-column probabilities. Constants are independent of p,n,N,alpha,beta, but may depend on fixed K.

The growing-p upper was still being finalized at this comparison's preparation. The proposed target has an ordinary sqrt(p) estimation term and a logarithmic cost for searching among candidate anchors. **This note does not certify that upper, its exact logarithmic factor, or a matched minimax theorem.** The existing stable `general_k_upper.md` (SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`) permits constants depending on p and cannot itself justify a growing-p assertion.

The two terms of a_n are equivalent, up to a factor sqrt(2), to

    sqrt{ [1+(N-1)beta]/[nN(N-1)beta^2] }.

The candidate substantive dependence is therefore the joint cost of vocabulary size, weak document diversity and rare anchors, including the transition at N beta of constant order. Merely producing sqrt(p/(nN)) or using anchor geometry is not the new part.

## 2. Tran–Liu–Donnat: two concrete reasons their theorem does not imply P1

Primary source: [Sparse Topic Modeling via Spectral Decomposition and Thresholding, JMLR 27(59), 2026](https://jmlr.org/papers/volume27/23-1344/23-1344.pdf). I read the published PDF's Assumptions 1–5, Theorem 19, Theorem 25(c), and Section 5. The journal landing page was also checked on 27 October 2026; the retained PDF identifies the May 2026 publication.

**Mixture conditioning is fixed, not a displayed uniform parameter.** Assumption 1, equation (13), requires sigma_K(WW'/n)>=c for a positive constant c, as well as strong A. Consequently its theorem is not uniform over a sequence beta tending to zero. It is legitimate to apply the theorem separately at a fixed positive conditioning floor. It is not legitimate to substitute a shrinking beta into an unspecified constant and infer the exponents in P1. The dependence is visible in the proof: Theorem 25(c) introduces 16/sigma_K(WW'/n) and bounds it by a constant. This is an actual missing uniformity premise, not a title-level difference. It does not prove their proof cannot be sharpened.

**The full-topic error uses weak sparsity; the growing-p lower class does not.** Let x=log(p vee n)/(nN). Under Assumptions 1–4, Theorem 19 first bounds the retained, renormalized topic rows by C x^(1/4). For the full A it additionally uses Assumption 5, the ordered weak-q radius

    s >= max_k max_j j A_(j),k^q,       0<q<1,

and requires s x^((1-q)/2)=o(1). Its resulting full L1 bound is C[x^(1/4)+s x^((1-q)/2)]. Assumption 3 also requires anchors above a corpus-frequency threshold of order sqrt(x), rather than an arbitrary independently varied alpha. The retained-row result cannot silently be read as full-topic recovery.

Here is a direct test on our new growing-vocabulary hypercube. Each of its first two topic columns has 2m tail entries at least 1/(64m). Therefore

    max_j j A_(j),k^q >= 2m (64m)^(-q)
                        = 2*64^(-q) m^(1-q).                 (P2)

For any fixed q<1, its weak-q radius necessarily grows at least as p^(1-q). Thus this family is not in the original paper's fixed-radius sparse class. Allowing s to grow is allowed by their statement, but restoring its stated rate and smallness condition then matters: the tail term has order at least

    [p sqrt{log(p vee n)/(nN)}]^(1-q).

For example, at fixed conditioning and strong anchors, p=(nN)^d with 1/2<d<1 makes that sufficient smallness condition fail, although the target sqrt(p/(nN)) estimation term tends to zero. This demonstrates why the printed full-A guarantee does not provide the proposed dense-tail upper. It is not a lower bound on their algorithm's actual performance.

**Consequence for the claimed open problem.** Section 5 asks for the minimax L1 rate under the weak-q assumption. P1 is a different four-parameter frontier on a broader, strongly separated class. It does not by itself resolve that sparse-model question. Earlier portfolio results about weak-q classes require their own bounds and assumptions; they must not be replaced by P1. Likewise, the target paper's nonseparable discussion is outside the exact-anchor claim here.

## 3. Bing–Bunea–Wegkamp: important overlap and exact missing hypotheses

Primary source: [Optimal Estimation of Sparse Topic Models, JMLR 21(177), 2020](https://www.jmlr.org/papers/volume21/20-079/20-079.pdf). I re-read Assumptions 1–2, Theorems 1–2, condition (24), Corollary 3, and its lower-bound design (8).

**The sqrt(p) lower mechanism is established.** Their Theorem 1 gives an L1 lower bound of parameter-count order K sqrt(||A||_0/(nN)). For fixed K and a dense non-anchor part this contains the familiar sqrt(p/(nN)) order. Its lower proof fixes W to groups of pure-topic documents. That design is not in our positive interior-mixture class, and it does not quantify a joint weakening beta or rare-anchor alpha. The presence of sqrt(p) in P1 is not evidence of a new distribution-estimation principle; the additional uniform beta/N/alpha dependence and the admissible nuisance-mixture construction are the pieces needing comparison.

**Unlike TLD, their main upper explicitly tracks weak conditioning.** Theorem 2 defines lambda_min=lambda_K(WW'/n)>0 and includes an inverse-lambda_min factor in its term II. Calling beta an entirely hidden constant in BBW would be incorrect. General K and quantitative inverse-conditioning bounds are also already present. However, its displayed rate does not directly yield P1's inverse-square-root beta term in the long-document regime. Corollary 3 obtains a parameter-count minimax rate under the stronger restriction lambda_min comparable to 1/K, along with its other balance and frequency assumptions.

**Its anchor-frequency premise excludes the full range at issue.** For the selected anchor set L, condition (24) requires the smallest corpus anchor frequency to be at least c0 log(n vee p)/N; it also imposes a maximum-document frequency condition involving log^2(n vee p)/N. The first condition alone is impossible asymptotically when N=2. It also excludes arbitrary alpha below that frequency threshold. Thus even a perfect simplification of Theorem 2's error expression cannot establish a uniform theorem for every N>=2 and all the rare-anchor floors in P1. The source's general statement that its finite-sample analysis allows arbitrary dimensions does not remove these quantitative hypotheses.

There can be substantial overlap in long-document, well-conditioned, sufficiently frequent-anchor subregimes. We do not claim BBW fails there, or that its algorithm cannot perform better than its published bound. Its classical co-occurrence reconstruction and anchor geometry remain direct methodological antecedents.

## 4. What strong topic geometry still excludes

Growing p is a real removal of the fixed-vocabulary restriction, but it does not make the class a general diffuse-vocabulary model. If every A_jk<=C/p with fixed C,K, then

    ||A||_F^2 = sum_jk A_jk^2 <= CK/p,

so even sigma_max(A) tends to zero. This contradicts the fixed positive sigma_min(A) floor in P1. The lower construction deliberately retains a finite strong common-word/anchor core and spreads a fixed tail mass over increasingly many words. Many tail entries are of order 1/p, but the whole topic is not.

Consequently neither an all-word-probabilities-of-order-1/p result nor a resolution of the general Ke–Wang short-document problem follows. The crossover N beta measures weak document diversity; N relative to p measures a different aspect of corpus size. They should not be conflated.

## 5. Bounded verdict and the exact novelty gate

The inspected TLD and BBW statements do not imply the full uniform four-parameter frontier by direct specialization. The reasons are explicit: fixed mixture conditioning and a sparse-tail premise in TLD; quantitative anchor-frequency restrictions and a different displayed conditioning dependence in BBW. Conversely, parameter-count lower bounds, raw pair moments, anchor reconstruction, and inverse-conditioning sensitivity are established antecedents.

The defensible prospective contribution is a uniform, strongly separated anchored-topic risk law for unknown deterministic mixtures, with p-dependent constants exposed and an all-N weak-diversity crossover. A stable growing-p upper and its independent review are still needed to promote P1 from a lower result to a nearly matched frontier. An anchor-search logarithmic gap, if retained, must be stated rather than called exactly minimax.

Even after that gate, this is not novelty clearance. A specialist might obtain the same bound by refining existing relative moment/anchor analyses or a uniform grouped-mixture information result. The concrete falsification question is whether an existing theorem supplies, with constants surviving vanishing anchor masses and mixture diversity, both the p-term and the alpha-term with the two N/beta scalings in a_n for arbitrary deterministic W. The two primary topic theorems inspected here do not supply that completed reduction. No conclusion is drawn from search silence.

## Source identity

All hashes are SHA256. Primary PDFs and text were read without modification.

| Source | Local artifact | Hash |
|---|---|---|
| TLD2026 published PDF | `../../sources/topic.pdf` | `f05b1194ac06c6e69afbd3cbb80ec29fc79d294de5efa39cec09c36fb84b3b5f` |
| TLD2026 extracted text | `../attack/paper.txt` | `912e25c226789e6a3cd8fba9a9e1c7a8e598d3889dd7e03206696dca6077c15c` |
| BBW2020 published PDF | `../novelty_decisive_gate_20261027/primary_sources/bbw2020.pdf` | `b26fbc99261e096674b8164dc67d6eef2caeceb64257b7eb8448102e3e8f1217` |
| BBW2020 extracted text | `../novelty_decisive_gate_20261027/primary_sources/bbw2020.txt` | `8f98186cefac6bb32be85ea5dacc674d08c36f5bf8d207927e3206b2e71eef41` |

The links above identify the primary publications. Existing portfolio comparison notes were used as locators; the theorem/assumption claims in this note were checked against the retained primary texts. The journal landing pages independently confirmed the publication identities. No comprehensive literature census or external expert review is claimed.
