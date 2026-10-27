# Primary scope and novelty gate for the sparse joint frontier

28 October 2026. Bounded theorem-level comparison. Primary statements below were reopened and read; existing local PDF/text identities were checked. No author contact, publication, or novelty clearance. The mathematical sources remain unchanged.

**Conclusion:** the new result extends the earlier fixed-conditioning sparse frontier uniformly to shrinking mixture diversity, with its full document-length transition. It does **not** newly resolve a portion of Tran--Liu--Donnat's fixed-conditioning question that our older anchor-strength continuum had left unresolved. At the source paper's anchor threshold, the new upper bound actually has a weaker logarithmic factor than that older result. The prospective contribution is the joint alpha/beta/N law and its sparse instance profile, not another claim to the fixed-beta sparse rates.

## 1. What the new package proves

For fixed K, prevalence and unnormalized topic-singular-value floors, exact anchors of corpus mass at least alpha, and fixed columnwise weak-q radius four, put

    m=nN,
    a=1/sqrt(m beta)+1/[beta sqrt(nN(N-1))],
    G_N=N(N-1)beta^2/[1+(N-1)beta].

Thus a is within sqrt(2) of (nG_N)^(-1/2). Let F_(q,p)(a) denote a for q<1/2, a log(2+min(p,1/a)) at q=1/2, and min(a^(2(1-q)),a p^(1-1/(2q))) for q>1/2, with bounded-loss caps. The new sources give

    c min{1,a/sqrt(alpha)+F_(q,p)(a)} <= minimax risk
      <= C min{1,log(2+1/alpha)a/sqrt(alpha)+F_(q,p)(a)}.  (P1)

The upper is an expected-risk result. Its estimator uses alpha, but not beta, q, the anchor locations, or W. The lower has interior deterministic unknown W and even permits disclosure of the designated anchor indices and their topic-column masses. At fixed positive alpha the constants absorb the anchor logarithm, so the sparse a-dependent rate is matched. For weakening alpha, P1 retains a logarithmic gap; it is not an exact log-sharp minimax theorem.

Bound sources: `weak_sparsity_joint_upper.md` SHA `fb24214c2aab2d510f1182cc3000489a0d117f1fe5f3e7aa4d9ee3db81a83ab9`; `observable_conditioning_threshold.md` SHA `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8`; `weak_sparsity_joint_lower.md` SHA `bd43ef4d96e7f7c561bd90b5c90d0a1e32a4e3b4ad527c11bd03380de25f3c09`. Separate internal audits are linked in this directory. They are mathematical evidence, not primary-literature evidence.

## 2. Exact comparison with the published question

I reread [Tran, Liu and Donnat, JMLR 27(59), 2026](https://www.jmlr.org/papers/volume27/23-1344/23-1344.pdf), Lemma 11, Assumptions 1--5, Theorem 19, and Section 5 (printed pp.11--15 and33). Their statistical assumptions fix positive conditioning constants for A and WW'/n. Assumption 3 places an anchor in J-minus, meaning its **corpus** mass exceeds C_source sqrt(L/m), where L=log(p vee n) and C_source is a fixed product of tuning constants. The weak-q radius may grow; our comparison fixes it at four. Theorem 19 gives a high-probability upper error of order (L/m)^(1/4)+s(L/m)^((1-q)/2), with failure o((p vee n)^(-1)). Section 5 leaves the weak-q minimax L1 rate open. Its discussion also includes nonseparable methods, outside our exact-anchor theorem.

The following substitutions are OUR algebra, not an additional claim from that paper. Write alpha_source=C_source sqrt(L/m). With beta bounded below,

    a approximately m^(-1/2),
    a/sqrt(alpha_source) approximately (mL)^(-1/4).

Therefore the NEW anchor upper term is

    log(2+1/alpha_source) (mL)^(-1/4).                    (P2)

The OLD known-alpha continuum, `../anchor_strength_continuum_20261027/known_strength_minimax.md` (SHA `196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`), already gives the matched expected-risk term

    sqrt(log(2+min(p,alpha_source^(-q)))) (mL)^(-1/4),     (P3)

plus the same ordinary weak-q profile F_(q,p)(m^(-1/2)). This source covers every N>=2, fixed or polynomially growing p, and arbitrary weakening alpha within its class. The earlier adaptive source also removes knowledge of alpha and q at fixed conditioning; the new beta-adaptive threshold does not supersede that alpha-adaptation result.

For an unambiguous rate comparison, take bounded N>=2 and p of order m. Then L is comparable to log m, and p exceeds the effective tail support m^q for every fixed q<1. Equations P2 and P3 become, respectively,

    NEW: m^(-1/4) L^(3/4),
    OLD: m^(-1/4) L^(1/4)=(L/m)^(1/4).                   (P4)

For q>3/4, the ordinary-tail term m^(q-1) dominates either anchor term, and both recover that rate. This is a valid source-class specialization, but it was already closed by the old continuum. For q<=3/4, the old continuum's anchor term dominates; the new estimate does not improve it. For fixed p the old location logarithm is constant, making the new anchor logarithm still less competitive. Strong fixed-alpha specializations were already covered by `../novelty_decisive_gate_20261027/strong_anchor_uniform_document_length_minimax.md` (SHA `77c48174ed7770d56d965c9d5c94ae496a11d281052fa831ff30a8455d5c6ff8`).

The new theorem has no polynomial-p restriction. That is useful, but should not be advertised as a new source-question resolution merely because the old theorem stated a polynomial range: its explicit instance bounds already retain a p exp(-c m) remainder, negligible whenever log p=o(m), and its sparse lower profiles saturate at polynomial effective support sizes. A source-bound extension would need to state these facts, rather than treat a presentation restriction as a new statistical barrier.

**Confidence is not interchangeable with expectation.** Our expected bound implies constant-confidence bounds by Markov, not the source's failure o((p vee n)^(-1)) at the same radius. Conversely, bounded loss converts their theorem into its displayed rate plus a 2K o((p vee n)^(-1)) expectation remainder. In the bounded-N example above that remainder is negligible; this must not be assumed for arbitrary extremely large N without checking it.

When beta tends to zero, TLD Assumption 1 no longer holds. Thus the new shrinking-beta result is an extension beyond that assumption, not an in-assumption counterexample or a newly answered specialization of the original fixed-beta open question.

## 3. Closest primary subsumption tests

**Bing--Bunea--Wegkamp2020.** I reread [Theorem 2, condition (24), and Corollary 3](https://jmlr.org/papers/volume21/20-079/20-079.pdf), printed pp.10--12. The theorem already treats arbitrary K and explicitly tracks lambda_min(WW'/n); those are not new subjects. Condition (24) requires selected-anchor average corpus frequency at least c log(n vee p)/N, together with a maximum-document frequency floor. In particular its printed hypotheses fail for fixed N and growing n. Its inverse-eigenvalue term does not directly produce P1's inverse-square-root-beta long-document term. Corollary 3 fixes the eigenvalue at constant order. This prevents direct theorem substitution, not a sharper reanalysis of their estimator.

**Ke--Jingming Wang2024.** I reread [Assumptions 1--3](https://arxiv.org/html/2405.17806v1). Their mixture concurrence eigenvalue has a fixed positive floor; their vanishing beta_n belongs to A'H^(-1)A, a different parameter. Word-mass and minimum-document-length assumptions further exclude our full rare-tail, N=2 class. Renaming beta_n as our beta is invalid. Their ordinary short-document result is not the claimed new result here.

**Grouped mixtures and weak identification.** [Raim--Neerchal--Morel2017, Theorem 2 and Remark 1](https://www.ism.ac.jp/editsec/aism/pdf/s10463-015-0542-9.pdf), printed pp.345--347, bound missing information by a polynomial times an exponentially decreasing group-length factor at given component parameters. Our hard prior is indeed a grouped two-component multinomial mixture, so this is a real antecedent. Its printed bound does not uniformly retain a rare-cell factor b_j or alpha while components coalesce. Even supposing an absolute remainder C N^2 exp(-cN beta), comparing it with complete directional information b_j N beta requires additional dependence on log(1/b_j); it does not establish a uniform transition at N beta alone. The required short-regime inequality is I_(N,j)<=C b_j N(N-1)beta^2, plus its long-regime C b_j N beta cap. This exact directional, vanishing-cell transfer remains the missing theorem-to-theorem reduction.

[Wu--Zhou2019, Theorem 10 and equation (199)](https://arxiv.org/pdf/1908.10935) already exhibit weak-signal directional minimax rates for symmetric Gaussian mixtures. Their spectral estimator also uses an empirical eigenvalue in equation (201), so plugging an observed eigenvalue into a scale is not a new general idea. Setting the heuristic signal strength to sqrt(N beta) predicts our crossover. The theorem does not supply an experiment equivalence uniform when N b_j or N alpha is small, nor an estimator over arbitrary deterministic unknown W. Gaussian intuition is therefore strong antecedent evidence, but not a completed reduction of P1.

Even a successful reduction of our lower information calculation to a general mixture inequality would not, by itself, provide the arbitrary-W upper bound. Conversely, no inference of novelty follows from the bounded search failing to locate that inequality. The exact question for a specialist is whether the full sparse count experiment and its uniform directional information are already covered, rather than whether the rate shape resembles known weak mixtures.

## 4. Narrow significance judgment and reading record

The defensible candidate contribution is an expected-risk sparse frontier, with constants uniform as document-mixture diversity weakens, valid for every N>=2, and an estimator that does not need the diversity floor. Its transition is meaningful at fixed token budget: increasing document length helps until N is of order1/beta, with the ordinary weak-q profile evaluated at the corresponding effective information. It retains exact anchors, known alpha, fixed K/q, strong unnormalized topic geometry, and an anchor logarithm gap. It is a coherent specialist-review theorem; this comparison supplies no basis to call it a newsworthy breakthrough or a fresh resolution of the whole published open question.

Primary identity record: the TLD PDF read locally has SHA `f05b1194ac06c6e69afbd3cbb80ec29fc79d294de5efa39cec09c36fb84b3b5f`; extracted text SHA `912e25c226789e6a3cd8fba9a9e1c7a8e598d3889dd7e03206696dca6077c15c`. The published www.jmlr.org PDF was reopened successfully after the non-www URL timed out. BBW and Ke--Wang were reopened directly. Retained Raim/Wu primary PDFs and hashes are in `../document_length_frontier_gate_20261027/primary_sources/manifest.json`; their exact theorem passages were reopened for this comparison. Earlier adaptive source SHA is `e221094bcc7e3a82eccb0ce428fa394aea49091c3aad9e7e6748c2ed0fa6d7d2`. No new broad absence-of-search claim is made.
