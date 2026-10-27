# Historical gate: joint adaptive sparse-topic recovery

28 October 2026. Targeted primary-theorem comparison, not a priority claim or an independent review of the held proofs. No experiment, publication, outreach, or frozen-source change was made.

**Finding.** There is now a precise published open-question connection: the Bernoulli 2020 topic paper leaves optimal recovery without its anchor-frequency restriction open. The held theorem gives a consistent, sharp constrained-adaptive result on an explicit short-document, weak-diversity subclass outside that restriction. Two recent potential subsumption routes do not supply it by direct application: adaptive multiview density estimation has a quantitatively ill-conditioned inverse to topics, and a September 2026 finite-mixture theorem has an identifiability premise that fails identically for two-token multinomial kernels. These are specific mathematical comparisons. They do not establish that no other publication contains the result.

## 1. Exact claim being compared

The experiment is independent counts `X_i ~ Multinomial(N,A w_i)` with unknown deterministic W, all N>=2, fixed K, a fixed positive mean-topic floor, strong unnormalised A, exact pure anchors of corpus mass at least alpha, and weak-q radius four. Put

    b=lambda_min(WW'/n),
    a_b=1/sqrt(nN b)+1/[b sqrt(nN(N-1))],
    H_a(d)=sum_j min(d_j,a sqrt(d_j)), d=A(W1/n).

The single observable estimator knows neither alpha, b or a floor beta, q, W, nor anchor identities. Its expected permutation-L1 risk is

    C min{1, H_(a_b)(d)+a_b sqrt(log(2+1/alpha)/alpha)}.       (H1)

Constants are uniform in n,p,N,alpha,b, with fixed K and geometry. The companion constrained lower is only for fixed p>=12, K=2, q=1/2 and even n. With

    G_N=N(N-1)beta^2/[1+(N-1)beta], T=nG_N,

any estimator not given alpha, even if given beta, with uniform O(T^-1/2) risk on the strong-anchor class must incur order

    min{1,sqrt(log(1/alpha)/(T alpha))}                       (H2)

on the weak-anchor class along every alpha->0, T->infinity sequence. This is not an ordinary minimax claim for every K,q,p.

The new selector attains H1 by D-optimal design, exact covariance compression and pivoted QR, with polynomial **exact-real arithmetic** after the weighted spectral rows have been formed. It does not establish finite-bit stability, practical speed, or cheaper moment construction. Its numerical ingredients are classical; statistical uniformity is the claim at issue.

| Held statement | SHA256 |
| --- | --- |
| `../joint_adaptation_gate_20261028/JOINT_ADAPTIVE_FRONTIER.md` | `74c6c292f7ad09bd00e896712c1162c081ed323ea1271769c794b9e9b6d87e1e` |
| `../joint_adaptation_gate_20261028/joint_adaptive_upper.md` | `7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd` |
| `../joint_adaptation_gate_20261028/paired_sign_constrained_lower.md` | `abe59e38ca5b8a8b28808848ce4da0c8e9fea80ea5b2d6c8966916f6e0483638` |
| `../efficient_joint_adaptation_gate_20261028/design_compression_selector_theorem.md` | `188c39bfbe31e11b668bddd7d31d251a56ba4d179b72fb7d23fbfb6339b70a16` |

## 2. A printed open question with an explicit uncovered regime

[Bing–Bunea–Wegkamp, Bernoulli 26(3), 2020, Theorem 7 and Remark 10](https://pi.math.cornell.edu/~marten/euclid.bj.1587974523.pdf), printed pp.1785–1786, directly concern A in the same deterministic-W multinomial experiment. Their general bound explicitly includes `||C^-1||_(infinity,1)`, C=WW'/n. The relaxed range still requires condition (49): every selected anchor has average probability at least `c log M/N` and maximum document probability at least `c' log^2 M/N`, M=n vee p vee N. Remark 10 explicitly leaves optimality without (49) open. Their Theorem 7 also assumes no quasi-anchors. Thus saying merely that older work allows N>=2, or already includes conditioning, does not verify its recovery theorem in the regime below. Conversely, our fixed-K, strong-A class is narrower than their general model; we do not resolve their full open question.

Here is a specialization of the held theorem, not an extrapolation of its constants. Take fixed p=12, K=2, q=1/2, even n->infinity,

    N=2, beta=c_beta n^(-1/8), alpha=c_alpha n^(-1/4),       (H3)

with fixed sufficiently small positive constants. The held paired-sign construction supplies admissible matrices and interior nuisance W, with every realization satisfying the required covariance floor. Since

    T asymp n^(3/4), a_beta asymp n^(-3/8),

the fixed-p tail is O(n^-3/8), while H1 and H2 give the sharp constrained-adaptive order

    n^(-1/4) sqrt(log n).                                  (H4)

The known-alpha fixed-p rate is n^-1/4. In H3 the right sides of (49) grow with n while the anchor probability shrinks, so that published theorem cannot be applied, even though H4 vanishes. The distinction is not an inconvenient constant or a large-n threshold.

This comparison supports the sentence: **the candidate supplies a restricted quantitative follow-up to the published rare-anchor/short-document question, with an unavoidable cost of adapting to unknown strength.** It does not support claiming the entire 2020 question solved.

## 3. The TLD question and what was already established internally

[Tran–Liu–Donnat, JMLR 27(59), 2026, Assumptions 1–5 and Section 5](https://www.jmlr.org/papers/volume27/23-1344/23-1344.pdf) fixes positive conditioning floors for A and WW'/n, requires a pure anchor above its J-minus corpus threshold of order `sqrt(log(p vee n)/(nN))`, and leaves the weak-q minimax L1 rate open. Its theorem is a high-probability bound, not a matching expected-risk characterization. Our shrinking-beta specialization H3 goes outside its fixed-conditioning model. The fixed-beta/fixed-radius expected-risk specialization of that question was already covered by earlier portfolio results and must not be counted again. The new scope is simultaneous unknown alpha, unknown weak mixture diversity, and all N. Strong A, exact anchors, fixed K, and the restricted constrained-lower subclass remain material limits.

## 4. Recent density estimation: an actual inverse obstruction

[Chhor–Klopp–Tsybakov, JMLR 26(236), 2025, Theorem 5](https://jmlr.org/papers/volume26/24-1729/24-1729.pdf), printed p.13, gives expected L1 error of order `sqrt(K d/n)(log n)^(3/2)` capped at one for a rank-K probability matrix from iid pairs. Its target is the density matrix P, not a particular nonnegative factorization. The final 52-page journal version was read; the older 38-page arXiv version was retained separately and is not used to assign the final theorem number.

[Tang–Chhor–Klopp–Tsybakov–Zhang, May 2026, Corollaries 2 and 4](https://arxiv.org/pdf/2605.24858) treat a multiview density tensor P under `Multinomial(n,P)` sampling. They analyze heterogeneous/dependent count noise, give oracle and feasible scaling, and retain explicit signal and slice/fiber conditions. Their L1 bounds are for P. These are direct statistical precedents; the word “heteroskedastic” is not a distinction. The following calculation shows why the density target cannot simply be replaced by A with a constant independent of rare anchors and weak diversity.

Use the exact held lower family. Let u=(1/2,1/2), f=(1,-1), v=2alpha and `S_theta=[[1-theta,theta],[theta,1-theta]]`, with 0<theta<=1/16. The alternative transforms every nonrare contrast row of A by S_theta and W by S_theta^-1; only the two pure rare rows remain untransformed. Consequently

    d=A0 u=A1 u,
    h0=sqrt(beta) A0 f,
    h1=sqrt(beta) A1 S_theta^-1 f=h0+delta_h.

Writing `kappa=2theta/(1-2theta)`, delta_h has exactly two nonzero entries `+/-v sqrt(beta) kappa`. Stochastic columns imply

    ||h0||1<=2sqrt(beta), ||delta_h||1=4alpha sqrt(beta) kappa.

The two-token density of one document after averaging its fair nuisance sign is exactly

    P_l=d d'+h_l h_l'.

Thus, for alpha<=1/256,

    ||P1-P0||1
      <=16alpha beta kappa+16alpha^2 beta kappa^2
      <=64alpha beta theta,                              (H5)

whereas the held quotient-topic distance is at least `(3/2)theta`. Any uniform inequality `d_topic(A1,A0)<=L||P1-P0||1` on this family must therefore have

    L>=3/(128alpha beta).                                (H6)

This is a population inverse modulus, not a new sample lower bound. It rules out an alpha/beta-independent Lipschitz transfer of the displayed density theorems. At fixed p, blindly transferring a root-n unweighted density bound with this worst-case modulus has scale `1/(alpha beta sqrt n)`, while the short-document topic anchor scale is `sqrt(log(1/alpha))/(beta sqrt(n alpha))`. The former loses a power of rare-anchor mass. A suitably weighted, local density analysis might avoid that loss, but that additional theorem would have to be proved; it is not in the displayed total-L1 conclusion.

There is also an experiment distinction: conditional on deterministic W, our documents need not be identically distributed. The paired prior used for H2 couples documents inside each pair. H5 concerns one marginal only and does not replace that full experiment by iid draws from P. Neither distinction says that density methods are incapable of topic recovery; they identify exactly what a valid reduction must add.

## 5. September 2026 finite-mixture adaptation: exact hypothesis failure

[Le–Nguyen–Pham–Rinaldo–Ho, September 2026, Assumption C(p), Proposition 4 and Theorem 1](https://arxiv.org/html/2609.16622) establish configuration-adaptive mixing-measure risk through partial optimal transport for iid mixtures from a known parametric family. Their theorem assumes C(2k), including linear independence of all parameter derivatives of the component CDF up to order 2k. It allows small mixing weights; small weights alone therefore do not distinguish our problem.

But a two-token multinomial kernel in p-1 free probability coordinates is a polynomial of degree at most two. Every count probability, and every CDF value obtained by summing them, has identically zero fourth derivative in any free coordinate. For k=2, choose the coefficient of that fourth derivative nonzero and all other coefficients zero in C(4). The asserted derivative combination is zero. Its strong-identifiability implication fails already at one parameter point. Hence this theorem cannot literally apply to the N=2 multinomial family. This is an exact premise failure, not an objection to the theorem or a conclusion about other mixture theorems. In addition, its latent mixing measure is not our arbitrary deterministic document-weight matrix.

## 6. Classical parts that remain subsumed

The constrained-risk inference is already a direct application of [Duchi–Ruan, Theorem 2](https://proceedings.mlr.press/v130/duchi21a/duchi21a.pdf), extending the Brown–Low principle. Set its target separation to the held quotient distance Delta and its affinity to the full paired-count likelihood second moment `rho<=exp(C T alpha theta^2)`. Their inequality gives `(sqrt(Delta)-sqrt(rho R0))_+^2`. Taking `R0<=C/sqrt(T)` and `theta` of order `min(1,sqrt(log(1/alpha)/(T alpha)))` gives H2 by the held three-case argument. The lower-bound engine and logarithmic adaptation mechanism are not new. The nonautomatic premise is the admissible all-N, weak-beta multinomial pair experiment and its affinity bound.

The D-optimal leverage stopping certificate, small-support covariance compression, ellipsoid preconditioning and robust SPA/QR are also established. The held selector comparison gives the exact mappings to Ahipasaoglu–Sun–Todd, Gillis–Vavasis and Mizutani. It would be misleading to describe this as a new general optimization method. What has to survive specialist review is the heteroscedastic statistical transfer with no unknown conditioning map supplied to the algorithm, not the existence of a polynomial D-optimal solver.

## 7. Significance and remaining falsification question

The strongest defensible case for author attention is the combination of H3–H4, the explicitly printed Bernoulli restriction, and the matching fixed-p adaptation cost. It describes a real loss of information when both rare anchors and document diversity weaken, and a procedure that adapts without being told either strength. The polynomial selector removes an internal exhaustive-search obstacle, but does not by itself establish practical relevance.

A contribution-killing prior theorem would need to imply H1 with constants uniform in alpha,b,N,p in this actual count experiment, or imply H2's uniform paired-count affinity premise together with the same strong-class guarantee. The new primary checks above rule out several **direct** imports. They do not rule out a more sophisticated reduction of robust NMF, local density estimation or earlier topic theory. The specialist question is now precise: is there already a rare-cell-weighted inversion/selection theorem whose constants give H1 across the N beta transition and whose adaptive consequence includes H2? A positive answer could demote the result to an application; a negative answer from an expert, together with independent proof scrutiny, would strengthen the case for a substantive topic-specific advance.

No claim of historical priority, newsworthiness, full resolution of either published question, or external validation follows from this search. The retained source manifest pins the inspected primary statements, the held theorem dependencies and this note. No search absence is used as proof.
