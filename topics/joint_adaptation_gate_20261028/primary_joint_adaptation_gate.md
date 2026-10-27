# Primary comparison: joint adaptation to rare anchors and weak mixture diversity

28 October 2026. Targeted theorem comparison, not novelty clearance or an
independent proof audit. The primary statements below were read, rather than
inferred from abstracts. Existing fixed-conditioning results were inspected
first. No frozen proof was changed and no author was contacted.

**Verdict.** Noise-level-free separable NMF, robust vertex recovery, demixing,
and constrained-risk inequalities are established. None of the inspected
theorems, with its actual premises and quantifiers, directly supplies the new
joint uniform guarantee. The defensible contribution candidate is a
topic-specific statistical adaptation theorem and its restricted matching
adaptation-price experiment. A new general NMF algorithm, a new principle of
adaptation, and a second resolution of the earlier fixed-beta question are
not supported claims.

## 1. Exact target and source binding

The upper observes independent multinomial counts with unknown deterministic
document weights, fixed K, positive mean-topic frequencies, a fixed
unnormalized singular-value floor for A, and exact pure anchors. Write

    b=lambda_min(WW'/n), m=nN,
    a(b)=1/sqrt(nN b)+1/[b sqrt(nN(N-1))],
    ell(alpha)=log(2+1/alpha),
    H_a(d)=sum_j min(d_j,a sqrt(d_j)).

Its single estimator knows neither anchor strength alpha, mixture floor beta,
actual b, weak-sparsity exponent q, nor anchor identities. The asserted bound
is C min{1,H_a(d)+a sqrt(ell(alpha)/alpha)}, uniformly in p,n,N>=2,alpha,b.
Weak-q summation produces the stated three sparse-tail regimes. The
algorithm still knows K and fixed geometry constants; its determinant
enumeration is not claimed computationally efficient.

The companion lower is narrower: K=2, q=1/2, fixed p>=12, even n, radius four,
interior deterministic weights, and the same strong topic geometry. Put

    G=N(N-1)beta^2/[1+(N-1)beta], T=nG.

An estimator not supplied alpha, even if supplied beta, that has uniform
O(T^(-1/2)) risk on the strong-anchor class must have risk at least order
min{1,sqrt(log(1/alpha)/(T alpha))} on the weak-anchor class, for every
alpha->0 sequence with T->infinity. This is constrained risk, not an
ordinary known-alpha minimax assertion for every K,q,p.

| Bound file | SHA256 |
| --- | --- |
| `joint_adaptive_upper.md` | `7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd` |
| `paired_sign_constrained_lower.md` | `abe59e38ca5b8a8b28808848ce4da0c8e9fea80ea5b2d6c8966916f6e0483638` |
| `independent_paired_sign_lower_audit.md` | `814af42be531839c56020f9e3ee6871869958706f492f11ae9913ba11b25eac7` |
| `root_adaptive_upper_audit.md` | `9bf48345df4bb23a9a87a9db5e6f9ecb0a91e62d1a39fc51ae0ffcbfdfc5e1ac` |
| `JOINT_ADAPTIVE_FRONTIER.md` | `74c6c292f7ad09bd00e896712c1162c081ed323ea1271769c794b9e9b6d87e1e` |

The lower audit concerns the lower only; the root audit separately reviews
the upper. This comparison does not substitute for either analytic review.

## 2. Strongest noise-adaptation match: refined Hottopixx

[Mizutani, Assumption 1 and Theorem 2](https://arxiv.org/pdf/2109.02863),
printed pp.3–5, already removes a noise-level input. Given rank r and a noisy
separable matrix, its postprocessed algorithm has error at most
136(r+1)epsilon/kappa when epsilon<kappa omega/[578(r+1)]. Its epsilon is the
maximum column L1 noise, not entrywise total error; normalized columns and
the displayed geometric constants remain assumptions of the theorem.
Theorem 1 additionally uses a nonduplicate-column gap. Thus “no noise level
is supplied” cannot be a new contribution by itself.

The attempted import would require a data transformation with maximum
column noise controlled by the sum of true-anchor penalties plus the global
excess error. The new upper does not establish that premise: its nonanchor
penalties can be large. Its affine coordinate map is analysis-only, and its
weighted determinant argument accommodates those rows directly. Producing
a different contraction or preconditioner that verifies the published
premises could still replace that elementary geometric argument. This gate
does not rule out such a reduction.

## 3. Heterogeneous interior noise: the exact SPA premise still matters

[Jin et al., ICLR 2024, Theorem 1 and equation (6)](https://proceedings.iclr.cc/paper_files/paper/2024/file/7504142a20a3e1fe9dd7de42f475828c-Paper-Conference.pdf)
already replaces maximum pointwise noise by the maximum of: distance of
every observed point outside the true simplex; and the best observed error
at each pure vertex. Its explicit conditioning threshold yields output
error bounded by this quantity times g_new(V). Hence large *interior*
errors are already allowed. Its later statistical pp-SPA guarantees use
additional Gaussian/proximate-point hypotheses. Our count experiment does
not provide those hypotheses merely because it has pure anchors.

Here is an exact obstruction to a particularly tempting shortcut. Take
ideal rows e1,e2,(1/2,1/2), observed rows e1,e2,(-1,2), and row penalties
0,0,3sqrt(2)/2. The anchor penalty and positive excess over these penalties
are both zero. The new multiplicative contraction sends the third row to

    (-1,2)/(1+6sqrt(2)).

It remains outside even conv(0,e1,e2), at distance at least
1/(1+6sqrt(2)), whereas the weighted maximum determinant still selects e1,e2
exactly. Thus the published outside-simplex parameter is not bounded by a
constant times our anchor-plus-excess quantity under this literal
transformation. This is a deterministic nonimplication of hypotheses, not
a counterexample to the SPA theorem or proof that no alternative
preprocessing can work.

The old portfolio's classical-SPA contraction reduction remains valid at
fixed conditioning. It uses a reliable frequent core and a fixed-radius
interior ball. Simply substituting a shrinking beta into it is invalid:
the raw core vertex matrix contains Sigma and its conditioning can shrink.
The new unknown coordinate map cannot be used as an observable SPA input.
This identifies the missing uniform step, rather than claiming determinant
selection or row shrinkage is historically new.

## 4. Recent smooth NMF and maximum-volume results

[Pan et al., July 2026 version, Assumptions 1–2 and Theorem 3](https://arxiv.org/html/2511.07109v2)
permits multiple pure representatives and estimates their locations by a
convex program. Its theorem still assumes every column's L1 noise is at
most epsilon and an explicit separation from nonpure coefficients. The
sufficient threshold is
epsilon<kappa(1-beta_NMF)/[5(p_M+1)(1+kappa beta_NMF)]. Here beta_NMF is a
coefficient gap and p_M is the largest number of pure representatives;
neither is our document covariance floor or vocabulary size. The result
therefore does not provide a rare-count penalty oracle or the joint
expected-risk law by literal substitution. In particular our class allows
nonanchors arbitrarily close to pure rows without a uniform coefficient
gap.

[Vu Thanh–Gillis, February 2026 version, Theorem 1 and Sections II-C–D](https://arxiv.org/html/2602.04795v2)
proves noiseless identifiability for maximum-volume NMF under sufficiently
scattered coefficients. Its noisy formulation balances Frobenius fit with
a determinant regularizer. The inspected identifiability theorem has no
empirical-frequency oracle bound or shrinking-alpha/beta count-risk
conclusion. It establishes substantial volume-method precedent; the shared
word “maximum-volume” is neither a reduction nor evidence of novelty.

## 5. Demixing: population overlap, statistical quantifier mismatch

[Katz-Samuels–Blanchard–Scott, Theorem 5](https://jmlr.org/papers/volume20/17-576/17-576.pdf)
gives DemixHat consistency under their joint irreducibility and full-rank
conditions. Definition 14, Appendix E.1, explicitly permits its deviation
constants and eventual sample threshold to depend on the distributional
ancestors. Uniformity over measurable events is not uniformity over
shrinking anchor mass or mixture diversity. The sampling model supplies
independent samples within a fixed collection of mixture distributions.

There is an exact population connection: the document distributions A w_i
are mixtures of the topic columns, and pure anchors imply irreducibility of
those base topics. But at N=2 each document supplies only two observations,
while the number and unknown weights of the document mixtures change.
That is not the fixed-mixture, increasing-within-mixture-sample limit.
Taking the unknown document weights as known labels or revealing a latent
sign would change the statistical experiment.

A second proposed reduction also needs care. Normalized population pair
rows satisfy C_j/d_j=B_j V with

    B=diag(d)^(-1) A diag(mu),
    V=diag(mu)^(-1) Sigma A'.

Rows of V are distributions, but they need not be jointly irreducible.
When Sigma has strictly positive entries, each row is a positive mixture
of the same topic columns; their finite-alphabet supports coincide. Nor do
the empirical factorial-pair rows supply independent samples from these
mixtures. Thus this algebraic factorization alone verifies neither the
relevant irreducibility nor the sampling premise of DemixHat.

## 6. Existing sparse-topic bounds explicitly track conditioning, but on another domain

[Bing–Bunea–Wegkamp, JMLR 2020, Theorem 2](https://www.jmlr.org/papers/volume21/20-079/20-079.pdf)
already includes lambda_min(WW'/n) explicitly and adapts to unknown
sparsity. It would be false to call all earlier conditioning dependence
implicit. Its condition (24), however, requires each selected anchor's
average word probability to exceed c log(n vee p)/N and its maximum
document probability to exceed c' log^2(n vee p)/N. These hypotheses exclude
the N=2 asymptotic rare-anchor regime. The minimax corollary also imposes
lambda_min comparable to 1/K and stronger anchor conditions. These are
specific obstacles to importing that theorem as the present all-N joint
adaptation guarantee, not criticisms of its stated theorem.

The existing TLD/fixed-beta comparison is preserved in the held primary
gate. That fixed-conditioning weak-q subproblem was already covered by
earlier portfolio results. This new step does not resolve it a second time.

## 7. The lower-bound engine is a literal classical corollary

[Duchi–Ruan, Theorem 2](https://proceedings.mlr.press/v130/duchi21a/duchi21a.pdf)
states, for a general loss distance Delta_L and likelihood second moment
rho, that

    R_1 >= (sqrt(Delta_L)-sqrt(rho R_0))_+^2.

Apply it to the two complete paired-prior count laws in our lower. Each
prior has a fixed target topic matrix despite mixing over nuisance W, so
the quotient-metric triangle inequality gives Delta_L=Delta. The source's
strong-class risk bound gives R_0<=C/sqrt(T), and its likelihood calculation
gives rho<=exp(C0 T alpha theta^2). With

    theta=tau min{1,sqrt(log(1/alpha)/(T alpha))},

the source's three cases show rho R_0/Delta->0. The displayed inequality
therefore directly yields the same lower order. The constrained-risk
principle and logarithmic adaptation mechanism are classical. The
topic-specific content requiring proof is the admissible paired-sign
experiment and its second-moment bound uniform in N and beta.

This is a reduction of the final inference step, not a claim that the cited
paper contains our multinomial construction.

## 8. Upper/lower class consistency and the precise remaining contribution

The common lower subclass has K=2,p fixed>=12,q=1/2, radius four and interior
mixture coordinates. Its topic geometry exceeds the upper's fixed floors;
the mean is exactly (1/2,1/2). Every paired-sign realization has covariance
eigenvalue at least 2beta, so no conditioning on a rare prior event is
needed. The null has strong anchors even while also possessing rare rows.
The upper is uniform over that strong class and gives O(T^(-1/2)) there,
because its finite-p sparse-tail profile is O(a) and alpha_s is fixed.
Consequently the lower's strong-class premise is genuinely supplied by the
upper. The weak-alpha term then dominates along alpha->0. This check does
not enlarge the lower to all K,q or growing p.

The bound integrated statement was also read in full. Its fixed-p comparison
correctly distinguishes the bounded known-alpha location logarithm from
log(1/alpha); when p>=alpha^(-q), those logarithms are comparable for fixed q.
The identity a=(m beta)^(-1/2)[1+{(N-1)beta}^(-1/2)] correctly preserves the
document-length transition at (N-1)beta of order one. Neither comparison
requires treating W as an observed random design or changing the target.

The potential new statistical claim is consequently narrow but concrete:
one estimator has a joint unknown-alpha/beta/q oracle upper across every
document length, and the log(1/alpha) adaptation price is necessary on a
fixed-p two-topic subclass even when beta is supplied. Established
geometry and constrained-risk machinery deserve explicit credit. The
additional proof work is the weak-conditioning spectral comparison,
full-document variance-sensitive row control, rare empirical-frequency
maximum with uncapped penalties, and the paired-sign count-law affinity.

A prior theorem would subsume this package if it supplied these same
uniform premises and the resulting oracle bound, or an explicit statistical
reduction with constants independent of alpha,beta,N,p. No such reduction
has been established by this targeted reading. That statement is not a
claim of exhaustive priority clearance. Strong A, exact anchors, fixed K,
and expected rather than uniform confidence loss remain material limits.

## 9. Evidence ledger

`primary_sources/manifest.json` pins the three freshly retrieved primary
sources and the read-only primary PDFs already retained in the portfolio.
It also pins the old fixed-beta adaptive theorem, the classical-SPA
contraction reduction, and both prior comparison notes. The fresh source
selection was aimed at contribution-killing overlaps, not keyword novelty.
The displayed elementary counterexample and theorem-to-theorem mappings
above are this note's derivations. No computational experiment is needed
for them.
