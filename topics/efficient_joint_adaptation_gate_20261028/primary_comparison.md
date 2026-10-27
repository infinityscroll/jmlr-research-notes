# Primary comparison: certified design compression for the joint adaptive topic bound

28 October 2026. Targeted theorem-to-theorem comparison. No priority clearance, practical superiority, or new general optimization principle is claimed.

**Verdict.** The optimization and final greedy recovery are classical. The defensible increment is a constructive, exact-real-arithmetic replacement for the exhaustive selector in the held joint statistical theorem. The inspected primary results do not directly supply its empirical-frequency/weak-diversity/all-document-length risk guarantee. Its new deterministic reduction is specialized and may be an elementary corollary of broader existing geometry; that possibility remains open.

## Bound target

`design_compression_selector_theorem.md`, SHA256 `188c39bfbe31e11b668bddd7d31d251a56ba4d179b72fb7d23fbfb6339b70a16`, replaces only the tuple search. Its statistical dependency is `../joint_adaptation_gate_20261028/joint_adaptive_upper.md`, SHA256 `7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd`. The independent selector audit is `independent_design_compression_audit.md`, SHA256 `a960bb22cb633c337992f0219f2b00343838cde5a919e6a15a757b3a251e0024`.

For fixed K, strong unnormalised topic geometry, exact anchors and a positive mean-topic floor, its expected quotient-L1 risk remains

    C min{1, sum_j min(d_j,a sqrt(d_j))
                + a sqrt(log(2+1/alpha)/alpha)},
    a = 1/sqrt(nN b) + 1/[b sqrt(nN(N-1))],
    b = lambda_min(WW'/n).

The estimator is not given alpha, b, a covariance floor beta, q, W, or anchor identities. Constants are uniform over their stated statistical ranges, including N>=2 and shrinking b. The computational assertion is polynomial real arithmetic given the formed weighted spectral rows. It is not a finite-bit algorithm, a practical runtime result, or a reduction of the inherited moment/spectral cost.

## What is directly classical

[Ahipasaoglu–Sun–Todd, Section 2, equations (2)–(8), Lemma 3.1 and Theorem 2.1](https://people.duke.edu/~psun/bio/ahisuntod_first_sub.pdf) give the D-optimal log-determinant dual, leverage gradient, rank-one update, observable optimality test, and polynomial iteration bounds. Theorem 2.2 adds a stronger local linear rate with data-dependent constants. Set their dimension to K, columns to our candidate rows transposed, and their simplex weights to omega. This literally identifies our optimization problem. Their concavity gap certificate is our E5. Our conservative fixed-step proof is self-contained bookkeeping, not an improved D-optimal solver.

[Gillis–Vavasis, Assumption 1, Theorems 4–5 and Section 4](https://arxiv.org/pdf/1310.2273v2) already combine ellipsoid preconditioning with SPA and discuss small active supports. Their initial premise is a uniform column-noise bound. At epsilon<=sigma_min(W)/(8r sqrt(r)), Theorem 4 bounds the transformed condition number by 40; Theorem 5 gives preconditioned-SPA recovery under the corresponding small-noise regime. Section 4 explicitly credits a support of size at most r(r+1)/2 to John. Our mass-and-covariance compression by linear dependence is standard finite-dimensional convex geometry, with one additional mass coordinate. It is not a new small-support principle.

[Mizutani, Assumption 1 and Theorem 2](https://arxiv.org/pdf/2109.02863) already provides noise-level-free separable-NMF recovery, with normalized columns and a maximum-column L1 noise premise. Thus absence of an externally supplied noise level is not new. The full quantitative comparison was retained in the held joint-adaptation primary gate below.

## The precise additional reduction and its limits

The published uniform-noise premise is not available on the *initial* weighted rows. Our analysis controls true-anchor penalties and a global positive excess over row-specific penalties; some nonanchor penalties remain large. Even with exact anchors and zero positive excess, a weighted nonanchor can remain outside the true simplex. The held gate provides the explicit example e1,e2,(-1,2)/(1+6 sqrt(2)). This is a failure of a literal premise substitution, not a counterexample to a published theorem.

The new source supplies the missing preprocessing implication. In unobserved analysis coordinates, trace and determinant bounds for a near-optimal design imply a weighted average of vertex distances of order e, where e is anchor penalty plus excess plus optimization gap. Exact mass/covariance compression preserves that bound. Discarding weights below 1/(8KJ), J=1+K(K+1)/2, leaves every vertex represented and gives *every retained row* error O_K(e). Observable whitening gives a uniformly conditioned ideal basis even though the raw spectral basis may deteriorate with b.

At that point the remaining task really is classical robust successive projection: the retained cloud consists of approximate copies of the K well-conditioned vertices. Our elementary QR lemma is not a new general recovery method. The proposed contribution is the earlier heavy-design reduction and its composition with the joint statistical envelopes. The trace/deficit argument is elementary enough that specialist review should explicitly test whether an existing robust optimal-design or ellipsoid theorem already states an equivalent implication. No absence of a matching search result settles that question.

The coordinate map is used only in the proof. Leverage scores, logdet gaps and the compressed covariance are affine-invariant; no unknown map or conditioning floor is supplied to the algorithm. A fixed-factor determinant approximation would leave nonvanishing e, so certified accuracy tending to zero is essential. Standard D-optimal algorithms can supply that accuracy; the present slow but explicit iteration is not the source of statistical novelty.

## Does a primary theorem subsume the joint risk law?

The held primary gate, SHA256 `d947b22e968345055fd9b0b6ec27fdad06198a07c483ce7a55351183485b20e8`, read TLD, Bing–Bunea–Wegkamp, refined Hottopixx, heterogeneous-noise SPA, and mutual-contamination demixing. Its premise mismatches remain material. In particular [Bing–Bunea–Wegkamp, Theorem 2 and condition (24)](https://www.jmlr.org/papers/volume21/20-079/20-079.pdf) explicitly track mixture conditioning but impose anchor-frequency requirements that exclude the rare-anchor N=2 asymptotic regime. The inspected demixing consistency theorem has distribution-dependent thresholds and a different increasing-within-mixture-sample experiment. Neither is transformed into our uniform joint bound merely by adding a polynomial selector.

The present work closes a computational-existence gap *within the internally developed statistical theorem*. It does not create a second statistical frontier or establish optimal runtime. A complete subsumption would need either the same uniform empirical-count risk guarantee, or a verifiable reduction whose constants remain independent of alpha,b,N,p. No such reduction has been established by the inspected primary statements. That is a bounded unresolved-novelty conclusion, not a declaration of novelty.

## Evidence

`primary_sources/manifest.json` pins the two newly retrieved primary manuscripts and text extractions, plus the held broader primary gate and its source manifest. The Duke manuscript was unavailable through one web request but successfully retrieved from the same author-hosted URL and read locally. The general theorem was independently audited; the 777 exact finite checks are algebra controls, not evidence of historical priority or numerical practicality.
