# Independent hostile audit: known-strength minimax continuum

27 October 2026. Reviewer: `status_claim_check`. Source reviewed in full: `known_strength_minimax.md`, SHA256 **`196e7a7341666a0f5a45b9f2d46f473d546aac122999b68c88b24855f262fde4`**. The producer source was not edited. No paid computation, external contact, or outcome inspection was performed.

**Verdict: no mathematical blocker found in the stated fixed-K, known-alpha expected-risk theorem.** I independently reconstructed the upper screening/core argument and all three ordinary-vocabulary lower constructions, rather than accepting the earlier decision memo or finite checks. The constants can be chosen independently of alpha, n, N and p under the stated fixed K,q,D and p<=m^D restrictions. This is an internal proof audit, not historical novelty clearance or external mathematical validation.

## 1. Exact experiment and quantifiers

The result concerns deterministic unknown W, independent multinomial documents, fixed K>=2 and fixed 0<q<1, with n divisible by K and every integer N>=2. The estimator knows the lower bound alpha and the fixed class constants, but does not use q, W, or anchor locations. The constants may depend on q; the theorem does **not** assert uniformity as q approaches 0, 1/2 from either side, or 1. Constants may also depend on K and D. There is no assertion that the exhaustive determinant search is computationally efficient.

The theorem's alpha-uniformity is a real part of the proof: it includes arbitrary positive sequences alpha tending to zero much faster than 1/m. In that regime the upper argument uses bounded stochastic-output loss and the lower mixture uses a capped angle. Neither argument substitutes an unjustified large-m-alpha approximation. The sufficiently-large-m requirement can be chosen independently of alpha. Vocabulary sizes may be fixed as long as p>=2K+8; the upper p<=m^D restriction is used to absorb the good-core failure probability.

## 2. Count moments and the frequent core

I checked C3's unbiasedness and row-sum identity, including the diagonal subtraction and odd N. For a random within-document pairing, the symmetric indicator kernel averages over the two token orders. Its conditional average given the counts is exactly the displayed factorial-count estimator. A fixed pairing has n floor(N/2)>=m/3 independent bounded kernels, even when document probabilities differ. Its summed variance is bounded by a constant times m d_j. Jensen applied to the centered exponential moment transfers Bernstein to the complete pairing average; the same argument gives the variance bound. Combining this with nonnegativity and unbiasedness gives the minimum of the linear-mass and square-root-mass expected errors in C4. This does not treat overlapping token pairs as independent observations.

The determinant argument in C6 is valid. Expansion of absolute determinants over all K-row subsets is bounded by the product of the K column sums; allowing repeated row indices only enlarges that sum. Together with Cauchy--Binet, max_R |det A_R| is at least kappa^(2K). Hadamard bounds each row norm in that core below by its determinant divided by K^(K-1), giving the fixed d_* floor after d_j>=c h_j.

On the stated frequency event, R_0 is included in H and H is contained in the deterministic fixed-cardinality set D_*. Uniform pair errors on D_* x D_* control every candidate determinant. The selected true C_RR is positive semidefinite and has determinant at least v_0/2. Its eigenvalues are at most one because C is nonnegative, positive semidefinite, and its total entry sum is one. Thus its least eigenvalue is at least v_0/2. Since Sigma<=I, this yields the alpha-independent singular-value bound for A_R. The probability bound C p exp(-c_* m) is legitimate: a union bound over all p frequency errors is made only at a **fixed** deviation threshold, while the moment-core index set has fixed cardinality.

This deterministic D_* containment is essential and is used correctly throughout: subsequent bounds cover every possible selected R inside D_*. No sample splitting or false independence from the adaptive core is assumed.

## 3. Rare false inclusions and expected normalized error

The shell exponent C10 is correct for Poisson-binomial counts with mean m d_j. At shell l, the adverse mean is m alpha/2^(l+2), and the threshold is m alpha/2. A valid numerical choice for its linear-shell lower coefficient is

    c_0=(log(2)-1/2)/2 > 0.

Indeed, writing t=l+1>=1, the inequality 1-2^(-t)<=t/2 gives the required bound. Shell cardinality is bounded using weak sparsity by C alpha^(-q)2^(q(l+3)); this produces a convergent geometric sum once m alpha exceeds a fixed q-dependent constant. Independently, the same per-row upper tail can be summed over p rows. Taking the minimum of these **two separately valid bounds** gives C11. Rows with zero population mass have identically zero counts and cannot be false candidates. The relative error condition on J_* also ensures inclusion of every actual anchor with d_j>=alpha.

For C14, every denominator in the deterministic index set is at least alpha/4. Applying C4 at u=log(4|D_*||J_*|)+t bounds each normalized error by C[sqrt(u/(m alpha))+u/(m alpha)]. Integrating the union tail produces the displayed expectation. C9 and the fixed size of D_* replace the logarithm by a constant multiple of Lambda. This argument is unconditional; it does not condition the concentration estimate on a data-selected core or on the screening event.

The split m alpha<=A Lambda is used only in the proof. In that range the claimed capped rate is bounded below by a fixed positive constant, so the same bounded-output estimator suffices. In its complement, the screen failure probability, expected Z, and the Markov bound for a large Z are all O(sqrt(Lambda/(m alpha))), with A chosen sufficiently large. There is no hidden requirement to make a bad-event probability m^(-2), and consequently no extra log m appears here.

## 4. Determinant vertex stability and reconstruction

The C16 lemma does not need an anchor/interior separation gap beyond the singular-value floor and presence of the actual vertices. Observed rows are uniformly bounded (in fact their restricted row sums are at most one), so determinants are uniformly Lipschitz. The anchor tuple and empirical maximizer comparison imply a selected stochastic B with |det B|>=1-O(e). Hadamard then forces each row norm to be at least 1-O(e). Because sum b_k^2<=max b_k for a stochastic row, each row has one entry 1-O(e), hence lies O(e) from a coordinate vector. Two rows cannot choose the same vector: row subtraction would make the determinant O(e), contradicting its lower bound. This establishes one common permutation and the inverse guard for sufficiently small e.

The inverse identity C_jR V^(-1)=A_j diag(mu) is exact. With V_hat close to P V, its inverse is close to V^(-1)P', which gives the permutation orientation in C19. The inverse perturbation term is controlled by the **sum of population numerator entries**, at most sum_jr C_jr=1. It therefore carries neither p nor alpha^(-1). For the numerator error the random core is replaced by the fixed finite sum over D_*. Column clipping cannot increase error from the nonnegative population target, and normalization costs at most 2/min_k mu_k<=2/c, including the zero-column fallback. On every excluded event the final stochastic estimator has loss at most 2K.

The weak-sparsity envelope for h_(j) gives the stated three tau_q regimes by summing min(h_j,sqrt(h_j/m)). At q=1/2 the split is at order sqrt(m); for q>1/2 both the full-tail split and the finite-p square-root sum are valid, so their minimum is valid. For q<1/2 the square-root series converges. These constants may depend on fixed q. The exponential remainder is uniformly absorbed for p<=m^D. Thus C20 implies the asserted upper bound without an oracle choice of q.

## 5. Capped unknown-location mixture lower bound

I checked the row count 2M+K+1, column sums, transformed W, all membership restrictions, and the complete count likelihood.

* The M definition gives M>=1, Ma<=1/16 and log(2+M) comparable to Lambda. The truncation at one candidate handles small q and fixed p; no argument here needs M to diverge.
* W_theta has positive entries. The only changed coordinates have shift delta=theta/[2(1-2theta)], smaller than 1/(2K). Its mean stays 1/K and Sigma's least eigenvalue is at least 1/(4K). The common two-topic block and the disjoint extra anchors give a singular-value floor independent of alpha. The shared row supplies the required positive Gram overlap. Candidate j remains a pure anchor with corpus mass exactly alpha.
* When M>=2 the source's threshold-count ledger is valid. When M=1 the separate ordered-entry argument is necessary and correct: each of the first two columns has exactly four nonpadding positive entries, all at least a, while the geometric padding is smaller. This avoids the invalid small-q shortcut of bounding two nominal candidate entries by a small weak-q budget. The other columns are easier.
* Only candidate pair j changes observably. In groups 1 and 2 its categorical second-moment increment is exactly a delta^2(1/u+1/v), giving C24; other groups do not change. Cross moments for different candidates equal one because their changes occupy disjoint pairs and each change sums to zero. Full document moments are powers N of the categorical expression, and only 2n/K documents are affected. Thus the exponent 2m/K is correct for every N, including unbounded N.
* The capped theta yields 4ma theta^2<=log(2+M)/(1024K^2). Concavity then bounds ((M+2)^epsilon-1)/M by 2epsilon even at M=1. This is an exact finite-experiment likelihood calculation, not a quadratic likelihood approximation valid only at large ma.
* A permutation moving an extra topic costs at least 2d; otherwise identity and the first-two-topic swap have common-block distances 2b theta and 2b(1-theta). The claimed quotient separation follows. Null-versus-mixture testing uses separation only from the null, not an unproved alternative packing. The resulting constant multiple of capped theta is comparable to r_alpha uniformly in alpha.

## 6. Ordinary-vocabulary lower bounds and the critical tail

The strong anchors have mass 1/(8K), exceeding every allowed alpha. The ordinary lower families therefore all belong to the same C_q(alpha), rather than only to a separate strong-anchor problem. Their deterministic W is the same well-conditioned W_0.

For q<1/2, the two common-row perturbations preserve column sums and retain a fixed singular-value floor. Their identity distance is 4b eta; any competing permutation has a fixed anchor cost. The categorical chi-square upper bound 36 eta^2 is conservative, and 36m eta^2=36/4096<1/96. Padding is below all four main positive entries and satisfies the same ordered weak-q argument. This gives the root-m lower bound uniformly over the allowed alpha.

For q>1/2, r<=m^q/8 gives mt>=8^(1/q)/128>=1/16, hence gamma<=1/8. The bounds 2rt<=1/64 and e<=1/48 make b>1/2. The weak-q count ledger checks: the packed contribution is at most 2(1+gamma)^q/128^q<=3/16<1/4, and the remaining anchor/common/shared/padding bounds leave slack below four. Column sums do not depend on the signs. C29 is obtained by summing the two directed categorical terms after a sign flip; its stated upper bound holds because w<=v<=1. Since m t gamma^2=1/1024, the complete-data neighbor KL is at most 1/96. The identity-family diameter is at most 4rt gamma<=1/256, below every nonidentity anchor permutation cost, so the full quotient distance is exactly the asserted weighted Hamming distance. Assouad then yields the stated finite-p/mass-truncated tau_q rate. The floor choices leave r comparable to min(m^q,p) with K-dependent constants, also for fixed p.

At q=1/2, the number of packed rows is 2 sum_(l=0)^L 2^l=4*2^L-2<4 Rbar, so all rows fit. Their total mass per topic is at most 1/32. From 2^L<=sqrt(m)/8 one gets gamma_l<=1/(32 sqrt(1/2))<1/8 at every scale. At threshold u, each packed entry is at most 9/(1024 r_l^2); summing dyadic r_l proves the source's 3/8 weak-half count contribution. Together with the stated core and padding contributions the sum is 29/8<4. Neighbor KL remains bounded at every scale. The full identity diameter is O(log m/sqrt(m)), uniformly in p, whereas a wrong permutation has a fixed anchor cost; this justifies weighted quotient Assouad for sufficiently large m. Each scale contributes exactly 1/(32 sqrt(128m)), and the number of scales is comparable to log(2+min(p,sqrt(m))) even for fixed p>=2K+8.

All KL calculations use the exact fact that multinomial KL is N times the categorical KL in each document. No bounded-N assumption or fictitious independence of all overlapping token pairs enters these lower bounds.

## 7. Final combination and limits of this verdict

The location and ordinary-tail lower bounds apply to subfamilies inside the same class. Their maximum controls half their sum. With r_alpha=min(1,sqrt(Lambda/(m alpha))) and bounded tau_q, this is comparable to the capped expression in C2. The upper statement follows from C20 and bounded stochastic-output loss. Floors, integer group sizes, and large-m permutation separation can all be accommodated by one m_0 depending only on K,q,D and the fixed class constants, not on alpha,n,N,p.

No repair is requested for the reviewed source. The result remains an expected-risk theorem for an exact-separable, conditioned fixed-K class with **known anchor-strength lower bound**. It does not prove unknown-alpha adaptation, computational efficiency, growing-K guarantees, a practical numerical implementation guarantee, or historical novelty. No previously uninspected primary paper was needed to validate the self-contained mathematical steps above; establishing contribution relative to the literature remains a separate task.
