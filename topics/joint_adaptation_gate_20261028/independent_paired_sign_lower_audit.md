# Independent audit of the paired-sign constrained-risk lower bound

28 October2026. Reviewer: hcm_end_to_end. The producer source was read in full and left unchanged.

**Verdict: no mathematical blocker found within the stated scope.** The paired nuisance prior is admissible for every sign realization, the two-document likelihood calculation has the claimed information scale, and the constrained-risk argument covers every alpha->0 sequence with T->infinity. This is an internal correctness review, not novelty clearance or a review of the separate adaptive upper theorem.

Source: `paired_sign_constrained_lower.md`, SHA256

`abe59e38ca5b8a8b28808848ce4da0c8e9fea80ea5b2d6c8966916f6e0483638`.

The common-class reference is `../anchor_selection_frontier_20261028/MATCHED_ALL_N_FRONTIER.md`, SHA256

`0002f4d1c2ea902bbd071df0e413a93b1c64199b05e15b9d9233f39507713a15`.

## 1. The constructed parameters belong to the same class

The row count is exactly p: one shared row, two strong-anchor rows, two rare-anchor rows, two common rows, and p-7 padding rows. Column sums are zeta+v0+v+b+e=1. The common block's least singular value is b(1-2theta)/2>7/32, and the shared row alone contributes1/16 to every topic Gram entry. These bounds are stronger than the common class requires.

The displayed square-root-sum bound is valid: the transformed strong block contributes at most sqrt(v0)(1+sqrt(theta))<=sqrt(1/8)(1+1/4); the rare block contributes sqrt(v)<=sqrt(1/128); the common block contributes at most sqrt(2b)<=sqrt(2*5/8); and the geometric padding sum is bounded by (1/sqrt32)2^-6. If a column's entries are sorted, j sqrt(A_(j)) cannot exceed their total square-root sum. Thus radius four holds without assuming any special ordering of rare and padding rows. All active word probabilities are positive under the interior mixtures, although exact pure anchors necessarily have zero entries in some topic columns.

I independently computed both K=2 permutations. The identity distance is (4v0+2b)theta; the swapped distance is (4v0+2b)(1-theta)+4v. The latter is larger throughout theta<=1/16. The quotient separation used in the test is therefore exact and at least(3/2)theta.

## 2. Pairing makes covariance and anchor masses deterministic

For each pair of document columns, the cross terms between u and f cancel. Hence their average covariance is exactly uu'+beta ff', for every latent sign realization. The two orthogonal eigenvectors have eigenvalues1/2 and2beta. Multiplication by S_theta^-1 leaves the u direction fixed and scales the f direction by1/(1-2theta), giving the stated alternative contrast eigenvalue. Under beta<=1/4096 it remains the smaller eigenvalue and exceeds beta.

The mean of every paired W is exactly u. All coordinates are at least1/2-(8/7)sqrt(beta)>1/8. In the null, the strong anchors therefore have corpus mass1/16, above alpha_s=1/128. In the alternative, the old strong rows cease to be pure, while the untransformed rare rows have corpus mass v/2=alpha. Thus the two priors are entirely supported on the two claimed deterministic-parameter classes.

Mixing over nuisance W induces dependence inside a document pair, but this does not violate the model. Conditional on each admissible deterministic W, the document counts have the required independent multinomial law. Uniform risk bounds can be averaged over this prior. No conditioning event, approximate covariance argument or inadmissible prior remainder enters the constrained-risk proof.

## 3. Short-information likelihood calculation

Write s_t=+1 for tokens in the first document and -1 for tokens in the second. Relative to the product baseline, the conditional density for block sign xi is product_t(1+xi*s_t*z(X_t)). Multiplying two sign-mixture densities and averaging each token gives 1+xi*xi'*<z,w>_d, because s_t^2=1 and both contrasts have mean zero. Averaging xi,xi' and multiplying all2N token factors proves equation(8) exactly with L=2N.

This identity uses all tokens in a two-document block. It does not count overlapping pairs as independent observations. The likelihood is invariant under permutations within either document, so reducing ordered token data to the two multinomial count vectors loses no likelihood information.

Under the gauge transformation, all nonrare word probabilities cancel exactly between the hypotheses. Only the rare pair changes its relative contrast by1+kappa. Thus <z,z>=V, <z,z1>=V+kappa*u_r, and <z1,z1>=V+(2kappa+kappa^2)u_r. These are precisely the three arguments in equation(9).

For N beta<=1, every argument satisfies Ls<=C and s<1. Consequently g_L''<=C L(L-1); integrating from g_L'(0)=0 gives g_L'(s)<=C L(L-1)s. Splitting equation(9) into a second difference of step kappa*u_r and an extra increment kappa^2*u_r yields the claimed C L(L-1)kappa^2(u_r beta+u_r^2) bound. Since L(L-1)<=6N(N-1) for N>=2 and u_r=8alpha beta, this has order alpha theta^2 N(N-1)beta^2.

The null density has the product-square-root lower bound regardless of the document sign reversal. The maximum squared contrast is4beta<=1/1024, and L beta<=2, so the floor is a fixed positive constant. Dividing the nonnegative squared density difference by that floor is legitimate. This proves the short-regime chi-square bound. It requires no signed-cross-term shortcut, since this is a single-alternative constrained-risk calculation.

## 4. Long-information calculation and corpus product

After revealing the same fair block sign under both hypotheses, the one-token null-relative chi-square is

    v*kappa^2*r^2/(1-r^2).

For example the rare pair contributes (v/2)kappa^2 r^2[1/(1+r)+1/(1-r)], which is the displayed quantity. Reversing the document's sign interchanges these denominators and changes nothing. Conditional on the revealed sign, all2N tokens are independent, so their second moment is the corresponding2N-th power and is bounded by exp(C N alpha theta^2 beta). This remains the same after averaging the sign because the bound is sign-independent. Removing the sign cannot increase chi-square by conditional Jensen.

The augmented information reveals xi, not W. That distinction is essential: W is a different function of xi under the alternative. The shared side-information experiment is nevertheless a valid more informative experiment for the original observations.

When N beta>1, (N-1)beta>N beta/2>1/2. Therefore G=N beta*((N-1)beta)/(1+(N-1)beta)>=N beta/3. This proves the claimed bound in G in the long regime. In the short regime, the factor1+(N-1)beta<=2 provides the reverse comparison needed to put its bound in G as well. The independent block signs then make the n/2 mixed block laws independent, giving equation(13) with T=nG. No statistical regime is omitted.

## 5. Constrained-risk quantifiers and every-sequence limit

The same estimator is used at the two hypotheses; supplying beta is allowed but supplying alpha is excluded in the statement. Its strong-class risk bound is uniform over A and W, and therefore applies to the null family even when the null contains additional arbitrarily rare anchors. It bounds the prior-averaged null risk by C/sqrt(T).

On E={d_topic(Ahat,A1)<Delta/3}, the quotient triangle inequality gives d_topic(Ahat,A0)>2Delta/3. Markov's inequality thus gives equation(15) with the correct factor3/2. Cauchy--Schwarz gives P1(E)^2<=E0 Q^2*P0(E), which is equation(16). The relevant likelihood is the complete observed count-experiment likelihood ratio, not a conditional or partially revealed ratio.

I checked all three asymptotic cases separately:

- If T alpha>=ell, then theta=tau sqrt(ell/(T alpha)), so the upper bound is C alpha^(1/2-epsilon)/sqrt(ell), tending to zero.
- If T alpha<=1 and T alpha<ell, theta=tau and the exponential is bounded, giving C/sqrt(T).
- If1<T alpha<ell, then alpha>1/T and ell<log(T); the bound is at most C T^(epsilon-1/2), tending to zero.

Because epsilon<1/4, these arguments apply to every alpha->0 sequence and every admissible n,N,beta sequence with T->infinity, including the transition and saturated-risk regime. Eventually alpha<=1/256, which is all the construction needs. The limit constant tau/2 is independent of the strong-risk constant C; C affects only how late the displayed convergence holds. Averaging risk over admissible deterministic W cannot exceed the supremum, completing the claimed lower bound.

## 6. Precise conclusion and limits

The result is a constrained adaptation-price lower bound on fixed p>=12, K=2, q=1/2, even n, and the stated beta domain. It shows why an estimator that is uniformly order T^-1/2 on the strong-anchor class must pay a sqrt(log(1/alpha)) factor along the weak-anchor sequences in this subclass. It does not assert this logarithm for an alpha-informed ordinary minimax estimator. It does not establish the separate jointly adaptive upper theorem, growing-K or general-q adaptation, efficient computation, confidence-set coverage, or historical novelty.

No simulations or new numerical parameter searches were needed for this audit. The nontrivial point is the exact admissibility of the paired prior together with its full-document information bound; a formal substitution of T into the earlier fixed-beta argument would not have justified either point.
