# Independent audit of the joint adaptive upper

28 October 2026. Reviewer: root; producer: status_claim_check. Source bound:
`joint_adaptive_upper.md`, SHA256
`7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd`.

**Verdict: no mathematical blocker found for J1--J2 with the stated fixed
geometry and exact anchors.** This is an internal analytic review, not a
machine-checked proof, external expert review or priority clearance. I read
the entire new source, the full all-N Bernstein source, the observed-eigenvalue
cutoff source, and the relative spectral-map derivation in the listed earlier
source. Their claims are used with their existing scope, not as empirical facts.

## Observable selection and spectral coordinates

Every operation in Section 2 uses counts, K and fixed class constants. Neither
the analysis-only b nor alpha appears in the implementation. The Kth pair
eigenvalue estimates b only on G0; the proof uses bounded loss elsewhere.
The bound ||T||<=C/b follows from ||H0^-1||<=C/sqrt(b),
||Sigma^-1/2||=1/sqrt(b), and ||diag(mu)||<=1. Each row of Chat is
nonnegative and has row sum dhat_j exactly, including N=2. Consequently
||Chat_j Uhat T/dhat_j||<=C/b on G0. This supplies J9 without dividing by
the true word frequency or assuming a frequent core.

The penalty is deliberately uncapped. Its linear term, combined with J9,
forces m*dhat_j>K_*ell(dhat_j) whenever positive excess occurs. The factor
b cancels. Capping that term before selection would invalidate this proof.
The multiplicative row weighting makes every candidate determinant transform
by the same det(T). Both the row choice and reconstruction are invariant to
the unknown coordinate map. An additive penalty on the raw determinant would
not inherit that property.

## Row maximum and empirical frequencies

The held full-document moment bound gives J7 with actual b and linear scale
1/(mb). The whitening argument uses the fixed prevalence floor; it does not
assume individual document leverages are bounded independently of b. The
larger a(b) and the linear term retain this dependence.

For balanced frequencies the choice u=3ell(d)+c0*d*t^2/a^2 yields a
d^3-weighted tail. The two additional threshold terms are O(sqrt(c0)*t)
and O(c0*t^2), because 1/(mb)<=a^2. A sufficiently small c0 and fixed
large A0 therefore give J12 uniformly in b. The lower penalty comparison
uses ell(x)/x>=ell(d)/(4d) for x<=2d.

For unbalanced frequencies I checked the active-count implication and both
Chernoff arguments. In the upper tail v=max(2d,s) obeys m*v>=K_*ell(v),
even when v=2d. On z=d/v<=1/2, the stated scalar inequality follows by
differentiating its difference and checking z=1/2. The split into two k/32
terms pays both log(1/v) and the retained m*d/16. Thus false inclusions of
arbitrarily rare words really receive the d^3 factor. Zero true-probability
rows are never observed and need no limiting argument.

The union bound is sum_j d_j^3 exp(-L*d_j)<=sup_x x^2 exp(-L*x), since
sum d_j=1. This yields the t^-4 tail and truncated expectation O(a).
Only min(1,Z), not the potentially much larger untruncated Z, is used on bad
selection events. No ambient-p factor or concealed log(1/b) is introduced.

## Weighted simplex geometry

For theta=p/(1+4p), a weighted row has norm at most1-3theta+z.
Designated anchors have distance at most5theta+z from the relevant vertex;
zero observed anchors are paid for by h=1. Thus small P0+z gives an available
determinant at least1-C(P0+z). Maximum determinant and Hadamard force EVERY
selected theta to be O(P0+z). This is stronger than merely selecting a
nondegenerate tuple: it controls its noise penalties and hence its row errors.

For a substochastic nonnegative row b, ||b||_2^2<=max_j b_j. A row whose
norm is near one is therefore within O(error) in L1 of one coordinate vector,
with no square-root loss. Repeated near-vertices would force a small determinant,
contradicting the near-unit lower bound. This verifies the common permutation
and bounded inverse in J20. The proof handles zero-count rows explicitly.

## Entire-vocabulary reconstruction and risk

The raw reconstruction error is C*delta_j+C*d_j*(P0+Z). The observed cutoff
is bounded above and below by fixed multiples of a(b)^2 on the SAME event;
there is no independence from the reconstruction errors. Unconditional
Cauchy--Schwarz and P(dhat_j>=c*a^2)<=d_j/(c*a^2) give the retained-row
bound min(d_j,a*sqrt(d_j)). For a large omitted row, variance of dhat_j
gives O(1/m), which is bounded by a*sqrt(d_j). Small omitted rows are bounded
by the same profile up to fixed constants. The sum is H_a(d).

Clipping cannot enlarge the L1 error to a nonnegative target. Normalization
costs a fixed factor because each target column has mass at least mu0; zero
estimated columns may use the bounded fallback with the usual same L1 bound.
The probability of G1 failure is controlled by P(G0^c), the truncated excess,
and designated-anchor penalties. Their contribution is absorbed by the anchor
term. Large a or large anchor rate uses bounded loss, not a claim that the
algorithm recognizes the population regime.

The weak-q envelope and monotonicity in b>=beta then give J2. At fixed p,
the logarithm log(2+1/alpha) is generally larger than the known-alpha location
logarithm. The source correctly refrains from claiming free adaptation to the
known-alpha minimax rate. A matching constrained lower requires its separate
proof and review.

## Scope of this approval

The new result removes alpha, beta and q as tuning inputs under fixed K,
strong unnormalized topic geometry and exact anchors, uniformly for every
N>=2 and arbitrary deterministic admissible W. It does not remove those
structural assumptions, give efficient maximum-volume search, certify a
floating-point implementation or establish priority. No source repair was
required for this bound version. Older fixed-beta adaptation is credited as
an antecedent, rather than counted as a fresh result.
