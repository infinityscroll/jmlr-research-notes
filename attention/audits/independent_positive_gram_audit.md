# Independent hostile audit: positive-Gram selected-path extension

28 October 2026. Independent source-level review by hcm_adversarial_boundary. Reviewed the complete general source and its fixed-input dependency. No producer file was edited by this reviewer.

## Binding and verdict

Final reviewed source: `positive_gram_extension.md`, SHA256 **29c18514bf16ab7282b227e46bafcee71e677332644c92af8d2ff78ccd97fc36**.

Dependency: `selected_path_noncollapse_theorem.md`, SHA256 **46db3f866ad368b39f1bf600e730133a2f52570b6f4a24464aebb39e57187ae7**. The general proof was checked directly, not inferred from that dependency's review.

**No remaining mathematical blocker found within the stated architecture and quantifiers.** One objective-scaling ambiguity was reported and clarified by the author before this final binding: the displayed KKT multipliers apply after multiplying the reduced objective by D0. This leaves the optimizer, directions and margin ratios unchanged. The superseded general-source hash was 395d1b8486195a70a6cdf634aa05165d8e07d7257da496122febb908ce3a9d13.

This is an analytic audit, not a novelty decision, a test-accuracy result or an independent execution of the released optimizer.

## 1. Actual full gradient and Gram factors

Independently differentiated c=b+pi(a-b) and m=(a-b)(x2+a d0)'k. The two lower derivatives are exactly

    c_a=pi+pi(1-pi)[m+(a-b)^2 d0'k],
    c_b=(1-pi)(1-pi m).

The query contribution (a-b)^2 d0'k is present; the upper-key contribution makes c_b negative at large positive m. The upper derivative is (a-b)^2 pi(1-pi)h1 d0'. Multiplication by eta Q c_head and projection onto d0 produces rho=eta Q c_head D0, and the Gram-weighted G4 equations follow. Averaging the paired sign examples produces no extra factor two: both signed predictions and their gradients agree.

The full-matrix decomposition is exact because every increment has right factor d0'. Conserved right-null components and the lower q component orthogonal to span{x1,x2} are genuinely irrelevant to this forward model. They need not be zero initially, and their finite values disappear only after division by log n. Thus the theorem does not optimize in a smaller parameter space than its comparator.

## 2. Uniform clock expansions, including the transverse channel

On the stated compact (x,v) region with bounded k_perp, write alpha=1-a. Then

    h1=x1-alpha d0,
    d0'k=(1-b0/a0)s+O(1),
    m=(1-alpha-v/s)[s-alpha d0'k]
      =s-v+O(s exp(-s)).

These identities establish the claimed uniform expansions for A and B. In particular the leading B term is -v exp(-s+v), including its sign and coefficient. The upper clock has leading factor rho a0 exp(-s+v), not rho exp(-s+v) unless a0=1.

The exact transverse projection gives G6. Its denominator tends to a0>0 even when b0>a0, and its numerator is alpha times the fixed projection of x2 orthogonal to x1. Therefore its norm is bounded by C exp(-s). No positivity of d0'k or coordinatewise positivity of the token vectors is needed.

The signed output is a convex combination of the two fixed head scores, so Q has fixed strictly positive upper and lower bounds. This proves the clock increment bounds before using any asymptotic conclusion.

## 3. Stable two-dimensional recurrence

Dividing G4 by the actual Delta s yields u-rv and ru-tv with O(1/s) errors. I checked the discrete product for v=s sigmoid(l2): its b Delta s term contributes O(1/s), and its quadratic remainders are controlled because |Delta l2|<=C Delta s. Thus G7 is an exact-update approximation with a uniform error tending to zero, not a gradient-flow substitution.

Solving F=0 gives

    v*=r/(t-r²), u*=t/(t-r²), x*=v*+log u*.

Differentiation yields G8. The trace is negative and the determinant is u*v*(t-r²)>0. Consequently the Lyapunov integral defines a finite positive-definite matrix P. Taylor control around the fixed point gives the stated local negative drift. The argument needs r>0 and t-r²>0; it makes no assertion on the excluded orthogonal or collinear boundaries.

## 4. Simultaneous discrete basin closure

The stopped-region proof does not assume the conclusion it needs. At a stopped state, the quadratic expansion of V gives G10 after using Delta s<=C_eta exp(-s) and absorbing its quadratic state term. On the outer ellipsoidal annulus the drift is negative for sufficiently large finite R0. In the inner ellipsoid, the bounded step in the P norm prevents a jump across the outer boundary.

For the other stopped boundary,

    sum ||Delta k_perp|| <= C sum exp(-s) Delta s
                          <= e C exp(-s(0))

when Delta s<=1. This holds on every finite stopped prefix and closes the transverse bound independently of eventual convergence. The increasing clock cannot leave through its lower boundary. Together these facts establish the full induction for each fixed finite eta, rather than merely a continuous-time inward condition.

The nonempty initialization set can realize its prescribed two lower logits because x1,x2 are linearly independent. The strict inequalities have an open preimage in all 2d² matrix coordinates. No equality is imposed on the conserved coordinates.

## 5. Convergence and normalization

A bounded s would contradict its positive increment lower bound, hence s diverges and the total clock is infinite. The scalar recursion

    V^+ <= (1-c Delta s)V+C Delta s/s²

then forces V to zero. The coefficient of exp(s)Delta s converges to rho_* a0 exp(v*); applying the exact exponential increment and Cesaro averaging gives G11, including the constants in l1 and the -log log n scale in l2.

Solving the Gram linear system gives q/log n=(c0 x1-b0 x2)/Delta. Its squared norm is c0/Delta, its x1 inner product is one and its x2 inner product is zero. These yield the full matrix limits G1 with all D0 and a0 factors intact.

For the sole distinct lower selected-path normal C=x1 d0', the global optimum at unit Frobenius norm is ||C||=sqrt(a0 D0). The trained normalized margin tends to sqrt(D0 Delta/c0), so the fraction is sqrt(Delta/(a0 c0)). Both unit directions have the same inner product, establishing the normalized p=2 Bregman discrepancy 1-minus-that-fraction.

The upper actual normal h1(h1-h2)' tends to x1 d0' with positive norm. Its limiting trained matrix is proportional to that same normal. Thus the upper fraction tends to one without normalizing a collapsing comparator.

## 6. The different constrained SVM, and an exact geometry check

For q=Wd0 the minimum matrix objective is ||q||²/(2D0). After the explicitly stated positive rescaling, the reduced objective is ||q||²/2. Its active constraints x1'q=1 and x2'q=0 have multipliers c0/Delta and b0/Delta. For the unscaled reduced objective the multipliers are divided by D0. Both describe the same q*. This constrained problem is correctly kept separate from the paper-matched one-normal comparator.

As an algebraic check outside the special planar fixture, take

    x1=(1,1,0), x2=(2,1,1), w=(1,0,-2).

Here a0=2,b0=3,c0=6,Delta=3,D0=2, so b0>a0 and the leading d0'k is negative. Nevertheless v*=2,u*=4, q*=(0,1,-1), and J=[[-4,11/2],[12,-18]] has trace -22 and determinant 6. The predicted selected-path fraction is exactly 1/2. This directly checks the sign regime that cannot be justified by an assumed nonnegative d0'k. It is not a trajectory experiment.

## 7. Open-data scope and unresolved claims

At each fixed admissible data point, Gram parameters and the fixed point vary smoothly; its Lyapunov matrix remains a strict Lyapunov matrix in a sufficiently small data neighborhood. Compact versions of the expansion and drift bounds provide a common local basin radius and a finite threshold. This justifies the claimed local joint openness.

That openness is in the two token vectors, fixed head and initial matrices **within the paired-sign experimental design**. The negative example remains constrained to be the negative copy; this is not an open set of two independently varying training examples. Dimension d is any fixed d>=2. Near collinearity, thresholds and constants may deteriorate without bound, as the source states.

The theorem establishes a selected-path discrepancy in genuinely coupled two-layer self-attention with distinct limiting memories. It does not refute the one-layer paper, prove poor generalization, cover learned values/head, p other than two, or certify small/random initialization. The late favorable basin and bounded-score positive limiting loss are material restrictions. No further repair is requested.

