# A computable selector for joint adaptive topic recovery

28 October 2026. New proof for independent review. The statistical premises
are the held joint-adaptive theorem. The selector replaces vocabulary-wide
K-tuple enumeration by a certified convex-design iteration, support
compression, and pivoted QR. This is an exact-real-arithmetic computational
theorem, not a finite-bit numerical-stability theorem or a runtime benchmark.
D-optimal design, ellipsoid preconditioning, support compression and greedy
projection are classical; no novelty of those general mechanisms is claimed.

## 1. Result and unchanged statistical experiment

Use the model, class constants, loss, factorial moment Chat, empirical
frequencies dhat, spectral matrix Zhat=Chat Uhat, eigenvalue lambda_hat,
penalties and multiplicative weights of the held `joint_adaptive_upper.md`.
In particular the observable candidate row is

    v_j=Zhat_j/[dhat_j(1+4pen_j)]                       (E1)

when dhat_j>0, and v_j=0 otherwise. Its penalty is UNCAPPED and uses the
observed lambda_hat. The original nonpositive-eigenvalue fallback is retained.
For positive lambda_hat set

    delta=min{1,a(lambda_hat)},
    a(t)=1/sqrt(nN t)+1/[t sqrt(nN(N-1))].              (E2)

Replace only the maximum-determinant tuple selection by Algorithm E below.
Reconstruct with Zhat times the inverse of the selected ORIGINAL weighted
rows v_j, not the whitened rows. Keep the same output frequency cutoff,
clipping, normalization and bounded stochastic fallback.

**Theorem E.** For fixed K and the same fixed geometry constants, this
estimator has the same expected-risk upper as the held theorem:

    E loss <= C min{1,H_(a(b))(d)
                       +a(b)sqrt(log(2+1/alpha)/alpha)}, (E3)

where b=lambda_min(WW'/n), d=A mu and
H_a(d)=sum_j min(d_j,a sqrt(d_j)). Consequently it has the same weak-q
profiles and is not supplied alpha,beta,q,W or anchor identities.
All constants in the statistical bound are uniform in n,p,N,alpha,b.

Given the p-by-K weighted spectral rows, Algorithm E uses a number of
arithmetic operations polynomial in p,K,delta^(-1). It has no p-choose-K
search. The inherited construction of Chat and its spectral coordinates is
not made cheaper by this theorem. No fixed-factor determinant approximation
is substituted for the vanishing-accuracy requirement.

## 2. Algorithm E, entirely in observable coordinates

Let J=1+K(K+1)/2 and h=1/(8KJ). All tie decisions are deterministic.

1. Form M0=p^(-1)sum_j v_j'v_j. If it is singular, use the bounded fallback.
   Initialize omega_j=1/p and M=M0.
2. Compute d_j=v_j M^(-1)v_j' and g=max_j d_j-K. If g<=delta, stop.
   Otherwise take a maximizing row j and update

       t=delta/[2(K+delta)^2],
       omega<-(1-t)omega+t e_j,
       M<-(1-t)M+t v_j'v_j.                            (E4)

   Repeat step 2. Section 3 proves a finite, explicit iteration bound.
3. Compress omega to a nonnegative weight vector omega_bar with mass one,
   the SAME covariance M, and at most J nonzero entries. The constructive
   elimination in Section 4 performs this step using linear algebra.
4. Retain the indices H={j:omega_bar_j>=h}. If fewer than K survive, fall
   back. Choose an observable whitening matrix L with L'ML=I, for example
   by Cholesky factorization, and put y_j=v_j L for j in H.
5. Starting with the zero span, select a remaining row y_j with largest
   Euclidean distance to the span of previously selected rows, for K steps.
   This is row pivoted QR / successive orthogonal projection. A zero pivot
   or singular selected raw matrix uses the bounded fallback.
6. Return the K selected RAW weighted rows v_j as Vhat. The topic estimate
   is obtained from Zhat Vhat^(-1) followed by the held output operations.

The labels of the true simplex vertices, the analysis coordinate map, and
the small-error quantities below are never used by the algorithm.

## 3. Certified approximate D-optimal design

For any full-column-rank row matrix v, define

    f(omega)=logdet(sum_j omega_j v_j'v_j), omega in Delta_p.

A maximizer exists and has positive determinant, since the uniform design
is positive definite. At a current positive-definite M, concavity gives

    f* - logdet M
       <=max_j v_j M^(-1)v_j' - tr(M^(-1)M)=g.          (E5)

Thus the stopping rule is an observable additive logdet-gap certificate.
The weighted mean of the leverage scores is K, so g>=0. If g>delta, put
D=K+delta and consider the chosen maximum score d_j>D. The determinant
lemma gives the exact increment

    f(omega_new)-f(omega)
       =(K-1)log(1-t)+log(1+t(d_j-1)).                 (E6)

This is increasing in d_j. Since delta<=1 and K>=2, t<=1/2. Using
log(1-t)>=-t-t^2 and log(1+u)>=u-u^2/2 for u>=0, at d_j=D its value is at
least

    t delta-t^2[(K-1)+(D-1)^2/2]
       >=t delta-t^2 D^2=delta^2/[4D^2].               (E7)

Every design covariance is at most pM0 in Loewner order. Therefore its
logdet value exceeds logdet M0 by at most K log p. It follows that the number
of updates is less than or equal to

    1+floor[4K(K+delta)^2 log(p)/delta^2].              (E8)

All iterates stay positive definite because t<1. This deliberately
conservative bound is sufficient; sharper classical D-optimal solvers may
be substituted only with a valid gap certificate. No lower bound on the
raw covariance eigenvalue is used in E5–E8.

For any invertible K-by-K analysis map T, define x_j=v_j T and
M_x=T'MT. Logdet gains and gaps are unchanged, and

    v_j M^(-1)v_j'=x_j M_x^(-1)x_j'.                  (E9)

Hence the optimization certificate and, with identical tie rules, the
iteration weights are exactly invariant to T. This concerns a linear
change of coordinates fixing the origin, not arbitrary translations.

## 4. Constructive support compression

For each active point form the vector

    phi_j=(1,vech(v_j'v_j)) in R^J.

If more than J weights are positive, take any J+1 of them and a nonzero
linear dependence sum_j c_j phi_j=0. The first coordinate implies sum c_j=0,
so the dependence has both positive and negative entries. Put

    s=min_(c_j>0) omega_j/c_j, omega_j<-omega_j-s c_j.

No weight becomes negative; at least one positive weight becomes zero.
Mass and covariance are preserved exactly. Repeat until at most J remain.
There are at most max{p-J,0} elimination steps. A dependence can be found by
Gaussian elimination on a J-by-(J+1) matrix. This proves the claimed
algorithm and support bound without an optimization or existence oracle.

Compression is performed in raw coordinates. Its output weights need not
coincide with those that an arbitrary coordinate-dependent elimination
rule would choose after T. They still represent the same M_x and have the
same mass, which is all the subsequent proof requires.

## 5. Deterministic geometry: linear average error from the design

The following lemma isolates the new computational transfer. In analysis
coordinates let B_j be nonnegative substochastic rows in R^K, including all
K coordinate vertices at designated anchor indices. Let p_j>=0 be row
penalties, and let z>=0 satisfy ||Y_j-B_j||<=p_j+z. Put

    x_j=Y_j/(1+4p_j), theta_j=p_j/(1+4p_j),
    P=sum_(designated anchors) min{1,p_j}.              (E10)

The held zero-count convention instead has x_j=0, theta_j=1/4 and capped
penalty one. It also satisfies the inequalities below. Define

    e=P+z+delta.

For all rows, including the zero convention,

    ||x_j||<=1-3theta_j+z,
    ||x_j-B_j||<=5theta_j+z.                           (E11)

For sufficiently small e (a threshold depending only on K), every design
with logdet gap at most delta, and every mass/covariance-preserving
compression of it, satisfies the conclusions of this section.

**Determinant and trace.** The designated weighted anchor matrix is within
C_K(P+z) of I in Frobenius norm. Telescoping its determinant gives determinant
at least 1-C_K(P+z). Equal design weight 1/K on these anchors then proves

    det M_x>=K^(-K)(1-C_K e),
    tr M_x<= (1+z)^2<=1+3z,
    tr M_x>=K(det M_x)^(1/K)>=1-C_K e.                (E12)

For the first inequality use exp(-delta)>=1-delta. At e small enough, E12
also implies

    lambda_min(M_x)>=1/(2K), lambda_max(M_x)<=2.        (E13)

For completeness, this fixed-K implication follows from compactness and
the equality case of arithmetic–geometric mean. If no small-e threshold
worked, a sequence of eigenvalue vectors with one coordinate below 1/(2K)
would have sum tending to one and product tending to K^(-K). They are
bounded, with product bounded away from zero, so a subsequence converges.
Equality in AM–GM forces every limiting coordinate to be 1/K, a
contradiction. E13 is needed only for bounded conditioning; no O(e)
ellipsoid-shape approximation is asserted.

**Penalty mass.** As 0<=theta_j<=1/4 and z<=1,

    ||x_j||^2<=(1-3theta_j)^2+3z
                <=1-3theta_j+3z.

Averaging and using the lower trace bound in E12 gives

    sum_j omega_j theta_j<=C_K e,
    sum_j omega_j ||x_j-B_j||<=C_K e.                  (E14)

Because ||x_j||<=2 and ||B_j||<=1, changing from x_j'x_j to B_j'B_j changes
the weighted covariance in operator norm, and its trace, by at most C_K e.
Consequently

    sum_j omega_j(1-||B_j||^2)<=C_K e.                 (E15)

Choose k(j) as a largest coordinate of B_j, with arbitrary deterministic
tie-breaking even if B_j=0. If s=sum B_j<=1 and M=max B_j, then
||B_j||^2<=sM<=M, so

    ||B_j-e_(k(j))||_1=1+s-2M
       <=2(1-M)<=2(1-||B_j||^2).

Equations E14–E15 yield the LINEAR average vertex-error bound

    sum_j omega_j ||x_j-e_(k(j))||<=C_K e.             (E16)

Let pi_k=sum_(k(j)=k)omega_j. Since ||x_j||<=2,

    ||M_x-diag(pi)||op<=3 sum_j omega_j
                                  ||x_j-e_(k(j))||<=C_K e.

Together with E13, and a smaller fixed small-error threshold, this gives

    pi_k>=1/(4K), every k.                            (E17)

Equations E12–E17 depend only on the design covariance and mass plus the
pointwise bounds E11. They therefore apply anew to the compressed design;
they do not assume its atoms retain their original weights.

## 6. Heavy compressed atoms give a uniformly accurate candidate set

Apply E16–E17 to omega_bar, whose support has size at most J. Dropping
weights below h=1/(8KJ) removes total mass at most1/(8K), so every vertex
label retains positive mass by E17. Each retained row also obeys

    ||x_j-e_(k(j))||<=C_K e/omega_bar_j<=C'_K e.       (E18)

There is thus at least one retained representative of every vertex, and
every retained representative is within C_K e of a vertex. In the small
error range this also excludes zero-count rows. This is the step that
turns an average design guarantee into a maximum error bound; applying a
uniform-noise SPA theorem before it would not be justified.

The algorithm whitens the RAW covariance M with L'ML=I. In analysis
coordinates y_j=v_j L=x_j R with R=T^(-1)L. Direct matrix algebra gives

    RR'=T^(-1)M^(-1)T^(-T)=M_x^(-1).                 (E19)

The ideal whitened vertices are the rows of R. By E13,

    sigma_min(R)>=1/sqrt(2), ||R||op<=sqrt(2K).

Hence E18 becomes a uniform C_K e perturbation of K well-conditioned
vertices, with every vertex represented. This reasoning does not require
computing T, and does not introduce its possibly diverging condition number
into the selection error.

## 7. Greedy projection on the candidate set

Here is a self-contained special case of standard robust QR/SPA reasoning.
Suppose a finite set consists of points within epsilon of rows r_1,...,r_K
of an invertible matrix R, each row has at least one representative, and
sigma_min(R)>=s>0, ||R||op<=L. For fixed K,s,L and sufficiently small epsilon,
pivoted row QR selects one representative of each row.

Induct on the number t of selected distinct labels. Their ideal row matrix
has minimum singular value at least s, since its Gram matrix is a principal
submatrix of RR'. The corresponding empirical row matrix differs by at
most sqrt(t)epsilon in operator norm. If this is at most s/2, its row span
projector differs from the ideal row span projector by at most
C sqrt(t)epsilon/s. One elementary proof bounds distances of unit vectors
in either span: their coefficient norm is at most1/s in the ideal matrix
and at most2/s in the empirical matrix; replace the spanning rows and use
the two directed subspace distances. The projector norm is bounded by the
sum of these two distances.

A point with an already selected label therefore has residual norm at
most epsilon+C L sqrt(K)epsilon/s. A representative of an unselected label
has residual at least

    s-epsilon-C L sqrt(K)epsilon/s.

Indeed the distance of any unselected ideal row to the span of the selected
ideal rows is at least s: any linear combination with its own coefficient
one has coefficient norm at least one, so multiplying by R has norm at
least s. For small epsilon the unselected residual is strictly larger.
Thus every greedy pivot has a new label, completing the induction. The
selected points themselves remain epsilon-close to their distinct labels;
the induction does not turn the error into sqrt(epsilon).

Apply this lemma with s=1/sqrt(2), L=sqrt(2K), epsilon=C_K e. Returning the
raw selected rows, not their whitening, gives a permutation Pi such that

    ||Vhat T-Pi||F<=C_K(P+z+delta),
    ||(Vhat T)^(-1)||op<=C_K.                          (E20)

This is precisely the selected-matrix property needed by the statistical
reconstruction. No near-unit approximation of a combinatorial determinant
was assumed or computed.

## 8. Statistical transfer without new oracle inputs

On the held spectral event G0, use its analysis map T, its ideal simplex
rows, P=P0 and z=Z. The held theorem supplies

    P(G0^c)<=C a(b),
    E[1_G0 P0]<=C min{1,a(b)sqrt(ell(alpha)/alpha)},
    E[1_G0 min{1,Z}]<=C min{1,a(b)},
    a(lambda_hat)<=C a(b).                            (E21)

The last comparison implies delta<=C a(b) on G0. Consequently

    P(G0^c or P0+Z+delta>epsilon_K)
       <=C min{1,a(b)+a(b)sqrt(ell(alpha)/alpha)}.      (E22)

This is a fixed-threshold Markov argument using the TRUNCATED excess
expectation, not a claim of integrability of the untruncated maximum.
On the complementary event E20 gives, after one permutation, raw row error

    C delta_j+C d_j(P0+Z+delta).                       (E23)

Here delta_j is the held row-noise envelope, distinct from the optimization
tolerance delta. The same-data output cutoff is still comparable to a(b)^2
on G0. The held unconditional Cauchy–Schwarz and omission arguments sum
the first term in E23 to C H_a(d), and sum the second to C(P0+Z+delta).
Clipping and column normalization use the same positive mean-topic floor.
Bounded loss controls E22, and E21 controls the good-event expectation.
This proves E3. Weak-q summation and b>=beta give the unchanged class bound.

## 9. What the computational assertion includes

With the p-by-K candidates already formed, a direct implementation costs
O(pK^2+K^3) arithmetic operations per design iteration and at most E8
iterations. Constructive compression costs at most O(pJ^3) operations;
the remaining whitening and QR operate on at most J=O(K^2) rows. These are
conservative bounds. Storage for this selector can be O(pK+p+K^2), apart
from elimination workspaces. There is no combinatorial vocabulary-wide
subset enumeration.

For this count statistic Chat has nonnegative entries with total sum one,
so ||Chat||op<=||Chat||F<=1 and 0<lambda_hat<=1 whenever this branch is used.
Thus delta>=1/sqrt(nN). E8 is in particular polynomial in the total number
of tokens. It is NOT asserted polynomial in the binary encoding length of
an arbitrarily huge N, or strongly polynomial, or optimal in tolerance.
The theorem treats real arithmetic, including the existing spectral step,
square roots, logarithms and exact rank comparisons. Rounding error,
conditioning of raw matrices, and certified finite-bit implementation
require separate work. Weakening b does not enter the STATISTICAL constants
or the coordinate-invariant stopping certificate; it can still matter for
ordinary floating-point arithmetic.

## 10. Antecedents and exact scope of this increment

D-optimal design is the dual of the centered minimum-volume enclosing
ellipsoid problem. The leverage gradient, rank-one update, and determinant
identity are classical; see Ahipasaoglu–Sun–Todd, Section 2, equations (2)–(6),
[primary manuscript](https://people.duke.edu/~psun/bio/ahisuntod_first_sub.pdf).
Our conservative E5–E8 proof is supplied to make the computational claim
independent of problem-dependent constants in stronger convergence results.

Ellipsoid preconditioning followed by SPA is also established. Gillis–Vavasis,
Theorems 4–5 and Section 4, [primary manuscript](https://arxiv.org/pdf/1310.2273),
prove robustness under uniform noise relative to the basis conditioning and
discuss small active sets. Those results must be credited. Here the initial
weighted rows can have substantial outward nonanchor errors; the new
statistical transfer does not assume their uniform-noise hypothesis.
E14–E18 supplies a linear-error, heavy-design-atom reduction before applying
the elementary greedy argument. This is a specialized application of known
optimization/geometry, not a new general theory of ellipsoids or SPA.

The held fixed-beta contraction already removed a vocabulary-wide greedy
bottleneck using a reliable interior center. It is not counted again. The
present increment preserves the JOINT unknown-alpha/beta/q risk through
the weakening-beta, all-N experiment without such an observable fixed-radius
core, while replacing the exhaustive selector by an explicit polynomial
real-arithmetic algorithm. No numerical speedup or historical priority is
inferred from this proof.

## 11. Immutable dependency

`../joint_adaptation_gate_20261028/joint_adaptive_upper.md`, SHA256
`7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd`,
including its exact statistical source bindings, is the sole imported risk
theorem. Its prior sources and audits remain unchanged. This new selector
requires its own independent analytic review.
