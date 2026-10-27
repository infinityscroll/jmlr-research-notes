# Rank-100 default instability driven by the actual ten-step power estimate

27 October 2026. New exact-arithmetic source for independent review. This
extends the earlier rank-two stress construction to the recommended
block fraction AND rank. It concerns the released practical defaults,
not a refutation of the different hypotheses in JMLR Theorem 17. No
floating-point trajectory, real-data performance, or historical novelty
claim follows from the result.

## 1. Configuration and result

Use the public `fast_krr` source at commit
`61cdb69cb11adea48ecb13c823ad654d46dc15df`. Set

    n=10000, b=100=n/100, Nyström rank r=100,
    lambda=1/100000000,
    delta in [1/20000000000,1/5000000000],
    K=delta I+(1-delta)11', A=K+lambda I.

K is the bandwidth-one Gaussian RBF Gram matrix of the distinct points
x_i=sqrt(-log(1-delta)) e_i in R^10000. This is a deliberately adverse,
highly correlated construction. The regularized condition number is
roughly 10^12; the theorem does not describe typical data.

Use uniform block sampling, default `rho='damped'`, automatic ten-step
random powering, default acceleration mu=lambda and nu=n/b=100, and
zero initial coefficients and momentum. The practical checks mu<nu and
mu*nu=10^-6<1 both hold. Define

    s=sqrt(mu/nu)=1/100000, gamma=1/sqrt(mu*nu)=1000.

Interpret the float64 branch in exact arithmetic, retaining its
stabilization shift and eigenvalue-floor rule. The ideal independent
Gaussian sketches/power starts are fresh at each step, as in the source.
The interval has delta>2^-52, so the eigenvalue floor is inactive under
this interpretation. This observation is not a finite-precision theorem.

Let u be any nonzero sum-zero vector, and give the solver response Au.
For BOTH the released gradient and the single-line repaired gradient,

    g_stale=K y+lambda w-Au,
    g_repaired=A y-Au,

the exact stochastic iterates satisfy, for every integer t>=1,

    E||w_t-u||_A^2 / ||u||_A^2
       >= (1/1000)(1000001/1000000)^(t-1).                (R100.1)

Thus mean-square optimization error diverges for each delta in the whole
stated interval, even after the stale-gradient repair. This is not a claim
that every realization diverges. Unlike the previous rank-two proof,
R100.1 does NOT hold by covering every possible realized stepsize with
the same growth certificate. The actual random-power law is essential.

## 2. Native Nyström and power routines

Every b-by-b block has eigenvalues delta (multiplicity b-1) and
b-(b-1)delta (multiplicity one). For a square, almost surely nonsingular
Gaussian sketch, the orthogonalized sketch is square orthogonal.
The released shifted Nyström construction therefore recovers K_BB
exactly after subtracting the shift, as in the earlier full-rank proof.
The default damping is lambda+delta, so the inserted block preconditioner is

    P_B=I_B' [K_BB+(lambda+delta)I]^-1 I_B.

Its inverse block denominator is
(lambda+2delta)[b+lambda-(b-2)delta]. The preconditioned operator in
`opts/utils/general.py::_get_L` is symmetric here because both factors
are functions of K_BB. Its eigenvalues are

    a=(lambda+delta)/(lambda+2delta), multiplicity b-1,
    h=[b+lambda-(b-1)delta]/[b+lambda-(b-2)delta], multiplicity one.

They obey 0<a<h<1. The source initializes an isotropic Gaussian vector,
normalizes it, then performs ten products and Rayleigh evaluations.
The returned Rayleigh quotient uses the vector after nine powers. If Z
is the squared initial projection onto the one-dimensional h eigenspace,
rotational symmetry gives EZ=1/b. At the final Rayleigh evaluation the
squared projection is

    W = R Z/[1+(R-1)Z], R=(h/a)^18,
    L_hat=a+(h-a)W, eta=1/L_hat.                         (R100.2)

Using twenty powers gives a convenient conservative bound. On the entire
delta interval,

    h/a <= 1/a <=52/51,
    R <=(52/51)^20 <3/2, E W<=3/(2b)=3/200.

The last strict rational inequality is checked exactly. Therefore

    E L_hat <=a+(3/200)(h-a) <=a+(3/200)(1-a),
    E eta >=1/E L_hat
           >=(lambda+2delta)/(lambda+(203/200)delta)=eta_lower,
    E eta <=1/a=(lambda+2delta)/(lambda+delta)=eta_upper. (R100.3)

The lower bound is Jensen for the reciprocal. It uses the ACTUAL
finite-iteration random estimate and is not an exact-largest-eigenvalue
substitution. Identical block matrices imply the same eta law for every
block; full-rank exact Nyström removes sketch dependence from the
preconditioner. Fresh draws make this law independent of coefficient errors.

The source bound uses ideal continuous Gaussians. Real pseudo-random
float64 operations and rounding of the near-singular Nyström factors are
not certified by this argument.

## 3. Why a certificate at the mean stepsize proves stochastic growth

Write e=w-u, f=v-u and Y=(e+s f)/(1+s). Each native step is

    g=K Y+lambda e        (stale), or g=A Y (repaired),
    e'=Y-eta P_B g,
    f'=(1-s)f+sY-gamma eta P_B g.                         (R100.4)

For a fixed block, its error-state matrix has the affine form
M_B(eta)=M_B(0)+eta D_B. For every positive semidefinite covariance C,

    E_eta[M_B(eta) C M_B(eta)']
      =M_B(E eta) C M_B(E eta)'
          +Var(eta) D_B C D_B'
      >=M_B(E eta) C M_B(E eta)'.                        (R100.5)

This PSD identity is the key step. A lower bound for an arbitrarily
chosen high eta would be insufficient. The eta mean in R100.5 belongs
to R100.3, for every block with the same law, so the uniform-block mean
covariance map dominates the map at one common number in that interval.

Let E=11'/n and P=I-E. An exchangeable state covariance has coordinates

    C(a,b,c,d,e,f)=[[aP+bE,cP+dE],[cP+dE,eP+fE]].

It is PSD exactly when its two 2-by-2 contrast and mean coordinate
matrices are PSD. Let Phi_eta be the block-average map at a common
numerical eta, and define

    C0=C(1,0,1,0,1,0),
    Cstar=C(1,0,499,0,500800,0).

The attached exact certificate proves simultaneously for both gradients,
all delta in the interval, and all eta in [eta_lower,eta_upper],

    Phi_eta(Cstar)>=(1000001/1000000)Cstar,
    Phi_eta(C0)>=(1/1000)Cstar.                           (R100.6)

Combining R100.5 with R100.6 gives the corresponding bounds for the
actual stochastic covariance map. Positive linearity propagates them.
The complete random update law and A-energy are permutation invariant.
Averaging deterministic (-u,-u)(-u,-u)' over permutations therefore does
not change expected energy, and yields ||u||^2/(n-1) times C0.
Since tr(AP)=(lambda+delta)(n-1), the first block of Cstar has exactly
the needed unit contrast coefficient. This proves R100.1 without
randomizing the actual response or zero initialization.

## 4. Finite exact certificate and its mathematical scope

`general_block_operator.py` computes the six output coordinates from
representative selected/unselected rows, for arbitrary n>b>=2. An error
row is represented by coefficients on its own coordinate, the selected
block sum, and the whole-vector sum, separately for e and f. For any
output cross block T, permutation averaging uses

    diagonal=[b T_00+(n-b)T_bb]/n,
    off-diagonal=[b(b-1)T_01+b(n-b)(T_0b+T_b0)
                  +(n-b)(n-b-1)T_b,b+1]/[n(n-1)].

These formulas follow by counting selected and unselected ordered pairs.
They do not materialize a 20000-by-20000 covariance matrix.

Set eta=eta_lower+(eta_upper-eta_lower)v, 0<=v<=1. A common positive
denominator for every error-state row is

    D(delta)=(lambda+2delta)[b+lambda-(b-2)delta]
              [lambda+(203/200)delta](lambda+delta).

The numerator degree is at most four in delta and one in v: the
block-inverse numerator and gradient each have delta degree at most one,
and the interpolated-eta numerator has delta degree at most two.
Hence D^2 times either residual in R100.6 has degree at most eight in
delta and two in v. The Fraction-only checker interpolates within this
proved degree bound, converts to the tensor Bernstein basis, and checks
all 9*3 coefficient matrices for each of the four residuals. Every
contrast block has positive first pivot/determinant. Every mean block
is a nonnegative multiple of [[1,1000],[1000,1000000]]. Nonnegative
Bernstein weights and D^2>0 establish the continuum inequalities.
Additional rational evaluations check the interpolation and conversion.

The saved certificate contains all 108 matrices. This is not a conclusion
from a floating spectral-radius grid. Exploratory spectra are separately
retained and explicitly labeled; some admissible realized stepsizes are
stable, which is why the mean-law argument was necessary.

## 5. What this changes, and what it does not

JMLR Section 2.5/Table 3 recommends b=n/100, r=100, uniform sampling,
adaptive damping, mu=lambda and nu=n/b. All of those choices are now
simultaneously represented, with the printed practical inequalities.
This removes the rank-two qualification in the earlier default stress
class. It exposes a mechanism involving finite randomized powering and
acceleration; the stale-gradient correction alone does not remove it.

Theorem 17 has additional theoretical sampling, blocksize, embedding and
acceleration hypotheses. They are not established for this family, so
this is a limitation of the practical default recipe, not a counterexample
to its condition-number-free theorem. A safe stepsize or unaccelerated
variant is not claimed here to be a competitive replacement. The lower
growth rate is small and asymptotic; it is not a measured failure frequency
or a matched-wall-time generalization result.

Primary sources:

- [Paper, Sections 2.4--2.5 and Theorem 17](https://www.jmlr.org/papers/volume27/25-0385/25-0385.pdf).
- [Pinned ASkotchV2](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/opts/askotchv2.py).
- [Pinned ten-step powering](https://github.com/pratikrathore8/fast_krr/blob/61cdb69cb11adea48ecb13c823ad654d46dc15df/fast_krr/opts/utils/general.py).

No author contact, publication, paid execution, or modification of earlier
frozen results occurred. Independent source/interface and mathematical
review remain separate requirements; this source alone is not their receipt.
