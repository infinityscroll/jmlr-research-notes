# A selected-path obstruction for every p>1 on an open input class

28 October 2026. Root-authored analytic extension, requiring its own independent
review. This source does not inherit an audit of the p=2 or p=3/2 source.
No new numerical trajectory or historical-priority claim is made.

## Statement and model

Fix p in (1,infinity), p'=p/(p-1), and J_p(z)=sign(z)|z|^(p-1), entrywise.
Use psi(W)=sum|W_ij|^p/p and its exact unnormalized mirror update
J_p(W^+)=J_p(W)-eta grad L(W), with fixed eta>0. Both full d-by-d matrices
are trained simultaneously; d>=2. The two examples are (X,+1),(-X,-1),
where X has token rows x1',x2'. The architecture is

    H0=X, H1=softmax_rows(H0 W1 H0') H0,
    H2=softmax_rows(H1 W2 H1') H1, f=w' H2_row1.

The loss is the mean paired logistic loss. Values and head are fixed; there
are no masks, residuals, factorized parameters or frozen upper memories.

Assume x1,x2 independent, d0=x1-x2 has no zero coordinates, x1 has no zero
coordinates, w'x1>w'x2, and w'x1>0. Define the strictly convex program

    q*=argmin ||q||_p^p/p subject to x1'q>=1, x2'q<=0.       (1)

Assume its two constraints are active and its KKT multipliers lambda,mu
are both strictly positive, so

    x1'q*=1, x2'q*=0, J_p(q*)=lambda x1-mu x2.             (2)

Assume every coordinate of q* is nonzero. These strict/nondegeneracy
conditions define an open class at each fixed p. Put

    S=x1'J_{p'}(x1)=||x1||_{p'}^{p'},
    k*=J_{p'}(x1)/S,
    c=sum_j |d0_j|^{p'}, z_d=J_{p'}(d0),
    C_p=c^(p-1)/(p-1),
    M_ij=sum_a x_i,a x_j,a |q*_a|^(2-p),
    a_top=sum_a x1_a^2 |k*_a|^(2-p).

**Theorem.** For every fixed admissible input/head, p and eta there is a
nonempty open set of finite initial full matrices for which

    H1_row1 -> x1, H1_row2 -> x2,
    W1/log n -> q* z_d'/c,
    W2/log n -> k* z_d'/c.                                (3)

The lower actual selected-query margin as a fraction of its global unit-lp
optimum tends to

    R=1/(||q*||_p ||x1||_{p'}) < 1.                       (4)

The upper actual checkpoint margin fraction tends to one. Both optimal
margin scales remain positive. The official normalized Bregman discrepancy
of the lower matrix has a strictly positive limit. The exact limit is

    1-<J_p(q*/||q*||_p), k*/||k*||_p>.                    (5)

The order in (5) is D_psi(optimal unit matrix, trained unit matrix), matching
the released metric. It is generally not 1-R away from p=2.

The open basin is at a sufficiently large finite scale. Random initialization,
an effective practical threshold, independent perturbations of the two
paired examples, trainable values/head and initialization in the source's
printed cones are not conclusions here. The separate p=2 cone result is
not silently promoted to all p.

## Exact gradients and dual invariants

Write q=W1 d0, k=W2 d0, l_i=x_i'q, a=sigmoid(l1), b=sigmoid(l2),
h1=x2+a d0, h2=x2+b d0, m=(a-b)h1'k, pi=sigmoid(m),

    D=w'd0>0, f=w'x2+D[b+pi(a-b)], Q=(1+exp(f))^(-1),
    A=a(1-a){pi+pi(1-pi)[m+(a-b)^2 d0'k]},
    B=b(1-b)(1-pi)(1-pi m), U=(a-b)^2 pi(1-pi).

The paired signed predictions and gradients coincide. Exact differentiation,
including the changing upper query, gives the dual updates

    Delta J_p(W1)=eta Q D (A x1+B x2)d0',
    Delta J_p(W2)=eta Q D U h1 d0'.                       (6)

For the lower layer decompose

    J_p(W1)=r d0'+G1, r in span{x1,x2},

by taking r to be the orthogonal projection of J_p(W1)d0/||d0||^2 onto that
span. G1 is then constant under (6). For the upper layer use

    J_p(W2)=(t x1+z)d0'+G2, z perpendicular to x1,

where G2 d0=0, and t x1+z=J_p(W2)d0/||d0||^2. G2 is constant. The equations
for r and t x1+z follow directly from (6), without restricting any trainable
matrix coordinate. Arbitrary bounded G1,G2 are allowed in their respective
complementary subspaces.

For a row define the exact physical row map

    F_G(r)_i=sum_j d0_j J_{p'}(r_i d0_j+G_ij).            (7)

It is strictly increasing in each r_i. On any fixed-sign cone with r_i
comparable to s^(p-1), bounded G gives uniformly

    F_G(r)_i=c J_{p'}(r_i)[1+O(s^(1-p))],
    partial_i F_G(r)=C_p |F_G(r)_i|^(2-p)
                         [1+O(s^(1-p))].                (8)

These follow by Taylor expansion of J_{p'} at nonzero coordinates; d0 and
the leading r_i are bounded away from zero relative to their fixed scales.
The second derivative is O(s^(3-2p)) on the same cones. The constants may
depend on fixed p and data and are not asserted uniform as p approaches 1
or infinity. No differentiability at a zero dual coordinate is used.

## Recovering the lower physical direction without assuming convergence

Let s=x1'k, x=s-l1 and v=s b. In a bounded neighborhood of the equilibrium
defined below, v is bounded away from zero. Thus exactly

    l1/s=1-x/s,
    l2/s=log[(v/s)/(1-v/s)]/s=O(log s/s).

The lower invariant dual affine space plus these two logits determines r
uniquely. To see existence and its uniform local estimate, rescale r by
s^(p-1). The map from its two coefficients in span{x1,x2} to (l1/s,l2/s)
converges in C1 near

    r*=c^(1-p) J_p(q*) in span{x1,x2}

to rbar -> (x1' c J_{p'}(rbar),x2' c J_{p'}(rbar)).
Its Jacobian at r* is a positive scalar times M and is nonsingular: M is
positive definite because x1,x2 are independent and its coordinate weights
are positive. The inverse function theorem with the bounded offsets in (8)
therefore gives a solution and

    q/s=q*+O(E(s)), E(s)=log(s)/s+s^(1-p).                (9)

For uniqueness, if r-r' is in span{x1,x2} and both logits agree, then
(r-r')'[F_G(r)-F_G(r')]=0. Coordinatewise strict monotonicity forces r=r'.
Consequently the trajectory cannot occupy a different branch with the same
logits. This validates (9) throughout the stopped region; it is not an
assumed limiting direction. The nonzero coordinates of q* ensure that
the fixed-sign estimates remain applicable there for large s.

For the upper layer, bounded z,G2 and s large give t>0 and

    k/s=k*+O(s^(1-p)).                                  (10)

Indeed F_G(t x1+z)=c t^(1/(p-1)) J_{p'}(x1) plus its
uniform lower-order term; its x1 projection determines the positive t.
The scalar projection is strictly increasing in t, so this inversion is
also unique. The nonzero coordinates of x1 ensure fixed signs.

## Exact discrete slow system

Choose a bounded small neighborhood in (x,v), |z|<=2, bounded G1,G2, and
s>=R. Equations (9)-(10) give ||q||+||k||=O(s). Direct softmax expansions,
uniform in this stopped region, yield

    1-a=e^(-s+x)[1+O(e^-s)], b=v/s,
    m=s-v+O(s e^-s),
    A=e^(-s+x)[1+O(s e^-s)],
    B=-v e^(-s+v)[1+O(1/s)],
    U=e^(-s+v)[1+O(1/s)].                               (11)

The exact dual step is O(e^-s). Apply (8) to this finite step; its Taylor
remainder divided by s^(2-p)e^-s is O(s^(1-p)e^-s). Using (9)-(10),

    h=Delta s=eta Q D C_p a_top s^(2-p)e^(-s+v)
                                     [1+O(E(s))]>0,
    Delta l1/h=(M11/a_top)exp(x-v)-(M12/a_top)v+O(E(s)),
    Delta l2/h=(M12/a_top)exp(x-v)-(M22/a_top)v+O(E(s)).   (12)

In particular c_eta s^(2-p)e^-s<=h<=C_eta s^(2-p)e^-s.
The finite-step product rule for v=s sigmoid(l2) gives

    Delta v=b h+s b(1-b)Delta l2
                 +O(s b(Delta l2)^2+b|h Delta l2|).

It follows that Delta(x,v)=h[F(x,v)+epsilon], with
|epsilon|<=C(E(s)+h), and

    F1=1-g11 exp(x-v)+g12 v,
    F2=v[g12 exp(x-v)-g22 v], g_ij=M_ij/a_top.             (13)

This is an expansion of discrete mirror descent, not gradient flow.

The positive equilibrium is

    v*=g12/(g11 g22-g12^2),
    u*=exp(x*-v*)=g22/(g11 g22-g12^2), x*=v*+log u*.

To verify g12>0, multiply (2) coordinatewise by |q*|^(2-p). This gives
q*=diag(|q*|^(2-p))(lambda x1-mu x2), hence
0=x2'q*=lambda M12-mu M22. Since lambda,mu,M22>0, M12>0.
The determinant of g is positive. The Jacobian of (13) at equilibrium is

    J=[[-g11 u*, g11 u*+g12],
       [v* g12 u*, -v*(g12 u*+g22)]].                   (14)

Its trace is negative and determinant is u* v* det(g)>0. Thus J is Hurwitz.

## Finite open basin, overshoot, and convergence

Let P be the positive definite solution of J'P+PJ=-I. A sufficiently small
ellipsoid V=y'Py<=epsilon0^2, y=(x-x*,v-v*), satisfies
2y'PF<=-|y|^2/2. Start with V<epsilon0^2, s>R0, |z|<1, and both conserved
offset norms less than one. Use the working bounds |z|<=2 and offset norms
at most one. Exact expansion of V using (13) and absorption of h^2|y|^2
give, uniformly for large R0,

    V^+-V<=-c h|y|^2+C h|y|E(s)+C h^2 E(s)^2.           (15)

On the annulus epsilon0^2/4<=V<=epsilon0^2, E(s)->0 makes the right side
negative. In the inner ellipsoid, |Delta y|<=C h and h->0 uniformly as
R0 grows prevent a jump outside the full ellipsoid. This addresses finite
step overshoot.

The upper transverse *dual* coordinate obeys exactly

    Delta z=-eta Q D U(1-a) projection_(x1 perpendicular)d0.

From (12), |Delta z|/h<=C e^-s s^(p-2). For R0 large this function is
decreasing and its logarithmic derivative is bounded. For h<=1 the sum is
bounded by a constant times its integral from s0 to infinity, which tends
to zero as s0 grows. Make that bound less than one. Then |z0|<1 prevents
escape from |z|<=2. No sign or smoothness of z itself is needed. These and
the increasing clock close the simultaneous stopped-region induction.

Nonemptiness follows by choosing G1=G2=0,z=0, any sufficiently large s,
x=x*,v=v*, and using the inversions above to set finite dual matrices.
All stated basin inequalities are strict and continuous in the full dual
matrices; J_p and its inverse are homeomorphisms. Hence their preimage is
open in all 2d^2 primal coordinates. The offset bounds describe open balls
in their complementary subspaces, not equalities imposed on parameters.

The clock cannot stay bounded because (12) would give a positive minimum
increment. Thus s->infinity, h->0 and sum h=infinity. Young's inequality
in (15) gives eventually

    V^+ <= (1-c h)V+C h E(s)^2.

Since E(s)->0, unrolling this scalar contraction proves V->0. Summability
of E(s) is not required. The upper transverse dual coordinate converges
absolutely by its integral bound. With Q*=(1+exp(w'x1))^(-1), let

    C*=eta Q* D C_p a_top exp(v*).

Equation (12) now gives Delta s~C* s^(2-p)e^-s. Apply the mean value theorem
to T(s)=e^s s^(p-2), whose derivative is asymptotic to itself. Then
Delta T(s)->C*, so T(s_n)/n->C*. Inverting gives

    s=log n+(2-p)loglog n+log C*+o(1),
    l1=s-x*+o(1), l2=-loglog n+log v*+o(1).              (16)

Equations (9)-(10) and the row expansion give the full matrix limits (3).
In particular the memories remain distinct and all upper inputs actually
move during training.

## Comparator, openness and a concrete family

For any q, Holder's inequality applied separately to each row gives the
unique minimum-lp matrix with Wd0=q as W=q z_d'/c. Its norm is
||q||_p/c^(1/p'). The isolated selected-query SVM has unique solution
Wmm=k* z_d'/c and optimal unit-norm margin ||x1||_{p'} c^(1/p'). This proves
(4). The inequality is strict: if q* were the isolated optimizer k*,
its active second constraint and mu>0 would contradict stationarity with
independent x1,x2. Equivalently strict convexity gives the unique isolated
minimum with a strictly smaller norm.

The upper normal h1(h1-h2)' tends to x1 d0', so the continuous unique
single-constraint lp optimum tends to Wmm and the upper fraction tends to
one. Unit norms remove the common right outer-product factor in the Bregman
pairing, yielding (5). Distinct unit directions and strict convexity make
this limit strictly positive.

For each fixed p, all the data assumptions persist in a neighborhood.
The equality-constrained KKT system has nonsingular bordered Hessian because
q* has no zero coordinates and x1,x2 are independent. Its solution and
positive multipliers therefore vary continuously. The field is smooth there;
one can keep P from a fixed data point on a small neighborhood. Uniform local
bounds then give a common ellipsoid and finite R0. This proves joint openness
in tokens/head and full initial weights, within the paired-sign design.

An explicit admissible input for every p>1 is

    x1=(1,1), x2=(2,1/2), w=(-1/3,4/3).

It has head scores one and zero, d0=(-1,1/2), q*=(-1/3,4/3), k*=(1/2,1/2).
Its positive multipliers are

    mu=(2/3)[(4/3)^(p-1)+(1/3)^(p-1)],
    lambda=(4/3)^(p-1)+mu/2.

Every needed coordinate is nonzero. Its lower margin fraction is

    R=3/[2^(1-1/p)(1+4^p)^(1/p)].                        (17)

At p=2 this is 3/sqrt(34), and at p=3/2 it is
3/[2^(1/3)9^(2/3)]. The theorem is not uniform in p, and these limits are
not finite-time empirical measurements. The original one-layer theorem is
unchanged; the additional active constraint comes from jointly training
the evolving upper layer.
