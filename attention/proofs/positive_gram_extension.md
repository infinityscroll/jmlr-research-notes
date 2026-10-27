# Positive query correlation changes the selected-path implicit direction

28 October 2026. General-geometry proof candidate, written by the root agent
from an independent reduction. It extends the fixed-input source
`selected_path_noncollapse_theorem.md`, SHA256
`46db3f866ad368b39f1bf600e730133a2f52570b6f4a24464aebb39e57187ae7`.
The discrete basin argument is reproduced below in its general form. This
source requires its own review; the fixed-input review is not automatically
a review of this extension. No new numerical trajectory is asserted.

## 1. Open input class and exact conclusion

Let x1,x2 be linearly independent vectors in R^d, d>=2, with positive inner
product. Fix a head w satisfying w'x1>w'x2 and w'x1>0. Write

    a0=||x1||², b0=x1'x2>0, c0=||x2||²,
    Delta=a0 c0-b0²>0, d0=x1-x2, D0=||d0||²,
    c_head=w'(x1-x2)>0,
    r=b0/a0, t=c0/a0, t-r²>0.

Use exactly the two-layer identity-value self-attention architecture of the
bound source, with final query 1, fixed head w, and the paired examples
(X,+1),(-X,-1). Both unrestricted d-by-d direct matrices train simultaneously
with logistic loss and constant-step p=2 unnormalized mirror descent. No
residual, mask, parameter factorization, frozen memory or restricted comparator
is introduced.

**Theorem.** For every such fixed input/head and every fixed eta>0, there is a
nonempty open set of finite initial matrices for which

    h1 -> x1, h2 -> x2,
    W1/log n -> q_* d0'/D0,
    W2/log n -> x1 d0'/(a0 D0),
    q_*=(c0 x1-b0 x2)/Delta.                              (G1)

The lower actual selected-path SVM has the sole distinct constraint
`x1'W d0>=1`; its unique solution is x1 d0'/(a0 D0). The trained lower
normalized margin as a fraction of this global optimum tends to

    sqrt(Delta/(a0 c0))
       =sqrt(1-(x1'x2)^2/(||x1||²||x2||²)) < 1.           (G2)

The normalized p=2 Bregman discrepancy tends to one minus G2. The upper actual
checkpoint SVM fraction tends to one. The limiting memories are distinct and
the upper optimal unit-norm margin tends to ||x1|| ||d0||>0.

The lower direction instead minimizes the following explicit *different*
quadratic problem:

    minimize ||W||_F²/2
    subject to x1'W d0>=1, x2'W d0<=0.                   (G3)

This is a characterization of the proved direction, not a replacement of the
paper's selected-path comparator. Both constraints in G3 are active in the
leading direction. The actual second logit diverges negatively at a slower
log-log scale, rather than remaining exactly zero.

The assumptions on inputs and head are strict and define an open data class.
The initialization basin is at a sufficiently large finite scale, depending
on the fixed problem and eta. Arbitrary or random initializations, practical
entry times, non-Euclidean p and trainable heads/values remain unproved.

## 2. Exact coordinate dynamics

Put

    q=W1 d0, k=W2 d0,
    l1=x1'q, l2=x2'q, a=sigmoid(l1), b=sigmoid(l2),
    h1=x2+a d0, h2=x2+b d0,
    m=(a-b)h1'k, pi=sigmoid(m),
    f=w'x2+c_head[b+pi(a-b)], Q=(1+exp(f))^(-1).

The paired examples have the same signed f and gradient. Define

    C_a=pi+pi(1-pi)[m+(a-b)^2 d0'k],
    C_b=(1-pi)(1-pi m),
    A=a(1-a)C_a, B=b(1-b)C_b,
    U=(a-b)^2 pi(1-pi), rho=eta Q c_head D0.

Differentiating all moving upper query, key and value paths gives exactly

    Delta q=rho(A x1+B x2), Delta k=rho U h1,
    Delta l1=rho(a0 A+b0 B),
    Delta l2=rho(b0 A+c0 B).                              (G4)

All quantities on the right are evaluated at the old state. Since the full
matrix gradients have right factor d0',

    W_j=[W_j d0]d0'/D0+G_j, G_j d0=0,

with G_j constant. The component of q orthogonal to span{x1,x2} is also
constant. These are finite irrelevant components of the unrestricted
parameterization, not restrictions on its trainable coordinates.

## 3. A stable system in the exact increasing clock

Use the scalar clock and transverse component

    s=x1'k,
    k_perp=k-(s/a0)x1,
    x=s-l1, v=s b, u=exp(x-v).

Let

    v_*=r/(t-r²)>0, u_*=t/(t-r²)>1,
    x_*=v_*+log u_*.

Consider a compact neighborhood of (x_*,v_*) with v bounded away from zero,
|k_perp|<=2, and s>=R. For sufficiently large R, a>b and every expression
below is uniform on that neighborhood. Direct expansion gives

    1-a=exp(-s+x)[1+O(exp(-s))], b=v/s,
    m=s-v+O(s exp(-s)),
    A=exp(-s+x)[1+O(s exp(-s))],
    B=-v exp(-s+v)[1+O(1/s)],
    Delta s=rho a0 exp(-s+v)[1+O(1/s)].                  (G5)

In the last line use `x1'h1=a0-(1-a)(a0-b0)`. This is positive on the working
region even if b0>a0. No sign condition on d0'k is needed: the possibly
negative extra term in C_a is O(s exp(-s)), so C_a tends to one.

The exact transverse ratio is

    Delta k_perp/Delta s
      =(1-a) projection_(x1 perpendicular)(x2)
                    /[a0-(1-a)(a0-b0)].                 (G6)

Its norm is O(exp(-s)). The bounds on f between its two fixed token scores
give fixed positive upper and lower bounds for Q, and hence
`c_eta exp(-s)<=Delta s<=C_eta exp(-s)`.

Divide the exact logit recurrences by Delta s. G5 gives

    Delta l1/Delta s=u-rv+O(1/s),
    Delta l2/Delta s=ru-tv+O(1/s).

The discrete product in `v=s sigmoid(l2)` is handled by Taylor expansion on
the actual finite increment, using |Delta l2|<=C Delta s:

    Delta v=b Delta s+s b(1-b)Delta l2
               +O(s b(Delta l2)^2+b|Delta s Delta l2|).

Consequently, for y=(x-x_*,v-v_*), h=Delta s,

    Delta y=h[F(x,v)+epsilon_n],
    F1=1-exp(x-v)+rv,
    F2=v[r exp(x-v)-tv],
    ||epsilon_n||<=C(1/s+h).                             (G7)

This is an estimate for the exact discrete updates, not a substitution of
gradient flow. The term b Delta s contributes the retained O(1/s) forcing.

The Jacobian at the fixed point is

    J=[[-u_*, u_*+r],
       [v_* r u_*, -v_*(t+r u_*)]].                      (G8)

Its trace is strictly negative and its determinant is
`u_* v_* (t-r²)>0`. Thus both eigenvalues have negative real parts. A positive
definite quadratic Lyapunov matrix is explicitly defined by

    P=integral_0^infinity exp(J' z) exp(J z) dz,
    J'P+PJ=-I.

The integral is finite by the two-dimensional Hurwitz condition just verified.
It also provides a standard finite linear system for the entries of P.

## 4. A genuine finite open basin and convergence

Choose epsilon>0 small enough that the ellipsoid y'Py<=epsilon² lies in the
working neighborhood and, by Taylor's theorem,

    2y'P F <= -||y||²/2.

Start at

    s(0)>R0, ||k_perp(0)||<1, y(0)'P y(0)<epsilon².      (G9)

Here R0 will be finite and large enough for the following estimates; no
certified small numerical value is asserted. Exact expansion of V=y'Py using
G7, and absorption of h²||y||² by h||y||², yield

    V^+-V <= -c h||y||²+C h||y||/s+C h²/s².             (G10)

On epsilon²/4<=V<=epsilon², a large finite R0 makes this strictly negative.
Inside V<epsilon²/4, the uniform bound ||Delta y||<=C h and small h prevent
a jump out of the full ellipsoid. This is a discrete overshoot check; a
continuous-time inward condition alone would not suffice.

Equation G6 gives, on every stopped prefix,

    sum ||Delta k_perp|| <= C sum exp(-s) Delta s
                          <= C' exp(-s(0))<1.

For h<=1 the sum is bounded by an integral with a factor e, so this inequality
does not assume infinitesimal steps. Together with the initial transverse
norm below one, it prevents escape from the working bound two. The clock is
strictly increasing and cannot cross its lower boundary. These estimates
close the simultaneous stopped-region induction for every finite eta>0 once
R0 is large enough.

The basin is nonempty: set k=(s/a0)x1, l1=s-x_* and
`l2=log[(v_*/s)/(1-v_*/s)]` at any sufficiently large s. Independence of x1,x2
permits a finite q with these two logits. Finite full matrices implementing
q,k exist. The strict conditions G9 give an open preimage in all 2d² matrix
coordinates. They impose no equality on conserved components.

If s were bounded, its positive increment lower bound would be impossible.
Hence s->infinity, h->0 and sum h=infinity. Young's inequality in G10 gives

    V^+ <= (1-c h)V+C h/s²

eventually. Unrolling this scalar contraction proves V->0: the forcing tends
to zero and the product of its contraction factors tends to zero. The
transverse k component converges absolutely by G6.

Thus x->x_*, v->v_*, a->1, b->0 and f->w'x1. Let
`rho_*=eta c_head D0/(1+exp(w'x1))`. Equation G5 and the exact exponential
increment give

    exp(s(n))/n -> rho_* a0 exp(v_*),
    s=log n+log(rho_* a0)+v_*+o(1),
    l1=log n+log(rho_* a0/u_*)+o(1),
    l2=-log log n+log v_*+o(1).                          (G11)

The final line uses the exact inverse logit with b=v/s. Solving the two
linear equations x1'q=l1, x2'q=l2, with its constant orthogonal component,
gives q/log n->q_*. The decomposition of k and of the full matrices proves G1.

## 5. Correct comparators and the geometry of the failure

The actual selected lower query is x1 and its eventual selected token is x1.
The negative paired example gives the identical matrix normal x1 d0'. The
global selected-path SVM therefore has optimizer x1 d0'/(a0 D0) and optimal
unit-Frobenius margin sqrt(a0 D0). From G1,

    x1'q_*=1, x2'q_*=0, ||q_*||²=c0/Delta.

The trained lower normalized margin tends to sqrt(D0 Delta/c0); dividing by
sqrt(a0 D0) gives G2. The same fraction is the inner product between the two
unit matrix directions, so the p=2 Bregman discrepancy is one minus G2.

To verify G3, fix q=Wd0. The minimum-norm W realizing it is q d0'/D0. Multiply
the reduced objective ||q||²/(2D0) by the positive constant D0, which leaves
its optimizer unchanged. The resulting program has objective ||q||²/2 and
constraints x1'q>=1 and x2'q<=0. Its KKT multipliers are c0/Delta and b0/Delta,
both positive, and its solution is q_*.
This demonstrates explicitly the extra zero-leading-margin constraint forced
by the coupled route. It does not relabel that constrained problem as the
isolated paper comparator.

The actual upper normal is `h1(h1-h2)'`. It converges to x1 d0', while the
upper matrix limit in G1 is precisely its minimum-norm separator. Its margin
fraction therefore tends to one with a positive optimal scale. All tokens,
queries and values in the upper layer are the genuinely moving lower outputs.

## 6. Robustness and scope

Every strict data condition in Section 1 persists in a neighborhood. The
fixed point and Jacobian depend smoothly on the Gram entries as long as
b0>0 and Delta>0. At any fixed admissible data point, one can keep its P on
a sufficiently small neighborhood: J'P+PJ stays strictly negative definite.
Compact local bounds in G5-G10 then give a common small ellipsoid radius and
finite large-scale threshold. This justifies a locally open set jointly in
inputs/head and initial weights, not merely a one-parameter perturbation
family. No robustness through orthogonality or linear dependence is claimed.

At x1=e1,x2=(1/2,1),w=e1, this theorem gives v_*=1/2,
u_*=5/4 and the bound source's exact fraction 2/sqrt(5). More generally the
limiting fraction can approach zero along increasingly positively correlated
independent query vectors, but the basin threshold and constants need not
remain uniform in that near-collinear limit.

This is a counterexample to a layerwise selected-path extension of the
one-layer attention-SVM law. It is not a refutation of the published
one-layer theorem or evidence of worse test accuracy. The fixed head, identity
values, two-token paired design, p=2 update and large finite favorable basin
remain material. Standard stability theory and gradient competition are
classical; historical novelty of this explicit attention limit is separate
from correctness of the proof.
