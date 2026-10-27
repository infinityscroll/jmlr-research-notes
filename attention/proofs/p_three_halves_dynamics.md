# Non-Euclidean selected-path failure under the exact released mirror update

28 October 2026. Analytic candidate, p=3/2. This is a separate proof, not an invocation of the held Euclidean theorem. It includes all simultaneous moving-query/key/value derivatives and a discrete invariant basin open in all eight direct-matrix coordinates. No trajectory or gradient-flow substitution is used.

## 1. Model, optimizer and conclusion

Fix

    x1=(1,0)', x2=(1/4,1)', d=x1-x2=(3/4,-1)',
    delta=1/4, D=3/4, w=e1,
    p=3/2, q=3, c=sum_j |d_j|^3=91/64.

Use two examples (X,+1),(-X,-1), where X has rows x1',x2', equal logistic-loss weights. The architecture is

    H1=softmax_rows(H0 W1 H0') H0,
    H2=softmax_rows(H1 W2 H1') H1,
    prediction=w' H2[1,:]'.                              (N1)

Both unrestricted 2-by-2 direct matrices train. Values are identity and the head is fixed. There is no residual, mask, detached memory, factorization, or coordinate constraint. Define the entrywise signed power `J_r(z)=sign(z)|z|^(r-1)`. The potential and exact simultaneous update are

    psi(W)=||W||_(3/2)^(3/2)/(3/2),
    X_l=J_(3/2)(W_l),
    X_l^+=X_l-eta grad_(W_l)L,
    W_l^+=J_3(X_l^+), eta>0 fixed.                       (N2)

This is the released `SMD(p=1.5,normalize=False)` update exactly. All norms on matrices are entrywise norms. The examples' signed predictions and full gradients agree, so their mean loss has precisely the single-positive-example gradient below.

**Theorem.** For every fixed eta>0 there is a nonempty open set of finite initial matrices such that the exact discrete iteration N2 satisfies

    H1[1,:]' -> x1, H1[2,:]' -> x2,
    W1(n)/log n -> (1,-1/4)' J_3(d)'/c,
    W2(n)/log n -> e1 J_3(d)'/c.                         (N3)

The upper selected query selects key1, and its selected lower query selects original key1. The true lower selected-query global p-token-SVM has the sole distinct constraint `x1'W d>=1`. Its solution is `e1 J_3(d)'/c`. The limiting trained lower unit-p-margin is only the fraction

    (1+delta^p)^(-1/p)=(8/9)^(2/3)<1                    (N4)

of the optimum. In the paper's argument order, its normalized Bregman discrepancy is

    D_psi(Wmm/||Wmm||_p,W1/||W1||_p)
       ->1-(8/9)^(1/3)>0.                              (N5)

The upper actual checkpoint p-SVM direction is recovered. Its optimal unit-p-margin tends to `c^(1/3)>0`, and the memories remain separated at distance 5/4. This is a selected-path noncollapse failure under a genuinely non-Euclidean update. The proof gives a large finite open basin, not arbitrary/random-start or practical entry-time guarantees.

## 2. Exact gradients and dual closure

Write

    q1=W1 d, k=W2 d, l_r=x_r'q1,
    a=sigmoid(l1), b=sigmoid(l2),
    h1=x2+a d, h2=x2+b d,
    m=(a-b)h1'k, pi=sigmoid(m),
    f=delta+D[b+pi(a-b)], Q=(1+exp(f))^(-1).

Here `delta<=f<=1`. Let

    C_a=pi+pi(1-pi)[m+(a-b)^2 d'k],
    C_b=(1-pi)(1-pi m),
    A=a(1-a)C_a, B=b(1-b)C_b,
    U=(a-b)^2 pi(1-pi), alpha=eta Q D.

Differentiating the full architecture gives

    grad_(W1)f=D(A x1+B x2)d',
    grad_(W2)f=D U h1 d'.                               (N6)

These identities include the upper query derivative in C_a and the negative upper-key contribution in C_b. Thus every dual increment has right factor d'. Decompose uniquely

    X_l=r_l d'+E_l,
    r_l=X_l d/||d||², E_l d=0.

Then E_l is constant, while the exact dual recurrences are

    Delta r_1=alpha(A x1+B x2),
    Delta r_2=alpha U h1.                               (N7)

This is a conserved dual decomposition of full trainable matrices. In particular, N7 does not say their primal matrices remain rank one. Nonzero E_l is allowed throughout the open basin.

For a row with scalar r and fixed row offset E define

    h(E)=sum_j |d_j| d_j E_j/c,
    e(E)=sum_j |d_j| E_j²-c h(E)²>=0.

Weighted Cauchy–Schwarz proves the last inequality. Whenever every `r d_j+E_j` has sign `sign(r)sign(d_j)`, exact square completion gives

    [J_3(r d'+E)d]
       =sign(r)[c(r+h(E))²+e(E)].                       (N8)

For bounded E this sign condition holds for all sufficiently large |r|. Formula N8 is exact, including its offset; no large-r term has yet been discarded. Its increment, as long as the signs are unchanged, is

    Delta q=sign(r)c[2(r+h(E))Delta r+(Delta r)²].       (N9)

The second upper row will remain bounded, and no fixed sign is asserted for it.

## 3. Working region and discrete mobility ratios

Set

    s=k_1, x=s-l1, v=s b,
    v*=1/2, u*=9/8, x*=1/2+log(9/8),
    y=(x-x*,v-v*)',
    P=[[109/198,28/33],[28/33,320/81]], r0=1/10000.

Work temporarily on the closed region

    s>=R, max_l ||E_l||_infinity<=1,
    |(r_2)_2|<=2, y'Py<=r0².                            (N10)

The E bounds are constant under N7. On this region, the second upper projection k_2 is bounded by a fixed constant: directly from its row formula, `|k_2|<=sum |d_j|(2|d_j|+1)²<14`. The first upper dual row grows positively, since k_1=s grows. The first lower row grows positively and the second negatively: indeed

    (q1)_1=s-x,
    (q1)_2=l2-delta(s-x),
    l2=log[(v/s)/(1-v/s)]=-log s+O(1).                  (N11)

For sufficiently large R all three large rows satisfy the sign condition in N8. Set their completed variables `T=r+h(E)`. Their magnitudes follow exactly from N8:

    T_upper,1=sqrt((s-e_upper,1)/c),
    T_lower,1=sqrt((s-x-e_lower,1)/c),
    |T_lower,2|=sqrt((delta(s-x)-l2-e_lower,2)/c).

All offset constants are uniformly bounded. Consequently

    T_lower,1/T_upper,1=1+O(1/s),
    |T_lower,2|/T_upper,1=sqrt(delta)+O(log s/s).         (N12)

The logarithm in the second error is retained; assuming an O(1/s) error here would be unjustified.

Let epsilon=1-a. The same exact forward architecture gives, uniformly in N10,

    epsilon=exp(-s+x)[1+O(exp(-s))], b=v/s,
    h1=(1-D epsilon,epsilon)',
    m=s-v+O(s exp(-s)),
    A=exp(-s+x)[1+O(s exp(-s))],
    B=-v exp(-s+v)[1+O(1/s)],
    U=exp(-s+v)[1+O(1/s)].                              (N13)

Since N7 gives each large-row dual increment O_eta(exp(-s)), a sufficiently large R ensures that no such row crosses a sign boundary during the next update. Thus N9 applies to the actual full step. For the upper first row,

    Delta s=2c T_upper,1 alpha U(1-D epsilon)
                 +c[alpha U(1-D epsilon)]²
       =2 sqrt(c) alpha sqrt(s) exp(-s+v)[1+O(1/s)].    (N14)

In particular `c_eta sqrt(s)exp(-s)<=Delta s<=C_eta sqrt(s)exp(-s)`. These bounds hold for each fixed positive eta. Writing h=Delta s, N9–N14 imply

    Delta l1/h=exp(x-v)-delta v+O(log s/s),
    Delta l2/h=delta exp(x-v)
                    -(delta²+sqrt(delta))v+O(log s/s).

The squared dual increments in N9 divided by h are O_eta(exp(-s)/sqrt(s)), hence are included in the stated error. Uniformly, `|Delta l1|+|Delta l2|<=C h`.

The exact product rescaling `v=s sigmoid(l2)` gives

    Delta v=b h+s b(1-b)Delta l2
                 +O(s b(Delta l2)²+b|h Delta l2|).

The logistic second derivative on the actual small intervening step is O(b). Therefore the reduced **discrete** system is

    Delta y=h[F(x,v)+epsilon_n],
    F1=1-exp(x-v)+v/4,
    F2=v[exp(x-v)/4-9v/16],
    ||epsilon_n||<=C(log s/s+h).                        (N15)

No continuous-time differential equation has replaced N2. The vanishing forcing need not be summable in physical time or in s.

## 4. Finite open basin without imposed rank-one identities

F vanishes at (x*,v*), and its exact Jacobian there is

    J=[[-9/8,11/8],[9/64,-27/64]], J'P+PJ=-I.          (N16)

P-I/10 is positive definite and trace(P)<5. On ||y||<=.01, direct second derivatives of F bound its Taylor remainder by `10||y||²`. Hence the ellipsoid in N10, where `||y||<=sqrt(10)/10000`, satisfies

    2 y'P F<=-||y||²/2.

For V=y'Py, expand its exact increment using N15, absorb the h²||y||² term for large R, and use h<=C_eta sqrt(s)exp(-s). This gives fixed c,C>0 with

    V^+-V<=-c h||y||²
              +C h||y|| log(s)/s+C h²(log(s)/s)².       (N17)

On the annulus `r0²/4<=V<=r0²`, sufficiently large finite R makes this negative. Inside the smaller ellipsoid, `||Delta y||<=C h` and small h prevent a single-step jump beyond V=r0². This checks discrete overshoot, not merely an inward vector field.

For the upper second dual coordinate, N7 and the exact positive denominator in N14 give

    0<=Delta(r_2)_2/h
       =epsilon/[2c T_upper,1(1-D epsilon)
                         +c alpha U(1-D epsilon)²]
       <=C exp(-s)/sqrt(s).                             (N18)

For h<=1 the stopped sum of this bound is dominated by a fixed multiple of the integral of exp(-s)/sqrt(s). It is less than one if R is sufficiently large. Initial `|(r_2)_2|<1` therefore prevents exit from its working bound two. Its sign and the signs of the associated finite primal entries may change; the argument does not restrict them.

Finally s increases and E_l is constant. These estimates close the first-exit induction for every initial point satisfying

    s>R0(eta), max_l||E_l||_infinity<1,
    |(r_2)_2|<1, y'Py<r0².                              (N19)

This set is nonempty. Take E_l=0, choose any large s, k=(s,0), l1=s-x*, and `l2=log[(1/(2s))/(1-1/(2s))]`. Set q1=(l1,l2-delta*l1)'. For each row choose r=sign(q)sqrt(|q|/c), then X_l=r_l d' and W_l=J_3(X_l). These choices implement the stated q1,k exactly and lie at the center y=0. The continuous coordinate maps and strict conditions N19 give an open neighborhood in all eight primal matrix entries. Nineteen imposes no equality on an initialized matrix; E_l=0 was used only to exhibit one interior point.

## 5. Convergence and exact clock scale

A bounded s would contradict its positive increment lower bound. Thus s->infinity, h->0, and sum h=infinity. Young's inequality in N17 gives eventually

    V^+<=(1-c h)V+C h(log(s)/s)².

The usual scalar contraction iteration, with forcing tending to zero and infinite total clock, yields V->0. One can fix any positive target tolerance, bound the forcing by that tolerance on a late tail, and unroll the recurrence; the contraction product tends to zero. Let the tolerance decrease. Consequently x->x*, v->1/2. The upper second dual row converges absolutely by N18, hence its primal row and k_2 have finite limits.

Since f->1, set

    alpha*=eta(3/4)/(1+exp(1)),
    K=2 sqrt(c) alpha* exp(1/2)>0.

Equation N14 implies `Delta s/(sqrt(s)exp(-s))->K`. The derivative of `G(s)=exp(s)/sqrt(s)` is `G(s)(1-1/(2s))`. Since h->0, the exact mean-value theorem gives `G(s^+)-G(s)->K`. Cesaro averaging and inversion therefore give

    exp(s(n))/(n sqrt(s(n)))->K,
    s(n)=log n+(1/2)loglog n+log K+o(1),
    l1(n)=log n+(1/2)loglog n
                 +log[2 sqrt(c) alpha*/(9/8)]+o(1),
    l2(n)=-loglog n-log 2+o(1).                         (N20)

In the inversion, first `s-(1/2)log s=log n+O(1)` implies s/log n->1, then substitution yields the displayed constant. Thus a->1,b->0 and the memories remain distinct.

From the exact row expression, for each large row,

    W_row=[q_row/c] J_3(d)'+O(sqrt(s)),

uniformly for bounded offsets. This follows by expanding its signed quadratic and using N8; the O(sqrt(s)) includes both the linear offset term and the finite completion constant. Using q1/log n->(1,-delta)' and k/log n->e1, while the second upper row stays bounded, proves N3. Finite dual offsets therefore do not change the leading primal direction.

## 6. The actual unrestricted p-comparators and Bregman order

For any required row projection z=W_row d, Holder's inequality gives

    ||W_row||_p>=|z|/||d||_3,

with unique equality at `W_row=z J_3(d)'/c`. Thus the unrestricted lower selected-query SVM, `min ||W||_p` subject to `e1'Wd>=1`, has solution `Wmm=e1 J_3(d)'/c`; unused row2 must be zero at its optimum. Its optimal unit-p-margin is c^(1/3).

The actual limiting lower matrix has both rows, in ratio -delta. Its p-norm is

    (1+delta^p)^(1/p)c^(-1/3),

and its selected logit is one. This proves N4. Denote the two unit-p directions by A=normalized Wmm and B=normalized bad matrix. For psi=||.||_p^p/p and unit arguments,

    D_psi(A,B)=1-<J_p(B),A>
              =1-(1+delta^p)^(-(p-1)/p).

At p=3/2, delta=1/4 this is N5. The reverse argument order instead gives `1-(8/9)^(2/3)`; the two values must not be confused.

At the upper checkpoint, `C_top=h1(h1-h2)'=(a-b)h1 d'` tends to `e1 d'`. Strict Holder equality gives the unique global p-SVM direction `J_3(C_top)/||J_3(C_top)||_p`, which converges to the upper direction in N3. Its optimum c^(1/3) stays positive.

As in the Euclidean example, the bad lower direction also solves the different problem with an extra zero-margin guard `x2'W d<=0`. For fixed q=Wd the objective reduces to ||q||_p; q1>=1 and delta*q1+q2<=0 force the minimizer q=(1,-delta)'. This is an interpretation of the proved limit, not a redefinition of the paper's selected-only comparator.

## 7. Source fidelity and limits

The entrywise potential, update, comparator and normalized Bregman order are those of [Julistiono, Ataee Tarzanagh and Azizan, Definition 5, Algorithm lp-AttGD and Theorem 10](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf). The held released `synthetic-data/tools/optimizers.py` SHA256 is `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`. The paper's key-query convention transposes our matrices and preserves the entrywise potential, mirror map and comparator. The proof uses normalize=False, not normalized mirror descent or gradient flow.

This does not contradict the fixed-input one-layer theorem. It gives a non-Euclidean counterexample to an unqualified layerwise selected-path extension. Fixed identity values/head, two-token paired-sign data, a large finite favorable initialization basin and p=3/2 remain explicit. No non-Euclidean printed-cone compatibility, random-start robustness, generalization failure, or historical novelty is claimed here. The argument is analytic; no new training runs were performed.
