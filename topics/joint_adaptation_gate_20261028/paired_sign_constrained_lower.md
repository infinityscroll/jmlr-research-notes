# The price of adapting to rare anchors with weak document diversity

28 October 2026. New proof by root, awaiting independent audit. This extends
the earlier fixed-diversity constrained-risk result. It is not an ordinary
minimax lower bound for a supplied anchor strength, and no historical novelty
claim is made. All statements concern the original multinomial counts.

## 1. Statement and quantifiers

Use the common class in `../anchor_selection_frontier_20261028/MATCHED_ALL_N_FRONTIER.md`,
with K=2, q=1/2, any fixed p>=12, weak-q radius four, and its fixed topic
geometry and interior-mixture bounds. Write C(alpha,beta) for this class.
The anchor bound alpha concerns corpus frequency, and beta is a lower bound
on lambda_min(WW'/n). W remains an unknown deterministic nuisance parameter.
Let n be even, n>=128, N>=2, and 0<beta<=1/4096. Put

    G = N(N-1) beta^2 / [1+(N-1)beta],   T=nG,
    a = 1/sqrt(nN beta)+1/[beta sqrt(nN(N-1))].          (1)

Thus T^(-1/2)<=a<=sqrt(2)T^(-1/2). Fix alpha_s=1/128.
Consider any sequences (n,N,beta) with T tending to infinity. Suppose an
estimator sequence, NOT supplied alpha, has the uniform strong-anchor bound

    sup_{C(alpha_s,beta)} E d_topic(Ahat,A)<=C T^(-1/2). (2)

It may even be supplied beta. Then, for every positive alpha tending to zero,

    liminf [sup_{C(alpha,beta)} E d_topic(Ahat,A)] /
      min{1,sqrt(log(1/alpha)/(T alpha))} >= c>0.        (3)

The fixed c does not depend on any of n,N,beta,alpha or their sequences.
The point after which the limit bound holds may depend on the fixed C in (2).
Since p is fixed, the sparse-tail upper envelope is O(a), and along alpha->0
the anchor term dominates. A uniform adaptive upper with anchor term
a sqrt(log(2+1/alpha)/alpha) therefore matches this constrained lower order.
This is a conditional sharpness statement about that upper, not its proof.

The null sequence below belongs to the strong class even though it also has
rare anchors. This is why (2) must be uniform over the strong class. No claim
that an estimator can infer the exact alpha of a matrix is involved.

## 2. Two topic matrices, all observations positive

For sufficiently small alpha<=1/256 set

    v=2alpha, v0=1/8, zeta=1/4,
    eps_l=(1/32)2^(-2(l+6)), l=1,...,p-7,
    e=sum_l eps_l, b=5/8-v-e,
    B=[[3/4,1/4],[1/4,3/4]],
    S_theta=[[1-theta,theta],[theta,1-theta]], 0<theta<=1/16.

A0 consists of rows zeta(1,1), v0 I_2, v I_2, b B, and the p-7
positive common rows eps_l(1,1). A1 replaces v0 I_2 by v0 S_theta
and b B by b B S_theta, leaving all other rows unchanged. Both have
stochastic columns. Since b>1/2, the common block alone gives
sigma_min(A_l)>=b(1-2theta)/2>7/32, and the shared row gives every
entry of A_l'A_l at least 1/16. These exceed the common class bounds.

The column sum of square roots is strictly less than

    1/2+sqrt(1/8)(1+1/4)+sqrt(1/128)
        +sqrt(2*5/8)+(1/sqrt(32))2^(-6)<4.

Consequently every column has weak-1/2 radius at most four: j sqrt(A_(j))
is bounded by that sum. This argument includes arbitrary interleaving of the
rare and padding rows, and applies to both matrices.

The identity-permutation distance is

    Delta=(4v0+2b)theta >=(3/2)theta.                    (4)

The swapped distance is (4v0+2b)(1-theta)+4v, which is larger. Hence
(4) is exactly the topic-permutation quotient distance, not just a labeled
matrix separation.

## 3. Paired signs make every nuisance matrix admissible

For h=1,...,n/2 draw independent fair signs xi_h only for the lower-bound
prior. With u=(1/2,1/2)' and f=(1,-1)', set

    w^0_{2h-1}=u+sqrt(beta)xi_h f,
    w^0_{2h}=u-sqrt(beta)xi_h f,
    w^1_i=S_theta^(-1)w^0_i.                            (5)

For EVERY realization of these signs, the mean mixture is u and

    W0 W0'/n = uu'+beta ff',
    lambda_min(W0 W0'/n)=2beta,
    lambda_min(W1 W1'/n)=2beta/(1-2theta)^2.             (6)

The other eigenvalue is 1/2. The displayed beta range guarantees the
contrast eigenvalue remains the smaller one. All mixture coordinates are
at least 1/2-(8/7)sqrt(beta)>1/8. Thus every constituent is admissible,
with no conditioning, exceptional prior mass or approximation in (6).
Conditional on W, documents remain independent as required by the model;
dependence between two documents arises only after mixing over the nuisance
prior for the lower bound.

A0 has strong anchors of corpus mass v0/2=1/16>=alpha_s. In A1 the
transformed strong and common rows are positive in both topics; the rare
rows remain the only pure anchors and have corpus mass v/2=alpha. All
observable word probabilities, including the padding, are strictly positive.
Therefore the priors are entirely supported on C(alpha_s,beta) and
C(alpha,beta), respectively. The fixed positive padding is optional for
class membership but makes the observation-support statement explicit.

## 4. A second-moment bound uniform in N and beta

Write d=A0u=A1u for the common baseline word distribution. Nonrare word
probabilities cancel exactly between A0W0 and A1W1. In one document of a
pair, the null relative contrasts z_j (probability d_j(1+xi z_j)) are
+/-r on the strong and rare pairs, +/-r/2 on the common pair, and zero
on the shared and padding rows, where r=2sqrt(beta). In the other document
all contrast signs are reversed. The alternative changes only the rare
pair's contrast to (1+kappa)z_j, where kappa=2theta/(1-2theta).
The rare pair has baseline total probability v=2alpha.

Let Q0,Q1 be the observed laws of one two-document block after averaging its
fair sign. We prove

    1+chi^2(Q1,Q0) <= exp(C alpha theta^2 G).             (7)

Here and below C denotes a fixed numerical constant which can increase.

### Short-information case: N beta<=1

Under the product baseline d^N tensor d^N, the null density is

    F_z = [product_{t in doc1}(1+z(X_t))
                 product_{t in doc2}(1-z(X_t))
          +product_{t in doc1}(1-z(X_t))
                 product_{t in doc2}(1+z(X_t))]/2.

Set L=2N and g_L(s)=((1+s)^L+(1-s)^L)/2. Since E_d z=0,
independence of the baseline tokens gives the EXACT identity

    E_d F_z F_w=g_L(<z,w>_d).                           (8)

The opposite contrast in the second document does not change its inner
product: (-z)(-w)=zw. This is a single block experiment, not independent
overlapping token pairs. The likelihood is symmetric within each document,
so all these identities hold for the sufficient pair of count vectors.

Put V=<z,z>_d<=r^2=4beta and u_r=v r^2=8alpha beta.
The alternative's second-moment numerator is, exactly,

    E_d(F_1-F_0)^2 =
      g_L(V+(2kappa+kappa^2)u_r)
          -2g_L(V+kappa u_r)+g_L(V).                  (9)

All arguments s in (9) are in [0,(1+kappa)^2r^2]. Under N beta<=1
and theta<=1/16, Ls is bounded by a numerical constant. Hence
|g_L''(s)|<=C L(L-1), and |g_L'(s)|<=C L(L-1)s because g_L'(0)=0.
Split (9) into a step of size kappa^2 u_r and a second difference of
size kappa u_r. It is at most

    C L(L-1) kappa^2 (u_r beta+u_r^2)
        <= C alpha theta^2 N(N-1) beta^2.              (10)

The comparison L(L-1)<=6N(N-1) uses N>=2. The null density has the
pointwise lower bound

    F_0=product_t sqrt(1-z_t^2) cosh(H)
           >=exp(-C L beta)>=c0>0.                    (11)

This follows from |z_t|<=r, r^2<=1/1024 and L beta<=2; H has the
appropriate plus/minus document signs. We divide the NONNEGATIVE square
in (9) by (11), obtaining chi^2(Q1,Q0)<=C alpha theta^2 N(N-1)beta^2.
Since 1+(N-1)beta<=2 in this regime, this proves (7).

### Long-information case: N beta>1

Reveal the block's sign xi, using the same fair prior under both hypotheses.
Do NOT reveal W. The one-token null-relative chi-square is exactly

    v kappa^2 r^2/(1-r^2) <= C alpha theta^2 beta.        (12)

It is independent of xi and of the document's sign reversal. For 2N tokens,
the full revealed experiment therefore has second moment at most
exp(C N alpha theta^2 beta). Removing xi cannot increase chi-square,
by conditional Jensen on the likelihood ratio. Finally (N-1)beta>1/2
when N beta>1 and N>=2, so G>=N beta/3. This proves (7) here too.

The independent prior signs make the n/2 observed blocks independent.
Writing P_l for the resulting FULL count-experiment laws and Q=dP1/dP0,
we therefore have

    E_0 Q^2 <= exp(C0 T alpha theta^2)                  (13)

for a fixed C0. All class, positivity and distance claims are deterministic
for every constituent nuisance W. There is no conditioning loss that could
overwhelm the strong-class risk in (2).

## 5. Constrained-risk argument

Let ell=log(1/alpha), and choose a fixed tau>0 so small that
tau<=1/16 and epsilon=C0 tau^2<1/4. Take

    theta=tau min{1,sqrt(ell/(T alpha))}.                (14)

Let E be the event d_topic(Ahat,A1)<Delta/3. The quotient-metric triangle
inequality and the prior average of (2) give

    P0(E)<=3C/(2Delta sqrt(T))<=C'/(theta sqrt(T)).      (15)

Cauchy--Schwarz with (13) yields

    P1(E)^2 <= C' exp(epsilon min(T alpha,ell))
                                  /(theta sqrt(T)).   (16)

This tends to zero for EVERY alpha->0 along T->infinity. If T alpha>=ell,
the right side is at most C alpha^(1/2-epsilon)/sqrt(ell). If T alpha<ell
and T alpha<=1, it is at most C/sqrt(T). In the remaining case,
1<T alpha<ell, one has alpha>1/T and ell<log(T), giving C T^(epsilon-1/2).
All three bounds tend to zero; no relation between n,N,beta beyond T->infinity
is imposed. Thus the alternative average risk is at least

    (Delta/3)(1-o(1)) >= (theta/2)(1-o(1)).              (17)

An average over admissible deterministic W cannot exceed the supremum risk.
Substituting (14) proves (3), for example with limiting constant tau/2.

## 6. Increment and limits

The previous fixed-beta lower used two deterministic document groups and
the revealed-token scale nN. Simply substituting T in that proof would be
invalid. The paired latent signs in (5) keep the nuisance covariance exact
while hiding the document contrasts; (8)--(11) supply the weak-information
scale and (12) supplies the long-document scale. They are the additional
statistical argument, using classical likelihood and constrained-risk tools.

This does not enlarge the lower theorem to growing K, all q, unknown K,
nonseparable topics, confidence sets, practical efficiency or arbitrary loss.
It is a matching adaptation-price theorem on a fixed-p, K=2, q=1/2 subclass.
It does not by itself establish the adaptive upper, publication priority,
external verification, Lean formalization or a newsworthy breakthrough.
