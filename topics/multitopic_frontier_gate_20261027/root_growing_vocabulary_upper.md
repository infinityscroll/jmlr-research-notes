# A vocabulary-explicit upper bound with the full document-length scale

27 October 2026. Root's independent reconstruction of the concentration route proposed by status_claim_check. New source for separate audit. Constants below depend only on fixed K,mu0,kappa0. They do not depend on vocabulary size p, document count n, document length N, alpha or beta.

Dependency: the exact estimator, affine invariance and deterministic maximum-volume lemma in `general_k_upper.md`, SHA256 `56aef7d5bbdad0e97cf092a21d31515d8fda07fa4d40c1926e9976e92e9147c6`. All dimension-sensitive statistical arguments are supplied here.

## 1. Model and theorem

Observe independent X_i~Multinomial(N,A w_i), N>=2. Matrices A and W have stochastic columns; W is deterministic and unknown. Put mu=W1/n, Sigma=WW'/n, d=A mu. Assume

    p>=K>=2, min mu_k>=mu0, sigma_min(A)>=kappa0,
    lambda_min(Sigma)>=beta>0,

and each topic has an exact pure anchor of corpus mass at leastalpha>0. The estimator is given alpha, not beta, W or anchor locations. Its output loss is entrywise-L1 error modulo topic permutation. Define

    a_n=1/sqrt(nNbeta)+1/[beta sqrt(nN(N-1))].

**Theorem.** The estimator of the dependency satisfies

    E loss <= C min{1, [sqrt(p)+log(2p)/sqrt(alpha)] a_n}.   (U1)

Its steps are: form the empirical word frequency dhat and unbiased factorial-pair matrix Chat; take Uhat for the K largest eigenvalues; set Zhat=Chat Uhat; retain rows dhat_j>=alpha/2; maximize the absolute determinant of K normalized rows Zhat_j/dhat_j; reconstruct Zhat times the inverse selected normalized-row matrix; clip negatives and normalize columns. Return fixed stochastic columns on any specified singular/insufficient-row fallback. The output loss is always at most2K.

This is an exact-arithmetic statistical estimator, with potentially expensive maximum-volume search. The theorem retains a fixed lower bound on the UNNORMALIZED singular value of A. In particular it does not automatically cover a regime where every topic-word probability is of order1/p and sigma_min(A) necessarily shrinks.

## 2. A dimension-free Hilbert moment inequality

If independent centered vectors Y_a in a real Hilbert space satisfy ||Y_a||<=B and sum E||Y_a||^2<=v, then for every q>=2,

    ||sum_a Y_a||_(Lq) <= C[sqrt(qv)+qB],             (U2)

where C is universal and ||Z||_(Lq) means (E||Z||^q)^(1/q). The bound is valid for nonidentically distributed vectors and conditionally on fixed coefficients.

Here is a dimension-free justification. For f(x)=cosh(lambda||x||), the Hessian norm is at most lambda^2 f(x): the radial eigenvalue is lambda^2 cosh(lambda||x||), and the transverse eigenvalues are smaller by tanh(t)<=t. Taylor's formula and cosh(a+b)<=cosh(a)e^b give

    E cosh(lambda||sum Y_a||)
      <=exp{v[e^(lambda B)-1-lambda B]/B^2}.

Centering removes each first derivative when conditioning successively. The power series bound k!>=2*3^(k-2) for k>=2 gives the Bernstein tail

    P(||sum Y_a||>sqrt(2vu)+(2B/3)u)<=2e^(-u).

Integrating this tail gives U2, using Gamma(q+1)^(1/q)<=Cq and Gamma(q/2+1)^(1/q)<=Csqrt(q). If B or v vanishes, the zero-vector case is immediate. This is the classical Hilbert Bernstein argument; neither the inequality nor its use as a concentration tool is claimed new.

## 3. Exact pair decomposition and global second moments

Let pi_i=A w_i. Represent each document by independent one-hot tokens Z_it, and write T_it=Z_it-pi_i and epsilon_i=N^(-1)sum_t T_it. Set

    Q_i=[N(N-1)]^(-1) sum_(a!=b) T_ia T_ib',
    V=A Sigma^(1/2),
    E=(1/n)sum_i epsilon_i w_i' Sigma^(-1/2),
    Qbar=(1/n)sum_i Q_i, M=V+E, R=Qbar-EE'.

Exactly as in the dependency,

    Chat=MM'+R.                                     (U3)

All norms in this proof are Euclidean/Frobenius/operator norms as indicated, until the final topic loss. The prevalence bound pi_ij<=d_j/mu0 and identity sum_i w_i'Sigma^(-1)w_i=nK imply

    E||E_j||^2<=C d_j/(nN), E||E||_F^2<=C/(nN).     (U4)

For Gamma_i=Cov(T_it), the exact degenerate-pair identity gives

    E||Q_i,j||^2
      =[Gamma_i,jj tr(Gamma_i)+||Gamma_i,j:||^2]/[N(N-1)]
      <=2pi_ij/[N(N-1)].

The sum over all rows is at most2/[N(N-1)] because tr(Gamma_i)<=1 and tr(Gamma_i^2)<=tr(Gamma_i)^2<=1. Documents are independent and Q_i is centered. Therefore

    E||Qbar_j||^2<=2d_j/[nN(N-1)],
    E||Qbar||_F^2<=2/[nN(N-1)].                     (U5)

There is no p factor in U4 or U5. Rows with d_j=0 are identically zero throughout the observations and error matrices.

## 4. Row moments for the first-order term and frequency

The row E_j is the sum of nN centered K-vectors

    T_it,j Sigma^(-1/2)w_i/(nN).

Their squared norms sum in expectation to at most C d_j/(nN), by U4, and each norm is at most1/(nN sqrt(beta)), since ||w_i||<=1. Hilbert Bernstein yields

    ||E_j||_(Lq)
      <=C[sqrt(q d_j/(nN))+q/(nN sqrt(beta))].       (U6)

Scalar Bernstein likewise gives

    ||dhat_j-d_j||_(Lq)
      <=C[sqrt(q d_j/(nN))+q/(nN)].                 (U7)

The constants in U6 depend only on K,mu0; those in U7 are universal.

## 5. The degenerate row keeps its N-squared variance scale

For each document randomly split its N token positions into disjoint groups of sizes L=floor(N/2) and H=N-L, independently of the tokens. Let a_i and b_i be the centered-token averages in those groups. Averaging over the split, CONDITIONAL on all tokens, gives the exact identity

    Q_i=E_split[(a_i b_i'+b_i a_i')/2].             (U8)

Indeed an ordered pair of distinct positions lies in the first/second groups with probability LH/[N(N-1)]. Symmetrizing gives the same coefficient1/[N(N-1)] for every ordered pair. This holds for odd N as well. Conditional Jensen for the convex function ||.||^q shows that the Lq row norm of Qbar is no greater than the average of the Lq norms of the two symmetrized split expressions. We bound

    S_j=(1/n)sum_i a_ij b_i.

Condition on all first-group tokens. Its remaining nH summands are independent centered Hilbert vectors a_ij T_it/(nH), with absolute norm at most2/(nH) and total conditional second moment at most sum_i a_ij^2/(n^2 H). U2 therefore gives

    (E[||S_j||^q | first groups])^(1/q)
      <=C[sqrt(q)/(n sqrt(H))*(sum_i a_ij^2)^(1/2)
                                                    +q/(nH)].

Now regard (a_1j,...,a_nj) as a single Hilbert vector: it is the sum of nL independent centered scalar-coordinate vectors e_i T_it,j/L. Their squared norms sum to at most

    (1/L)sum_i pi_ij=n d_j/L,

and every summand norm is at most1/L. Applying U2 again gives

    ||(sum_i a_ij^2)^(1/2)||_(Lq)
       <=C[sqrt(q n d_j/L)+q/L].

Taking the unconditional Lq norm in the previous conditional inequality yields

    ||S_j||_(Lq)
      <=C[q sqrt(d_j)/(sqrt(nLH))
                        +q^(3/2)/(nL sqrt(H))+q/(nH)].

Since L,H>=N/3, the last two terms are bounded by Cq^2/(nN). The transposed split expression has the same proof with L and H exchanged. U8 then proves

    ||Qbar_j||_(Lq)
      <=C[q sqrt(d_j)/(sqrt(n)N)+q^2/(nN)].         (U9)

This argument keeps the full factorial-pair statistic. Replacing it by disjoint pairs and pretending those pairs give an N-squared variance improvement would be incorrect. U8's balanced-half identity and its degenerate centering are what retain that scale.

## 6. A global spectral event with dimension-free failure probability

Let

    G0={||E||_op<=kappa0 sqrt(beta)/4,
         ||Qbar||_op<=kappa0^2 beta/32}.

On this event, sigma_min(M)>=3kappa0 sqrt(beta)/4 and

    ||R||_op<=3kappa0^2 beta/32.

Therefore lambda_K(Chat)>0. For H0=M'Uhat,

    H0'H0>= [sigma_min(M)^2-2||R||_op] I
           >=3kappa0^2 beta I/8.

The analysis-only invertible coordinate map

    T=H0^(-1) Sigma^(-1/2)diag(mu)

gives exactly Zhat T=A diag(mu)+D. Since ||E||_op is at most a constant times sqrt(beta), the EE' row of R can be absorbed into the first-order row error. Thus, on G0,

    ||D_j||<=delta_j,
    delta_j=C[||E_j||/sqrt(beta)+||Qbar_j||/beta].    (U10)

Define the right-hand side on all outcomes. U4-U5 imply

    E delta_j<=C sqrt(d_j) a_n,
    sum_j E delta_j<=C sqrt(p) a_n.                 (U11)

Markov's inequality applied to the dimension-free global second moments also gives

    P(G0^c)<=C a_n.                                 (U12)

As in the dependency, the coordinate map does not define an oracle estimator: every candidate normalized-row determinant is multiplied by the same det(T), and the right factors cancel exactly in reconstruction.

## 7. A single normalized error controls the entire anchor search

Define

    Z=max_j [delta_j+|dhat_j-d_j|]/(d_j+alpha).

Take q=2+log(p). Then p^(1/q)<=e. For a finite collection, the Lq norm of its maximum is at most p^(1/q) times the largest individual Lq norm. Using U6-U9, beta<=1, and

    sqrt(d)/(d+alpha)<=1/(2sqrt(alpha)),
    1/(d+alpha)<=1/alpha,

gives

    E Z <=C[log(2p) a_n/sqrt(alpha)
                           +log^2(2p)/(nN alpha beta)]. (U13)

The use of beta<=1 is justified by trace(Sigma)<=1 for stochastic mixture columns. All logarithms are natural; replacing q by log(2p) changes only universal constants because p>=2.

For sufficiently small z0 depending only on K, the event Z<=z0 provides all the screening facts formerly obtained by a fixed-p union bound. If d_j>=alpha, then |dhat_j-d_j|<=2Z d_j, so every true anchor is retained. If d_j<alpha/4, then dhat_j<=alpha/4+(5alpha/4)Z<alpha/2, so it is excluded. Every retained row therefore has d_j>=alpha/4, d_j+alpha<=5d_j, and dhat_j>=d_j/2 when z0<=1/10.

On G0 intersect {Z<=z0}, each retained row in analysis coordinates satisfies

    ||Zhat_j T/dhat_j - A_j diag(mu)/d_j||
       <=2[delta_j+|dhat_j-d_j|]/d_j <=10Z.          (U14)

The population rows on the right are stochastic K-vectors and contain all K coordinate vertices through the anchors. The deterministic maximum-volume lemma from the dependency therefore returns a matrix within C_K Z of a permutation, with uniformly bounded inverse. That lemma is a statement in K-dimensional simplex geometry; its constants do not depend on the number p of candidate rows. Thus reconstruction, clipping and column normalization give

    loss<=C[sum_j delta_j+Z]                         (U15)

on this good event. The normalization constant depends on mu0, not p.

## 8. Expected loss and absorption of the linear Bernstein remainder

Use loss<=2K on the complement, U12, Markov's inequality for Z, and U11-U15. Then

    E loss<=C{[sqrt(p)+log(2p)/sqrt(alpha)]a_n
                             +log^2(2p)/(nN alpha beta)}.

Let r=[sqrt(p)+log(2p)/sqrt(alpha)]a_n. Since a_n>=1/sqrt(nNbeta), the last term is at most r^2. For r<=1 it is absorbed into r; for r>1 the deterministic loss bound applies. This proves U1. No linear concentration term has been discarded merely because it looked lower order.

## 9. What this changes and what it retains

The proof makes the vocabulary cost explicit: summing full-row reconstruction errors contributes sqrt(p), while searching for sufficiently frequent simplex vertices contributes at most log(2p)/sqrt(alpha). The first-order and degenerate-pair terms retain their different beta powers and full N dependence. The estimator and its affine maximum-volume geometry are unchanged.

This result does not eliminate exact anchors, known alpha, fixed K, strong unnormalized topic geometry or exact arithmetic. It is not a computational improvement or a refutation of a published sparse-topic theorem. A separate lower bound is needed to call it near-minimax; a primary-source comparison is needed to assess novelty. This source does not replace either obligation with the concentration calculation.
