# The document-length frontier for every fixed topic count

27 October 2026. New analytic candidate. No frozen source was edited. This source proves an upper bound; a matching general-K lower embedding and external novelty assessment are separate requirements.

## 1. Model and claim

Fix integers p>=K>=2 and constants mu0,kappa0>0. Observe independent

    X_i ~ Multinomial(N,A w_i), i=1,...,n, N>=2.

The p-by-K topic matrix A and K-by-n mixture matrix W have stochastic columns. The mixtures are deterministic and unknown. Define

    mu=W1/n, Sigma=WW'/n, d=A mu, C=A Sigma A'.

Assume

    min_k mu_k >= mu0,
    sigma_min(A) >= kappa0,
    lambda_min(Sigma) >= beta>0,

and each topic has a pure anchor whose corpus frequency d_j is at least alpha>0. Anchor indices, A, W, mu and beta are unknown. The estimator is given alpha. Exact anchors are required; all constants below may depend on p,K,mu0,kappa0, but never on n,N,alpha,beta. Additional fixed overlap, interior-mixture or weak-sparsity restrictions only reduce the class.

**Theorem.** The explicit estimator in Section 2 obeys

    E min_P ||Ahat-AP||_1
      <= C0 min{1,
           1/sqrt(nN alpha beta)
            +1/[beta sqrt(nN(N-1)alpha)]}.                 (G1)

Here the norm is entrywise L1 and P ranges over K-by-K permutation matrices. Thus the two-topic upper rate extends to every fixed K without an additional inverse-beta factor. The proof uses the raw unbiased pair moment: covariance centering is not necessary once its perturbation is measured in an anisotropic, freely changeable coordinate system.

This is an exact-arithmetic statistical estimator. It does not claim a growing-p/K rate, unknown-alpha adaptation, computational optimality, or historical priority.

## 2. Observable estimator

Compute

    dhat=(1/n) sum_i X_i/N,
    Chat_jr=(1/n) sum_i X_ij(X_ir-1{j=r})/[N(N-1)].

Chat is real symmetric and has row sums dhat. Let Uhat be an orthonormal basis for the eigenspace corresponding to its K largest eigenvalues, with deterministic tie rules. If the Kth eigenvalue is nonpositive, return fixed stochastic columns. Otherwise set

    Zhat=Chat Uhat,       J={j:dhat_j>=alpha/2}.

If |J|<K, return the fallback. Among all ordered K-tuples of distinct indices in J, select one, I=(i_1,...,i_K), maximizing the absolute determinant of

    Rhat_I=diag(dhat_I)^(-1) Zhat_I.                     (G2)

Use a fixed tie rule. If its determinant is zero, return the fallback. Form

    Xhat=Zhat Rhat_I^(-1).                              (G3)

Clip negative entries of Xhat to zero and normalize each column to mass one. A zero clipped column is replaced by a fixed probability vector. All outputs are stochastic, so loss is always at most 2K.

Multiplying Zhat on the right by ANY invertible matrix leaves the selected tuple unchanged and leaves Xhat unchanged: every candidate determinant is multiplied by the same nonzero determinant, while the right factors cancel in G3. This elementary affine invariance is the key to the conditioning rate. The estimator itself never computes the population coordinate change used below.

## 3. Exact factor-plus-remainder decomposition

Write pi_i=A w_i, epsilon_i=X_i/N-pi_i. With independent categorical tokens Z_it within document i, put

    Q_i=[N(N-1)]^(-1) sum_(a!=b)
                       (Z_ia-pi_i)(Z_ib-pi_i)'.

The exact pair identity is

    U_i=pi_i pi_i'+pi_i epsilon_i'+epsilon_i pi_i'+Q_i.

Since Sigma is positive definite, define the symmetric positive definite square root and

    V=A Sigma^(1/2),
    E=(1/n) sum_i epsilon_i w_i' Sigma^(-1/2),
    Qbar=(1/n) sum_i Q_i,
    M=V+E,             R=Qbar-EE'.

Then, without approximation,

    Chat=VV'+VE'+EV'+Qbar=MM'+R.                        (G4)

No iid distribution on W or Gaussian approximation is used.

The prevalence assumption implies pi_ij<=d_j/mu0. Independence and centering give

    E||E_j||_2^2
      <=(1/n^2N) sum_i pi_ij w_i' Sigma^(-1)w_i
      <=K d_j/(mu0 nN),

    E||E||_F^2 <=K/(mu0 nN).                            (G5)

The identity sum_i w_i' Sigma^(-1)w_i=nK is exact. The degenerate-pair covariance calculation gives, including j=r,

    Var(Q_i,jr)
      =[Var(T_j)Var(T_r)+Cov(T_j,T_r)^2]/[N(N-1)]
      <=2 pi_ij/[N(N-1)],        T=Z-pi_i.

Thus

    E||Qbar_j||_2 <=C sqrt(d_j/[nN(N-1)]).

Moreover ||(EE')_j||_2<=||E_j||_2||E||_F. Cauchy–Schwarz and G5 imply

    E||(EE')_j||_2<=C sqrt(d_j)/(nN).

Because 1/(nN)<=1/sqrt(nN(N-1)),

    E||R_j||_2<=C sqrt(d_j)/sqrt(nN(N-1)),
    E||R||_op<=C/sqrt(nN(N-1)).                         (G6)

Constants absorb fixed p. Finally

    E|dhat_j-d_j|<=sqrt(d_j/(nN)).                       (G7)

A zero-mass row is identically zero in all data, factors, and errors.

## 4. A coordinate change with only the necessary beta powers

Define the analysis-only event

    E0={||E||_op<=kappa0 sqrt(beta)/2,
        ||R||_op<=kappa0^2 beta/16}.                    (G8)

On E0, sigma_min(M)>=kappa0 sqrt(beta)/2. Weyl's inequality gives

    lambda_K(Chat)>=sigma_min(M)^2-||R||_op>0.

Let H=M'Uhat. Because the columns of Uhat are eigenvectors for the K largest eigenvalues,

    H'H=Uhat'MM'Uhat
       =Uhat'Chat Uhat-Uhat'R Uhat
       >=[sigma_min(M)^2-2||R||_op]I
       >=kappa0^2 beta I/8.                            (G9)

Therefore H is invertible, even though its orientation and singular values are unknown to the estimator. Define the analysis-only invertible matrix

    T=H^(-1) Sigma^(-1/2) diag(mu).

Multiplication of G4 by Uhat and then T gives the exact identity

    Zhat T=A diag(mu)+D,
    D=E Sigma^(-1/2)diag(mu)
        +R Uhat H^(-1)Sigma^(-1/2)diag(mu).              (G10)

Consequently, on E0,

    ||D_j||_2 <= delta_j
      :=C[||E_j||_2/sqrt(beta)+||R_j||_2/beta].          (G11)

The right side is defined on every outcome. Equations G5–G6 yield

    E delta_j <=C sqrt(d_j) a_n,
    a_n=1/sqrt(nN beta)+1/[beta sqrt(nN(N-1))].          (G12)

The estimator may be analyzed after the right transformation T because of G2–G3 invariance. Crucially, no orthogonal Procrustes alignment is needed. Such an alignment can introduce a spurious global rotation-error term and an extra inverse square root of beta.

Markov's inequality, using E||E||_op<=sqrt(E||E||_F^2), and G6 give

    P(E0^c)<=C a_n.                                    (G13)

These bounds need not be smaller than one; the final bounded-loss argument covers the uninformative regime.

## 5. Screening and normalized row error

Let Jstar={j:d_j>=alpha/4}. Let Escreen be the event that

    |dhat_j-d_j|<=d_j/2 for every j in Jstar,
    no j outside Jstar has dhat_j>=alpha/2.

Then Escreen retains every designated anchor of mass at least alpha, J is contained in Jstar, and dhat_j>=d_j/2 for j in J. By G7 and Markov's inequality,

    P(Escreen^c)<=C/sqrt(nN alpha).                     (G14)

For false inclusions use dhat_j-d_j>=alpha/4 and d_j<alpha/4. Fixed p is essential to the constants here.

For d_j>0 define the population barycentric row

    P_j=A_j diag(mu)/d_j.

P_j is nonnegative and sums to one. Each topic's pure anchor has P_j equal to its corresponding coordinate vector. On E0 intersect Escreen,

    ||(Zhat_j T)/dhat_j-P_j||_2
      <=2[delta_j+|dhat_j-d_j|]/d_j <=rho,               (G15)

where rho is the maximum of the middle expression over all j in Jstar. Define rho=0 if Jstar is empty (the assumptions actually prevent that). It is a nonnegative random variable on all outcomes, and

    E rho<=C a_n/sqrt(alpha).                          (G16)

Here beta<=1, so a_n dominates 1/sqrt(nN). Selection and the empirical eigenspace cause no conditioning problem: the bounds hold simultaneously for all rows and every relevant coordinate transformation on E0.

## 6. Max-volume recovery at linear error

We use the following finite-dimensional deterministic lemma.

**Lemma.** Suppose rows p_j lie in the probability simplex in R^K and include every coordinate vector. Suppose ||y_j-p_j||_2<=rho. If Bhat consists of the K rows y_j of maximal absolute determinant, then, for rho<=c_K, there is a permutation matrix Pi such that

    ||Bhat-Pi||_F<=C_K rho,
    ||Bhat^(-1)||_op<=C_K.                             (G17)

**Proof.** The designated coordinate rows give a candidate determinant at least 1-C_K rho, by the polynomial determinant expansion. All perturbed rows are uniformly bounded for rho<=1. The same expansion shows that the unperturbed selected-row matrix B has |det B|>=1-C_K rho. Every row of B is stochastic and therefore has Euclidean norm at most one. Hadamard's inequality implies each row norm is at least |det B|. Hence each row has an entry at least its squared norm, and so at least 1-C_K rho; its L1 distance from that coordinate vector is at most C_K rho. Those dominant coordinates must be distinct. If two coincide, subtract those two rows in the determinant; the difference has norm at most C_K rho, and all other row norms are at most one, giving |det B|<=C_K rho, a contradiction for sufficiently small rho. Thus B is within C_K rho of a permutation matrix. The same holds for Bhat, and the Neumann-series bound gives its inverse estimate. This proof requires no separation gap between anchor and nearly-anchor rows. End proof.

Apply the lemma after the right transformation T. Determinant maximization in G2 selects exactly the same tuple in these coordinates. On E0 intersect Escreen intersect {rho<=c_K}, the transformed selected-row matrix Bhat=Rhat_I T satisfies G17. From G3 and G10,

    Xhat=(A diag(mu)+D) Bhat^(-1).

Thus, up to the corresponding column permutation,

    ||Xhat-A diag(mu)Pi'||_1
       <=C[sum_j delta_j+rho].                         (G18)

Indeed the total entrywise mass of A diag(mu) is one; its multiplication by Bhat^(-1)-Pi' costs at most C rho. The remaining term is bounded by the row errors and the inverse bound.

Each target column A diag(mu)Pi' has mass at least mu0. Clipping negatives cannot increase L1 distance to that target. Normalizing a nonnegative approximate column of target mass mu_k multiplies its error by at most 2/mu_k, including the specified zero-column fallback (then the raw error is at least mu_k). Therefore G18 also bounds the final topic loss up to a constant depending on mu0.

## 7. Expected loss and what has changed

Let G=E0 intersect Escreen intersect {rho<=c_K}. Equations G13–G16 imply

    P(G^c)<=C a_n/sqrt(alpha).                         (G19)

Integrate G18 without conditioning its error terms on G, and use loss<=2K on G^c. G12 and G16 give

    E loss <=C a_n/sqrt(alpha).

Combine with the deterministic loss bound to prove G1.

The proof is uniform over arbitrary deterministic mixture matrices with the displayed spectrum and prevalence floors. It does not require equal nonzero centered-covariance eigenvalues, a rank-one contrast, or a bounded condition number for Sigma beyond the explicit beta floor. No extra spectral parameter was needed for this fixed-dimensional upper bound.

The first term in G1 comes from the anisotropic first-order factor error E, after one inverse square root of Sigma. The second term comes from the degenerate pair remainder R and has two inverse-square-root factors. Consequently the short/long transition remains (N-1)beta of constant order. This is a mathematical generalization of the preceding K=2 upper bound, not by itself a novelty or minimax claim. Its mechanisms—moment factorization, affine anchor geometry, maximum-volume selection, and degenerate U-statistics—are classical. A matching general-K lower embedding and primary-theorem comparison still determine the research significance.
