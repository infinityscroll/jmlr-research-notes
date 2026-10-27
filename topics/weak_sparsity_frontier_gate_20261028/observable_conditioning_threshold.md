# Removing the mixture-conditioning input from the sparse upper estimator

28 October 2026. A separate corollary of `weak_sparsity_joint_upper.md`, SHA256 `fb24214c2aab2d510f1182cc3000489a0d117f1fe5f3e7aa4d9ee3db81a83ab9`. The observation by root is that the already-computed Kth empirical pair-moment eigenvalue estimates the relevant scale up to fixed factors on the same spectral event. No unbiasedness, independent tuning sample, or adaptive minimax priority is claimed.

## 1. Observable algorithm and conclusion

Use exactly the model and notation of W1--W3 in the dependency. Keep the known-alpha anchor-selection and raw reconstruction steps. Let

    lambda_hat=lambda_K(Chat),
    A(t)=1/sqrt(nN t)+1/[t sqrt(nN(N-1))], t>0.

If lambda_hat<=0, return fixed stochastic columns. Otherwise replace the known-beta output threshold a^2 by the observable threshold

    tau_hat=A(lambda_hat)^2.                              (O1)

Threshold raw reconstructed rows using dhat_j>=tau_hat, then clip and normalize exactly as before. This estimator needs neither beta nor q nor a sparsity radius. It still uses K and alpha, and retains all the original structural assumptions.

**Corollary.** Write b=lambda_min(Sigma), the actual unknown mixture eigenvalue. The observable estimator satisfies

    E loss<=C min{1, L_alpha*A(b)/sqrt(alpha)+H_(A(b))(d)}. (O2)

In a class specified only by b>=beta, monotonicity A(b)<=A(beta) gives W3 with a=A(beta). All weak-q consequences W17 therefore hold for this same estimator, without beta or q input. Constants depend only on K,mu0,kappa0.

## 2. Relative spectral comparison on the existing good event

Define E,Qbar,M,R exactly as in the imported pair decomposition, and define G0 using the actual b:

    ||E||_op<=kappa0 sqrt(b)/4,
    ||Qbar||_op<=kappa0^2 b/32.

The proof of W4 and the dependency's U12 gives P(G0^c)<=C A(b). On G0,

    sigma_K(M)>=(3kappa0/4)sqrt(b),
    ||R||_op<=3kappa0^2 b/32.

For the upper comparison, each column of A has Euclidean norm at most one, hence ||A||_op<=sqrt(K). If v is a unit eigenvector for b, then ||A Sigma^(1/2)v||<=sqrt(Kb); therefore

    sigma_K(A Sigma^(1/2))<=sqrt(Kb),
    sigma_K(M)<=(sqrt(K)+kappa0/4)sqrt(b).

Since Chat=MM'+R and M has K columns, Weyl's eigenvalue inequality gives

    c0 b<=lambda_hat<=C0 b,                              (O3)
    c0=15kappa0^2/32,
    C0=(sqrt(K)+kappa0/4)^2+3kappa0^2/32.

In particular the observed nonpositive-eigenvalue fallback cannot occur on G0. Set

    cA=min{C0^(-1/2),C0^(-1)},
    CA=max{c0^(-1/2),c0^(-1)}.

Comparing separately the two positive terms defining A(t) gives on G0

    cA A(b)<=A(lambda_hat)<=CA A(b),
    cA^2 A(b)^2<=tau_hat<=CA^2 A(b)^2.                  (O4)

These are deterministic comparisons on the good event, not a claim that lambda_hat is an unbiased or uniformly accurate estimator outside it.

## 3. Random thresholding requires no independence

Repeat the dependency's entire anchor argument with actual b in the analysis. Write a_b=A(b), and let G be the intersection of G0 with its anchor events. Its raw reconstruction still satisfies W11, and the second moments satisfy E delta_j^2<=C d_j a_b^2. On G, O4 gives the pointwise indicator bounds

    1{dhat_j>=tau_hat}<=1{dhat_j>=cA^2 a_b^2},
    1{dhat_j<tau_hat}<=1{dhat_j<CA^2 a_b^2}.             (O5)

For retained errors, unconditional Cauchy--Schwarz and frequency Markov now give

    E[1_G delta_j 1{dhat_j>=tau_hat}]
      <=C a_b sqrt(d_j) min{1,sqrt(d_j)/(cA a_b)}
      <=C min{d_j,a_b sqrt(d_j)}.                        (O6)

For omitted mass, if d_j<=2CA^2 a_b^2 then d_j is at most a constant times min{d_j,a_b sqrt(d_j)}. If d_j>2CA^2 a_b^2, the scalar frequency variance and O5 give

    E[1_G d_j 1{dhat_j<tau_hat}]<=4/(nN)
      <=C a_b sqrt(d_j),                               (O7)

because a_b>=1/sqrt(nN). Constants may depend on cA,CA and hence only on the fixed geometry parameters. Thus W14--W15 hold with unchanged instance profile up to fixed constants. The threshold uses the same data as every other step, and the proof never conditions on it or assumes independence.

The remainder of W13--W15, clipping/normalization, bad-event control, and quadratic-remainder absorption is unchanged. For a_b>=1 the deterministic loss bound directly proves O2; the algorithm need not detect this population case. This proves the corollary.

## 4. Scope

This removes one input from the new joint upper bound, not exact anchors or known alpha. Its relative eigenvalue event depends on the fixed unnormalized topic singular-value floor. It should not be transferred to a diffuse-topic class where that floor vanishes. Earlier fixed-conditioning unknown-alpha/unknown-q results remain separately credited; joint adaptation to unknown alpha together with shrinking b is not supplied here.
