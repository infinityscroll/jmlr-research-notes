# Independent hostile audit: rank-100 practical-default instability

27 October 2026. Reviewer: the independent `hcm_adversarial_boundary` agent. No producer source or result was edited. No paid computation, cloud launch, contact, or publication occurred.

**Verdict: no blocking mathematical or source-interface error found in the bound theorem, within its explicitly stated exact-arithmetic and ideal-independent-Gaussian scope.** This is not an audit of infinite-time floating-point execution, typical data, generalization, historical novelty, or JMLR Theorem 17 applicability.

## 1. Bound artifacts and review independence

The reviewed `theorem.md` is SHA256 `1b1cb234971e70130c0072aacac7988c2112ae04ddcd68703847f088f952e57b`.

Producer artifacts read in full:

| File | SHA256 |
|---|---|
| `general_block_operator.py` | `eecb2c18bb1ec6fc5d443d41bbd937190e1ecdd3cf54e1b3f4adf3dc8aa2777e` |
| `check_rank100_mean_step.py` | `7b7633766c127720c6f74a3eafa72de7d89e788de8b279aff965478e9d6dbfe1` |
| `rank100_mean_step_certificate.json` | `cb4c1f8a0ed7b519784211d1962d1a339d4b0685fcaa25e2978759f620d997ad` |

I wrote a separate dense rational implementation, `independent_dense_and_certificate_check.py`, SHA256 `173a8ba6356bc69d76fa70a9a6fc63503aa8d6ac39e8425c9cbae36eadb14b27`. Its result `independent_dense_certificate.json`, SHA256 `514d769d9b21338cbee2acfc49eb00bb018a1f5febe421706df2ba7f4efcea90`, passed 706 assertions in about 1.51 local CPU seconds. It verifies 48 dense covariance images, 108 saved PSD coefficient matrices, 116 polynomial identities, 12 exact power-formula cases, and a deterministic-initialization permutation identity.

The dense implementation does not reuse the producer's row coefficients or Sherman--Morrison inverse. It forms the full native state matrix, computes each selected block inverse by rational Gauss--Jordan, enumerates every selected subset, and compares the result with the producer's reduction. The saved-certificate verifier does not invoke the producer's Vandermonde solver or coefficient-generation code. It evaluates the already saved Bernstein coefficients on a full unisolvent tensor grid and extra points.

## 2. Released source and the claimed configuration

The local official checkout is at commit `61cdb69cb11adea48ecb13c823ad654d46dc15df`. I read these actual source files:

| Relative to `../official/fast_krr/` | SHA256 |
|---|---|
| `opts/askotchv2.py` | `dead2dc97aed91e485133dc39e86f1980053b3372d67ca4540612366750f3cad` |
| `opts/utils/general.py` | `17f5acbe8e693579e302ca5ac5dd18145b4a5b6f2878525f518098285dce7f51` |
| `opts/utils/bcd.py` | `18d1c33169965f9dc3cb2ea8458d0da5795a9ed96d4ebae2ab1a376dfc6ea17d` |
| `preconditioners/nystrom.py` | `f8470b8ac5d20bf0d86a35815970e4bb92d34886b24e02290606329f9e844f74` |
| `models/full_krr.py` | `3b853b5fff803ab20796cf5c0373c882afcb7fe2ef03065343f868ee76dfc1e6` |
| `kernels/rbf.py` | `394b4adce1e07a760ff1d55683d2697c4ad7370dfb48948ef1771194de0887c8` |

The [paper](https://www.jmlr.org/papers/volume27/25-0385/25-0385.pdf), Section 2.5/Table 3, lists b=n/100, rank 100, uniform sampling, mu=lambda, nu=n/b, and damping lambda plus the smallest retained eigenvalue. The local extracted paper `../result_assessment_sources/askotch.txt` is SHA256 `d62f7c61a8ae0472f976ae64bca925e2d1261eed69d84af6a2353e330b50db93`. I checked the recommendations, the preceding practical ten-iteration description, and Theorem 17 directly.

For n=10000,b=100, all listed Table-3 settings match. The native alpha is s/(1+s), beta=1-s, and gamma=1/(nu*s), giving s=1e-5 and gamma=1000. Subtracting the exact solution u from both stored state vectors gives the theorem's error update. The source regularizer uses stored w rather than its evaluation argument, giving precisely the stale gradient; the one-line repair gives A times the extrapolated error. There is no missing affine forcing term after shifting by the solution.

The released RBF is exp(-distance_squared/(2 sigma_squared)). The proposed distinct points at bandwidth one therefore give diagonal 1 and off-diagonal 1-delta exactly. The regularized system is SPD. Its extreme condition number and its 10000-dimensional equilateral construction are material limitations, already disclosed by the source.

## 3. Full-rank Nyström and finite powering

For a square Gaussian sketch, the reduced QR matrix is square orthogonal almost surely. If H=K_BB+shift*I and the shifted Cholesky/SVD factor is F, direct multiplication gives FF'=H. Subtracting the shift from its squared singular values therefore recovers K_BB exactly. Since delta>2^-52 throughout the interval, the float64 spectral-floor rule does not fire in this exact interpretation. The residual orthogonal-complement term in the float64 inverse is exactly zero. This establishes the damping lambda+delta and the inserted inverse in the theorem, independently of the sketch.

This would not justify discarding rounding from a real Nyström execution. In particular, the float32 floor changes this example; no transfer to that branch is implied.

The power routine performs ten matrix products but returns the last product's Rayleigh quotient using `v_old`. That vector has undergone exactly nine previous powers. Thus, if the starting top-eigenspace squared mass is Z, its final mass is

    W=(h/a)^18 Z / [1+((h/a)^18-1)Z].

The two factors in the preconditioned operator commute in this construction, so the operator is symmetric and this Rayleigh formula is valid. For the ideal isotropic Gaussian start, E Z=1/100. The bounds 0<a<h<1 and h/a<=52/51 hold throughout the full delta interval. The exact inequality (52/51)^20<3/2 legitimately bounds the exponent-18 ratio; it does not confuse nine and ten powers. Therefore W<=(3/2)Z and E W<=3/200.

Since eta=1/L_hat and L_hat is positive, reciprocal convexity gives

    E eta >= 1/E L_hat
           >= (lambda+2delta)/(lambda+(203/200)delta).

The upper bound E eta<=1/a is pointwise. I checked the signs and the 203/200 coefficient. The argument needs no claim that ten iterations approximate the largest eigenvalue accurately. Its purpose is to show that the finite powering law is concentrated enough toward the high inverse stepsizes in this highly degenerate spectrum.

Every selected block has the same numerical matrix up to ordering. Ideal fresh power draws therefore give the same conditional eta law for every block, independent of past state errors. Full-rank exact reconstruction removes dependence on the Nyström sketch. Those conditions justify using one common mean stepsize in the subsequent covariance certificate.

## 4. Covariance Jensen and propagation

The word covariance here can be read as the uncentered error second moment; centeredness is not required. For any PSD C, affine state matrices M(eta)=M0+eta D satisfy exactly

    E[M(eta) C M(eta)'] - M(E eta) C M(E eta)'
       = Var(eta) D C D' >= 0.

Both eta and its second moment are bounded because a>0. This identity applies conditionally on each block and on the previous history. Its use is sound. It would be wrong to replace E eta by an arbitrary pointwise lower bound inside MCM' on a monotonicity argument; the theorem does not do that. Instead its certificate holds at every common eta in the interval containing E eta.

The resulting actual covariance map is positive and linear. The two certified inequalities for Cstar and C0 therefore propagate by induction to all integer t>=1. This argument proves mean-square growth, not almost-sure divergence or divergence on every block/power sequence.

The actual zero-start error is (-u,-u), with deterministic sum-zero u. Averaging its outer product over all permutations gives ||u||^2/(n-1) times C0. The update law and A-energy commute with those permutations, so this averaging changes neither expected energy nor the physical fixed-response experiment. Since the top-left Cstar block is P and tr(AP)=(lambda+delta)(n-1), the normalization in R100.1 is exactly 1/1000. No random-response assumption is hidden here.

## 5. General-block operator and continuum certificate

The independent dense check uses (n,b)=(4,3),(5,3),(6,4),(5,4), both gradients, and every one of the six covariance-coordinate basis matrices. It enumerates every block and matches the complete 2n-by-2n image. This includes the b=n-1 edge where the producer's two-unselected-row count is zero. The comparison checks linearity on a full basis, including the indefinite cross-coordinate basis elements; it is not restricted to a few positive covariance examples.

I also reconstructed the row reduction analytically. Each gradient row has own-coordinate and whole-sum terms. Summing selected gradient rows gives the selected-block sum and b times the whole-sum term. The generic block inverse yields exactly the producer's selected-row correction. The ordered-pair counts in Section 4 recover the diagonal and off-diagonal of the permutation average, including the asymmetric mixed output cross block. Conversion to contrast/mean coordinates is diagonal-minus-off-diagonal and diagonal+(n-1)*off-diagonal, as implemented.

For the continuum statement, write c=203/200. The interpolated stepsize has numerator

    (lambda+2delta)[lambda+delta+v(c-1)delta]

over denominator (lambda+c delta)(lambda+delta). With the source's positive common denominator D, every native state-row numerator has degree at most four in delta and one in v. Multiplying a covariance residual by D^2 consequently gives degree at most eight and two respectively. Constants s, gamma, n and b cause no additional delta denominators. Thus the degree bound used in finite interpolation is valid.

The saved 108 coefficient matrices consist of four residuals times 9-by-3 coefficients. Every contrast 2-by-2 coefficient has positive first pivot and determinant. Every mean block is PSD and has the stated rank-one direction (1,1000). The independent verifier recomputes these inequalities and checks each saved tensor polynomial against the rational map on a full 9-by-3 interpolation grid plus two additional rational points per residual. Combined with the established degree bound, these are exact polynomial identities. Nonnegative Bernstein weights on the rectangle and D^2>0 prove the full-interval PSD inequalities.

## 6. Scope that must remain attached to the result

The strongest justified statement is the theorem's mean-square divergence for both gradients, under all six listed Table-3 hyperparameter choices, in the exact interpretation of the released float64 routines and ideal independent Gaussian randomness. This removes the earlier rank-two/block-fraction qualification.

It does not establish failure of Theorem 17: that theorem specifies additional blocksize/effective-dimension, ARLS sampling, sparse-sign embedding, theoretical stepsize and acceleration conditions. Those hypotheses are not verified here. It also does not establish infinite-time real float64 divergence, any float32 result, a frequent practical failure, a benchmark reversal, or a fair wall-clock advantage for an alternative solver. This audit executed exact local algebra only; it did not execute the native rank-100 optimizer.

No source repair is requested. The new practical-default limitation is mathematically supported under the bound scope; its novelty and practical significance need separate evidence.
