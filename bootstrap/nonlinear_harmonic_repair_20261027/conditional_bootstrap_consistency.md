# Conditional consistency in the nonlinear harmonic regime

27 October 2026. Candidate consequence of the source-bound linearization already proved in this folder. This adds a conditional-bootstrap statement that the earlier files deliberately did not claim. It does not change their proofs or imply finite-sample accuracy.

Bound dependencies:

- `nonlinear_critical_bootstrap_theorem.md`, SHA256 `6eaae8f09c1266cbe1a7b4aab31421f602e9bd409175ae1f7408f5452ab61bb5`.
- `mean_square_continuity_extension.md`, SHA256 `8cf2b32cae345521e8699466f4441801a37809cda5ad1cc0311b6d69d50a4840`.

## Statement

Under the mean-square-continuity extension's assumptions, let `D_n=sigma(Z_1,...,Z_n)` be the observed data sigma-field. With U,T_n,Gamma defined in the base theorem,

\[
d_{\rm BL}\left(\mathcal L\left(T_nU^T(\bar X_n^{*}-\bar X_n)
                       \mid\mathcal D_n\right),
                       N(0,\Gamma)\right)\xrightarrow{P}0.
\tag{C1}
\]

Here d_BL is bounded-Lipschitz distance and the conditional randomness is the online multiplier sequence. The corresponding original statistic `T_n U^T(bar X_n-theta)` converges unconditionally to the same Gaussian. A fixed number B of replicates have conditional joint limit `N(0,I_B tensor Gamma)` in probability. This is not an almost-sure conditional convergence claim, a statement for growing B, or an unnormalized root-n claim in critical directions.

## 1. Deterministic weighted law of large numbers

If Y_t are iid integrable scalar variables, deterministic signed weights c_nt satisfy `sup_n sum_t |c_nt|<infinity` and `max_t|c_nt|->0`, then

\[
\sum_t c_{nt}(Y_t-EY_t)\longrightarrow0\quad\text{in }L^1.
\tag{C2}
\]

Proof: truncate Y at a fixed magnitude M. The centered bounded part has variance at most a constant depending on M times `sum c_nt^2`, which tends to zero because it is at most `max|c_nt| sum|c_nt|`. The unbounded part's expected absolute weighted sum is at most twice the common absolute-weight bound times `E[|Y|1{|Y|>M}]`. Let n grow and then M grow. No fourth moment is needed.

## 2. Conditional Gaussian limit for the leading weighted multiplier array

Write `xi_t=U^T g(theta,Z_t)` and `d_nt,j=s_n(a_j)b_nt(a_j)`. The base theorem and extension prove

\[
T_nU^T\bar D_n^b
=-\sum_{t=1}^n\operatorname{diag}(d_{nt,j})(W_t^b-1)\xi_t
+R_n^b,\qquad R_n^b\xrightarrow{P}0.
\tag{C3}
\]

The remainders here are for the actual untruncated processes; the earlier localization has already been removed. Conditional on the data, the leading summands are independent and centered. Their conditional covariance V_n has entries

\[
(V_n)_{ij}=\sum_t d_{nt,i}d_{nt,j}\,\xi_{t,i}\xi_{t,j}.
\tag{C4}
\]

The product weights have bounded absolute sum by Cauchy--Schwarz and (N15), and their maximum tends to zero. The variables `xi_i xi_j` are integrable by finite second moments. Applying (C2) entrywise, followed by the deterministic covariance-weight limits (N19), yields `V_n->Gamma` in probability, indeed in L1 entrywise.

Let `D_nt=diag(d_nt,j)` and `a_n=max_t||D_nt||`, which tends to zero; `sum_t||D_nt||^2` stays bounded. For every epsilon>0 the expectation over the data of the conditional Lindeberg sum is bounded by

\[
\left(\sum_t\|D_{nt}\|^2\right)
 E\left[\|(W-1)\xi\|^2
          1\{\|(W-1)\xi\|>\epsilon/a_n\}\right]\to0.
\tag{C5}
\]

Independence and finite second moments of W-1 and xi make the displayed squared norm integrable. Thus the conditional Lindeberg sum tends to zero in probability by Markov's inequality. The same argument applies to any fixed vector projection.

To make the conditional convergence mode precise, take any subsequence. The covariance and Lindeberg convergence in probability permit a further subsequence on which both hold almost surely, simultaneously for countably many positive rational thresholds. For almost every data sequence along that subsequence, the ordinary deterministic multivariate triangular-array CLT applies to the conditional multiplier laws. These conditional laws converge weakly to N(0,Gamma), hence in d_BL. The subsequence criterion then proves convergence in probability for the original sequence.

## 3. Transfer of the actual nonlinear remainder

Unconditional `R_n^b->0` in probability is enough for transfer in conditional probability:

\[
E\left[P(\|R_n^b\|>\epsilon\mid\mathcal D_n)\right]
=P(\|R_n^b\|>\epsilon)\to0.
\tag{C6}
\]

Thus the conditional tail probability tends to zero in L1 and in probability. Equivalently `E[min(2,||R_n^b||)|D_n]->0` in probability, using boundedness and convergence in probability. This controls the bounded-Lipschitz distance between the actual statistic and its leading conditional array, proving (C1). No conditional convergence of the original estimator to a nondegenerate Gaussian is assumed: given the data it is a fixed center.

Replicates are conditionally independent given the data, since they share a fixed initial point and only their mutually independent multiplier sequences remain random. For fixed B, products of the single-replicate conditional laws converge to the Gaussian product law; alternatively apply the same covariance/Lindeberg proof to the stacked array and union-bound its remainder. The unconditional original/replicate joint independence and finite-B Student/F conclusions were already established separately.

## Scope

This closes the conditional-bootstrap-consistency restriction in the preceding nonlinear harmonic result, under the same stability, local spectral and mean-square-continuity assumptions. It does not upgrade to a Berry--Esseen bound, uniform coverage near a changing critical eigenvalue, an offline resampling theorem, or historical novelty. The weighted-LLN and conditional triangular-array arguments are classical. The specific application retains the actual online gradient multiplier update and its full averaging rule.
