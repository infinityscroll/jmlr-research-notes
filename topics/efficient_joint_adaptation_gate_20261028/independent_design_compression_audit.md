# Independent analytic audit of the design-compression selector

28 October 2026. Hostile mathematical review of the complete new selector proof and its exact statistical dependency. No producer source was edited and no experiment or numerical optimizer was run.

**Source reviewed:** `design_compression_selector_theorem.md`, final SHA256 `188c39bfbe31e11b668bddd7d31d251a56ba4d179b72fb7d23fbfb6339b70a16`. The full proof was read at preceding SHA256 `445f4bb97b3dfc8daf29cbe663b1a93b57a6473f3ce54dab542bf607f430e7ad`; the sole subsequent change was the compression-count clarification recorded below, which was checked in the final source.

**Imported statistical theorem read in full:** `../joint_adaptation_gate_20261028/joint_adaptive_upper.md`, SHA256 `7e150f93282f68228e49a2c1068eaa831b2188da590f140c7b68eca0819293fd`.

**Verdict:** no blocking mathematical error found in the real-arithmetic selector, its deterministic recovery guarantee, or the stated transfer of the held joint-adaptive expected-risk bound. The producer corrected one harmless literal count in Section 4 after this review: the number of compression eliminations is at most `max{p-J,0}`, not `p-J` when `p<J`. The algorithm already performed zero eliminations in that case. No repair remains requested. This review does not establish finite-bit stability, a practical runtime improvement, or historical novelty.

## 1. The stopping certificate and finite iteration bound are valid

For `M=sum omega_j v_j'v_j`, the derivative of log determinant in the jth design coordinate is `d_j=v_j M^(-1)v_j'`. Concavity gives

    f*−f(omega) <= sum omega*_j d_j−sum omega_j d_j
                 <= max_j d_j−K.

The second sum is exactly K. This proves E5 and the nonnegative certificate without requiring an unknown condition number. The initial covariance is positive definite whenever the candidate rows span K dimensions. On the statistical small-error event the true weighted anchors are independent, so the singular-initial-covariance fallback cannot occur there.

For a vertex update the determinant lemma gives exactly

    det[(1−t)M+t v'v]/det M
      =(1−t)^(K−1)[1+t(d−1)].

The increment is increasing in d. Therefore it is legitimate to replace the possibly arbitrarily large maximum score by `D=K+delta` before using the quadratic logarithm bounds. With `t=delta/(2D^2)`, the increment is at least `delta^2/(4D^2)` whenever the rule has not stopped. No Taylor expansion at the actual potentially huge leverage is being used. The inequalities `log(1−t)>=−t−t^2` for t<=1/2 and `log(1+u)>=u−u^2/2` for u>=0 suffice.

Every feasible covariance is bounded above by `sum v_j'v_j=p M0`, giving the total logdet budget `K log p`. These facts prove finite stopping and E8, including singular or near-singular raw data away from the good statistical event: singular M0 falls back, and positive definite M0 suffices for every later algebraic step. The tolerance is not silently replaced by a fixed approximation factor.

## 2. Compression preserves the right objects

The first coordinate in `phi_j=(1,vech(v_j'v_j))` forces every nonzero dependence to have coefficients of both signs. Subtracting the minimum positive-ratio multiple preserves mass and covariance and eliminates at least one active atom without creating negative weights. This constructs a support of size at most J. The bound is `max{p-J,0}` eliminations.

Raw-coordinate elimination need not choose the same support after an analysis transformation. The proof does not require that. If `x_j=v_j T`, the compressed design still has covariance `M_x=T'MT` and total mass one. All the subsequent average estimates are re-derived from that covariance and the pointwise row inequalities. There is no hidden affine-invariance assumption about the particular compression pivot rule.

## 3. The crucial linear-error geometry closes

For positive-count rows, direct subtraction proves

    ||x_j|| <= 1−3theta_j+z,
    ||x_j−B_j|| <= 5theta_j+z,
    theta_j=p_j/(1+4p_j)<=1/4.

For a zero-count row the stated convention also satisfies both bounds, even if its ideal B_j is nonzero. A zero-count designated anchor contributes one to P, so it cannot occur when `e=P+z+delta` is sufficiently small.

The K weighted anchors form a matrix `I+O_K(P+z)` after fixing labels. Its equal-weight design gives a determinant lower bound `K^(-K)(1−O_K(P+z))`; additive logdet accuracy multiplies this by at least `1−delta`. Every row has norm at most `1+z`, so the trace is at most `1+3z`. AM–GM supplies the matching lower trace `1−O_K(e)`. Compactness then supplies the fixed eigenvalue bounds E13. An O(e) ellipsoid-shape claim is neither needed nor proved; a fixed condition bound is sufficient.

Since `(1−3theta)^2<=1−3theta` on `0<=theta<=1/4`, the near-one trace forces `sum omega theta=O_K(e)`. Replacing x by B in covariance costs `O_K(e)` using the norm bounds, giving `sum omega(1−||B||^2)=O_K(e)`. For a substochastic nonnegative row with largest coordinate M,

    ||B||^2<=M,
    ||B−e_argmax||_1=1+sum B−2M<=2(1−||B||^2).

This proves the **linear**, rather than square-root, average vertex-error bound. It also shows that replacing each x by its closest assigned vertex changes covariance by `O_K(e)`. The eigenvalue floor then forces each label mass to be at least `1/(4K)`. These deductions apply to the compressed design itself; previously tiny weights are not treated as unchanged.

## 4. Heavy atoms and observable whitening avoid an unknown-coordinate loss

There are at most J compressed atoms. Removing weights less than `h=1/(8KJ)` loses at most `1/(8K)` total mass, less than half the established mass of any label. Hence at least one representative of every label survives. Each surviving atom has error at most the total weighted error divided by h, which is `O_K(e)`. In particular all retained rows, not only an unknown good subset, have controlled error.

The whitening orientation in E19 is correct. From `L'ML=I` one has `LL'=M^(-1)`. With `R=T^(-1)L`,

    RR'=T^(-1)M^(-1)T^(-T)=(T'MT)^(-1)=M_x^(-1).

Thus the ideal whitened vertices are the rows of R and have bounded singular values depending only on K. The potentially large norm or condition number of T does not enter the whitened perturbation: `v_j L=x_j R`. The algorithm never computes T.

For pivoted QR, any selected subset of ideal rows has minimum singular value at least `sigma_min(R)`, by the principal-Gram-matrix inequality. A previously selected label has projection residual `O_K(e)`; an unselected ideal label has residual at least `sigma_min(R)`, because its coefficient on its own row is one. Perturbing both the row and the selected span preserves a strict gap for small e. Therefore QR selects distinct labels and returns rows with the same O(e) error. No square-root degradation or unproved general noisy-SPA theorem is imported.

## 5. Statistical transfer and fallback accounting are sound

The held source supplies the actual spectral event G0, observable-eigenvalue comparison, truncated maximum-excess bound, and designated-anchor penalty expectation. On G0, the new tolerance obeys `delta<=C a(b)`. Markov at a fixed threshold uses `min{1,Z}`, so the proof never assumes integrability of an untruncated spectral row excess when b is small.

On `G0 intersect {P0+Z+delta<=epsilon_K}`, the new selected matrix has the same required bounded-inverse and permutation-error property as the held determinant selector. None of Algorithm E's rank, heavy-support-count, or zero-pivot fallbacks can occur on this event. The identity

    Zhat Vhat^(-1)=(A diag(mu)+D)(Vhat T)^(-1)

then gives the row bound E23, with the additional optimization error only in `d_j delta`. Its sum is `delta`, since `sum d_j=1`. The inherited same-data cutoff argument bounds retained noise and omitted mass by `H_a(d)` without conditioning on selected rows or eigenvalues. The good-event selection error and the bad-event bounded loss are controlled by the same two expectations in E21, plus `C a(b)`. That last term is absorbed by the displayed anchor term. Constants may depend on fixed K and geometry but not on b, alpha, p, n or N.

## 6. Computational and novelty limits

The new selector genuinely removes vocabulary-wide K-tuple enumeration. Direct leverage scans and matrix operations per design step, constructive compression, and QR on at most J rows give the stated polynomial arithmetic count. Since the factorial matrix is nonnegative with total sum one, its operator norm is at most one. Thus `lambda_hat<=1` and `delta>=1/sqrt(nN)` on the positive branch, proving the stated polynomial dependence on the **number of tokens**. This is not a bit-complexity or strongly polynomial claim.

The spectral factorization and factorial-moment construction remain part of the inherited procedure and may dominate cost. The proof treats exact comparisons and real arithmetic; small b may cause severe floating-point conditioning. The design, compression, whitening and QR mechanisms are established. The reviewed increment is the error-preserving heavy-atom reduction for the held jointly adaptive statistical experiment. Historical novelty of that specialized composition was not audited here.
