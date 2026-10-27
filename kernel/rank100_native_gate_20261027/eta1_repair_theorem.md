# A fixed relative step restores mean square convergence in the rank 100 stress family

27 October 2026. For the entire Gaussian-kernel family in the preceding rank-100 instability theorem, replacing the reciprocal ten-step power estimate by the fixed relative step **eta=1** restores geometric expected-error convergence while retaining the same acceleration. This is an exact-arithmetic result for this family. It is not a general ASkotch modification or a new acceleration principle.

## Statement

Take n=10000, b=r=100, lambda=10^-8 and

    K=delta I+(1-delta)11', A=K+lambda I,
    1/(20000000000) <= delta <= 1/(5000000000).

Use uniform independently sampled blocks, full-rank Nyström with default damping, mu=lambda, nu=n/b, s=sqrt(mu/nu)=10^-5 and gamma=1/sqrt(mu*nu)=1000. Interpret the released float64 branch in exact arithmetic, as in [the instability theorem](../rank100_default_gate_20261027/theorem.md). Full-rank Nyström gives the deterministic inserted inverse

    P_B=I_B'[K_BB+(lambda+delta)I]^-1 I_B.

Set eta=1 in every update. For any deterministic nonzero sum-zero u, response Au and zero initial coefficients and momentum, **both** the released stale-gradient update and the corrected-gradient update satisfy

    E ||w_t-u||_A^2 / ||u||_A^2 <= 4 (999999/1000000)^t,
                                                        t=0,1,2,... . (S1)

The random Nyström sketch has no effect on the exact full-rank preconditioner. The power routine can be omitted when the relative step is fixed; our finite probe retained it solely to match random draws across controls. This statement does not certify float32 arithmetic, a low-rank Nyström sketch, a different Gram matrix, or the choice eta=1 for general kernels.

## Positive covariance comparison

Write E=11'/n and P=I-E. Exchangeable error second moments have the coordinates

    C(a,b,c,d,e,f)=[[aP+bE,cP+dE],[cP+dE,eP+fE]].

The matrix is positive semidefinite exactly when both [[a,c],[c,e]] and [[b,d],[d,f]] are positive semidefinite. Let Phi_delta be the exact uniform-block covariance map at eta=1. The operator is the same independently checked six-coordinate map used in the instability theorem; no numerical spectral radius is used to establish (S1).

Divide the closed delta interval into 32 equal closed subintervals. For each of the two gradient variants and each subinterval, the saved certificate supplies one fixed positive definite covariance U with first contrast coefficient one and proves

    C0=C(1,0,1,0,1,0) <= 3U,
    Phi_delta(U) <= rho U,       rho=999999/1000000,    (S2)

throughout that subinterval. Delta is a fixed property of the problem. The witness is chosen once for its subinterval; this is not a statement about arbitrary switching between different kernels or witness matrices.

The stochastic covariance map is positive and linear, so (S2) implies

    Phi_delta^t(C0) <= 3 rho^t U.

For a fixed sum-zero response vector u, permutation averaging of the zero-start error (-u,-u) gives ||u||^2/(n-1) times C0. The uniform-block law and A-energy are permutation equivariant. This averaging therefore leaves the expected error unchanged and does not require randomizing the physical target or initialization.

If the first two coefficients of U are a=1 and b_U, its relative A-energy after this averaging is

    1 + [n+lambda-(n-1)delta]/[(n-1)(lambda+delta)] b_U.

The coefficient of b_U is decreasing in delta and b_U is nonnegative. The certificate checks at each subinterval's left endpoint that three times this expression is strictly below four. The comparison proves (S1).

## Exact verification of every parameter in the interval

The block inverse has the positive common denominator

    D(delta)=(lambda+2delta)[b+lambda-(b-2)delta].

Each error-state row has numerator degree at most two in delta after multiplying by D: the gradient has degree one, the inverse numerator has degree one, and the unchanged-state terms acquire D. Therefore

    D(delta)^2 [rho U-Phi_delta(U)]

is a matrix polynomial of degree at most four. On each subinterval, the checker interpolates its six coordinates at five rational nodes, converts to the degree-four Bernstein basis, and checks all five coefficient matrices for positive semidefiniteness using exact rational principal minors. Nonnegative Bernstein weights establish the continuum inequality. Two additional rational points in every subinterval independently check the polynomial evaluation. The initial domination and energy prefactor are also exact rational checks.

There are 64 witnesses and 320 PSD coefficient matrices. Witnesses were proposed by solving the center-point Lyapunov equation and rounding its coefficients. That proposal step uses floating conversion; it is not part of the proof. The resulting rational witnesses and every inequality used above are checked with Fraction arithmetic. A rejected proposal cannot yield a passing certificate.

Files: `certify_eta1_repair.py` and `eta1_repair_certificate.json`. The general covariance source remains unchanged at SHA256 `eecb2c18bb1ec6fc5d443d41bbd937190e1ecdd3cf54e1b3f4adf3dc8aa2777e`.

## Relation to observed runs

The two retained float64 runs of the unchanged released optimizer, with a structured equicorrelation model adapter, already reduced their errors substantially under the original random-power rule. The fixed-step controls also converged. Those observations do not demonstrate practical divergence or contradict an expectation-only instability theorem. The theorem here supplies the missing expected-error stability comparison on the exact stress family; it does not turn the observed default runs into failures.
