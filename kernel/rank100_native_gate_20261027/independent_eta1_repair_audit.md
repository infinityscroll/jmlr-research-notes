# Independent audit of the fixed eta=1 repair

27 October 2026. Reviewer: `hcm_end_to_end`. **No blocking mathematical or source-interface error found within the stated exact-arithmetic scope.** The retained certificate establishes the claimed bound for both gradient conventions and the whole specified delta interval. No producer source, certificate, or experiment was modified or rerun. This review used local exact arithmetic only.

## Bound sources and independent verification

| Artifact | SHA256 |
|---|---|
| `eta1_repair_theorem.md` | `e72f428b57cd871d6bd594b9faa640fe961e7a5e3d51feb3419df4c0e8010013` |
| `certify_eta1_repair.py` | `2ea52b974c326a5ad09b3ff32ad16bdba9578ffb44876009e089ffdb6525c54b` |
| `eta1_repair_certificate.json` | `eebce83eedda40caea24d995f262fffab199dae690f6ee9825a1a4929bc2c209` |
| `../rank100_default_gate_20261027/general_block_operator.py` | `eecb2c18bb1ec6fc5d443d41bbd937190e1ecdd3cf54e1b3f4adf3dc8aa2777e` |
| New `independent_eta1_saved_check.py` | `8d6636be78ad71c71713f06febe1f6fc4e52ffc562c04801f28f9a130b42c449` |
| New `independent_eta1_saved_certificate.json` | `764c99af25bfb58de07147a1331c5056cf2344c41a2469934fef13fe6e0d747e` |

I read the theorem and producer checker in full, the general operator and its prior independent dense audit, and the pinned released `ASkotchV2` and `FullKRR` source. The six-coordinate map is the previously independently audited map; this review does not claim another independent dense implementation of it. I reconstructed its row reduction analytically below.

The new checker does not import the producer proposal, Vandermonde solver, interpolation routine, or coefficient-generation code. It reads the retained rational witnesses and Bernstein coefficients, checks every principal minor itself, and evaluates the coefficients by de Casteljau recursion. Five fresh interior rational nodes are

    1/13, 2/11, 3/7, 7/11, 12/13.

They are distinct from all five producer interpolation nodes and both of its extra evaluation points. Both endpoints are also checked. The cleared residual is proved below to have degree at most four; equality at the five distinct fresh nodes therefore proves polynomial identity, rather than merely agreement on a numerical grid.

The checker passed:

- all 64 strictly positive definite witnesses, with first contrast coordinate exactly one;
- all 64 initial domination inequalities;
- all 320 Bernstein PSD coefficient matrices, including equality of every saved minor to its recomputation;
- all 448 direct rational map/polynomial evaluations, amounting to 2,688 coordinate equalities;
- all interval endpoints and complete coverage by 32 boxes for each gradient convention;
- all 64 exact energy bounds.

The largest energy prefactor is exactly

    966570000000009937218814069268255121
    /322190000000000000000000000000000000,

approximately 3.0000000000000306 and strictly below four. Floating display is not used in any inequality.

## Native update and degree bound

Let c=1-delta, lambda=10^-8, s=10^-5 and gamma=1000. Subtracting the solution u from the released coefficient and momentum states gives e=w-u, f=v-u and Y=(e+s f)/(1+s). The actual source acceleration has alpha=s/(1+s) and beta=1-s, so at eta=1 the state update is exactly

    g=delta Y+c*1*(1'Y)+lambda e   (stale),
    g=delta Y+c*1*(1'Y)+lambda Y   (corrected),
    e'=Y-P_B g,
    f'=(1-s)f+sY-gamma P_B g.

The stale lambda term follows from `FullKRR._get_block_grad` using the stored `self.w`, even when its evaluation argument is y. There is no residual affine forcing after subtracting u, because both formulas use response Au. Initial zero coefficient and momentum imply e=f=-u and the same extrapolated relation at time zero.

For a selected block, the full-rank preconditioner has inverse matrix

    [(lambda+2delta)I+c*11']^-1.

Put L=b+lambda-(b-2)delta and D=(lambda+2delta)L. Sherman–Morrison gives its selected output row as

    (P_B g)_i = [L*g_i-c*sum_(j in B)g_j]/D.

Both L and c are affine in delta; every row coefficient of g is affine in delta. Thus each selected correction has numerator degree at most two. The uncorrected state terms have constant coefficients in delta, so multiplying them by D gives degree at most two as well. The same common denominator covers selected and unselected rows of both state blocks. Consequently D^2 Phi_delta(U) has degree at most four for each FIXED witness U, and so does D^2[rho U-Phi_delta(U)]. There are no extra delta denominators from s, gamma, eta or U. D is strictly positive on the full interval.

For completeness, the row reduction represents each row by its coefficients on its own coordinate, the selected-block sum, and the full-coordinate sum, separately for e and f. Their inner products are determined by own-index equality, selection membership, b and n. Permutation averaging then uses selected/unselected diagonal counts b,n-b and ordered off-diagonal counts b(b-1),b(n-b),(n-b)(n-b-1). This yields the six-coordinate map used in the checks, including the mixed state block. Its earlier independent dense comparison remains a credited dependency, not an assumption about an unreviewed numerical operator.

The full-rank Nyström identification and inactive float64 spectral floor are inherited from the bound instability source and its prior source audit. Here eta is deliberately fixed to one. The earlier finite random-power law and its Jensen lower bound are irrelevant to the repair proof and are not silently retained in the covariance map.

## PSD propagation and the deterministic target

Write E=11'/n and P=I-E. The representation

    C(a,b,c,d,e,f)=[[aP+bE,cP+dE],[cP+dE,eP+fE]]

is PSD exactly when its contrast and constant-direction 2-by-2 matrices are PSD. These are precisely the principal minors checked in the new verifier. Nonnegative Bernstein weights sum to one on each closed box. Hence PSD of all five coefficient matrices, their exact polynomial identity, and D^2>0 establish

    Phi_delta(U) <= rho U

throughout that box. The inequalities use one constant rational U per box; delta is fixed during the iteration. No switching-kernel assertion is made.

The map Phi_delta is a positive linear raw-second-moment map, since it averages M_B C M_B' over independent uniformly sampled blocks. It need not be a centered covariance map. From C0<=3U, induction gives

    Phi_delta^t(C0)<=3 rho^t U

for every integer t>=0. The inequality direction is correct for an upper bound. Taking the positive A-energy functional preserves it.

For any fixed nonzero sum-zero u, the permutation average of uu' is ||u||^2 P/(n-1). Therefore the average of the zero-start joint error outer product (-u,-u)(-u,-u)' is ||u||^2 C0/(n-1). Because both the uniform block law and A commute with coordinate permutations, this analytical averaging leaves the expected energy of the original fixed-target experiment unchanged. It does not require random targets, random initializations, or mean-zero stochastic state errors.

The eigenvalues of A are lambda+delta on P and n+lambda-(n-1)delta on E. Since the first two witness coefficients are 1 and b_U>=0, the relative first-state A-energy of U is

    1 + [n+lambda-(n-1)delta] b_U
            /[(n-1)(lambda+delta)].

The bracketed coefficient is decreasing in delta: its derivative is

    -n(1+lambda)/[(n-1)(lambda+delta)^2] < 0.

Thus evaluating the energy at each box's left endpoint is a valid upper bound across the box. The verified factor-three energies are all below four, proving exactly

    E||w_t-u||_A^2 / ||u||_A^2 <=4(999999/1000000)^t.

This includes t=0 and both gradient conventions. No momentum-energy bound with prefactor four is claimed or needed.

## Scope and verdict

The theorem is supported for n=10000, b=r=100, the specified positive-delta equicorrelation interval, lambda=10^-8, uniform independent blocks, zero initialization, sum-zero deterministic target, exact full-rank damped preconditioning, the retained acceleration, and fixed relative eta=1. It is an exact expected-error stability result for this stress family.

It does not certify finite-precision infinite-time execution, float32, a different kernel, a low-rank sketch, arbitrary switching between interval points, a competitive wall-clock algorithm, or a general ASkotch learning-rate recommendation. It does not refute JMLR Theorem17. The already retained convergent default float64 trajectories remain evidence limiting a practical-divergence claim; nothing in this repair proof changes their interpretation.

No source repair is requested. Independent internal verification is not expert review, formal proof-assistant verification, or novelty clearance.
