# Root audit: released ASkotchV2 mean-square instability

2026-10-27. Internal mathematical and implementation audit; no external endorsement or novelty clearance.

Audited theorem SHA256: `31310da5f52c1ac30237f83b24a16b5d1c1ad4fe8acca10a173aebc5b92659d4`.

**Verdict: no blocker found for the stated, supported Newton-preconditioned code-level example.** This is not a refutation of the paper's convergence theorem, nor evidence about its 23-task benchmark results.

I reconstructed the six-dimensional native update independently from its scalar equations, without importing the proposed certificate or its matrix helpers. `root_exact_audit.py` verifies the six matrix inequalities using full 6-by-6 rational Schur complements, including the zero-pivot conditions. It does not assume the proposed invariant-block decomposition. All checks pass; `root_exact_certificate.json` binds this result to the exact theorem and checker.

The RBF equilateral construction gives a positive definite Gram matrix. Its contrast eigenvalue after regularization is exactly 1/6250, so the supplied labels give target (1,-1,0). The native extrapolation is y=(w+s v)/(1+s), s=1/100. Reading `ASkotchV2.step`, `_get_block_update`, `_get_block_grad`, the Newton inverse, and `_get_L` verifies that the uncorrected direction is K y + lambda w - b. The power operator is exactly the identity for the supported Newton option with rho=regularization, hence the mathematical stepsize is one. The correction changes only lambda w to lambda y.

The actual zero initialization produces a deterministic rank-one error covariance. Its six-permutation average is precisely Cinit. Kernel, sampling law and squared-error observable are permutation equivariant, so symmetrizing is legitimate even though each experiment has fixed labels. This is not an assumption of random initialization. Positivity of the covariance operator then propagates the exact subcovariance inequality and proves the exponential lower bound. The corresponding positive definite supercovariance proves contraction after the one-term correction. The conclusions concern expectations in exact arithmetic; neither almost-sure divergence nor typical finite-run divergence is established.

I read the released-code interface checker and its certificate: all three blocks, six native basis directions, the fixed point and actual zero-start state are covered for both versions. It calls the actual model, Newton preconditioner, automatic stepsize and optimizer; only block selection is controlled and the corrected subclass adds the isolated gradient difference. The maximum reported one-step numerical discrepancy is 8.50e-11. This floating-point check connects the exact proof to code; it is not the proof of divergence.

On 2026-10-27 I separately retrieved the public default-branch `full_krr.py` through the GitHub connector: the stale `self.w[block]` term remains present. The agent's read-only remote HEAD result is the pinned commit 61cdb69cb11adea48ecb13c823ad654d46dc15df. All 79 returned issue/PR titles and bodies were inspected for a directly matching report. Open PR78 adds ASkotchV3 and does not modify this model file; its new optimizer evaluates at model.w. No matching correction was found in that bounded inspection. Comments and every historical diff were not exhaustively searched, so priority remains unestablished.

The printed practical checks mu<nu and mu nu<1 hold. They are not substitutes for Theorem17's spectral, rank, block or parameter hypotheses. No such theorem-level claim is endorsed. The concrete advance is a reproducible implementation defect with an exact divergence witness and a matched correction.
