# Root check of the full-rank Nyström equivalence

2026-10-27. Internal analytic audit of `nystrom_full_rank_equivalence_20261027.md`, SHA256 `fd599b8c5c13328b3fcfa45f1a4db6da6da3241d755e05d63360d42450beabc5`.

I read the pinned `Nystrom.update` and `inv_lin_op` source. The right triangular solve computes F=Y L^{-T}. For a square orthogonal sketch, FF^T=B+hI exactly, so subtracting h from the squared singular values recovers B. Both eigenvalues in the stated example exceed the clipping threshold. The full orthonormal basis then makes the complementary inverse term zero and yields (B+lambda I)^{-1}. The resulting power operator is the identity. No blocker found.

The statement is an exact-arithmetic interpretation retaining the specified stabilization shift as a fixed scalar. It is almost sure over ideal continuous Gaussian sketches; it is not a finite-precision bitwise equivalence claim. The numerical released-code checker covers Newton only. Neither this addendum nor the original example establishes the other hypotheses of the paper's convergence theorem, or covers low-rank/damped benchmark configurations.
