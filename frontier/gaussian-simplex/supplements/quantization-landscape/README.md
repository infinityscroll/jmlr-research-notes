# Prescribed-mass Gaussian quantization has no spurious local minima

For a standard Gaussian in dimension `N`, choose `m` centers and fix their
positive probabilities in advance. If `N >= m - 1`, every local minimum of
the optimal transport distortion is global. Every nonglobal stationary
configuration with distinct centers has a negative Hessian direction.
The local-minimum statement also covers coincident centers.

This is a corollary of the repository's covariance-concavity theorem. The
center Gram matrix gives a convex formulation, and a continuous polar
factorization transfers its global geometry back to the centers. The
strict-saddle argument additionally establishes a boundary derivative at
singular Gram matrices.

For equal probabilities, the global centers form a centered regular simplex.
Writing `mu_m = E max(Z_1,...,Z_m)` for independent standard Gaussians, the
minimum squared distortion is `N - m * mu_m^2 / (m - 1)`.

- [Complete theorem and proof](PRESCRIBED_MASS_GAUSSIAN_KMEANS_LANDSCAPE_20261031.txt)
- [Independent cleanroom audit](CLEANROOM_QUANTIZATION_LANDSCAPE_AUDIT_20261031.txt)
- [Root review](ROOT_LANDSCAPE_AUDIT_20261031.txt)
- [Dimension counterexample and one-step Lloyd bounds](DIMENSION_BOUNDARY_AND_LLOYD_SEPARATION_20261031.txt)
- [Appendix audit](CLEANROOM_DIMENSION_BOUNDARY_AUDIT_20261031.txt)
- [Primary-source scope comparison](BOUNDED_PRIMARY_SCOPE_COMPARISON_20261031.txt)
- [Portable provenance and dependency map](PUBLIC_SOURCE_MAP.json)

The dimension assumption matters: with three prescribed probabilities
`(1/2, 1/4, 1/4)` in one dimension, the appendix constructs a strict local
minimum worse than another configuration by more than `423/78688`. This
does not assert a sharp dimension threshold for every possible mass vector.

Run the bounded exact check from the repository root:

```sh
python frontier/gaussian-simplex/supplements/quantization-landscape/verify.py
```

It validates source hashes and nine rational inequalities supporting the
dimension example. It does **not** mechanically verify the analytic proofs.
The mathematical audits were performed by AI agents. External expert review
and exhaustive priority clearance remain outstanding.

The assignment has fixed capacities and depends on the observed data point.
The result does not cover empirical data, Gaussian mixtures, free cluster
probabilities, anisotropic Gaussians, or global convergence of Lloyd's
algorithm. The main manuscript and release archives remain unchanged;
this supplement was completed afterward.
