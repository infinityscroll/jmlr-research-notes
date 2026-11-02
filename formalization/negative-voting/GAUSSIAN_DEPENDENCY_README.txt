PINNED GAUSSIAN BASIS AND NOISE DEPENDENCY PILOT

This isolated project checks a reusable Gaussian spectral dependency before
migrating the existing negative-voting formalization to a newer Lean release.
It does not by itself prove the manuscript's full simplex optimality theorem.

UPSTREAM MATERIAL

The two SlowEquilibration source files are unchanged copies from
https://github.com/pmaronow/slowequilibration-palomar at
  a28aaa336343c4caf43791ababd8ed0ee5c7b58e
and retain their Apache-2.0 license and attribution. GaussianHermite's body is
credited to openai/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
lean/OAI/Computability/MinUncut/Estimates/Basic.lean. This is borrowed foundational
formalization; UPSTREAM_PROVENANCE.json records exact file hashes and sources.
third_party/slow-equilibration/LICENSE contains the applicable Apache-2.0 license.

PINNED BUILD

Lean: leanprover/lean4:v4.35.0-rc2
Mathlib: 065356127b1dc0016f66b7283ce0ce2c4055aa55
The complete transitive package revisions are pinned in lake-manifest.json.

With the toolchain on PATH, run:
  lake exe cache get Mathlib
  python3 verify_dependency.py

When using an isolated toolchain executable, pass:
  python3 verify_dependency.py --lake /absolute/path/to/lake

The verifier checks actual compiler version, actual mathlib checkout, pinned
manifest revision, unchanged upstream source hashes, and builds precisely
SlowEquilibration.GaussianNoiseL2 and its dependencies, and runs nine explicit
transitive #print axioms audits. It rejects missing/duplicate audit output or
any axiom outside propext, Classical.choice, and Quot.sound. Successful execution with --write-evidence
writes GAUSSIAN_DEPENDENCY_BUILD_RECEIPT.json and a complete build/audit transcript.
The independent local build and all nine transitive axiom audits have passed.
The receipt and transcript record that successful execution.

ACTUAL INTERFACE

OAI.MinUncut.GaussianHermite.hermiteBasis is a complete Hilbert basis indexed by
natural numbers on real L2 of the actual standard normal probability measure.
productHermiteBasis is its finite-dimensional complete product counterpart,
indexed by all multi-indices iota -> Nat.

noise rho s Q x is the actual Gaussian integral of Q(rho*x+s*y) over y.
rotation_preserves proves the underlying rotation preserves the product law.
The basis coefficients are actual integrals against normalized Hermite products.

SlowEquilibration.GaussianMaximalCorrelation.noise_coefficient_L2 states:
  coeff (noise rho s Q) a = rho^(degree a) * coeff Q a
assuming rho^2+s^2=1, Q measurable, and Q in the actual Gaussian L2 space.
No sign restriction is imposed on rho. memLp_noise_L2 proves the image is L2;
the bounded-test noise_coefficient theorem is separately audited as well.

The child project GaussianSpectralBridge.lean connects those dependency APIs to
concrete signed-noise stability and degree-grouped chaos energies. Its build and
axiom audit are separate from this dependency verifier. NegativeVoting modules
are the separately owned migration of the current project's concrete main goal.
