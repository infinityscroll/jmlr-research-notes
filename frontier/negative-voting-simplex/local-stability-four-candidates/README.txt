TETRAHEDRAL GAUSSIAN NOISE: STRICT SECOND VARIATION IN EVERY FINITE DIMENSION
1 November 2026

Read THEOREM_AND_PROOF_ACCEPTED_20261101.txt first.

For every finite N>=3, the paired tetrahedral partition at correlation1/3
has a coercive second variation under label-by-label matching masses.
The common mass vector may vary. On the full finite-energy boundary-speed
space, the Hessian is at least8/25 times squared distance from simultaneous
rotation speeds. These rotations are its entire neutral space, of dimension
3N-6. The equivalent reflected formulation uses correlation-1/3.

This is a computer-assisted second-variation theorem. It does not prove
global tetrahedral optimality, the four-label Standard Simplex conjecture,
a uniform nonlinear neighborhood theorem, or sharp MAX-4-CUT hardness.
It is independent of the separate large-alphabet proof candidate.

The computational input is a rigorous enclosure of the complete boundary
operator, using Arb, exact polynomial cubature, proved curvature and tail
bounds, and an explicitly audited IEEE binary64 error budget. It is not
an inference from a finite polynomial eigenvalue scan. This is not Lean
formalization. Internal mathematical and implementation audits were carried
out by separate AI-agent runs; no external endorsement or novelty clearance
is claimed.

An additional independent lemma in COMMON_MASS_LOCALIZATION_20261101.txt
shows that every competitive matched-mass pair has each mass in(1/8,3/8).
That lemma uses an exact rational certificate and does not assert optimality.

REPRODUCE
Use Python3.12 with the repository's requirements.txt:
  python -m pip install -r requirements.txt
  python frontier/negative-voting-simplex/local-stability-four-candidates/verify.py

The wrapper checks source integrity, reruns four exact arithmetic checks,
then recomputes the full moment certificate in a temporary directory. It
asserts the precise interval inequalities used by the8/25 theorem. Saved
research results are not overwritten. No remote compute is used.

PROVENANCE
SOURCE_PROVENANCE.json identifies unchanged research sources. The public
main certificate differs from its audited original only by removing two
workspace-specific dependency-search lines. The original is preserved in
frozen_source/. All mathematical operations are unchanged; verify.py checks
that assertion. The earlier conditional9/100draft is historical; the
accepted successor and final frozen-source receipt settle its status.

Some retained notes describe earlier exploratory scans or local environment
commands. Those are provenance, not prerequisites for the portable verifier.
No private correspondence, third-party articles, or installed dependencies
are redistributed.
