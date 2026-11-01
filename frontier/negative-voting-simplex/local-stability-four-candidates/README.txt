TETRAHEDRAL GAUSSIAN NOISE: LOCAL STABILITY IN EVERY FIXED FINITE DIMENSION
1 November 2026

Read NONLINEAR_LOCAL_THEOREM_READING_GUIDE_20261101.txt first, followed by
the R3 arbitrary-measurable proof and the all-finite-dimensions successor.

For every fixed finite N>=3, arbitrary measurable four-label paired
partitions sufficiently close to the cylindrical tetrahedral orbit obey

 J_-1/3(P,Q)-J_-1/3(C,C)>=d_orb(P,Q)^2/1000.

The two partitions have exactly matching label masses; their common mass
vector may vary. The distance uses one common orthogonal transformation.
No smoothness, normal-graph, stationarity or minimizer premise is imposed.
Reflection of the second rule gives the positive-correlation1/3 version
near opposite tetrahedral partitions.

The coefficient is universal, but the neighborhood may depend on N and
its numerical radius is not supplied. This is local stability. Global
four-label Standard Simplex optimality and sharp MAX-4-CUT hardness are
not proved. The result is independent of the large-alphabet candidate.

The proof uses the accepted all-speed Hessian gap8/25 modulo all3N-6
common rotation modes, then compresses nearby label transfers into normal
mass coordinates. Compact weighted operators control the remaining
transfers. This analytic step upgrades the second variation to a finite
L1 neighborhood for arbitrary measurable competitors.

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

The wrapper checks source integrity, reruns eight finite arithmetic checks,
then recomputes the full moment certificate in a temporary directory. It
asserts the precise interval inequalities used by the8/25 Hessian theorem.
The compactness and nonlinear analytic proofs are separately audited, not
formally verified by running these scripts. Saved
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

FINAL NONLINEAR REVIEW
TRANSFER_COMPACTNESS_AND_FRACTIONAL_ALL_DIMENSION_INDEPENDENT_AUDIT_20261101.txt
pins and independently checks the corrected pure R3 and all-dimension
proofs. Its Section10 also proves the fractional-assignment extension.
FRACTIONAL_REFLECTION_NOTATION_20261101.txt clarifies that reflection of
an assignment means theta(-x), not a negative probability vector.
