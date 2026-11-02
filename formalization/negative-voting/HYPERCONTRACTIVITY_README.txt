Gaussian hypercontractivity: independently checked dependency and actual-integral bridge

This project builds the finite-dimensional Gaussian hypercontractivity theorem
from Michael R. Douglas's markov-semigroups development and specializes it to the
actual Gaussian averaging integral used by the negative-voting formalization.
It uses Lean 4.35.0-rc2 and mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55.

The actual operator is
  gaussianAverage tau f x = integral f(tau*x + sqrt(1-tau^2)*y) d gamma_n(y),
where gamma_n is the product of n independent standard real Gaussian measures.
For every 0 < tau < 1 and every real f with MemLp f 2 gamma_n, the bridge proves:

  ||gaussianAverage tau f||_2 <= ||f||_(1+tau^2),
  ||gaussianAverage tau f||_(1+tau^(-2)) <= ||f||_2.

The norms are mathlib's extended-real eLpNorm. The second conclusion also gives
finite higher integrability. The input functions can be unbounded and need only
be Gaussian square-integrable; no pointwise Borel representative is required.
AE congruence is proved through the genuine measure-preserving Gaussian kernel.
A separate bounded-measurable specialization derives the L2 input condition.
These statements cover polynomial-subtracted high-chaos inputs as soon as their
natural square-integrability obligation is discharged.

The original endpoint is GaussianFin.stdGaussianFin_isHypercontractive. Its
semigroup is a genuine Gaussian OU operator on the L2 carrier, and its original
scope requires both L2 membership and membership in the source Lp space. It is
not advertised here as an Lp-only extension outside L2. For the L^(1+tau^2)-to-L2
specialization, source membership follows from Gaussian L2 membership. For the
L2-to-higher-Lq specialization it is precisely the existing L2 condition.

Verification

The complete 17-file dependency closure and GaussianHypercontractivityBridge.lean
were compiled locally. All 11 bridge theorems, its gaussianAverage definition,
and three selected upstream endpoints passed transitive #print axioms audits:
only propext, Classical.choice, and Quot.sound are permitted. The active source
has no custom axioms, sorry/admit, unsafe, native_decide, implemented_by, or extern.
The pinned mathlib dependency is the usual trusted library build/cache.

  elan toolchain install leanprover/lean4:v4.35.0-rc2
  lake exe cache get
  python3 verify_hypercontractivity.py

A separately installed compiler can be selected with --lake /absolute/path/to/lake.
The verifier checks the observed compiler commit, toolchain file, actual mathlib
checkout and manifest pin, preserved original hashes, active proof-mechanism
scan, complete bridge declaration inventory, build exits, and transitive axioms.
With --write-evidence, its receipt records the exact source, verifier, manifest
and provenance hashes. Ordinary verification leaves these records unchanged.
The local .lake directory is a disposable cache and is not part of the source
release. A fresh checkout uses the pinned Lake manifest normally.

Provenance and compatibility port

Upstream: https://github.com/mrdouglasny/markov-semigroups
Commit: 0b5dd80ad918f7e8ab23bb2fac5eb9c7d373a795
License: Apache-2.0 (third_party/markov-semigroups/LICENSE; original file attribution retained)
Original Lean: 4.30.0
Original mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

HYPERCONTRACTIVITY_PROVENANCE.json records the exact 17 source paths and original SHA256s.
The verbatim originals are preserved under third_party/markov-semigroups/originals/. HYPERCONTRACTIVITY_PORT.patch records
the full port. Most changes adapt modern function eta/definitional equality,
MemLp/eLpNorm APIs, and explicit structure projection elaboration.

One existing helper statement changed:
GrossODE.integral_abs_eq_eLpNorm_one_toReal now explicitly assumes
AEStronglyMeasurable f. Modern eLpNorm makes this hypothesis necessary, and its
existing caller supplies it from already available measurability. A local Fatou
argument also quantifies over Lp representatives to retain measurability.
The final Gross theorem and concrete Gaussian endpoint retain their original
hypotheses and conclusions. HYPERCONTRACTIVITY_DECLARATION_HEADER_COMPARISON.json compares 455
upstream theorem/lemma/def/abbrev/opaque headers; it records that helper change,
one added private definitional helper, and the three removed wrappers below.
This source-level comparison does not include anonymous instances or structures.

The upstream abstract file contained three legacy axioms and three wrappers that
were unused by the concrete endpoint. The complete endpoint and bridge were first
compiled and axiom-audited with those declarations present. Only then were those
six unused declarations removed. HYPERCONTRACTIVITY_LEGACY_AXIOM_REMOVAL.patch records that removal.
A fresh clean rebuild and axiom audit succeeded. The concrete endpoint type and
the IsHypercontractive definition printed before and after removal are identical.
The historical source comments remain attributable to their upstream author;
the clean receipt, rather than old comments describing formerly postulated
lemmas, records the actual checked dependency status.

Evidence

HYPERCONTRACTIVITY_LEGACY_PRESENT_RECEIPT.json and corresponding transcript:
  Historical build/audit before removing unused legacy declarations.
HYPERCONTRACTIVITY_CLEAN_RECEIPT.json and corresponding transcript:
  Final active sources; 15 audited constants; no custom source axioms.
HYPERCONTRACTIVITY_ENDPOINT_TYPE_BEFORE.txt / AFTER.txt:
  Identical checked concrete endpoint type and hypercontractivity predicate.
GeneratedHypercontractivityAudit.lean:
  Exact current declaration inventory used for the final audit.
HYPERCONTRACTIVITY_ACTIVE_SOURCE_FILES.txt:
  Exact active source list for integration.

This supplies a classical Gaussian analytic input. It is not a proof of the
negative-voting comparison itself: that theorem still needs the original
quantitative geometric and remainder estimates listed in the main project's
coverage ledger. The dependency's mathematical authorship remains upstream;
the actual-integral specialization and compatibility/audit work are recorded
separately here.
