# Negative Gaussian simplex formalization

This project checks concrete parts of the negative-voting manuscript in Lean.
The complete Gaussian optimality and equality theorem is **not proved here**.
Its exact quantifiers and admissible class are recorded in
[MainGoal.lean](NegativeVoting/MainGoal.lean) as `FullNegativeVotingStatement`.

The development now connects the actual correlated-Gaussian integral to the
complete signed Hermite expansion, identifies the mass, centroid and quadratic
terms, constructs regular references in the required dimensions, and proves
reference symmetries and moments. It also checks the actual affine-reference
comparison, prescribed Gaussian fan masses, the actual offset Jacobian,
polyhedral covariance bounds with an explicit Ehrhard correction, and local
Gaussian cap and weighted facet estimates. [COVERAGE.md](COVERAGE.md) records
which analytic obligations remain and the hypotheses of each checked component.

## Rebuild and audit

Lean 4.35.0-rc2 and mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned, together with every Lake
dependency. With the pinned toolchain available:

```sh
lake exe cache get Mathlib
python3 verify_dependency.py
python3 verify_mulgund.py
python3 verify_hypercontractivity.py
python3 verify_extended_dependencies.py
python3 verify.py
```

Each verifier accepts `--lake /absolute/path/to/lake`. Dependency verifiers are
read-only by default; `--write-evidence` deliberately refreshes their saved
receipts and transcripts. The first-party inventory is taken from the compiled
modules, not a count of theorem names in the source. Every theorem constant
from those modules, including generated helpers, must appear exactly once in
`AxiomAudit.lean`. The allowed logical axioms are `propext`, `Classical.choice`,
and `Quot.sound`; proof admissions and additional mathematical axioms are
rejected. `BUILD_RECEIPT.json` pins the distributed proof inputs.

## Attributed foundations

- **Gaussian Hermite basis and noise action:** unchanged files from
  [pmaronow/slowequilibration-palomar](https://github.com/pmaronow/slowequilibration-palomar),
  with the original Gaussian Hermite development credited to
  [openai/math](https://github.com/openai/math). Exact revisions and hashes:
  [UPSTREAM_PROVENANCE.json](UPSTREAM_PROVENANCE.json).
- **Gaussian hypercontractivity:** the actual Gaussian instance from Michael R.
  Douglas's [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups),
  ported to the common toolchain. Its L²-to-Lq and Lp-to-L² integral statements
  are connected to raw square-integrable functions, including unbounded
  projections. [Provenance](HYPERCONTRACTIVITY_PROVENANCE.json) and
  [compatibility notes](HYPERCONTRACTIVITY_README.txt).
- **Equal-threshold Gaussian comparison:** Abhijeet Mulgund's
  [weak-simplex-conjecture-lean](https://github.com/abhmul/weak-simplex-conjecture-lean).
  The independent boundary statement displays the covariance, diagonal,
  rank-one domination and Gaussian event explicitly.
  [Provenance](MULGUND_PROVENANCE.json).

- **Gaussian polyhedral support calculus:** the fixed-normal support and slice
  calculus from [full-simplex-conjecture-lean](https://github.com/abhmul/full-simplex-conjecture-lean),
  with its Weak Simplex and StatLean dependencies.
  [Pinned sources and compatibility edits](third_party/polyhedral-support/SOURCE_MANIFEST.json).
- **Ehrhard concavity:** OpenAI's smooth Gaussian quantile proof, preserved
  verbatim through the pinned slowequilibration vendor. Our extension proves
  the actual finite-polyhedron statement and derives the quantitative
  conditional covariance bound.
  [Provenance](third_party/openai-ehrhard/OPENAI-EHRHARD-PROVENANCE.json).
- **Singular Schur complements:** [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
  supplies the canonical covariance pseudoinverse and singular matrix theorem.
  All compiled constants in the 31-module closure are audited.
  [Port manifest](third_party/tauceti/PORT_MANIFEST.json).

The [reuse search ledger](REUSE_SEARCH_20261102.json) records the exact revisions,
selected theorems, and why other candidates did not match the needed hypotheses.

These are prior results and attributed software dependencies. Their original
licenses and preserved sources are included under `third_party/`; the StatLean
material retains its own Apache-2.0 notice. The Markov source history contains
three legacy axioms and wrappers, preserved verbatim only in the archival
originals. They were unused by the concrete Gaussian endpoint and removed from
the active source. Transitive audits before and after removal agree, and the
endpoint type is identical. Active dependencies introduce no extra axioms.

The manuscript's new geometric comparison, uniform constants and final theorem
require further formal proof. Compilation of the components does not establish
those remaining obligations.
