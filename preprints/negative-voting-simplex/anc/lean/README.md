# Negative Gaussian simplex formalization

This project checks concrete parts of the negative-voting manuscript in Lean.
The complete Gaussian optimality and equality theorem is **not proved here**.
Its exact quantifiers and admissible class are recorded in
[MainGoal.lean](NegativeVoting/MainGoal.lean) as `FullNegativeVotingStatement`.

The development now connects the actual correlated-Gaussian integral to the
complete signed Hermite expansion, identifies the mass, centroid and quadratic
terms, constructs regular references in the required dimensions, and proves
reference symmetries and moments. It also checks the actual affine-reference
comparison and local Gaussian cap estimates. [COVERAGE.md](COVERAGE.md) records
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
