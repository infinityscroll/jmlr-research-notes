# Negative Gaussian simplex formalization

The complete original Gaussian target is now proved in Lean:

```lean
theorem NegativeVoting.full_negative_voting :
  NegativeVoting.FullNegativeVotingStatement
```

[Final theorem](GaussianFullNegativeVoting.lean) · [Exact statement](NegativeVoting/MainGoal.lean) · [Publication verification](completion-evidence/PUBLICATION-VERIFICATION-20261103.json) · [Scope ledger](COVERAGE.md)

The statement gives one alphabet threshold M, uniform in ambient dimension and correlation. For every m ≥ M, every ambient dimension d ≥ m−1, and every −1/(m−1) ≤ ρ < 0, a regular-simplex assignment minimizes actual Gaussian noise stability over all AE-measurable fractional simplex assignments. Equality holds exactly for assignments AE equal to a regular-simplex assignment. No equal-mass restriction, numerical covariance hypothesis or remaining analytic premise is imposed.

The full build, exact-target regression and exhaustive axiom audit pass for **8,403 compiled first-party theorem constants, 4,504 named source declarations and 505 modules**. Only `propext`, `Classical.choice` and `Quot.sound` occur. No proof admissions or extra mathematical axioms are used. The original `MainGoal.lean` and its defining files are unchanged; the old comment in that file describing an outstanding goal is retained as historical source provenance and is superseded by the new theorem above.

This completes the repository's recorded Gaussian target. It does not supply an explicit numerical M, settle every small alphabet, formalize the separate discrete voting/UGC consequences, or establish publication priority. The manuscript PDF and historical source archives are unchanged. This directory contains the completed formalization.

The earlier [stop checkpoint](../../checkpoints/negative-voting-2026-11-02/STATUS.txt) and stages 1–17 are preserved as historical evidence. The final source hashes and original full transcript are in the [stage-18 receipt](completion-evidence/STAGE18-VERIFICATION.json). A fresh build and exhaustive audit are recorded in the publication verification; it also records the documentation-only changes since stage 18. Separate internal [semantic](completion-evidence/FINAL-TARGET-SEMANTICS-AUDIT-A-20261103.txt) and [composition](completion-evidence/FINAL-COMPOSITION-SCOPE-AUDIT-BC-20261103.txt) reviews check the statement and assembled scope; these are not external peer review.

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
rejected. `BUILD_RECEIPT.json` pins the historical distributed inputs; the stage and publication receipts pin the completed work. The original public checkout omitted the Cheeger adapter and its KLS dependencies. They are restored here with [explicit recovery provenance](KLS_RECOVERY_PROVENANCE_20261102.json); the adapter is reconstructed and is not represented as the missing original file.

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
- **Gaussian Cheeger variance bridge:** seven pinned files from [HongruZhao/KLS500](https://github.com/HongruZhao/KLS500), commit `c1a50992a81456849996deef2971d4a0b3190bdd`, with Apache-2.0 license and preserved originals under `upstream/kls500/`. The reconstructed adapter and its unchanged downstream Cheeger theorems pass the axiom audit.
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

The final composition discharges the actual balanced second-energy bound, local mass and tail absorption, exterior localization, and AE representative transfer before applying the exact inequality/equality assembly. `verify.py` also pins the original target source and checks a closed proof of that exact proposition, so a component-only build cannot pass as completion.
