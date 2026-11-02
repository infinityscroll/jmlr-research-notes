# Isolated singular Schur-complement dependency port

This project rebuilds a pinned subset of [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/92efba7b44b38e541bc007dc7839ff09613b2bc9) on the negative-voting project's exact Lean and Mathlib versions. It is a dependency compatibility and logical audit, not a proof of the negative-voting theorem.

## Pins and attribution

- Tau Ceti: commit `92efba7b44b38e541bc007dc7839ff09613b2bc9`, Apache-2.0. All original source headers and `LICENSE` are preserved.
- Original Tau Ceti toolchain: preserved in `upstream_original/lean-toolchain`; original configuration and dependency lockfile are also preserved.
- Port toolchain: Lean `v4.35.0-rc2`.
- Port Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- Compatibility backport: exact `IsProperStar` class semantics and the zero-quadratic-form proof from Mathlib commit `2cabef97b63d3275776b8b060d802de6a6fa1055`. The two complete original Mathlib source files are preserved under `upstream_mathlib_original/`; authorship is retained in the compatibility module.

The original fetched manifest had 35 rows describing 30 distinct Lean files. `SOURCE_MANIFEST_DEDUPLICATED.json` verifies all original hashes, removes the five identical duplicate rows, and records their paths. No original source bytes were changed in `upstream_original/`.

## What compiles

The one-file `TauCeti.LinearAlgebra.Matrix.SchurComplement` closure compiles unchanged. Its general theorem proves

`PSD [A B; B* D]`, `P*=P`, and `P D P=P` imply `PSD (A−B P B*)`.

This result does not require an invertible pivot. However, its premise permits a general outer inverse, including zero; canonical optimal elimination is supplied by the separately verified Moore–Penrose construction and block cancellation.

The full target is `TauCeti.Analysis.Matrix.SchurComplement`. Its concrete real-matrix endpoints are:

- `Matrix.PosSemidef.schur_complement₂₂_covariancePseudoInverse`: a PSD block matrix has PSD complement `A−B D⁺ B*`.
- `Matrix.PosSemidef.schur_complement₁₁_covariancePseudoInverse`: the symmetric statement for the first block.
- `Matrix.PosSemidef.toBlocks₁₂_mul_covariancePseudoInverse_mul`: a PSD block matrix satisfies `S₁₂ S₂₂⁺ S₂₂=S₁₂`, even when `S₂₂` is singular.

The construction `covariancePseudoInverse` is concrete finite-spectrum functional calculus. For PSD matrices, the imported proofs establish all four Penrose equations, uniqueness, orthogonal range projection, the regularized-inverse limit, and Borel measurability. Its definition returns zero for non-PSD inputs; the Schur endpoint assumes the whole block matrix is PSD, which implies the required diagonal-block positivity. Thus this fallback branch does not make the relevant application vacuous.

The endpoint statements are unchanged. The only original-file edit adds one compatibility import and changes one proof call to its proper-star zero-form lemma. `PORT_PATCHES.diff` records the complete edit plus the new compatibility file. The compatibility module reproduces the newer proper-star hypothesis instead of strengthening it to the older `NoZeroDivisors` hypothesis.

## Verification

Run `python3 verify.py`, optionally setting `TAUCETI_AUDIT_LAKE` to the matching `lake` executable. The project currently shares the existing pinned Mathlib package/cache directory through `.lake/packages`; a standalone checkout can fetch the exact lockfile dependencies instead.

The verifier checks original and port hashes, the actual Mathlib Git revision, the Lean version, all source imports, and the source absence of proof escapes. It rebuilds the target and inventories every compiled constant from the 31 source modules, including private helpers and generated declarations. The axiom audit traverses the actual compiled `Name` values with Lean's `collectAxioms`, so numeric components of private names are not lost through textual parsing. Every dependency must use only `propext`, `Classical.choice`, and `Quot.sound`, or none of them. It rejects custom axioms in the imported source modules.

Evidence: `BUILD_RECEIPT.json`, `BUILD_TRANSCRIPT.txt`, `INVENTORY.txt`, and `AXIOM_AUDIT.txt`. This is a Lean kernel proof audit under the standard logical axioms; it is not an independent mathematical certification of the downstream research claim.

## Consequences for the Gaussian proof

At the finite-matrix layer, this removes the need to assume:

1. invertibility of the offset covariance/Hessian block;
2. a separately postulated generalized inverse or Penrose equations;
3. independent off-diagonal kernel/range compatibility: it follows from full block PSD;
4. exclusion of zero blocks or empty coordinate types.

It does not identify a Gaussian fan's actual Hessian with these matrices. The remaining analytic work includes the moving-facet derivative formulas, existence and regularity of the mass-constrained branch, the correct Hessian/Schur-complement identity after the chosen parameterization, and the quantitative bounds uniform in label count and rank limits. In particular, PSD of a Schur complement alone is not the manuscript's cycle-refined coercivity or uniform localization estimate. If a gauge-fixed inverse is used elsewhere, it still must be shown to agree with this canonical pseudoinverse on the relevant range; no such Gaussian identification is asserted here.

No sources in the main negative-voting project or publication repository were changed by this port.
