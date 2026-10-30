# Marcus's block-permanent inequality for three blocks

For every positive integer `k` and every complex Hermitian positive
semidefinite matrix `A` of order `3k`, partitioned into `k`-by-`k` blocks,
the theorem proves

```text
per(A) >= per([per(A_ij)]_{i,j=1}^3).
```

There is no Gram-rank restriction. The proof treats every block size
analytically; finite checks are corroboration.

- [Read the manuscript PDF](manuscript.pdf) · [LaTeX source](review/main.tex)
- [Complete proof](review/PURE_ENTRY_THREE_BLOCK_PROOF.txt)
- [Independent derivation](review/PURE_MIXING_THREE_BLOCK_PROOF.txt)
- [Root audit](review/ROOT_UNIFORM_THEOREM_AUDIT.txt)
- [Primary-literature comparison](review/LITERATURE_REVIEW.txt)
- [Frozen downloadable package](../../archives/marcus_three_blocks_all_k_20261030.zip)

From the repository root:

```sh
python frontier/marcus-three-blocks/verify.py
```

The wrapper checks the frozen manifest and runs the two independent
standard-library exact checkers in a temporary directory. It preserves the
published evidence files. The manuscript compiled successfully, and the
argument received three internal AI-agent derivations/audits.

This is the **three-block theorem**. The arbitrary-number-of-blocks conjecture
and equality classification remain unresolved here. External expert review,
exhaustive priority clearance and formal verification remain outstanding.

The frozen source directory and archive are unchanged. Their historical
local-only status describes creation, before this public release.

Archive SHA256: `7ebb6b46de5b4fc94d2d7eb928b74b8fe84935de4aa98c73dae19a72a9fdf572`.
