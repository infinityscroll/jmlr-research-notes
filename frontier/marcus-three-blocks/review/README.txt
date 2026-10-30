Marcus's block-permanent inequality for three blocks
30 October 2026. Internally audited research draft.

THE STATEMENT
For every k>=1 and every complex Hermitian PSD matrix A of order3k,
partitioned into k-by-k blocks Aij, per(A)>=per([per(Aij)]).
There is no Gram-rank restriction and no equality characterization.
This is the three-block case, not the full arbitrary-block conjecture.

START HERE
main.tex is the formatted, self-contained paper. It compiled successfully
with the Codex desktop LaTeX compiler. Opening this project in Codex shows
its PDF preview. PURE_ENTRY_THREE_BLOCK_PROOF.txt is a complete plain-text
proof, and PURE_MIXING_THREE_BLOCK_PROOF.txt is an independent derivation.
ROOT_UNIFORM_THEOREM_AUDIT.txt records the third audit and conventions.

RUN THE EXACT CHECKS
Python3 standard library only, from this directory:
  python3 check_pure_mixing.py
  python3 check_literal_layers.py
The checkers do not import each other or any operator generator. The first
checks transport counting, the subset kernel and the literal trace map.
The second checks the complete complex polynomial identity independently.
The all-k result follows analytically from the proof, not from a finite sweep.

STATUS
External review, exhaustive priority clearance and Lean formalization remain
outstanding. The proof has received three independent internal derivations/
audits. See LITERATURE_REVIEW.txt for the bounded source check.
The broader breakthrough goal remains active and unachieved: this archive
must not be described as a proof of the entire Marcus conjecture.

METHOD
The pure-entry coefficient makes every nonfinal contraction layer positive.
A literal trace of the preceding boundary term controls the only negative
square in the final layer. The dimension range d<=8k^2/9 includes d<=2k
for all k>=3. A separate elementary trace bound covers k2, and normal
ordering transfers the matrix result to every Gram rank.

The earlier frozen k2-through-k6 archive was not modified. No paid compute,
public upload or external correspondence was used to create this package.
