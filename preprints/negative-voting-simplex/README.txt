NEGATIVE GAUSSIAN SIMPLEX STABILITY FOR SUFFICIENTLY MANY PARTS
Research preprint, 2 November 2026

Author: Jitendra Prajapati
ORCID: https://orcid.org/0009-0008-7493-0311
No institutional affiliation is asserted.

READING
The main document is main.tex; the compiled deliverable is
output/pdf/negative_voting_simplex_preprint.pdf.
This integrated edition expands the earlier 20-page manuscript with the
current localization, covariance-gap, local-comparison, and endpoint
arguments. Earlier frozen releases remain unchanged.

The PDF is not a replacement for the longer analytic proofs in anc/.
Appendix A and the bibliography identify the exact supporting notes.
anc/ contains the proof notes and derivations needed to assess the claim;
third-party papers are cited through their primary public URLs.

BUILD
With an ordinary TeX Live installation, from this directory run:
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
Run a third pass if LaTeX requests another cross-reference pass.
No shell escape, external BibTeX run, system font, or repository-relative
input is required. The bibliography is included in 08_references.tex.
Alternatively:
  tectonic --outdir output/pdf main.tex

SCOPE
The claimed Gaussian theorem covers every sufficiently large fixed number
of parts, every finite N >= m-1, and rho in [-1/(m-1),0), for one arbitrary
measurable simplex-valued assignment with no prescribed masses. The
threshold is existential. UGC is assumed only for the hardness consequence.
Small remaining alphabets and the full Standard Simplex conjecture remain
outside the claim.

VERIFICATION
The companion Lean project is a partial formalization, with its actual
kernel-checked declarations, hypotheses, and remaining obligations recorded
in its own README. It does not formalize the full Gaussian theorem.
Internal analytic reconstructions were performed by separate AI-agent
runs. The assistance is disclosed in Appendix A; no external expert
endorsement or independent proof-assistant verification of the analytic
interfaces is claimed.

SUBMISSION
See SUBMISSION.txt and submission.json for arXiv metadata and the remaining
submission steps. Publishing this GitHub package does not create an arXiv
identifier. Source hashes and immutable release timestamps establish
artifact identity and publication history, not mathematical validity or
exclusive priority.
