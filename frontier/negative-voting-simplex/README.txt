NEGATIVE GAUSSIAN SIMPLEX STABILITY FOR SUFFICIENTLY MANY PARTS
AI-assisted manuscript, 31 October 2026. Revision 2.
The original 18-page manuscript and its review manifest remain unchanged
in the sibling negative_voting_simplex_manuscript_20261031 folder.

STATUS
Internally audited proof candidate for independent review. No external
endorsement, peer review, formal verification or human authorship is
asserted. The theorem is for sufficiently large m, every finite N>=m-1,
and rho in[-1/(m-1),0), for single measurable simplex assignments without
prescribed masses. No numerical threshold m0 is supplied.

PROJECT
main.tex is the remembered main document for the desktop LaTeX editor.
The six numbered TeX files contain the statement/prior inputs, complete
new calibration proof, complete radial-support proof, exterior/full-noise
assembly, discrete applications, and source ledger. The PDF is exported under output/pdf/.

The new arguments correspond to frozen sources be93031a,1eb5d9f6 and
84e1de62. Revision 2 additionally proves the endpoint and zero-remainder
facts explicitly from covariance concavity using 907e0360, repairing
two notation issues (the min operator and the scalar iid maximum). The authoritative theorem statement is e05b2c1e. Earlier
endpoint, localization and local comparison results are stated precisely
as prior inputs rather than claimed to be reproved here. The 18 exact internal
source copies and their complete SHA-256 hashes are in sources/ and
source_manifest.json. Eight external primary references are represented
by URL/hash metadata only; their full articles are not bundled. Existing sources and master files were not edited.

BUILD
The desktop compiler successfully compiles this directory. To export
using the bundled Tectonic executable from this project directory:

/Applications/ChatGPT.app/Contents/Resources/tectonic/tectonic --keep-logs -o output/pdf main.tex

The engine writes output/pdf/main.pdf; rename this output to
negative_gaussian_simplex_stability_v2.pdf after a successful build.

REVIEW
The source ledger contains human-readable references and full hashes.
The Mulgund and discrete-transfer primary references use verified public
author/title metadata and external links. Internal sources carry no human author attribution.
Rendered pages, the contact sheet and extracted text are in tmp/pdfs/
for the parent's final PDF review. QA_RECORD.txt records checks.
The direct competitive proof removes full-noise attainment/purity.
The discrete corollaries include negative Plurality is Stablest and
the exact Frieze--Jerrum MAX-m-CUT ratio, with UGC explicitly required
for hardness. The optional simple-unweighted proof is cited to its
audited companion rather than reproduced.

TRANSITIVE REVIEW COMPANION
The unchanged dependency_review/ capsule supplies 34 internal sources
with precise section scopes, external-input metadata and a verifier.
Its old snapshot is documented in DEPENDENCY_REVIEW_NOTE.txt. The source
ledger now includes the standard BL, Ehrhard, isoperimetric and Gaussian
hypercontractive primary references. Only public metadata is included.
