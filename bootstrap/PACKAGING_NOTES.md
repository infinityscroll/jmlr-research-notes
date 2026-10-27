# Release packaging notes

28 October 2026.

The 43 scientific source/result files listed in `copy_provenance.json` are
unchanged copies. No proof, simulation, or exact checker was edited for this
release. The newly written `verify.py` runs the original checks in disposable
directories, so retained outputs cannot be overwritten. It checks arithmetic
and data only; it is not a proof assistant.

The archive-relative source paths in provenance identify the original research
snapshot without exposing machine-specific directories. Original historical
manifests may mention other archive files or locally retained primary PDFs;
those references document prior work, not files required by the portable
verification. Primary papers are linked by URL and are not redistributed.

Some immutable notes say “audit pending” or “not yet audited.” The later,
included source-bound reviews record the completed internal review status.
All such reviews were produced by AI agents. In particular, the moderate
report's final audit-pending sentence predates `root_moderate_curvature_audit.md`.
The nonlinear harmonic comparison predates its conditional-consistency
extension. Neither chronological update implies outside expert validation.

The original endpoint `verification.json` records successful LaTeX compilation
in the research environment; this release does not supply an exported PDF or
claim to have recompiled it. Its recorded “no publication/contact” fields refer
to that historical preparation, not the present authorized public release.

The moderate-curvature original `result_manifest.json` was omitted because it
contained a machine-local primary-PDF path. Its scientific files and their
original hashes are preserved in `copy_provenance.json` instead. No underlying
data or negative control was removed. No downloaded paper, upstream repository,
outreach draft, credential, or cached bytecode is included.

The default validation reads both million-step bias certificates, checks their
source/checker bindings and exact rational conclusions, but does not recompute
their recurrences. `--full-bias` explicitly reruns both recurrences in temporary
copies with separate per-process time limits. Monte Carlo discovery runs are
never invoked by the verifier.
