NEGATIVE GAUSSIAN SIMPLEX STABILITY BEYOND THE VOTING RANGE
2 November 2026 local; proof work completed 1 November UTC.

START WITH
  QUANTITATIVE_NEGATIVE_SIMPLEX_BEYOND_THE_VOTING_INTERVAL_V2_20261102.txt

For every sufficiently large m and every finite ambient dimension N>=m-1,
the candidate theorem covers 0<r<=m^(-7/8)/(1+log m)^2 and every measurable
simplex-valued assignment f. It asserts regular-simplex optimality and

 S_-r(f)-S_-r(g) >= c min{r/m^2,
       ||E f-U||^2+r*d1(f)^4/[m^(5/2)(1+log m)^2]}.

d1 is the full Gaussian-L1 distance to the orthogonal/label orbit.
No winning-probability, purity, stationarity or smoothness premise is
imposed on f. Equality is classified up to that orbit and null sets.
The alphabet threshold is existential; no numerical m0 is supplied.

WHY THIS EXTENSION MATTERS
The ratio of the new endpoint to 1/(m-1) tends to infinity. Thus the
candidate eventually covers the complete negative voting interval and a
larger Gaussian interval. The discrete m-symbol channel does not extend
beyond its original cutoff. No additional discrete hardness consequence
is claimed outside the voting range, and UGC remains a hardness assumption.

NEW INGREDIENTS
1. A first-moment mass bound valid on an L2 neighborhood of uniform
   probabilities, including zero and unusually large labels.
2. A centered equal-row proxy built from aggregate radial error and
   operator spread, with an explicit 64-times-radial-error bound. It allows
   zero rows and preserves the row span exactly. The operator condition
   is necessary: an explicit rank-one odd-row obstruction is supplied.
3. The local affine-tail and all-amplitude cap arguments are re-derived
   at the larger correlation range. An older voting-only cap theorem is
   not invoked outside its hypotheses.

FINAL INTERNAL REVIEWS
  mass/WIDER_V2_FINAL_MASS_ASSEMBLY_REVIEW_20261102.txt
  proxy/WHOLE_WIDER_RANGE_V2_REVIEW_AND_SIGN_CORRECTION_20261102.txt
  local/FINAL_V2_WIDER_RANGE_LOCAL_SCOPE_AND_L1_REVIEW_20261102.txt

These are independent AI-agent reviews, not external expert validation.
They preserve the proof's stated foundational dependencies. The final
revision fixes an unknown-sign energy coefficient and explicitly reuses
the exterior proof under the new hypotheses. Earlier drafts and reviews
are retained as history, including their acknowledged oversight.

DEPENDENCIES AND VERIFICATION
The earlier quantitative supplement and the 34-source dependency review
remain unchanged. Absolute paths in two provenance manifests are replaced
by relative public paths; SOURCE_PROVENANCE.json records both hashes.
Most path-and-hash objects resolve from their manifest directory. Hash-only
maps naming mass/, proxy/, or local/ resolve from this supplement root;
the original proxy's two-file map resolves from proxy/.

Run python3 local/check_extended_local_exponents_20261101.py to reproduce
13 exact rational endpoint checks. These check algebraic exponents only;
they do not formally verify the analytical proofs. The repository release
manifest pins this package and all earlier release files.

The priority/ note checks a recent related Gaussian partition-function
paper from its primary text. It is a bounded overlap check, not exhaustive
novelty clearance. External mathematical verification and defensible
priority assessment remain open. The full Standard Simplex Conjecture
for all alphabets and all negative correlations is not claimed solved.
