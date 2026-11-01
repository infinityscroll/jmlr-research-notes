GLOBAL QUANTITATIVE STABILITY: REVIEW SUPPLEMENT
1 November 2026. Internally audited mathematical proof candidate.

The new theorem strengthens the eventual-large-m negative-voting result:
near-optimal arbitrary measurable rules are close to the regular simplex,
with a dimension-independent fourth-power Gaussian-L1 modulus.

Let E=S_-r(f)-S_-r(g), delta=||E f-U||^2, L=1+log m, and d1 be the
Gaussian-L1 distance to the regular simplex orbit. For all sufficiently
large m, all finite N>=m-1, and 0<r<=1/(m-1), the proof gives

  E >= c min{r^2/m, delta+r*d1^4/[m^(5/2)*L^2]}.

On E<=r^2/m it also gives E>=(delta+r*R_U(B))/6 for the ACTUAL
centroids B, without assuming E>=0 in advance. No mass, purity,
stationarity or interface regularity assumption is imposed on f.
The constants are absolute; the threshold m1 is existential and is not
numerically specified. Neither the exponent nor its m-dependence is
claimed sharp. This is a SINGLE-rule statement, not the paired theorem.

START WITH
  GLOBAL_QUANTITATIVE_NEGATIVE_VOTING_STABILITY_20261101.txt

THREE SEPARATE INTERNAL RECONSTRUCTIONS
  mass/QUANTITATIVE_SUCCESSOR_MASS_REVIEW_20261101.txt
  covariance/ROOT_QUANTITATIVE_SECTION3_REVIEW_20261101.txt
  local/QUANTITATIVE_STABILITY_DRAFT_INDEPENDENT_LOCAL_AUDIT_20261101.txt

These are AI-agent mathematical reviews, not external expert validation
or Lean formalization. The new result depends on the same foundational
proof chain as the main candidate. The existing 34-source companion at
../../dependency_review/ supplies those inputs. All primary attribution,
including Mulgund's Gaussian-maximum comparison and the known FJ endpoint
formula, remains in that package and the earlier endpoint supplement.
The original manuscript/PDF/archive remain unchanged.

PROOF CLARIFICATIONS
The mass audit makes the fractional first-moment optimization explicit.
It corrects 'no attainment anywhere' to 'no FULL-NOISE attainment':
fixed-m first-moment attainment is legitimately used. The local audit
supplies a sparse tangent-shift construction proving the required facet
probability bound. The covariance audit exhibits an exact obstruction to
dropping the fixed row cap; the actual-assignment entropy bound supplies
that cap uniformly here. None of these is a counterexample to the stated
main candidate.

REPRODUCIBILITY AND LIMITS
SOURCE_PROVENANCE.json records byte-identical proof/audit copies and the
two portable mass-manifest adaptations. Existing release verification
checks their integrity, not mathematical truth. Numerical stress outputs
are illustrative and are not interval certificates or a theorem threshold.
The isolated mass-coefficient gate near10^13 is not a value of m1.
To reproduce the optional mass calculation, copy stress_mass_constants.py
into a scratch directory and run it there; it writes JSON beside itself.
The covariance script prints its analytic cap-free obstruction bounds.
No private correspondence or third-party full articles are included.

This supplement supports review of the substantial large-alphabet
candidate. External verification and priority remain open. It does not
settle the full all-alphabet Standard Simplex or Plurality conjectures.
