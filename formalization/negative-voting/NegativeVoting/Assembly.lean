import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The finite algebra of the local/exterior assembly

These are implications between explicit real inequalities. The Gaussian estimates
that supply the hypotheses are NOT proved in this file. In particular, no Gaussian
simplex theorem or complexity-theoretic hardness theorem is declared here.
-/

namespace NegativeVoting

/-- The retained squared-centroid-distance term cancels the affine norm exactly.
`mm`, `bb`, and `mb` represent squared norms and an inner product, respectively. -/
theorem centroid_cancellation (r w mm bb mb : ℝ) :
    r * (w - mm) + r * (mm + bb - 2 * mb) =
      2 * r * ((w + bb) / 2 - mb) := by
  ring

/-- A Hermite degree-two bound and a signed-tail bound imply the exterior
comparison. All analytic content is represented by the explicit hypotheses. -/
theorem exterior_from_hermite_bounds
    (E D J r Q T A B : ℝ)
    (hD : D = r * J)
    (hE : E = D + r ^ 2 * Q + T)
    (hsecond : -A * J ≤ Q)
    (htail : |T| ≤ B * r ^ 3 * J) :
    D * (1 - A * r - B * r ^ 2) ≤ E := by
  have hq := mul_le_mul_of_nonneg_left hsecond (sq_nonneg r)
  have ht : -(B * r ^ 3 * J) ≤ T := (abs_le.mp htail).1
  rw [hE, hD]
  nlinarith [hq]

/-- A positive deficit excludes an exterior competitor when the relative losses
sum to at most one half. -/
theorem exterior_strict (E D a b : ℝ)
    (hD : 0 < D) (hbound : D * (1 - a - b) ≤ E)
    (hloss : a + b ≤ 1 / 2) : 0 < E := by
  have : 0 < D * (1 - a - b) := mul_pos hD (by linarith)
  exact lt_of_lt_of_le this hbound

/-- The scalar zero-deficit argument inside the local region. -/
theorem local_rigidity (E δ R r : ℝ)
    (hr : 0 < r) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hlocal : δ / 2 + r * R ≤ E) (hcompetitive : E ≤ 0) :
    E = 0 ∧ δ = 0 ∧ R = 0 := by
  have hrR : 0 ≤ r * R := mul_nonneg (le_of_lt hr) hR
  have hδzero : δ = 0 := by linarith
  have hrRzero : r * R = 0 := by linarith
  have hRzero : R = 0 := (mul_eq_zero.mp hrRzero).resolve_left (ne_of_gt hr)
  exact ⟨by linarith, hδzero, hRzero⟩

/-- Conditional two-region closure. The local and exterior estimates are only
required for competitive assignments (`E ≤ 0`), as in the manuscript.
The conclusion is scalar equality and localization, not Gaussian rigidity. -/
theorem competitive_assembly
    (E d δ R D r τ a b : ℝ)
    (hr : 0 < r) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hlocal : E ≤ 0 → d ≤ τ → δ / 2 + r * R ≤ E)
    (hexterior : E ≤ 0 → τ < d → 0 < D ∧ D * (1 - a - b) ≤ E)
    (hloss : a + b ≤ 1 / 2) (hcompetitive : E ≤ 0) :
    E = 0 ∧ δ = 0 ∧ R = 0 ∧ d ≤ τ := by
  by_cases hd : d ≤ τ
  · obtain ⟨hE, hδzero, hRzero⟩ :=
      local_rigidity E δ R r hr hδ hR (hlocal hcompetitive hd) hcompetitive
    exact ⟨hE, hδzero, hRzero, hd⟩
  · obtain ⟨hD, hbound⟩ := hexterior hcompetitive (lt_of_not_ge hd)
    have hpositive := exterior_strict E D a b hD hbound hloss
    linarith

/-- Conditional scalar optimality, allowing all noncompetitive assignments too.
This theorem does not provide either analytic comparison hypothesis. -/
theorem nonnegative_of_local_exterior
    (E d δ R D r τ a b : ℝ)
    (hr : 0 < r) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hlocal : E ≤ 0 → d ≤ τ → δ / 2 + r * R ≤ E)
    (hexterior : E ≤ 0 → τ < d → 0 < D ∧ D * (1 - a - b) ≤ E)
    (hloss : a + b ≤ 1 / 2) : 0 ≤ E := by
  by_cases h : E ≤ 0
  · have hz := (competitive_assembly E d δ R D r τ a b
      hr hδ hR hlocal hexterior hloss h).1
    exact le_of_eq hz.symm
  · exact le_of_lt (lt_of_not_ge h)

end NegativeVoting
