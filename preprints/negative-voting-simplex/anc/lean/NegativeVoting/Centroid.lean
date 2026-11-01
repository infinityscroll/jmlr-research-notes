import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact finite-coordinate algebra used by the retained centroid-square term. -/

namespace NegativeVoting

open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Coordinatewise squared distance decomposition, with all sums explicit. -/
theorem squared_distance_identity (M B : ι → ℝ) :
    ∑ i, (M i - B i) ^ 2 =
      (∑ i, M i ^ 2) + (∑ i, B i ^ 2) - 2 * ∑ i, M i * B i := by
  calc
    ∑ i, (M i - B i) ^ 2 = ∑ i, (M i ^ 2 + B i ^ 2 - 2 * (M i * B i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The exact retained-square cancellation for actual finite centroid arrays.
The index can be the product of labels and ambient coordinates. -/
theorem finite_centroid_cancellation (M B : ι → ℝ) (r w : ℝ) :
    r * (w - ∑ i, M i ^ 2) + r * (∑ i, (M i - B i) ^ 2) =
      2 * r * ((w + ∑ i, B i ^ 2) / 2 - ∑ i, M i * B i) := by
  rw [squared_distance_identity]
  ring

/-- An exact squared mass defect vanishes precisely at the specified mass vector. -/
theorem squared_defect_eq_zero_iff (p u : ι → ℝ) :
    (∑ i, (p i - u i) ^ 2) = 0 ↔ ∀ i, p i = u i := by
  constructor
  · intro h i
    have hz : (p i - u i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p j - u j))).mp h i
        (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    simp [h]

end NegativeVoting
