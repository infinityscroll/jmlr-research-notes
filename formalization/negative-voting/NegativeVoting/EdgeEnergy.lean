import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact finite-simplex normal-strain algebra

For a centered symmetric matrix, the squared changes of all pairwise squared
edge lengths control its full squared Frobenius norm. This is the finite
identity used in the manuscript's covariance-gap argument. No Gaussian facet
bound or transport inequality is assumed or proved in this module.
-/

namespace NegativeVoting

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The ordered-edge form of the centered symmetric simplex identity. The
unordered-edge sum in the manuscript is one half of the left-hand side. -/
theorem centered_symmetric_edge_energy (E : ι → ι → ℝ)
    (hsym : ∀ i j, E i j = E j i) (hrow : ∀ i, ∑ j, E i j = 0) :
    (∑ i, ∑ j, (E i i + E j j - 2 * E i j) ^ 2) =
      2 * (Fintype.card ι : ℝ) * (∑ i, (E i i) ^ 2) +
      2 * (∑ i, E i i) ^ 2 + 4 * (∑ i, ∑ j, (E i j) ^ 2) := by
  classical
  have hcol (j : ι) : ∑ i, E i j = 0 := by
    calc
      ∑ i, E i j = ∑ i, E j i := Finset.sum_congr rfl (fun i _ => hsym i j)
      _ = 0 := hrow j
  have hr : (∑ i, ∑ j, E j j * E i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_zero]
    simp
  have ha : (∑ i, ∑ _j : ι, (E i i) ^ 2) =
      (Fintype.card ι : ℝ) * ∑ i, (E i i) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hb : (∑ _i : ι, ∑ j, (E j j) ^ 2) =
      (Fintype.card ι : ℝ) * ∑ i, (E i i) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have expand (a b c : ℝ) : (a + b - 2 * c) ^ 2 =
      a ^ 2 + b ^ 2 + 4 * c ^ 2 + 2 * (a * b) -
        4 * (a * c) - 4 * (b * c) := by ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [ha, hb, hr]
  simp_rw [hrow, mul_zero]
  simp only [Finset.sum_const_zero, ← Finset.sum_mul]
  ring

/-- Edge strain controls the Frobenius energy with an explicit constant. -/
theorem frobenius_energy_le_ordered_edge_energy (E : ι → ι → ℝ)
    (hsym : ∀ i j, E i j = E j i) (hrow : ∀ i, ∑ j, E i j = 0) :
    4 * (∑ i, ∑ j, (E i j) ^ 2) ≤
      ∑ i, ∑ j, (E i i + E j j - 2 * E i j) ^ 2 := by
  rw [centered_symmetric_edge_energy E hsym hrow]
  have hsum : 0 ≤ ∑ i, (E i i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (E i i))
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith [mul_nonneg hcard hsum, sq_nonneg (∑ i, E i i)]

/-- Zero edge strain determines a centered symmetric matrix uniquely. -/
theorem centered_edge_energy_zero_iff (E : ι → ι → ℝ)
    (hsym : ∀ i j, E i j = E j i) (hrow : ∀ i, ∑ j, E i j = 0) :
    (∑ i, ∑ j, (E i i + E j j - 2 * E i j) ^ 2) = 0 ↔
      ∀ i j, E i j = 0 := by
  classical
  constructor
  · intro hz
    have hbound := frobenius_energy_le_ordered_edge_energy E hsym hrow
    have hrowpos (i : ι) : 0 ≤ ∑ j, (E i j) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (E i j))
    have hpos : 0 ≤ ∑ i, ∑ j, (E i j) ^ 2 :=
      Finset.sum_nonneg (fun i _ => hrowpos i)
    have htotal : (∑ i, ∑ j, (E i j) ^ 2) = 0 := by rw [hz] at hbound; linarith
    intro i j
    have hi : (∑ j, (E i j) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrowpos i)).mp htotal i (Finset.mem_univ i)
    have hij : (E i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (E i j))).mp hi j (Finset.mem_univ j)
    exact (sq_eq_zero_iff).mp hij
  · intro hzero
    simp only [hzero, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero]

end NegativeVoting
