/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of upstream files: Kim Morrison; Alexander Bentkamp, Mohanad Ahmed.

Compatibility backport for mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
The exact IsProperStar class and the proof of the zero quadratic-form criterion
are from mathlib commit 2cabef97b63d3275776b8b060d802de6a6fa1055,
Mathlib/Algebra/Star/Basic.lean and Mathlib/LinearAlgebra/Matrix/PosDef.lean.
Helper names are scoped to avoid shadowing the older NoZeroDivisors versions.
No theorem statement in the pinned Tau Ceti sources is weakened or strengthened.
-/
module
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

variable {R : Type*}

/-- A *proper star* is when `star x * x = 0` implies `x = 0`. -/
class IsProperStar (R : Type*) [Mul R] [Zero R] [Star R] : Prop where
  eq_zero_of_star_mul_self_eq_zero {x : R} : star x * x = 0 → x = 0

instance (priority := low) [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] [StarRing R] :
    IsProperStar R where
  eq_zero_of_star_mul_self_eq_zero := by
    intro x hx
    rcases mul_eq_zero.mp hx with h | h
    · exact star_eq_zero.mp h
    · exact h

namespace TauCetiCompat

@[simp] theorem star_mul_self_eq_zero [MulZeroClass R] [Star R] [IsProperStar R] {x : R} :
    star x * x = 0 ↔ x = 0 :=
  ⟨IsProperStar.eq_zero_of_star_mul_self_eq_zero, fun h ↦ by simp [h]⟩

open Matrix
variable {n : Type*} [Fintype n]
variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [IsProperStar R]

theorem dotProduct_star_self_eq_zero {v : n → R} : star v ⬝ᵥ v = 0 ↔ v = 0 :=
  (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans <|
    by simp [funext_iff]

/-- Backported proper-star version; the older library requires NoZeroDivisors. -/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n R} (hA : A.PosSemidef) {x : n → R} :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  suffices h : ∀ y, star x ⬝ᵥ A *ᵥ y = 0 by
    refine dotProduct_star_self_eq_zero.mp ?_
    simpa [dotProduct_mulVec, star_mulVec, hA.isHermitian.eq] using h (A *ᵥ x)
  intro y
  set z := star x ⬝ᵥ A *ᵥ y with hz
  suffices h : star z * z ≤ 0 by simpa using le_antisymm h (by simp)
  calc star z * z ≤ 2 • (star z * z) + star z * z * (star y ⬝ᵥ A *ᵥ y) := by
        rw [two_smul, add_assoc]
        apply le_add_of_nonneg_right (add_nonneg (by simp) _)
        exact mul_nonneg (by simp) (hA.dotProduct_mulVec_nonneg y)
    _ ≤ 0 := neg_nonneg.mp <| le_of_le_of_eq
        (hA.dotProduct_mulVec_nonneg (-(1 + star y ⬝ᵥ A *ᵥ y) • x + star z • y)) <| by
      simp [mulVec_add, mulVec_smul, hx, ← hz, ← hA.isHermitian.star_dotProduct_mulVec_comm x y,
        hA.isHermitian.star_dotProduct_mulVec_comm y y]
      ring

end TauCetiCompat
