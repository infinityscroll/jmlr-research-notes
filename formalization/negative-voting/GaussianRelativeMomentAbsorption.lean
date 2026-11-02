import GaussianRelativeTailMomentComparison
import GaussianLocalRectangleAbsorption

/-! The relative maximum-tail error is paid by the actual covariance
curvature, including zero deficit. No fixed positive remainder is retained. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace NegativeVotingRelativeMomentAbsorption
open NegativeVotingGaussianMaximumSecondMoment

lemma cutoff_exponential_le (m : ℝ) (hm : 1 ≤ m) :
    Real.exp (-16*(1+Real.log m)) ≤ 1/m^16 := by
  have hm0 : 0 < m := by linarith
  calc
    _ ≤ Real.exp (-16*Real.log m) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [show -16*Real.log m=Real.log m*(-16:ℝ) by ring,←Real.rpow_def_of_pos hm0,
        Real.rpow_neg hm0.le]
      norm_num

theorem eventually_cutoff_coefficient_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀α : ℝ, 1/((n:ℝ)+2) ≤ α →
      C*((n:ℝ)+2)^2*Real.exp (-16*(1+Real.log ((n:ℝ)+2))) ≤ α := by
  have ht : Tendsto (fun n:ℕ => C/((n:ℝ)+2)^13) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : (13:ℕ) ≠ 0)).comp size_tendsto).const_div_atTop C
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
  intro α hα
  have hm : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hexp := cutoff_exponential_le ((n:ℝ)+2) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hx := mul_le_mul_of_nonneg_left hexp (show 0 ≤ C*((n:ℝ)+2)^2 by positivity)
  have heq : C*((n:ℝ)+2)^2*(1/((n:ℝ)+2)^16)=(C/((n:ℝ)+2)^13)/((n:ℝ)+2) := by
    field_simp <;> ring
  rw [heq] at hx
  exact hx.trans ((div_le_div_of_nonneg_right hn.le hm.le).trans hα)

lemma cutoff_root_le (L : ℝ) (hL : 1 ≤ L) :
    2*Real.sqrt (128*L)+1 ≤ 25*L := by
  have hs := Real.sq_sqrt (show 0 ≤ 128*L by positivity)
  have hs0 := Real.sqrt_nonneg (128*L)
  have hbound : Real.sqrt (128*L) ≤ 12*L := by nlinarith [sq_nonneg (L-1)]
  linarith

/-- A covariance-squared CDF remainder gives a purely deficit-relative
free-moment bound after the explicit sqrt(128 logScale) cutoff. -/
theorem relative_moment_paid (α m F R G Q C : ℝ)
    (hm : 1 ≤ m) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hmean : α^2*G ≤ α*R)
    (hcurv : α^2*F^2 ≤ C*m*R)
    (hQ : Q ≤ 2*Real.sqrt (128*(1+Real.log m))*G+
      9600*m*F^2*Real.exp (-16*(1+Real.log m)))
    (hcut : 9600*C*m^2*Real.exp (-16*(1+Real.log m)) ≤ α) :
    α^2*Q ≤ (25*(1+Real.log m))*α*R := by
  have hm0 : 0 < m := by linarith
  have hα : 0 ≤ α := (by positivity : 0 ≤ 9600*C*m^2*Real.exp (-16*(1+Real.log m))).trans hcut
  have h1 := mul_le_mul_of_nonneg_left hQ (sq_nonneg α)
  have h2 := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ 2*Real.sqrt (128*(1+Real.log m)) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hcurv
    (show 0 ≤ 9600*m*Real.exp (-16*(1+Real.log m)) by positivity)
  have h4 := mul_le_mul_of_nonneg_right hcut hR
  have hL : 1 ≤ 1+Real.log m := by linarith [Real.log_nonneg hm]
  have h5 := mul_le_mul_of_nonneg_right (cutoff_root_le (1+Real.log m) hL)
    (mul_nonneg hα hR)
  nlinarith only [h1,h2,h3,h4,h5]

end NegativeVotingRelativeMomentAbsorption
