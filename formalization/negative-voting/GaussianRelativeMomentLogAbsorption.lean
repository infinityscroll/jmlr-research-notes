import GaussianRelativeMomentAbsorption

noncomputable section
set_option maxHeartbeats 1800000
open Filter Set
open scoped Topology
namespace NegativeVotingRelativeMomentLogAbsorption
open NegativeVotingRelativeMomentAbsorption NegativeVotingGaussianMaximumSecondMoment

theorem eventually_cutoff_coefficient_log_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀α : ℝ, 1/((n:ℝ)+2) ≤ α →
      C*((n:ℝ)+2)^2*(1+Real.log ((n:ℝ)+2))*
        Real.exp (-16*(1+Real.log ((n:ℝ)+2))) ≤ α := by
  have ht : Tendsto (fun n:ℕ => C/((n:ℝ)+2)^12) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : (12:ℕ) ≠ 0)).comp size_tendsto).const_div_atTop C
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
  intro α hα
  have hm : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hL : 0 ≤ 1+Real.log ((n:ℝ)+2) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hLm : 1+Real.log ((n:ℝ)+2) ≤ (n:ℝ)+2 := by
    linarith [Real.log_le_sub_one_of_pos hm]
  have hexp := cutoff_exponential_le ((n:ℝ)+2) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  calc
    _ ≤ C*((n:ℝ)+2)^2*((n:ℝ)+2)*(1/((n:ℝ)+2)^16) := by gcongr
    _ = (C/((n:ℝ)+2)^12)/((n:ℝ)+2) := by field_simp <;> ring
    _ ≤ 1/((n:ℝ)+2) := div_le_div_of_nonneg_right hn.le hm.le
    _ ≤ α := hα

theorem physical_relative_moment_paid (α m F R G Q C : ℝ)
    (hα : 0 ≤ α) (hm : 1 ≤ m) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hmean : G ≤ R)
    (hcurv : α^2*F^2 ≤ C*m*(1+Real.log m)*R)
    (hQ : Q ≤ 2*α*Real.sqrt (128*(1+Real.log m))*G+
      9600*α^2*m*F^2*Real.exp (-16*(1+Real.log m)))
    (hcut : 9600*C*m^2*(1+Real.log m)*Real.exp (-16*(1+Real.log m)) ≤ α) :
    Q ≤ (25*(1+Real.log m))*α*R := by
  have hm0 : 0 < m := by linarith
  have h2 := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ 2*α*Real.sqrt (128*(1+Real.log m)) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hcurv
    (show 0 ≤ 9600*m*Real.exp (-16*(1+Real.log m)) by positivity)
  have h4 := mul_le_mul_of_nonneg_right hcut hR
  have hL : 1 ≤ 1+Real.log m := by linarith [Real.log_nonneg hm]
  have h5 := mul_le_mul_of_nonneg_right (cutoff_root_le (1+Real.log m) hL)
    (mul_nonneg hα hR)
  nlinarith only [hQ,h2,h3,h4,h5]

end NegativeVotingRelativeMomentLogAbsorption
