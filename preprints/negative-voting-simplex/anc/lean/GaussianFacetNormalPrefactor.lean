import GaussianFacetSchurBounds

/-! Quantitative control of the actual normal PDF and transformed-edge prefactor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace NegativeVotingFacetConditionalPlane
variable {d : ℕ}

theorem log_normalVariance_abs_le (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) (hE : ‖covarianceError S‖ ≤ 1/2) :
    |Real.log (normalVariance S n)| ≤ 2*‖covarianceError S‖ := by
  have hp : 0 < normalVariance S n := by
    have hh := (normalVariance_near_bounds S n hn hE).1;linarith
  have hlow := Real.one_sub_inv_le_log_of_pos hp
  have hupp := Real.log_le_sub_one_of_pos hp
  have hinv := normalVariance_inverse_difference S n hn hE
  have hvar := normalVariance_sub_one_abs_le S n hn
  have hnE := normalError_norm_le S n hn
  apply abs_le.mpr
  constructor
  · have hh := (abs_le.mp hinv).1
    linarith
  · have hh := (abs_le.mp hvar).2
    have hnon := norm_nonneg (covarianceError S)
    linarith

theorem log_transformed_norm_abs_le (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (hE : ‖covarianceError S‖ ≤ 1/2) :
    |Real.log ‖S n‖| ≤ ‖covarianceError S‖ := by
  have hh := log_normalVariance_abs_le S n hn hE
  rw [normalVariance_eq_norm_sq S hS,Real.log_pow,abs_mul] at hh
  norm_num at hh
  linarith

theorem transportedLevel_sq_le (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1)
    (hE : ‖covarianceError S‖ ≤ 1/2) :
    (transportedLevel S n h)^2 ≤ 2*‖h‖^2 := by
  have hp : 0 < normalVariance S n := by
    have hh := (normalVariance_near_bounds S n hn hE).1;linarith
  have hi : |inner ℝ n h| ≤ ‖h‖ := by
    simpa only [hn,one_mul] using abs_real_inner_le_norm n h
  have hsq : (inner ℝ n h)^2 ≤ ‖h‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi
  have he : (transportedLevel S n h)^2=(inner ℝ n h)^2/normalVariance S n := by
    simp only [transportedLevel,div_pow,neg_sq,normalVariance_eq_norm_sq S hS]
  rw [he,div_eq_mul_inv]
  calc
    (inner ℝ n h)^2*(normalVariance S n)⁻¹ ≤ ‖h‖^2*2 :=
      mul_le_mul hsq (normalVariance_inv_le_two S n hn hE)
        (inv_nonneg.mpr hp.le) (sq_nonneg _)
    _=2*‖h‖^2 := by ring

/-- This is the full additive prefactor error needed beside the fixed-cap
logarithmic probability ratio. -/
theorem normal_prefactor_error_le (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1)
    (hE : ‖covarianceError S‖ ≤ 1/2) :
    (transportedLevel S n h)^2/2+|Real.log ‖S n‖| ≤ ‖h‖^2+‖covarianceError S‖ := by
  have ha := transportedLevel_sq_le S hS n h hn hE
  have hl := log_transformed_norm_abs_le S hS n hn hE
  linarith

end NegativeVotingFacetConditionalPlane
