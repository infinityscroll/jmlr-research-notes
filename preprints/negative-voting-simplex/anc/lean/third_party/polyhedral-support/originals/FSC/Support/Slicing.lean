import FSC.Support.Definitions
import FSC.Gaussian.SinglePin

/-! Exact standard-Gaussian slicing along a unit normal in the original ambient space. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FSC

/-- Orthogonal residual without a dimension reduction or choice of basis. -/
def normalResidual {d : ℕ} (w : Coord d) : Coord d →L[ℝ] Coord d :=
  ContinuousLinearMap.id ℝ (Coord d) - (innerSL ℝ w).smulRight w

@[simp] theorem normalResidual_apply {d : ℕ} (w y : Coord d) :
    normalResidual w y = y - inner ℝ w y • w := rfl

theorem normalResidual_reconstruction {d : ℕ} (w y : Coord d) :
    inner ℝ w y • w + normalResidual w y = y := by
  simp only [normalResidual_apply]
  abel

/-- The actual scalar projection law, valid also for a zero normal. -/
theorem map_inner_stdGaussian {d : ℕ} (w : Coord d) :
    (stdGaussian (Coord d)).map (innerSL ℝ w) = gaussianReal 0 (‖w‖ ^ 2).toNNReal := by
  have h : HasGaussianLaw (innerSL ℝ w) (stdGaussian (Coord d)) :=
    IsGaussian.hasGaussianLaw_id.map (innerSL ℝ w)
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm] using h.map_eq_gaussianReal

/-- A unit projection is a standard real Gaussian. -/
theorem map_unit_inner_stdGaussian {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) :
    (stdGaussian (Coord d)).map (innerSL ℝ w) = gaussianReal 0 1 := by
  simpa [hw] using map_inner_stdGaussian w

/-- Scalar projection and its orthogonal residual are jointly Gaussian and independent. -/
theorem normalResidual_indep_inner {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) :
    IndepFun (normalResidual w) (innerSL ℝ w) (stdGaussian (Coord d)) := by
  have hjoint : HasGaussianLaw
      (fun y : Coord d ↦ (normalResidual w y, inner ℝ w y)) (stdGaussian (Coord d)) :=
    IsGaussian.hasGaussianLaw_id.map ((normalResidual w).prod (innerSL ℝ w))
  apply hjoint.indepFun_of_covariance_inner
  intro u v
  have heq : (fun y : Coord d ↦ inner ℝ u (normalResidual w y)) =
      fun y ↦ inner ℝ (u - inner ℝ u w • w) y := by
    funext y
    simp only [normalResidual_apply, inner_sub_right, inner_sub_left,
      real_inner_smul_right, real_inner_smul_left]
    ring
  rw [heq]
  have hcov : cov[fun y : Coord d ↦ inner ℝ (u - inner ℝ u w • w) y,
      fun y ↦ inner ℝ w y; stdGaussian (Coord d)] = inner ℝ (u - inner ℝ u w • w) w := by
    simpa only [covarianceBilin_stdGaussian, innerSL_apply_apply] using!
      (covarianceBilin_apply_eq_cov (μ := stdGaussian (Coord d))
        IsGaussian.memLp_two_id (u - inner ℝ u w • w) w).symm
  simp only [RCLike.inner_apply, conj_trivial]
  rw [covariance_mul_const_right, hcov]
  simp [inner_sub_left, real_inner_smul_left, hw]

/-- Exact product law in the original ambient residual space. -/
theorem map_normalResidual_inner {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) :
    (stdGaussian (Coord d)).map (fun y ↦ (normalResidual w y, inner ℝ w y)) =
      ((stdGaussian (Coord d)).map (normalResidual w)).prod (gaussianReal 0 1) := by
  have h := (normalResidual_indep_inner w hw).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)
  simpa only [map_unit_inner_stdGaussian w hw, innerSL_apply_apply] using! h

/-- Frozen slice law is translation of the actual orthogonal residual law. -/
theorem sliceLaw_eq_map_normalResidual {d : ℕ} (w : Coord d) (z : ℝ) :
    sliceLaw w z = ((stdGaussian (Coord d)).map (normalResidual w)).map
      (fun r ↦ z • w + r) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Fubini for all real normal pins, obtained from the exact Gaussian product law. -/
theorem lintegral_normalSlice {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1)
    (f : Coord d × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y : Coord d, f (y, inner ℝ w y) ∂stdGaussian (Coord d)) =
      ∫⁻ z : ℝ, ∫⁻ y : Coord d, f (y, z) ∂sliceLaw w z ∂gaussianReal 0 1 := by
  let H : Coord d × ℝ → ℝ≥0∞ := fun p ↦ f (p.2 • w + p.1, p.2)
  have hH : Measurable H := hf.comp (by fun_prop)
  calc
    (∫⁻ y : Coord d, f (y, inner ℝ w y) ∂stdGaussian (Coord d)) =
        ∫⁻ y : Coord d, H (normalResidual w y, inner ℝ w y) ∂stdGaussian (Coord d) := by
      apply lintegral_congr
      intro y
      simp only [H, normalResidual_reconstruction]
    _ = ∫⁻ p, H p ∂(stdGaussian (Coord d)).map
        (fun y ↦ (normalResidual w y, inner ℝ w y)) :=
      (lintegral_map hH (by fun_prop)).symm
    _ = ∫⁻ p, H p ∂((stdGaussian (Coord d)).map (normalResidual w)).prod
        (gaussianReal 0 1) := by rw [map_normalResidual_inner w hw]
    _ = ∫⁻ z : ℝ, ∫⁻ r : Coord d, f (z • w + r, z)
        ∂(stdGaussian (Coord d)).map (normalResidual w) ∂gaussianReal 0 1 :=
      lintegral_prod_symm' H hH
    _ = ∫⁻ z : ℝ, ∫⁻ y : Coord d, f (y, z) ∂sliceLaw w z ∂gaussianReal 0 1 := by
      apply lintegral_congr
      intro z
      rw [sliceLaw_eq_map_normalResidual]
      exact (lintegral_map (hf.comp (measurable_id.prodMk measurable_const))
        (by fun_prop)).symm

/-- The unit-normal coordinate is fixed at the prescribed real pin almost surely. -/
theorem sliceLaw_inner_ae {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) (z : ℝ) :
    ∀ᵐ y ∂sliceLaw w z, inner ℝ w y = z := by
  rw [sliceLaw]
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) measurable_const)).2
  apply Filter.Eventually.of_forall
  intro y
  simp [inner_add_right, inner_sub_right, real_inner_smul_right, hw]

/-- A nonzero Gaussian linear functional has no atom at any real boundary. -/
theorem ae_inner_ne {d : ℕ} (w : Coord d) (hw : w ≠ 0) (a : ℝ) :
    ∀ᵐ y ∂stdGaussian (Coord d), inner ℝ w y ≠ a := by
  have hv : (‖w‖ ^ 2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hw)))
  haveI := noAtoms_gaussianReal (μ := (0 : ℝ)) hv
  have h := (gaussianReal 0 (‖w‖ ^ 2).toNNReal).ae_ne a
  rw [← map_inner_stdGaussian w] at h
  exact (ae_map_iff (innerSL ℝ w).measurable.aemeasurable
    (measurableSet_eq_fun measurable_id measurable_const).compl).1 h

end FSC
