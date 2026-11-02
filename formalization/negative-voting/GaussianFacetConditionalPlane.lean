import GaussianFacetDisintegration
import GaussianPositiveCovarianceFactor
import FSC.Support.Definitions

/-! Actual affine transport of a Gaussian normal slice onto a fixed plane. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology
namespace NegativeVotingFacetConditionalPlane
open NegativeVotingDisintegration NegativeVotingPositiveCovariance
variable {d : ℕ}

abbrev Ambient (d : ℕ) := FSC.Coord d

def covariance (S : Ambient d ≃L[ℝ] Ambient d) : Ambient d →L[ℝ] Ambient d :=
  S.toContinuousLinearMap.comp S.toContinuousLinearMap

def normalVariance (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) : ℝ :=
  inner ℝ n (covariance S n)

def transportedNormal (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) : Ambient d :=
  ‖S n‖⁻¹ • S n

def transportedLevel (S : Ambient d ≃L[ℝ] Ambient d) (n h : Ambient d) : ℝ :=
  -inner ℝ n h/‖S n‖

def conditionalMean (S : Ambient d ≃L[ℝ] Ambient d) (n h : Ambient d) : Ambient d :=
  h-(inner ℝ n h/normalVariance S n) • covariance S n

def normalProjection (u : Ambient d) : Ambient d →L[ℝ] Ambient d :=
  ContinuousLinearMap.id ℝ (Ambient d)-(innerSL ℝ u).smulRight u

def conditionalLinear (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) : Ambient d →L[ℝ] Ambient d :=
  S.toContinuousLinearMap.comp (normalProjection (transportedNormal S n))

def schurCovariance (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) : Ambient d →L[ℝ] Ambient d :=
  covariance S-(normalVariance S n)⁻¹ • (innerSL ℝ (covariance S n)).smulRight (covariance S n)

def transportedSliceLaw (S : Ambient d ≃L[ℝ] Ambient d) (n h : Ambient d) : Measure (Ambient d) :=
  (FSC.sliceLaw (transportedNormal S n) (transportedLevel S n h)).map (fun x => S x+h)

@[simp] theorem covariance_apply (S : Ambient d ≃L[ℝ] Ambient d) (x : Ambient d) :
    covariance S x=S (S x) := rfl

@[simp] theorem normalProjection_apply (u x : Ambient d) :
    normalProjection u x=x-inner ℝ u x • u := rfl

@[simp] theorem conditionalLinear_apply (S : Ambient d ≃L[ℝ] Ambient d) (n x : Ambient d) :
    conditionalLinear S n x=S x-inner ℝ (transportedNormal S n) x • S (transportedNormal S n) := by
  simp [conditionalLinear,map_sub,map_smul]

theorem normalVariance_eq_norm_sq (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) :
    normalVariance S n=‖S n‖^2 := by
  have hh := hS n (S n)
  change inner ℝ (S n) (S n)=inner ℝ n (S (S n)) at hh
  simpa only [normalVariance,covariance,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,real_inner_self_eq_norm_sq] using hh.symm

theorem transformed_normal_norm_pos (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) : 0 < ‖S n‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hn0 : n=0 := S.injective (by simpa using h)
  simpa [hn0] using hn

theorem normalVariance_pos (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) :
    0 < normalVariance S n := by
  rw [normalVariance_eq_norm_sq S hS]
  exact sq_pos_of_pos (transformed_normal_norm_pos S n hn)

theorem transportedNormal_unit (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1) : ‖transportedNormal S n‖=1 := by
  have hp := transformed_normal_norm_pos S n hn
  rw [transportedNormal,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ hp.ne']

theorem mapped_transportedNormal (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) :
    S (transportedNormal S n)=‖S n‖⁻¹ • covariance S n := by
  simp only [transportedNormal,map_smul,covariance_apply]

theorem conditionalMean_mem_plane (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    inner ℝ n (conditionalMean S n h)=0 := by
  have hv := normalVariance_pos S hS n hn
  simp only [conditionalMean,inner_sub_right,real_inner_smul_right]
  change inner ℝ n h-(inner ℝ n h/normalVariance S n)*normalVariance S n=0
  field_simp
  ring

theorem mapped_slice_anchor (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    S (transportedLevel S n h • transportedNormal S n)+h=conditionalMean S n h := by
  have hp := transformed_normal_norm_pos S n hn
  have hc : transportedLevel S n h*‖S n‖⁻¹=-(inner ℝ n h/normalVariance S n) := by
    rw [normalVariance_eq_norm_sq S hS]
    unfold transportedLevel
    field_simp
    <;> ring
  rw [map_smul,mapped_transportedNormal,smul_smul,hc]
  unfold conditionalMean
  module

theorem transportedSliceLaw_eq_affineGaussian (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    transportedSliceLaw S n h=(stdGaussian (Ambient d)).map
      (fun x => conditionalMean S n h+conditionalLinear S n x) := by
  unfold transportedSliceLaw FSC.sliceLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  have hh := mapped_slice_anchor S hS n h hn
  change S (transportedLevel S n h • transportedNormal S n+
    (x-inner ℝ (transportedNormal S n) x • transportedNormal S n))+h=_
  rw [map_add,map_sub,map_smul]
  rw [conditionalLinear_apply]
  rw [←hh]
  simp only [map_smul]
  abel



theorem conditionalLinear_adjoint_apply (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n x : Ambient d) :
    (conditionalLinear S n).adjoint x =
      S x-inner ℝ (transportedNormal S n) (S x) • transportedNormal S n := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,conditionalLinear_apply]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  have h1 : inner ℝ (S y) x=inner ℝ y (S x) := hS y x
  have h2 : inner ℝ (S (transportedNormal S n)) x=
      inner ℝ (transportedNormal S n) (S x) := hS _ _
  rw [h1,h2,real_inner_comm (transportedNormal S n) y]
  ring

theorem unit_projection_inner (n x y : Ambient d) (hn : ‖n‖=1) :
    inner ℝ (x-inner ℝ n x • n) (y-inner ℝ n y • n)=
      inner ℝ x y-inner ℝ n x*inner ℝ n y := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow]
  rw [real_inner_comm x n]
  ring

theorem covariance_pairing (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (x y : Ambient d) :
    inner ℝ x (covariance S y)=inner ℝ (S x) (S y) := by
  rw [covariance_apply]
  exact (hS x (S y)).symm

theorem transportedNormal_pairing (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n x : Ambient d) :
    inner ℝ (transportedNormal S n) (S x)=
      ‖S n‖⁻¹*inner ℝ (covariance S n) x := by
  simp only [transportedNormal,real_inner_smul_left,covariance_apply]
  congr 1
  exact (hS (S n) x).symm

theorem conditionalLinear_adjoint_inner (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (x y : Ambient d) :
    inner ℝ ((conditionalLinear S n).adjoint x) ((conditionalLinear S n).adjoint y)=
      inner ℝ x (schurCovariance S n y) := by
  rw [conditionalLinear_adjoint_apply S hS,conditionalLinear_adjoint_apply S hS,
    unit_projection_inner _ _ _ (transportedNormal_unit S n hn),
    transportedNormal_pairing S hS,transportedNormal_pairing S hS]
  simp only [schurCovariance,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,inner_sub_right,real_inner_smul_right]
  rw [covariance_pairing S hS,normalVariance_eq_norm_sq S hS,
    real_inner_comm x (covariance S n)]
  ring

theorem conditionalLinear_mem_plane (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) (x : Ambient d) :
    inner ℝ n (conditionalLinear S n x)=0 := by
  have hnS := transformed_normal_norm_pos S n hn
  have h1 (y : Ambient d) : inner ℝ n (S y)=
      ‖S n‖*inner ℝ (transportedNormal S n) y := by
    have hh : inner ℝ (S n) y=inner ℝ n (S y) := hS _ _
    rw [←hh,transportedNormal,real_inner_smul_left]
    field_simp
  have h2 : inner ℝ n (S (transportedNormal S n))=‖S n‖ := by
    rw [h1,real_inner_self_eq_norm_sq,transportedNormal_unit S n hn]
    ring
  rw [conditionalLinear_apply,inner_sub_right,real_inner_smul_right,h1 x,h2]
  ring

/-- The literal transported slice has the displayed Schur conditional mean. -/
theorem integral_id_transportedSliceLaw (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    ∫ x,x ∂transportedSliceLaw S n h=conditionalMean S n h := by
  rw [transportedSliceLaw_eq_affineGaussian S hS n h hn,
    integral_map (by fun_prop) (by fun_prop)]
  have hi : Integrable (fun x : Ambient d => conditionalLinear S n x)
      (stdGaussian (Ambient d)) :=
    ((conditionalLinear S n).comp_memLp' IsGaussian.memLp_two_id).integrable (by norm_num)
  rw [integral_add (integrable_const _) hi,
    (conditionalLinear S n).integral_comp_comm IsGaussian.integrable_fun_id,
    integral_id_stdGaussian]
  simp

/-- The actual covariance bilinear form of the transported slice is the Schur complement. -/
theorem covarianceBilin_transportedSliceLaw (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1)
    (x y : Ambient d) :
    covarianceBilin (transportedSliceLaw S n h) x y=
      inner ℝ x (schurCovariance S n y) := by
  have hh : (stdGaussian (Ambient d)).map
      (fun z => conditionalMean S n h+conditionalLinear S n z)=
      ((stdGaussian (Ambient d)).map (conditionalLinear S n)).map
        (fun z => conditionalMean S n h+z) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [transportedSliceLaw_eq_affineGaussian S hS n h hn,hh,
    covarianceBilin_map_const_add,covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,innerSL_apply_apply]
  exact conditionalLinear_adjoint_inner S hS n hn x y


theorem transportedSliceLaw_isGaussian (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    IsGaussian (transportedSliceLaw S n h) := by
  have hh : IsGaussian (((stdGaussian (Ambient d)).map (conditionalLinear S n)).map
      (fun z => conditionalMean S n h+z)) := inferInstance
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hh
  rw [transportedSliceLaw_eq_affineGaussian S hS n h hn]
  exact hh

theorem transportedSliceLaw_plane_ae (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n h : Ambient d) (hn : ‖n‖=1) :
    ∀ᵐ x ∂transportedSliceLaw S n h,inner ℝ n x=0 := by
  rw [transportedSliceLaw_eq_affineGaussian S hS n h hn]
  apply (ae_map_iff (by fun_prop) (by exact (isClosed_eq (by fun_prop)
    continuous_const).measurableSet)).2
  filter_upwards with x
  rw [inner_add_right,conditionalMean_mem_plane S hS n h hn,
    conditionalLinear_mem_plane S hS n hn,add_zero]

theorem normalProjection_mem_plane (n : Ambient d) (hn : ‖n‖=1) (x : Ambient d) :
    inner ℝ n (normalProjection n x)=0 := by
  rw [normalProjection_apply,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn]
  ring

theorem normalProjection_eq_self (n x : Ambient d) (hx : inner ℝ n x=0) :
    normalProjection n x=x := by simp [normalProjection_apply,hx]

theorem normalProjection_adjoint_apply (n x : Ambient d) :
    (normalProjection n).adjoint x=normalProjection n x := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,normalProjection_apply,
    normalProjection_apply,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,
    real_inner_comm y n]
  ring

end NegativeVotingFacetConditionalPlane
