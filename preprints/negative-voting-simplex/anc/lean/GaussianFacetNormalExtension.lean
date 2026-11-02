import GaussianFacetConditionalPlane
import GaussianCovarianceRealization

/-! Positive ambient extension of the actual Schur slice covariance.
The independent normal direction is restored, so a cylindrical event can be
handled by an ordinary nondegenerate affine Gaussian in the fixed ambient space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology
namespace NegativeVotingFacetConditionalPlane
open NegativeVotingPositiveCovariance
variable {d : ℕ}

def extendedCovariance (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) :
    Ambient d →L[ℝ] Ambient d :=
  schurCovariance S n+(innerSL ℝ n).smulRight n

def cylindricalEvent (n : Ambient d) (A : Set (Ambient d)) : Set (Ambient d) :=
  (normalProjection n) ⁻¹' A

theorem schurCovariance_symmetric (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) :
    (schurCovariance S n).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (schurCovariance S n x) y=inner ℝ x (schurCovariance S n y)
  rw [real_inner_comm,←conditionalLinear_adjoint_inner S hS n hn,
    real_inner_comm,conditionalLinear_adjoint_inner S hS n hn]

theorem schurCovariance_normal (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) :
    schurCovariance S n n=0 := by
  have hv := normalVariance_pos S hS n hn
  change covariance S n-(normalVariance S n)⁻¹ •
    (inner ℝ (covariance S n) n • covariance S n)=0
  rw [real_inner_comm]
  change covariance S n-(normalVariance S n)⁻¹ •
    (normalVariance S n • covariance S n)=0
  rw [smul_smul,inv_mul_cancel₀ hv.ne',one_smul,sub_self]

theorem schurCovariance_projection (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (x : Ambient d) :
    schurCovariance S n (normalProjection n x)=schurCovariance S n x := by
  rw [normalProjection_apply,map_sub,map_smul,schurCovariance_normal S hS n hn]
  simp

theorem schurCovariance_mem_plane (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (x : Ambient d) : inner ℝ n (schurCovariance S n x)=0 := by
  have hh : inner ℝ (schurCovariance S n n) x=inner ℝ n (schurCovariance S n x) :=
    schurCovariance_symmetric S hS n hn n x
  rw [←hh,schurCovariance_normal S hS n hn,inner_zero_left]

theorem extendedCovariance_symmetric (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) :
    (extendedCovariance S n).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (schurCovariance S n x+inner ℝ n x • n) y=
    inner ℝ x (schurCovariance S n y+inner ℝ n y • n)
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  have hh : inner ℝ (schurCovariance S n x) y=inner ℝ x (schurCovariance S n y) :=
    schurCovariance_symmetric S hS n hn x y
  rw [hh,real_inner_comm x n]
  ring

theorem extendedCovariance_quadratic (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (x : Ambient d) :
    inner ℝ x (extendedCovariance S n x)=
      ‖(conditionalLinear S n).adjoint x‖^2+(inner ℝ n x)^2 := by
  change inner ℝ x (schurCovariance S n x+inner ℝ n x • n)=_
  rw [inner_add_right,real_inner_smul_right,
    ←conditionalLinear_adjoint_inner S hS n hn,real_inner_self_eq_norm_sq,
    real_inner_comm x n]
  ring

theorem extendedCovariance_pd (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1) :
    extendedCovariance S n ∈ pdCone := by
  refine ⟨extendedCovariance_symmetric S hS n hn,?_⟩
  intro x hx
  rw [extendedCovariance_quadratic S hS n hn]
  by_contra hnot
  have hle := le_of_not_gt hnot
  have hnorm : ‖(conditionalLinear S n).adjoint x‖=0 := by
    nlinarith [sq_nonneg (inner ℝ n x),norm_nonneg ((conditionalLinear S n).adjoint x)]
  have hnx : inner ℝ n x=0 := by
    nlinarith [sq_nonneg (‖(conditionalLinear S n).adjoint x‖)]
  have hz := norm_eq_zero.mp hnorm
  rw [conditionalLinear_adjoint_apply S hS] at hz
  have he : S x=inner ℝ (transportedNormal S n) (S x) • transportedNormal S n :=
    sub_eq_zero.mp hz
  let a := inner ℝ (transportedNormal S n) (S x)*‖S n‖⁻¹
  have hxa : x=a • n := by
    apply S.injective
    rw [he,map_smul,transportedNormal,smul_smul]
    rfl
  have ha : a=0 := by
    rw [hxa,real_inner_smul_right,real_inner_self_eq_norm_sq,hn] at hnx
    simpa using hnx
  exact hx (by rw [hxa,ha,zero_smul])

theorem extendedCovariance_projected_pairing (S : Ambient d ≃L[ℝ] Ambient d)
    (hS : S.toLinearMap.IsSymmetric) (n : Ambient d) (hn : ‖n‖=1)
    (x y : Ambient d) :
    inner ℝ (normalProjection n x) (extendedCovariance S n (normalProjection n y))=
      inner ℝ x (schurCovariance S n y) := by
  change inner ℝ (normalProjection n x)
    (schurCovariance S n (normalProjection n y)+inner ℝ n (normalProjection n y) • n)=_
  rw [normalProjection_mem_plane n hn,zero_smul,add_zero,
    schurCovariance_projection S hS n hn,normalProjection_apply,
    inner_sub_left,real_inner_smul_left,schurCovariance_mem_plane S hS n hn]
  ring

theorem symmetric_equiv_adjoint_apply (R : Ambient d ≃L[ℝ] Ambient d)
    (hR : R.toLinearMap.IsSymmetric) (x : Ambient d) :
    R.toContinuousLinearMap.adjoint x=R x := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact hR y x

theorem integral_id_linearGaussian (L : Ambient d →L[ℝ] Ambient d) :
    ∫ x,x ∂(stdGaussian (Ambient d)).map L=0 := by
  rw [integral_map (by fun_prop) (by fun_prop),
    L.integral_comp_comm IsGaussian.integrable_fun_id,integral_id_stdGaussian,map_zero]

/-- Restoring an independent normal component changes no projected slice law. -/
theorem transportedSliceLaw_eq_projectedGaussian
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (n h : Ambient d) (hn : ‖n‖=1)
    (R : Ambient d ≃L[ℝ] Ambient d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=extendedCovariance S n) :
    transportedSliceLaw S n h=(stdGaussian (Ambient d)).map
      (fun x => conditionalMean S n h+normalProjection n (R x)) := by
  let L := (normalProjection n).comp R.toContinuousLinearMap
  have hc : (stdGaussian (Ambient d)).map (conditionalLinear S n)=
      (stdGaussian (Ambient d)).map L := by
    apply ProbabilityTheory.IsGaussian.ext
    · change (∫ x,x ∂(stdGaussian (Ambient d)).map (conditionalLinear S n))=
        (∫ x,x ∂(stdGaussian (Ambient d)).map L)
      rw [integral_id_linearGaussian,integral_id_linearGaussian]
    · ext x y
      rw [covarianceBilin_map IsGaussian.memLp_two_id,
        covarianceBilin_map IsGaussian.memLp_two_id,
        covarianceBilin_stdGaussian,innerSL_apply_apply,innerSL_apply_apply,
        conditionalLinear_adjoint_inner S hS n hn]
      have hLa (z : Ambient d) : L.adjoint z=R (normalProjection n z) := by
        simp only [L,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
          normalProjection_adjoint_apply,symmetric_equiv_adjoint_apply R hR]
      rw [hLa,hLa]
      calc
        inner ℝ x (schurCovariance S n y)=
            inner ℝ (normalProjection n x) (extendedCovariance S n (normalProjection n y)) :=
          (extendedCovariance_projected_pairing S hS n hn x y).symm
        _=inner ℝ (R (normalProjection n x)) (R (normalProjection n y)) := by
          rw [←hRR]
          exact (hR _ _).symm
  rw [transportedSliceLaw_eq_affineGaussian S hS n h hn]
  have hh := congrArg (fun μ : Measure (Ambient d) => μ.map
    (fun x => conditionalMean S n h+x)) hc
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

/-- The probability of a fixed planar event equals the probability of its cylinder
under the nondegenerate ambient Gaussian extension. -/
theorem transportedSliceLaw_event_eq_cylinder
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (n h : Ambient d) (hn : ‖n‖=1)
    (R : Ambient d ≃L[ℝ] Ambient d) (hR : R.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=extendedCovariance S n)
    (A : Set (Ambient d)) (hA : MeasurableSet A) :
    transportedSliceLaw S n h A=
      ((stdGaussian (Ambient d)).map (fun x => conditionalMean S n h+R x))
        (cylindricalEvent n A) := by
  unfold cylindricalEvent
  rw [transportedSliceLaw_eq_projectedGaussian S hS n h hn R hR hRR,
    Measure.map_apply (by fun_prop) hA,
    Measure.map_apply (by fun_prop) (hA.preimage (by fun_prop))]
  congr 1
  ext x
  change (conditionalMean S n h+normalProjection n (R x)∈A) ↔
    normalProjection n (conditionalMean S n h+R x)∈A
  rw [map_add,normalProjection_eq_self n _ (conditionalMean_mem_plane S hS n h hn)]

/-- A symmetric invertible covariance factor exists; it is not an input. -/
theorem exists_extended_factor_and_event_law
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (n h : Ambient d) (hn : ‖n‖=1) :
    ∃R : Ambient d ≃L[ℝ] Ambient d,
      R.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=extendedCovariance S n ∧
      ∀A : Set (Ambient d),MeasurableSet A →
        transportedSliceLaw S n h A=
          ((stdGaussian (Ambient d)).map (fun x => conditionalMean S n h+R x))
            (cylindricalEvent n A) := by
  obtain ⟨R,hR,_,hRR⟩ := exists_positive_factor _ (extendedCovariance_pd S hS n hn)
  exact ⟨R,hR,hRR,fun A hA =>
    transportedSliceLaw_event_eq_cylinder S hS n h hn R hR hRR A hA⟩


theorem extendedCovariance_eq_id (S : Ambient d ≃L[ℝ] Ambient d)
    (n : Ambient d) (hn : ‖n‖=1)
    (hC : covariance S=ContinuousLinearMap.id ℝ (Ambient d)) :
    extendedCovariance S n=ContinuousLinearMap.id ℝ (Ambient d) := by
  simp only [extendedCovariance,schurCovariance,normalVariance,hC,
    ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,hn,one_pow,inv_one,one_smul]
  abel

theorem conditionalMean_zero (S : Ambient d ≃L[ℝ] Ambient d) (n : Ambient d) :
    conditionalMean S n 0=0 := by simp [conditionalMean]

/-- The factor may be chosen positive semidefinite as well as invertible. -/
theorem exists_positive_psd_factor (C : Ambient d →L[ℝ] Ambient d) (hC : C∈pdCone) :
    ∃R : Ambient d ≃L[ℝ] Ambient d,
      R.toContinuousLinearMap∈psdCone ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=C := by
  obtain ⟨R,hR,hRR⟩ := NegativeVotingCovarianceRealization.exists_psd_factor C
    (pdCone_subset_psdCone hC)
  have hi : Function.Injective R := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hx
    have hz : R (x-y)=0 := by rw [map_sub,hxy,sub_self]
    have hcz : C (x-y)=0 := by
      rw [←hRR]
      change R (R (x-y))=0
      rw [hz,map_zero]
    have hp := hC.2 (x-y) hx
    rw [hcz,inner_zero_right] at hp
    exact (lt_irrefl (0:ℝ)) hp
  let T := ContinuousLinearEquiv.ofBijective R (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨T,hR,hRR⟩

theorem exists_extended_psd_factor_and_event_law
    (S : Ambient d ≃L[ℝ] Ambient d) (hS : S.toLinearMap.IsSymmetric)
    (n h : Ambient d) (hn : ‖n‖=1) :
    ∃R : Ambient d ≃L[ℝ] Ambient d,
      R.toContinuousLinearMap∈psdCone ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=extendedCovariance S n ∧
      ∀A : Set (Ambient d),MeasurableSet A →
        transportedSliceLaw S n h A=
          ((stdGaussian (Ambient d)).map (fun x => conditionalMean S n h+R x))
            (cylindricalEvent n A) := by
  obtain ⟨R,hR,hRR⟩ := exists_positive_psd_factor _ (extendedCovariance_pd S hS n hn)
  exact ⟨R,hR,hRR,fun A hA =>
    transportedSliceLaw_event_eq_cylinder S hS n h hn R hR.1 hRR A hA⟩

end NegativeVotingFacetConditionalPlane
