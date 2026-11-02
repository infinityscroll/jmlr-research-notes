import GaussianRegularFacetCylinder
import GaussianRegularFacetMean
import GaussianAffinePolynomialComparison

/-! Actual mass and finite affine stability of the fixed regular-facet cap. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularCapProbability
open NegativeVotingFacetConditionalPlane NegativeVotingRegularFacetSeed
  NegativeVotingRegularFacetMean NegativeVotingBalancedReference NegativeVotingFan
  NegativeVotingFanJacobian NegativeVotingAffineLogScale NegativeVotingAffineLogMassBound
  NegativeVotingAffinePolynomialComparison NegativeVotingAffineNormControl
variable {n d : ℕ}

theorem regularCap_mass_eq (hn : 0 < n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    FSC.capMass (regularFacetNormal B i j) 0=
      referenceScale n*Real.sqrt 2/(((n:ℝ)+2)*gaussianPDFReal 0 1 0) := by
  let I := ContinuousLinearEquiv.refl ℝ (FSC.Coord d)
  have hI : I.toLinearMap.IsSymmetric := by intro x y; rfl
  have hrow := regular_gram_rows_ne B _ hG i j hij
  have hnrm := pairNormal_norm B i j hrow
  have hRR : I.toContinuousLinearMap.comp I.toContinuousLinearMap=
      extendedCovariance I (pairNormal B i j) := by
    rw [extendedCovariance_eq_id I _ hnrm (by ext x; rfl)]
    ext x; rfl
  have hh := regularFacetWeight_eq_affineCap I hI B _ hG 0 i j hij I hI hRR
  have hrows : transportedRows I B=B := rfl
  have hoff : scoreOffsets B (0 : FSC.Coord d)=0 := by ext k; simp [scoreOffsets]
  rw [hrows,hoff,regular_facetWeight hn B hG i j hij] at hh
  have he : referenceScale n/((n:ℝ)+2)=
      gaussianPDFReal 0 1 0/Real.sqrt 2*FSC.capMass (regularFacetNormal B i j) 0 := by
    simpa only [I,ContinuousLinearEquiv.refl_apply,inner_zero_right,
      transportedLevel,neg_zero,zero_div,conditionalMean_zero,add_zero,hnrm,mul_one,
      FSC.capMass,Set.setOf_mem_eq] using hh
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hφ : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (eq_div_iff (ne_of_gt (mul_pos hm hφ))).mpr
  field_simp [hm.ne',hφ.ne',hs.ne'] at he
  nlinarith

theorem regularCap_mass_pos (hn : 0 < n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    0 < FSC.capMass (regularFacetNormal B i j) 0 := by
  rw [regularCap_mass_eq hn B hG i j hij]
  exact div_pos (mul_pos (referenceScale_pos n) (Real.sqrt_pos.mpr (by norm_num)))
    (mul_pos (by positivity) (gaussianPDFReal_pos 0 1 0 (by norm_num)))

theorem regularCap_mass_lower (hn : 0 < n) (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    1/((n:ℝ)+2)^2 ≤ FSC.capMass (regularFacetNormal B i j) 0 := by
  rw [regularCap_mass_eq hn B hG i j hij,←regular_intrinsicFacet_mass hn B hG i j hij]
  exact regular_intrinsicFacet_mass_lower hn hmean B hG i j hij

theorem regularCap_log_bound (hn : 0 < n) (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    1+Real.log (1/FSC.capMass (regularFacetNormal B i j) 0) ≤
      2*(1+Real.log ((n:ℝ)+2)) := by
  have hp := regularCap_mass_pos hn B hG i j hij
  have hl := regularCap_mass_lower hn hmean B hG i j hij
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hi : 1/FSC.capMass (regularFacetNormal B i j) 0 ≤ ((n:ℝ)+2)^2 := by
    apply (div_le_iff₀ hp).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hm)).mp hl
    nlinarith
  have hh := Real.log_le_log (div_pos zero_lt_one hp) hi
  rw [Real.log_pow] at hh
  norm_num at hh
  rw [one_div,Real.log_inv]
  linarith

theorem regularCap_affine_log_ratio_bound (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : 4*Real.exp 1*operatorHilbertSchmidt A ≤ 1) (z : FSC.Coord d) :
    |Real.log (lineMass (regularFacetNormal B i j) 0 A z 1 /
      FSC.capMass (regularFacetNormal B i j) 0)| ≤
      128*(Real.exp 1)^3*(operatorHilbertSchmidt A*(1+Real.log ((n:ℝ)+2))+
        ‖z‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖z‖^2) := by
  have hh := affine_mass_polynomial_log_ratio_bound (regularFacetNormal B i j)
    (regularFacetNormal_unit B _ hG i j hij) 0
    (regularFacetNormal_noCoincident B _ hG i j hij)
    (regularCap_mass_pos hn B hG i j hij) A hA z
  have hL := regularCap_log_bound hn hmean B hG i j hij
  have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have hroot : Real.sqrt (1+Real.log (1/FSC.capMass (regularFacetNormal B i j) 0)) ≤
      2*Real.sqrt (1+Real.log ((n:ℝ)+2)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2*Real.sqrt (1+Real.log ((n:ℝ)+2)))).mp
    have hs := Real.sq_sqrt (show 0 ≤ 1+Real.log ((n:ℝ)+2) by linarith)
    have hr := Real.sq_sqrt (show 0 ≤ 1+Real.log (1/FSC.capMass (regularFacetNormal B i j) 0) by
      have hi : FSC.capMass (regularFacetNormal B i j) 0 ≤ 1 := measureReal_le_one
      have hp := regularCap_mass_pos hn B hG i j hij
      have hz := Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hi))
      linarith)
    nlinarith
  have hlin := mul_le_mul_of_nonneg_left hL (operatorHilbertSchmidt_nonneg A)
  have hshift := mul_le_mul_of_nonneg_left hroot (norm_nonneg z)
  have hsum : operatorHilbertSchmidt A*(1+Real.log (1/FSC.capMass (regularFacetNormal B i j) 0))+
      ‖z‖*Real.sqrt (1+Real.log (1/FSC.capMass (regularFacetNormal B i j) 0))+‖z‖^2 ≤
      2*(operatorHilbertSchmidt A*(1+Real.log ((n:ℝ)+2))+
        ‖z‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖z‖^2) := by nlinarith [sq_nonneg ‖z‖]
  have hc := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 64*(Real.exp 1)^3)
  nlinarith

end NegativeVotingRegularCapProbability
