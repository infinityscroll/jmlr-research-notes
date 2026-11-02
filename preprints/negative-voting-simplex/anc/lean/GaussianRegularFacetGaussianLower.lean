import GaussianRegularFacetStability

/-! A global Gaussian lower envelope for literal regular-fan facet weights
under arbitrary score shifts. This is an input to the noise-potential quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetGaussianLower
open NegativeVotingRegularFacetStability NegativeVotingFacetConditionalPlane
  NegativeVotingBalancedReference NegativeVotingFanJacobian
  NegativeVotingAffineLogMassBound
variable {n d : ℕ}

def facetLogConstant : ℝ := 4096*(Real.exp 1)^3
def facetGaussianConstant : ℝ := facetLogConstant^2+facetLogConstant

theorem facetLogConstant_pos : 0 < facetLogConstant := by unfold facetLogConstant;positivity
theorem facetGaussianConstant_pos : 0 < facetGaussianConstant := by
  unfold facetGaussianConstant
  have hh := facetLogConstant_pos
  positivity

theorem linear_quadratic_le_gaussian (L z : ℝ) (hL : 1 ≤ L) (hz : 0 ≤ z) :
    facetLogConstant*(z*Real.sqrt L+z^2) ≤ 1+facetGaussianConstant*L*z^2 := by
  have hs : (Real.sqrt L)^2=L := Real.sq_sqrt (by linarith)
  have hcs := sq_nonneg (facetLogConstant*z*Real.sqrt L-1)
  have hbase : facetLogConstant*(z*Real.sqrt L) ≤ 1+facetLogConstant^2*L*z^2 := by
    have hh := sq_nonneg (facetLogConstant*z*Real.sqrt L)
    nlinarith [facetLogConstant_pos,Real.sqrt_nonneg L]
  have hq := mul_le_mul_of_nonneg_left hL
    (mul_nonneg facetLogConstant_pos.le (sq_nonneg z))
  unfold facetGaussianConstant
  nlinarith

theorem regular_shifted_facet_gaussian_lower (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i ≠ j) :
    (referenceScale n/((n:ℝ)+2))*
      Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*‖h‖^2) ≤
        facetWeight B (scoreOffsets B h) i j := by
  let S := ContinuousLinearEquiv.refl ℝ (FSC.Coord d)
  have hS : S.toLinearMap.IsSymmetric := by intro x y;rfl
  have he : covarianceError S=0 := by ext x;simp [covarianceError,covariance,S]
  have hsmall : 32*Real.exp 1*operatorHilbertSchmidt (covarianceError S) ≤ 1 := by
    simp [he,operatorHilbertSchmidt,operatorEntries]
  have hb := regular_facetWeight_log_stability hn hmean B hG S hS hsmall h i j hij
  have hw := regular_transported_facetWeight_pos hn B hG S hS h i j hij
  have hrows : transportedRows S B=B := by funext k;rfl
  rw [hrows] at hb hw
  have hzero : operatorHilbertSchmidt (covarianceError S)=0 := by
    simp [he,operatorHilbertSchmidt,operatorEntries]
  simp only [hzero,zero_mul,zero_add] at hb
  change |Real.log (facetWeight B (scoreOffsets B h) i j/(referenceScale n/((n:ℝ)+2)))| ≤
    facetLogConstant*(‖h‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖h‖^2) at hb
  have hL : 1 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    linarith
  have hq := linear_quadratic_le_gaussian (1+Real.log ((n:ℝ)+2)) ‖h‖ hL (norm_nonneg h)
  have hw0 : 0 < referenceScale n/((n:ℝ)+2) :=
    div_pos (referenceScale_pos n) (by positivity)
  have hlo : -1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*‖h‖^2 ≤
      Real.log (facetWeight B (scoreOffsets B h) i j/(referenceScale n/((n:ℝ)+2))) := by
    have hh := (abs_le.mp hb).1
    linarith
  have hh := Real.exp_le_exp.mpr hlo
  rw [Real.exp_log (div_pos hw hw0)] at hh
  have hr := (le_div_iff₀ hw0).mp hh
  simpa only [mul_comm] using hr

end NegativeVotingRegularFacetGaussianLower
