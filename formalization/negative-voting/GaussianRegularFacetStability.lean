import GaussianRegularFacetLogComparison
import GaussianFacetNormalPrefactor
import GaussianProcrustesDistance

/-! Uniform finite stability of the actual regular Gaussian facet weights,
with all conditional factors and affine Gaussian estimates discharged. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetStability
open NegativeVotingFacetConditionalPlane NegativeVotingRegularCapProbability
  NegativeVotingRegularFacetLogComparison NegativeVotingBalancedReference NegativeVotingFan
  NegativeVotingFanJacobian NegativeVotingAffineLogMassBound NegativeVotingAffinePathDerivative
  NegativeVotingAffinePositiveMass NegativeVotingAffineNormControl NegativeVotingPositiveCovariance
  NegativeVotingProcrustes
variable {n d : ℕ}

theorem regular_transported_facetWeight_pos (hn : 0 < n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    0 < facetWeight (transportedRows S B) (scoreOffsets B h) i j := by
  have hN := pairNormal_norm B i j (regular_gram_rows_ne B _ hG i j hij)
  obtain ⟨R,hR,hRR⟩ := exists_positive_psd_factor _ (extendedCovariance_pd S hS _ hN)
  have hw := regularFacetWeight_eq_affineCap S hS B _ hG h i j hij R hR.1 hRR
  have hp := affineMass_pos (regularFacetNormal B i j)
    (regularFacetNormal_unit B _ hG i j hij) 0 (regularCap_mass_pos hn B hG i j hij)
    R (conditionalMean S (pairNormal B i j) h)
  change facetWeight (transportedRows S B) (scoreOffsets B h) i j=
    gaussianPDFReal 0 1 (transportedLevel S (pairNormal B i j) h)/
      (Real.sqrt 2*‖S (pairNormal B i j)‖)*
      affineMass (regularFacetNormal B i j) 0 R.toContinuousLinearMap
        (conditionalMean S (pairNormal B i j) h) at hw
  rw [hw]
  exact mul_pos (div_pos (gaussianPDFReal_pos 0 1 _ (by norm_num))
    (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (transformed_normal_norm_pos S _ hN))) hp

/-- Finite actual facet stability in the covariance perturbation and score mean.
There is no supplied factor, conditional-law, moment, or facet-ratio estimate. -/
theorem regular_facetWeight_log_stability (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (hsmall : 32*Real.exp 1*operatorHilbertSchmidt (covarianceError S) ≤ 1)
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    |Real.log (facetWeight (transportedRows S B) (scoreOffsets B h) i j /
      (referenceScale n/((n:ℝ)+2)))| ≤
      4096*(Real.exp 1)^3*(operatorHilbertSchmidt (covarianceError S)*(1+Real.log ((n:ℝ)+2))+
        ‖h‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖h‖^2) := by
  let N := pairNormal B i j
  have hN : ‖N‖=1 := pairNormal_norm B i j (regular_gram_rows_ne B _ hG i j hij)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hε := operatorHilbertSchmidt_nonneg (covarianceError S)
  have hop := operator_norm_le_HilbertSchmidt (covarianceError S)
  have hE : ‖covarianceError S‖ ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_right he hε
    nlinarith
  obtain ⟨R,hR,hRR⟩ := exists_positive_psd_factor _ (extendedCovariance_pd S hS N hN)
  have hdist := psd_sqrt_HilbertSchmidt_distance R.toContinuousLinearMap hR
  rw [hRR] at hdist
  have hdist8 := hdist.trans (extendedCovariance_HilbertSchmidt_le S N hN hE)
  have hRsmall : 4*Real.exp 1*operatorHilbertSchmidt
      (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdist8 (by positivity : 0 ≤ 4*Real.exp 1)
    nlinarith
  have hraw := regular_facetWeight_log_ratio_bound hn hmean B hG S hS h i j hij R hR.1 hRR hRsmall
  have hβ := conditionalMean_norm_le S N h hN hE
  have hpref := (normal_prefactor_error_le S hS N h hN hE).trans (add_le_add le_rfl hop)
  have hL : 1 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    linarith
  have hLn : 0 ≤ 1+Real.log ((n:ℝ)+2) := by linarith
  have hlin := mul_le_mul_of_nonneg_right hdist8 hLn
  have hshift := mul_le_mul_of_nonneg_right hβ (Real.sqrt_nonneg (1+Real.log ((n:ℝ)+2)))
  have hβsq := pow_le_pow_left₀ (norm_nonneg _) hβ 2
  have hterms := add_le_add (add_le_add hlin hshift) hβsq
  have hscaled := mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ 128*(Real.exp 1)^3)
  have htotal := hraw.trans (add_le_add hpref hscaled)
  have he3 : 1 ≤ (Real.exp 1)^3 := one_le_pow₀ he
  have hεL := mul_le_mul_of_nonneg_left hL hε
  have hεC := mul_le_mul_of_nonneg_right he3 (mul_nonneg hε hLn)
  have hhC := mul_le_mul_of_nonneg_right he3 (sq_nonneg ‖h‖)
  have hcross : 0 ≤ (Real.exp 1)^3*(‖h‖*Real.sqrt (1+Real.log ((n:ℝ)+2))) := by positivity
  nlinarith

private theorem strict_weight_bounds_of_abs_log {w w0 : ℝ} (hw : 0 < w) (hw0 : 0 < w0)
    (hlog : |Real.log (w/w0)| < Real.log 2) : w0/2 < w ∧ w < 2*w0 := by
  have hr : 0 < w/w0 := div_pos hw hw0
  have hh := abs_lt.mp hlog
  have hhi : w/w0 < 2 := (Real.log_lt_log_iff hr (by norm_num)).mp hh.2
  have hlo : 1/2 < w/w0 := by
    apply (Real.log_lt_log_iff (by norm_num : (0:ℝ)<1/2) hr).mp
    simpa only [one_div,Real.log_inv] using hh.1
  constructor
  · have h := (lt_div_iff₀ hw0).mp hlo
    linarith
  · exact (div_lt_iff₀ hw0).mp hhi

/-- The strict comparability conclusion required by a continuation bootstrap.
Every probability and surface weight is the actual Gaussian quantity. -/
theorem regular_facetWeight_strict_comparable (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (hsmall : 32*Real.exp 1*operatorHilbertSchmidt (covarianceError S) ≤ 1)
    (h : FSC.Coord d)
    (hsize : 4096*(Real.exp 1)^3*(operatorHilbertSchmidt (covarianceError S)*(1+Real.log ((n:ℝ)+2))+
      ‖h‖*Real.sqrt (1+Real.log ((n:ℝ)+2))+‖h‖^2) < Real.log 2)
    (i j : Fin (n+2)) (hij : i≠j) :
    (referenceScale n/((n:ℝ)+2))/2 < facetWeight (transportedRows S B) (scoreOffsets B h) i j ∧
      facetWeight (transportedRows S B) (scoreOffsets B h) i j < 2*(referenceScale n/((n:ℝ)+2)) := by
  exact strict_weight_bounds_of_abs_log (regular_transported_facetWeight_pos hn B hG S hS h i j hij)
    (div_pos (referenceScale_pos n) (by positivity))
    ((regular_facetWeight_log_stability hn hmean B hG S hS hsmall h i j hij).trans_lt hsize)

end NegativeVotingRegularFacetStability
