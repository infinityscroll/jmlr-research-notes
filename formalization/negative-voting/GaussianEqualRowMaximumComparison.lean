import GaussianEqualRowMaximumLaw
import GaussianMaximumUpperTail
import GaussianBalancedReference

/-! Actual equal-row Gaussian maximum comparison, derived from the singular
common-threshold theorem and exact common-noise moments. There is no assumed
stochastic order, moment deficit, or deficit-relative tail remainder. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical ENNReal NNReal
namespace NegativeVotingEqualRowMaximumComparison
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingBalancedReference
  NegativeVotingEqualRowMaximumLaw NegativeVotingMaximumMomentComparison NegativeVotingMaximumUpperTail
variable {m d : ℕ} [NeZero m]

theorem normalized_row_maximum_mean_le (B : Fin m→FSC.Coord d)
    (hB : ∀ i,inner ℝ (B i) (B i)=1-1/(m:ℝ)) :
    (∫ x,rowMaximum B x ∂standardGaussian (Fin d)) ≤
      ∫ y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m) := by
  let c := Real.sqrt (1/(m:ℝ))
  have hc : c^2=1/(m:ℝ) := Real.sq_sqrt (by positivity)
  have hh := integral_le_of_cdf_ge
    (standardGaussian (Fin d⊕Fin 1)) (standardGaussian (Fin m))
    (addedMaximum B c) maximum (addedMaximum_measurable B c) maximum_measurable
    ((addedMaximum_memLp_two B c).integrable (by norm_num : (1:ENNReal)≤2))
    maximum_integrable (addedMaximum_cdf_ge B hB c hc)
  rwa [addedMaximum_mean] at hh

theorem normalized_row_maximum_second_comparison (B : Fin m→FSC.Coord d)
    (hB : ∀ i,inner ℝ (B i) (B i)=1-1/(m:ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ((∫ y : Fin m→ℝ,(maximum y)^2 ∂standardGaussian (Fin m))-1/(m:ℝ))-
        (∫ x,(rowMaximum B x)^2 ∂standardGaussian (Fin d)) ≤
      2*T*((∫ y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m))-
        (∫ x,rowMaximum B x ∂standardGaussian (Fin d)))+
          16*(m:ℝ)*Real.exp (-T^2/8) := by
  let c := Real.sqrt (1/(m:ℝ))
  have hc : c^2=1/(m:ℝ) := Real.sq_sqrt (by positivity)
  have hh := second_moment_difference_le
    (standardGaussian (Fin d⊕Fin 1)) (standardGaussian (Fin m))
    (addedMaximum B c) maximum (addedMaximum_measurable B c) maximum_measurable
    (addedMaximum_memLp_two B c) maximum_memLp_two (addedMaximum_cdf_ge B hB c hc) T
  rw [addedMaximum_mean,addedMaximum_second_moment,hc] at hh
  have ht := iid_upper_shortfall_sq_le (ι:=Fin m) T hT
  simp only [Fintype.card_fin] at ht
  linarith

theorem rowMaximum_pos_smul (B : Fin m→FSC.Coord d) (α : ℝ) (hα : 0 < α)
    (x : Fin d→ℝ) : rowMaximum (α•B) x=α*rowMaximum B x := by
  unfold rowMaximum NegativeVotingRegularScoreLaw.coordinateScores
  have he : (fun i=>∑ j,((α•B) i).ofLp j*x j)=
      (fun i=>α*(∑ j,(B i).ofLp j*x j)) := by
    funext i
    simp only [Pi.smul_apply,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [he,maxScore_mul_pos _ α hα]

theorem equal_row_maximum_comparison (Z : Fin m→FSC.Coord d)
    (α : ℝ) (hα : 0 < α)
    (hZ : ∀ i,inner ℝ (Z i) (Z i)=α^2*(1-1/(m:ℝ)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ x,rowMaximum Z x ∂standardGaussian (Fin d)) ≤
        α*(∫ y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m)) ∧
    α^2*((∫ y : Fin m→ℝ,(maximum y)^2 ∂standardGaussian (Fin m))-1/(m:ℝ))-
        (∫ x,(rowMaximum Z x)^2 ∂standardGaussian (Fin d)) ≤
      2*α*T*(α*(∫ y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m))-
        (∫ x,rowMaximum Z x ∂standardGaussian (Fin d)))+
          16*α^2*(m:ℝ)*Real.exp (-T^2/8) := by
  let B : Fin m→FSC.Coord d := α⁻¹•Z
  have hB i : inner ℝ (B i) (B i)=1-1/(m:ℝ) := by
    dsimp [B]
    rw [real_inner_smul_left,real_inner_smul_right,hZ]
    field_simp
    <;> ring
  have he : α•B=Z := by dsimp [B];rw [smul_smul,mul_inv_cancel₀ hα.ne',one_smul]
  have hm := normalized_row_maximum_mean_le B hB
  have hs := normalized_row_maximum_second_comparison B hB T hT
  have hmean : (∫ x,rowMaximum Z x ∂standardGaussian (Fin d))=
      α*(∫ x,rowMaximum B x ∂standardGaussian (Fin d)) := by
    rw [←he]
    simp_rw [rowMaximum_pos_smul B α hα]
    rw [integral_const_mul]
  have hsecond : (∫ x,(rowMaximum Z x)^2 ∂standardGaussian (Fin d))=
      α^2*(∫ x,(rowMaximum B x)^2 ∂standardGaussian (Fin d)) := by
    rw [←he]
    simp_rw [rowMaximum_pos_smul B α hα,mul_pow]
    rw [integral_const_mul]
  constructor
  · rw [hmean]
    exact mul_le_mul_of_nonneg_left hm hα.le
  · rw [hmean,hsecond]
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg α)
    nlinarith only [hh]

end NegativeVotingEqualRowMaximumComparison
