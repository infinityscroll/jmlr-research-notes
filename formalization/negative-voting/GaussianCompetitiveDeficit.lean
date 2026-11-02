import GaussianCompetitiveSharpMass

/-! Actual competitive deficit bounds that preserve the full r^2 scaling
as the negative correlation tends to zero. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
universe u
namespace NegativeVotingCompetitiveDeficit
open NegativeVoting NegativeVotingModern NegativeVotingCompetitiveSharpMass
  NegativeVotingFractionalMass NegativeVotingRegularSecondGap
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  NegativeVotingRegularScoreLaw

variable {κ : Type*} [Fintype κ]

def competitiveDeficit (n : ℕ) (r : ℝ) (f : (κ → ℝ) → Fin (n+2) → ℝ) : ℝ :=
  massDeficit n f+r*(referenceFirstWeight n-assignmentFirstEnergy f)

theorem quadratic_remainder_bound (m r : ℝ) (hm : 0 < m) (hr0 : 0 ≤ r)
    (hr2 : r ≤ 2/m) (hr1 : r ≤ 1) :
    r^2*(50/m)+r^3+r^4 ≤ 54*r^2/m := by
  have hrsq : r^2 ≤ r := by
    have hh := mul_nonneg hr0 (sub_nonneg.mpr hr1)
    nlinarith
  have hbase : 50/m+r+r^2 ≤ 54/m := by
    simp only [div_eq_mul_inv] at hr2 ⊢
    linarith
  have hm' := mul_le_mul_of_nonneg_left hbase (sq_nonneg r)
  simp only [div_eq_mul_inv] at hm' ⊢
  nlinarith

/-- The exact small-r deficit estimate for a literal Gaussian competitor.
Only the displayed mass-value bound remains an analytic input. -/
theorem actual_competitive_deficit_bounds (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (hn : 0 < n)
    (hell : 0 ≤ referenceEll n)
    (hgap : 0 ≤ referenceSecondWeight n-referenceJensenFloor n ∧
      referenceSecondWeight n-referenceJensenFloor n ≤ 50/((n:ℝ)+2))
    (hmajor : sharpMassMajorant K n ≤ 1/8)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1))
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r)
      (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ))
    (hvalue : assignmentFirstEnergy f ≤ referenceFirstWeight n+
      K*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f) :
    0 ≤ competitiveDeficit n r f ∧ massDeficit n f ≤ 2*competitiveDeficit n r f ∧
      r*|assignmentFirstEnergy f-referenceFirstWeight n| ≤ competitiveDeficit n r f ∧
      competitiveDeficit n r f ≤ 128*r^2/((n:ℝ)+2) := by
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hm1 : 0 < (n:ℝ)+1 := by positivity
  have hr1 : r ≤ 1 := hr.trans ((div_le_one hm1).mpr (by linarith))
  have hrhalf : r ≤ 1/2 := hr.trans ((div_le_div_iff₀ hm1 (by norm_num : (0:ℝ)<2)).mpr (by linarith))
  have hr2 : r ≤ 2/((n:ℝ)+2) := voting_noise_le_two_div ((n:ℝ)+2) r
    (by linarith) (by simpa only [show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hr)
  have hδ : 0 ≤ massDeficit n f := Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hL : 0 ≤ K*(1+Real.log ((n:ℝ)+2))^2 := mul_nonneg hK (sq_nonneg _)
  have hfloor : referenceJensenFloor n ≤ referenceSecondWeight n := by linarith [hgap.1]
  have hcoef := voting_reference_coefficient n hn hell hfloor r hr0 hr
  have hsmall := (mass_coefficient_le_majorant K hK n hn hell hfloor r hr0 hr).trans hmajor
  have hquad0 : 0 ≤ r^2*referenceEll n*(referenceEll n+2)/2 := by positivity
  have hlinear0 : 0 ≤ r*K*(1+Real.log ((n:ℝ)+2))^2 := by positivity
  have hsmallL : r*K*(1+Real.log ((n:ℝ)+2))^2 ≤ 1/8 := by linarith
  have hsmallQuad : r^2*referenceEll n*(referenceEll n+2)/2 ≤ 1/8 := by linarith
  have hrell : r*referenceEll n ≤ 1/2 := by
    nlinarith [mul_nonneg (sq_nonneg r) hell]
  have hW := mul_le_mul_of_nonneg_left hvalue hr0
  have hLd := mul_le_mul_of_nonneg_right hsmallL hδ
  have hD0 : 0 ≤ competitiveDeficit n r f := by
    unfold competitiveDeficit
    nlinarith
  have hδD : massDeficit n f ≤ 2*competitiveDeficit n r f := by
    unfold competitiveDeficit
    nlinarith
  have hWD : r*|assignmentFirstEnergy f-referenceFirstWeight n| ≤ competitiveDeficit n r f := by
    by_cases hd : 0 ≤ assignmentFirstEnergy f-referenceFirstWeight n
    · rw [abs_of_nonneg hd]
      unfold competitiveDeficit
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hd)]
      unfold competitiveDeficit
      nlinarith
  have hcδ : 0 ≤ r*referenceEll n-r^2*referenceEll n*(referenceEll n+2)/2 := by
    have hb : 0 ≤ 1-r*(referenceEll n+2)/2 := by nlinarith [hcoef.1]
    have hh := mul_nonneg (mul_nonneg hr0 hell) hb
    nlinarith
  have hpar := competitive_second_energy_bound n hn r hr0 hr1 f hf hp hcomp
  have htan := mul_le_mul_of_nonneg_left (second_energy_tangent_gap n hell f hf hp) (sq_nonneg r)
  have hgapR := mul_le_mul_of_nonneg_left hgap.2 (sq_nonneg r)
  have hkey : (1-r*referenceEll n)*competitiveDeficit n r f+
      (r*referenceEll n-r^2*referenceEll n*(referenceEll n+2)/2)*massDeficit n f ≤
        r^2*(50/((n:ℝ)+2))+r^3+r^4 := by
    unfold competitiveDeficit
    nlinarith
  have hpδ := mul_nonneg hcδ hδ
  have hhalf := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ) ≤ 1-r*referenceEll n by linarith) hD0
  have hrem := quadratic_remainder_bound ((n:ℝ)+2) r hm hr0 hr2 hr1
  have hupper : competitiveDeficit n r f ≤ 128*r^2/((n:ℝ)+2) := by
    have hratio : 0 ≤ r^2/((n:ℝ)+2) := div_nonneg (sq_nonneg r) hm.le
    simp only [div_eq_mul_inv] at hkey hhalf hrem hratio ⊢
    nlinarith
  exact ⟨hD0,hδD,hWD,hupper⟩

theorem eventually_uniform_competitive_deficit_bounds (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B)
      (f : (κ → ℝ) → Fin (n+2) → ℝ)
      (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1)),
      gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment B) →
      assignmentFirstEnergy f ≤ referenceFirstWeight n+
        K*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f →
      0 ≤ competitiveDeficit n r f ∧ massDeficit n f ≤ 2*competitiveDeficit n r f ∧
        r*|assignmentFirstEnergy f-referenceFirstWeight n| ≤ competitiveDeficit n r f ∧
        competitiveDeficit n r f ≤ 128*r^2/((n:ℝ)+2) := by
  have hm : ∀ᶠ n in atTop,sharpMassMajorant K n<1/8 :=
    (tendsto_order.mp (sharpMassMajorant_tendsto_zero K)).2 (1/8) (by norm_num)
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one,
    eventually_reference_second_gap,hm] with n hn hmean hgap hmajor
  intro κ _ B hB f hf hp r hr0 hr hcomp hvalue
  rw [regularAssignment_noise_eq_canonical n B hB (-r)] at hcomp
  exact actual_competitive_deficit_bounds K hK n hn (referenceEll_nonneg_of_mean_sq n hmean)
    hgap hmajor.le r hr0 hr f hf hp hcomp hvalue

end NegativeVotingCompetitiveDeficit
