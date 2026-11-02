import GaussianReferenceSecondEnergy
import NegativeVoting.VotingRange

/-! Actual cubic-scale competitive mass localization. The only pending analytic
input at the final endpoint is the explicit mass-value quadratic bound. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
universe u
namespace NegativeVotingCompetitiveSharpMass
open NegativeVoting NegativeVotingModern NegativeVotingCompetitiveParity
  NegativeVotingFractionalMass NegativeVotingSecondChaosLower NegativeVotingRegularSecondGap
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingRegularMaximum
  NegativeVotingRegularScoreLaw OAI.MinUncut.GaussianHermite

variable {κ : Type*} [Fintype κ]

theorem reference_first_energy_le_one (n : ℕ) (hn : 0<n) : referenceFirstWeight n ≤ 1 := by
  let f := (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
  have hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin (n+2))) :=
    fun i=>(measurable_maxWeights id (fun k=>measurable_pi_apply k) i).aemeasurable
  have hp : ∀ᵐ x ∂standardGaussian (Fin (n+2)),SimplexWeights (f x) := ae_of_all _ maxWeights_simplex
  have hs := gaussian_chaosEnergy_summable_of_ae f hf hp
  have hh := hs.sum_le_tsum ({1} : Finset ℕ) (fun k _=>chaosEnergy_nonneg f k)
  have h := hh.trans (gaussian_chaosEnergy_le_one_of_ae f hf hp)
  simpa only [Finset.sum_singleton,f,canonical_chaosEnergy_one n hn] using h

theorem referenceEll_le_size_minus_one (n : ℕ) (hn : 0<n) : referenceEll n ≤ (n:ℝ)+1 := by
  have h := mul_le_mul_of_nonneg_left (reference_first_energy_le_one n hn)
    (show 0 ≤ (n:ℝ)+2 by positivity)
  unfold referenceEll
  linarith

theorem gaussian_negative_second_lower (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x)) :
    chaosEnergy f 0-r*chaosEnergy f 1+r^2*chaosEnergy f 2-r^3 ≤ gaussianNoiseStability (-r) f := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  have hs := gaussian_chaosEnergy_summable_of_ae f hf hp
  have ht := (abs_le.mp (bounded_energy_tail _ (chaosEnergy_nonneg f) hs
    (gaussian_chaosEnergy_le_one_of_ae f hf hp) r hr0 hr1 3)).1
  rw [gaussianNoiseStability_spectral_of_ae (-r) hr f hf hp,
    chaos_series_split_three _ (chaosEnergy_nonneg f) hs (-r) hr]
  nlinarith

theorem competitive_second_energy_bound (n : ℕ) (hn : 0<n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r)
      (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)) :
    massDeficit n f ≤ r*(assignmentFirstEnergy f-referenceFirstWeight n)+
      r^2*(referenceSecondWeight n-chaosEnergy f 2)+r^3+r^4 := by
  have hl := gaussian_negative_second_lower r hr0 hr1 f hf hp
  have hu := canonical_negative_upper n hn r hr0 hr1
  rw [chaosEnergy_zero,chaosEnergy_one] at hl
  rw [massDeficit_eq n f hf hp]
  change (∑ i,(assignmentMass f i)^2)-r*assignmentFirstEnergy f+r^2*chaosEnergy f 2-r^3 ≤
    gaussianNoiseStability (-r) f at hl
  nlinarith

theorem second_energy_tangent_gap (n : ℕ) (hell : 0 ≤ referenceEll n)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x)) :
    referenceSecondWeight n-chaosEnergy f 2 ≤
      (referenceSecondWeight n-referenceJensenFloor n)-
        referenceEll n*(assignmentFirstEnergy f-referenceFirstWeight n)+
        referenceEll n*(referenceEll n+2)/2*massDeficit n f := by
  have ht := secondChaos_affine_tangent f hf hp (referenceEll n) hell
  have hp2 : assignmentMassSquares f=massDeficit n f+1/((n:ℝ)+2) := by
    rw [massDeficit_eq n f hf hp]
    unfold assignmentMassSquares
    ring
  rw [hp2] at ht
  have he : referenceEll n*referenceFirstWeight n-referenceEll n*(referenceEll n+2)/2/((n:ℝ)+2)=
      referenceJensenFloor n := by
    unfold referenceJensenFloor referenceEll
    field_simp
    ring
  simp only [div_eq_mul_inv,one_mul] at ht he ⊢
  nlinarith

def sharpMassMajorant (K : ℝ) (n : ℕ) : ℝ :=
  (2/((n:ℝ)+2))*K*(1+Real.log ((n:ℝ)+2))^2+2*referenceSecondWeight n+2/((n:ℝ)+2)

theorem sharpMassMajorant_tendsto_zero (K : ℝ) : Tendsto (sharpMassMajorant K) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ=>1/((n:ℝ)+2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 2)
  have h1 : Tendsto (fun n : ℕ=>Real.log ((n:ℝ)+2)/((n:ℝ)+2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero,pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp size_tendsto
  have h2 : Tendsto (fun n : ℕ=>Real.log ((n:ℝ)+2)^2/((n:ℝ)+2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp size_tendsto
  have hbase := (((hi.add (h1.const_mul (2:ℝ))).add h2).const_mul (2*K)).add
    ((referenceSecondWeight_tendsto_zero.const_mul (2:ℝ)).add (hi.const_mul (2:ℝ)))
  convert hbase using 1
  · funext n
    unfold sharpMassMajorant
    ring
  · norm_num

theorem voting_reference_coefficient (n : ℕ) (hn : 0<n)
    (hell : 0 ≤ referenceEll n) (hfloor : referenceJensenFloor n ≤ referenceSecondWeight n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1)) :
    r*referenceEll n ≤ 1 ∧
    r^2*referenceEll n*(referenceEll n+2)/2 ≤ 2*referenceSecondWeight n+2/((n:ℝ)+2) := by
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hm1 : 0 < (n:ℝ)+1 := by positivity
  have hrm1 := (le_div_iff₀ hm1).mp hr
  have hel := mul_le_mul_of_nonneg_left (referenceEll_le_size_minus_one n hn) hr0
  have hrell : r*referenceEll n ≤ 1 := by linarith
  have hr1 : r ≤ 1 := hr.trans ((div_le_one hm1).mpr (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith))
  have hr2 : r ≤ 2/((n:ℝ)+2) := voting_noise_le_two_div ((n:ℝ)+2) r
    (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith) (by simpa only [show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hr)
  have hmr := (le_div_iff₀ hm).mp hr2
  have hmr2 : ((n:ℝ)+2)*r^2 ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hmr hr0
    nlinarith
  have hA := referenceSecondWeight_nonneg n
  have hs : (referenceEll n)^2 ≤ referenceSecondWeight n*(2*((n:ℝ)+2)) := by
    exact (div_le_iff₀ (show 0<2*((n:ℝ)+2) by positivity)).mp hfloor
  have hsR := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  have hAR := mul_le_mul_of_nonneg_right hmr2 hA
  have hlinear := mul_le_mul_of_nonneg_left hrell hr0
  refine ⟨hrell,?_⟩
  nlinarith

theorem mass_coefficient_le_majorant (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (hn : 0<n)
    (hell : 0 ≤ referenceEll n) (hfloor : referenceJensenFloor n ≤ referenceSecondWeight n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1)) :
    r*K*(1+Real.log ((n:ℝ)+2))^2+r^2*referenceEll n*(referenceEll n+2)/2 ≤ sharpMassMajorant K n := by
  have hc := (voting_reference_coefficient n hn hell hfloor r hr0 hr).2
  have hr2 : r ≤ 2/((n:ℝ)+2) := voting_noise_le_two_div ((n:ℝ)+2) r
    (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith) (by simpa only [show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hr)
  have hm := mul_le_mul_of_nonneg_right hr2 (mul_nonneg hK (sq_nonneg (1+Real.log ((n:ℝ)+2))))
  unfold sharpMassMajorant
  nlinarith

/-- The numeric cubic remainder is derived for the entire interval, including r=0. -/
theorem cubic_remainder_bound (m r : ℝ) (hm2 : 2 ≤ m) (hr0 : 0 ≤ r)
    (hr2 : r ≤ 2/m) (hr1 : r ≤ 1) :
    m^3*(r^2*(50/m)+r^3+r^4) ≤ 216 := by
  have hm : 0 < m := by linarith
  have hmr : m*r ≤ 2 := by simpa only [mul_comm] using (le_div_iff₀ hm).mp hr2
  have hx0 : 0 ≤ m*r := mul_nonneg hm.le hr0
  have h2 := pow_le_pow_left₀ hx0 hmr 2
  have h3 := pow_le_pow_left₀ hx0 hmr 3
  norm_num at h2 h3
  have h4 : r^4 ≤ r^3 := by
    have hh := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 3)
    nlinarith
  have h4m := mul_le_mul_of_nonneg_left h4 (pow_nonneg hm.le 3)
  have he : m^3*(r^2*(50/m)+r^3+r^4)=50*(m*r)^2+(m*r)^3+m^3*r^4 := by
    field_simp [ne_of_gt hm]
  rw [he]
  nlinarith

/-- A literal competitive Gaussian assignment has cubic-scale mass deficit.
The only remaining analytic input here is the displayed mass-value estimate. -/
theorem actual_sharp_mass_bound (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (hn : 0<n)
    (hell : 0 ≤ referenceEll n)
    (hgap : 0 ≤ referenceSecondWeight n-referenceJensenFloor n ∧
      referenceSecondWeight n-referenceJensenFloor n ≤ 50/((n:ℝ)+2))
    (hmajor : sharpMassMajorant K n ≤ 1/2)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1))
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r)
      (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ))
    (hvalue : assignmentFirstEnergy f ≤ referenceFirstWeight n+
      K*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f) :
    massDeficit n f ≤ 512/((n:ℝ)+2)^3 := by
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hm1 : 0 < (n:ℝ)+1 := by positivity
  have hr1 : r ≤ 1 := hr.trans ((div_le_one hm1).mpr (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith))
  have hr2 : r ≤ 2/((n:ℝ)+2) := voting_noise_le_two_div ((n:ℝ)+2) r
    (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith) (by simpa only [show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hr)
  have hδ : 0 ≤ massDeficit n f := Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hL : 0 ≤ K*(1+Real.log ((n:ℝ)+2))^2 := mul_nonneg hK (sq_nonneg _)
  have hfloor : referenceJensenFloor n ≤ referenceSecondWeight n := by linarith [hgap.1]
  have hcoeff := voting_reference_coefficient n hn hell hfloor r hr0 hr
  have hcoef0 : 0 ≤ r-r^2*referenceEll n := by
    have hh := mul_nonneg hr0 (sub_nonneg.mpr hcoeff.1)
    nlinarith
  have hcoefr : r-r^2*referenceEll n ≤ r := by
    nlinarith [mul_nonneg (sq_nonneg r) hell]
  have hV : assignmentFirstEnergy f-referenceFirstWeight n ≤
      K*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f := by linarith
  have hVm := mul_le_mul_of_nonneg_left hV hcoef0
  have hVcap := mul_le_mul_of_nonneg_right hcoefr (mul_nonneg hL hδ)
  have hpar := competitive_second_energy_bound n hn r hr0 hr1 f hf hp hcomp
  have htan := mul_le_mul_of_nonneg_left (second_energy_tangent_gap n hell f hf hp) (sq_nonneg r)
  have hgapR := mul_le_mul_of_nonneg_left hgap.2 (sq_nonneg r)
  have hbound : massDeficit n f ≤
      (r*K*(1+Real.log ((n:ℝ)+2))^2+r^2*referenceEll n*(referenceEll n+2)/2)*massDeficit n f+
        r^2*(50/((n:ℝ)+2))+r^3+r^4 := by
    nlinarith
  have hsmall := (mass_coefficient_le_majorant K hK n hn hell hfloor r hr0 hr).trans hmajor
  have hsmallδ := mul_le_mul_of_nonneg_right hsmall hδ
  have hδrem : massDeficit n f ≤ 2*(r^2*(50/((n:ℝ)+2))+r^3+r^4) := by nlinarith
  have hδm := mul_le_mul_of_nonneg_left hδrem (pow_nonneg hm.le 3)
  have hrem := cubic_remainder_bound ((n:ℝ)+2) r (by have hh := Nat.cast_nonneg (α:=ℝ) n; linarith) hr0 hr2 hr1
  apply (le_div_iff₀ (pow_pos hm 3)).mpr
  nlinarith

/-- One eventual threshold is chosen before the ambient dimension, regular
reference, competitor and noise parameter. The sole pending analytic hypothesis
is the stated mass-value bound with a single fixed absolute K. -/
theorem eventually_uniform_sharp_mass_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B)
      (f : (κ → ℝ) → Fin (n+2) → ℝ)
      (hf : ∀ i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1)),
      gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment B) →
      assignmentFirstEnergy f ≤ referenceFirstWeight n+
        K*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f →
      massDeficit n f ≤ 512/((n:ℝ)+2)^3 := by
  have hm : ∀ᶠ n in atTop,sharpMassMajorant K n<1/2 :=
    (tendsto_order.mp (sharpMassMajorant_tendsto_zero K)).2 (1/2) (by norm_num)
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one,
    eventually_reference_second_gap,hm] with n hn hmean hgap hmajor
  intro κ _ B hB f hf hp r hr0 hr hcomp hvalue
  rw [regularAssignment_noise_eq_canonical n B hB (-r)] at hcomp
  exact actual_sharp_mass_bound K hK n hn (referenceEll_nonneg_of_mean_sq n hmean)
    hgap hmajor.le r hr0 hr f hf hp hcomp hvalue

end NegativeVotingCompetitiveSharpMass
