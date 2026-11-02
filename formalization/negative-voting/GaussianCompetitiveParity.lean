import GaussianRegularChaosCoefficients
import NegativeVoting.GaussianSpectral

/-! Actual single-rule negative-noise parity comparison for fractional Gaussian assignments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology Classical
namespace NegativeVotingCompetitiveParity
open NegativeVoting NegativeVotingModern NegativeVotingRegularMaximum
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  OAI.MinUncut.GaussianHermite

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- Completed-measure admissibility implies the actual total Hermite energy bound. -/
theorem gaussian_chaosEnergy_le_one_of_ae [Nonempty ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    (∑' k, chaosEnergy f k) ≤ 1 := by
  obtain ⟨g,hg,hgs,hfg,_⟩ := gaussian_simplex_representative f hf hp
  have he : chaosEnergy f=chaosEnergy g := funext (gaussian_chaosEnergy_congr_ae f g hfg)
  rw [he]
  exact simplex_chaos_energy_le_one g hg (fun x => (hgs x).1) (fun x => (hgs x).2)

theorem bounded_energy_tail (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (hS : Summable A)
    (hE : (∑' k, A k) ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : ℕ) :
    |∑' k, (-r)^(k+K)*A (k+K)| ≤ r^K := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  have htail : (∑' k, A (k+K)) ≤ 1 := by
    have hs := hS.sum_add_tsum_nat_add K
    have hpre : 0 ≤ ∑ k ∈ Finset.range K, A k := Finset.sum_nonneg (fun k _ => hA k)
    linarith
  have h := chaos_tail_abs_le A hA hS (-r) hr K
  simp only [abs_neg,abs_of_nonneg hr0] at h
  exact h.trans ((mul_le_mul_of_nonneg_left htail (pow_nonneg hr0 K)).trans_eq (mul_one _))

theorem negative_series_lower (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (hS : Summable A)
    (hE : (∑' k, A k) ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    A 0-r*A 1-r^3 ≤ ∑' k, (-r)^k*A k := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  have ht := (abs_le.mp (bounded_energy_tail A hA hS hE r hr0 hr1 3)).1
  rw [chaos_series_split_three A hA hS (-r) hr]
  nlinarith [mul_nonneg (sq_nonneg r) (hA 2)]

theorem negative_series_upper (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (hS : Summable A)
    (hE : (∑' k, A k) ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑' k, (-r)^k*A k) ≤ A 0-r*A 1+r^2*A 2+r^4 := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  have hs := (chaos_series_absolutely_summable A hA hS (-r) hr).of_norm
  have he := hs.sum_add_tsum_nat_add 4
  norm_num [Finset.sum_range_succ] at he
  have ht := (abs_le.mp (bounded_energy_tail A hA hS hE r hr0 hr1 4)).2
  nlinarith [mul_nonneg (pow_nonneg hr0 3) (hA 3)]

theorem gaussian_negative_lower [Nonempty ι] (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    chaosEnergy f 0-r*chaosEnergy f 1-r^3 ≤ gaussianNoiseStability (-r) f := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  rw [gaussianNoiseStability_spectral_of_ae (-r) hr f hf hp]
  exact negative_series_lower _ (chaosEnergy_nonneg f) (gaussian_chaosEnergy_summable_of_ae f hf hp)
    (gaussian_chaosEnergy_le_one_of_ae f hf hp) r hr0 hr1

theorem gaussian_negative_upper [Nonempty ι] (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    gaussianNoiseStability (-r) f ≤ chaosEnergy f 0-r*chaosEnergy f 1+r^2*chaosEnergy f 2+r^4 := by
  have hr : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr0] using hr1
  rw [gaussianNoiseStability_spectral_of_ae (-r) hr f hf hp]
  exact negative_series_upper _ (chaosEnergy_nonneg f) (gaussian_chaosEnergy_summable_of_ae f hf hp)
    (gaussian_chaosEnergy_le_one_of_ae f hf hp) r hr0 hr1

theorem canonical_chaosEnergy_zero (n : ℕ) :
    chaosEnergy (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) 0=1/((n:ℝ)+2) := by
  rw [chaosEnergy_zero]
  change (∑ i : Fin (n+2), (∫ x, maxWeights x i ∂standardGaussian (Fin (n+2)))^2)=1/((n:ℝ)+2)
  simp_rw [canonical_mass]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp

theorem canonical_negative_upper (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    gaussianNoiseStability (-r) (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) ≤
      1/((n:ℝ)+2)-r*referenceFirstWeight n+r^2*referenceSecondWeight n+r^4 := by
  have h := gaussian_negative_upper r hr0 hr1
    (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
    (fun i => (measurable_maxWeights id (fun k => measurable_pi_apply k) i).aemeasurable)
    (ae_of_all _ maxWeights_simplex)
  rwa [canonical_chaosEnergy_zero,canonical_chaosEnergy_one n hn,canonical_chaosEnergy_two n hn] at h

/-- Arbitrary ambient dimensions and completed-measure fractional competitors
are covered. Only the defining competitive noise inequality is assumed. -/
theorem competitive_mass_first_energy_bound (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤
      gaussianNoiseStability (-r) (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)) :
    (∑ i, (∫ x, f x i ∂standardGaussian κ)^2)-1/((n:ℝ)+2) ≤
      r*((∑ i, ∑ j, (∫ x, x j*f x i ∂standardGaussian κ)^2)-referenceFirstWeight n)+
      r^2*referenceSecondWeight n+r^3+r^4 := by
  have hl := gaussian_negative_lower r hr0 hr1 f hf hp
  have hu := canonical_negative_upper n hn r hr0 hr1
  rw [chaosEnergy_zero,chaosEnergy_one] at hl
  change (∑ i, (∫ x, f x i ∂standardGaussian κ)^2)-
    r*(∑ i, ∑ j, (∫ x, x j*f x i ∂standardGaussian κ)^2)-r^3 ≤ gaussianNoiseStability (-r) f at hl
  nlinarith

end NegativeVotingCompetitiveParity
