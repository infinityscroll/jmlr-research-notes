import GaussianSpectralBridge
import GaussianSecondChaos
import NegativeVoting.Admissible
import NegativeVoting.HermiteTail

/-! Connect the attributed concrete Gaussian spectral development to exactly
the almost-everywhere assignments and noise objective of `MainGoal.lean`.
No spectral expansion or finite-energy hypothesis is postulated. -/
noncomputable section
namespace NegativeVoting
open MeasureTheory OAI.MinUncut.GaussianHermite NegativeVotingModern
open scoped BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem gaussian_hermite_coefficient_congr_ae
    (f g : (κ → ℝ) → ι → ℝ) (hfg : f =ᵐ[standardGaussian κ] g)
    (i : ι) (a : κ → ℕ) :
    coeff (fun x => f x i) a = coeff (fun x => g x i) a := by
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem gaussian_chaosEnergy_congr_ae
    (f g : (κ → ℝ) → ι → ℝ) (hfg : f =ᵐ[standardGaussian κ] g)
    (k : ℕ) : chaosEnergy f k = chaosEnergy g k := by
  unfold chaosEnergy labelCoefficientEnergy
  apply tsum_congr
  intro a
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussian_hermite_coefficient_congr_ae f g hfg i a.1]

/-- Exact signed Hermite representation for the actual noise objective and the
same completed-measure admissible class appearing in the full target. -/
theorem gaussianNoiseStability_spectral_of_ae [Nonempty ι]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    gaussianNoiseStability ρ f = ∑' k : ℕ, ρ ^ k * chaosEnergy f k := by
  obtain ⟨g, hg, hgs, hfg, hvalue⟩ := gaussian_simplex_representative f hf hp
  rw [hvalue ρ hρ]
  have hgvalue := actual_simplex_noise_stability_spectral ρ hρ g hg
    (fun x => (hgs x).1) (fun x => (hgs x).2)
  change gaussianNoiseStability ρ g = _ at hgvalue
  rw [hgvalue]
  apply tsum_congr
  intro k
  rw [gaussian_chaosEnergy_congr_ae f g hfg k]

/-- The actual Gaussian energy sequence is summable; neither finite energy
nor a chosen abstract basis is an assumption on the assignment. -/
theorem gaussian_chaosEnergy_summable_of_ae [Nonempty ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    Summable (chaosEnergy f) := by
  obtain ⟨g, hg, hgs, hfg, _⟩ := gaussian_simplex_representative f hf hp
  have heq : chaosEnergy f = chaosEnergy g :=
    funext (gaussian_chaosEnergy_congr_ae f g hfg)
  rw [heq]
  exact (chaos_energy_hasSum g hg
    (simplex_component_memLp g hg (fun x => (hgs x).1) (fun x => (hgs x).2))).summable

/-- Actual noise separates its mass, centroid, second-chaos and entire signed
tail terms. This is the spectral identity used by the manuscript's assembly. -/
theorem gaussianNoiseStability_negative_expansion [Nonempty ι]
    (r : ℝ) (hr : |r| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    gaussianNoiseStability (-r) f =
      (∑ i, (∫ x, f x i ∂standardGaussian κ) ^ 2) -
      r * (∑ i, ∑ j, (∫ x, x j * f x i ∂standardGaussian κ) ^ 2) +
      r ^ 2 * chaosEnergy f 2 +
      ∑' k, (-r) ^ (k + 3) * chaosEnergy f (k + 3) := by
  have hneg : |-r| ≤ 1 := by simpa using hr
  rw [gaussianNoiseStability_spectral_of_ae (-r) hneg f hf hp,
    chaos_series_split_three (chaosEnergy f) (chaosEnergy_nonneg f)
      (gaussian_chaosEnergy_summable_of_ae f hf hp) (-r) hneg,
    chaosEnergy_zero, chaosEnergy_one]
  ring

/-- The concrete first three Gaussian chaos levels, with the second level
written as its full quadratic moment tensor. The residual is the entire signed
tail, with no truncation assumption. -/
theorem gaussianNoiseStability_negative_moment_expansion [Nonempty ι] [LinearOrder κ]
    (r : ℝ) (hr : |r| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    gaussianNoiseStability (-r) f =
      (∑ i, (∫ x, f x i ∂standardGaussian κ) ^ 2) -
      r * (∑ i, ∑ j, (∫ x, x j * f x i ∂standardGaussian κ) ^ 2) +
      (r ^ 2 / 2) * (∑ i, ∑ j, ∑ k,
        (∫ x, f x i * (x j * x k - if j = k then 1 else 0)
          ∂standardGaussian κ) ^ 2) +
      ∑' k, (-r) ^ (k + 3) * chaosEnergy f (k + 3) := by
  rw [gaussianNoiseStability_negative_expansion r hr f hf hp, chaosEnergy_two]
  simp only [quadraticMoment, quadraticCoordinate]
  change _ = _
  ring

end NegativeVoting
