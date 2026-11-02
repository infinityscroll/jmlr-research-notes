import Mathlib
import NegativeVoting.NoiseStability

/-! Every almost-everywhere measurable fractional assignment has an everywhere
measurable simplex representative. This handles completed-measure assignments
without silently narrowing the main theorem to Borel pointwise rules. -/
namespace NegativeVoting
open MeasureTheory
open scoped BigOperators

/-- Nonnegative finite coordinates summing to one form a measurable condition. -/
theorem measurableSet_simplexWeights {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (f : Ω → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i)) :
    MeasurableSet {x | SimplexWeights (f x)} := by
  classical
  have hn : MeasurableSet {x | ∀ i, 0 ≤ f x i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (hf i))
  have hs : MeasurableSet {x | ∑ i, f x i = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum Finset.univ (fun i _ => hf i))
      measurable_const
  exact hn.inter hs

/-- A genuine Borel, everywhere-simplex representative of any a.e. measurable,
a.e. simplex assignment. The exceptional set is repaired with a fixed vertex. -/
theorem exists_measurable_simplex_representative {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) (f : Ω → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) μ)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (f x)) :
    ∃ g : Ω → ι → ℝ, (∀ i, Measurable (fun x => g x i)) ∧
      (∀ x, SimplexWeights (g x)) ∧ f =ᵐ[μ] g := by
  classical
  let a : Ω → ι → ℝ := fun x i => (hf i).mk (fun x => f x i) x
  have ha (i : ι) : Measurable (fun x => a x i) := (hf i).measurable_mk
  have hfa : f =ᵐ[μ] a := by
    have hall : ∀ᵐ x ∂μ, ∀ i, f x i = a x i :=
      ae_all_iff.mpr (fun i => (hf i).ae_eq_mk)
    exact hall.mono (fun _ h => funext h)
  have hpa : ∀ᵐ x ∂μ, SimplexWeights (a x) := by
    filter_upwards [hp, hfa] with x hx hxa
    rwa [← hxa]
  let t : ι := Classical.choice inferInstance
  let v : ι → ℝ := fun i => if i = t then 1 else 0
  have hv : SimplexWeights v := by
    constructor
    · intro i
      dsimp [v]
      split_ifs <;> norm_num
    · simp [v]
  let g : Ω → ι → ℝ := fun x => if SimplexWeights (a x) then a x else v
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    simpa only [g, ite_apply] using
      (Measurable.ite (measurableSet_simplexWeights a ha) (ha i)
        (measurable_const : Measurable (fun _ : Ω => v i)))
  · intro x
    dsimp [g]
    split_ifs with h
    · exact h
    · exact hv
  · filter_upwards [hfa, hpa] with x hxa hx
    simpa [g, hx] using hxa

/-- Almost-everywhere admissible Gaussian rules have pointwise-simplex Borel
representatives preserving the actual objective at every valid correlation. -/
theorem gaussian_simplex_representative {κ ι : Type*} [Fintype κ]
    [Fintype ι] [Nonempty ι] (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    ∃ g : (κ → ℝ) → ι → ℝ, (∀ i, Measurable (fun x => g x i)) ∧
      (∀ x, SimplexWeights (g x)) ∧ f =ᵐ[standardGaussian κ] g ∧
      ∀ ρ : ℝ, |ρ| ≤ 1 → gaussianNoiseStability ρ f = gaussianNoiseStability ρ g := by
  obtain ⟨g, hg, hgs, hfg⟩ := exists_measurable_simplex_representative
    (standardGaussian κ) f hf hp
  exact ⟨g, hg, hgs, hfg, fun ρ hρ => gaussianNoiseStability_congr_ae ρ hρ f g hfg⟩

/-- The actual integrand remains integrable for completed-measure assignments;
Lean's zero convention for nonintegrable integrals is not used. -/
theorem integrable_noiseIntegrand_of_ae {κ ι : Type*} [Fintype κ]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    Integrable (noiseIntegrand ρ f) ((standardGaussian κ).prod (standardGaussian κ)) := by
  obtain ⟨g, hg, hgs, hfg⟩ := exists_measurable_simplex_representative
    (standardGaussian κ) f hf hp
  have hfirst : (fun z : (κ → ℝ) × (κ → ℝ) => f z.1) =ᵐ[
      (standardGaussian κ).prod (standardGaussian κ)] (fun z => g z.1) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg
  have hsecond := (correlatedVector_measurePreserving ρ hρ).quasiMeasurePreserving.ae_eq_comp hfg
  apply (integrable_noiseIntegrand ρ g hg hgs).congr
  filter_upwards [hfirst, hsecond] with z hz₁ hz₂
  change f (correlatedVector ρ z) = g (correlatedVector ρ z) at hz₂
  unfold noiseIntegrand
  rw [hz₁, hz₂]

/-- Probability bounds for every a.e.-measurable a.e.-simplex rule. -/
theorem gaussianNoiseStability_bounds_of_ae {κ ι : Type*} [Fintype κ]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    0 ≤ gaussianNoiseStability ρ f ∧ gaussianNoiseStability ρ f ≤ 1 := by
  obtain ⟨g, hg, hgs, _, hvalue⟩ := gaussian_simplex_representative f hf hp
  rw [hvalue ρ hρ]
  exact gaussianNoiseStability_bounds ρ g hg hgs

end NegativeVoting
