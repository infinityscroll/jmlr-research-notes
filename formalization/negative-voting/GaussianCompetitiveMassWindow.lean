import GaussianFractionalMassEnergy

/-! A dimension-independent first mass window, uniformly over the complete
negative voting interval, derived from actual Gaussian noise competition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical
universe u
namespace NegativeVotingCompetitiveMassWindow
open NegativeVoting NegativeVotingModern NegativeVotingRegularMaximum
  NegativeVotingCompetitiveParity NegativeVotingFractionalMass
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization

variable {κ : Type*} [Fintype κ]

theorem reference_first_energy_le_envelope (n : ℕ) (hn : 0 < n) :
    referenceFirstWeight n ≤ centroidEnvelope n := by
  let f := (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
  have hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian (Fin (n+2))) :=
    fun i => (measurable_maxWeights id (fun k => measurable_pi_apply k) i).aemeasurable
  have hp : ∀ᵐ x ∂standardGaussian (Fin (n+2)), SimplexWeights (f x) :=
    ae_of_all _ maxWeights_simplex
  have he : assignmentFirstEnergy f=referenceFirstWeight n := by
    rw [←canonical_chaosEnergy_one n hn,chaosEnergy_one]
    rfl
  have hd : massDeficit n f=0 := by
    unfold massDeficit assignmentMass
    simp only [f,canonical_mass,sub_self,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  have h := assignmentFirstEnergy_le_envelope n hn f hf hp
  simpa only [he,hd,mul_zero,add_zero] using h

theorem competitive_mass_deficit_parity (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤
      gaussianNoiseStability (-r) (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)) :
    (1-r*curvatureBound n)*massDeficit n f ≤
      r*(centroidEnvelope n-referenceFirstWeight n)+r^2*referenceSecondWeight n+r^3+r^4 := by
  have hp' := competitive_mass_first_energy_bound n hn r hr0 hr1 f hf hp hcomp
  change (∑ i, (assignmentMass f i)^2)-1/((n:ℝ)+2) ≤
    r*(assignmentFirstEnergy f-referenceFirstWeight n)+r^2*referenceSecondWeight n+r^3+r^4 at hp'
  rw [←massDeficit_eq n f hf hp] at hp'
  have he := mul_le_mul_of_nonneg_left (assignmentFirstEnergy_le_envelope n hn f hf hp) hr0
  nlinarith

/-- The exact finite coefficient is now a bound for actual competitive
fractional Gaussian assignments, not an assumed localization expression. -/
theorem competitive_mass_deficit_coefficient (n : ℕ) (hn : 0 < n)
    (hden : 0 < 1-curvatureBound n/((n:ℝ)+1))
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1))
    (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (hcomp : gaussianNoiseStability (-r) f ≤
      gaussianNoiseStability (-r) (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)) :
    ((n:ℝ)+2)^2*massDeficit n f ≤ localizationCoefficient n := by
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hn1 : 0 < (n:ℝ)+1 := by positivity
  have hR0 : 0 ≤ 1/((n:ℝ)+1) := by positivity
  have hR1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one hn1).2 (by linarith)
  have hB : 0 ≤ curvatureBound n := by unfold curvatureBound; positivity
  have hδ : 0 ≤ massDeficit n f := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hgap : 0 ≤ centroidEnvelope n-referenceFirstWeight n :=
    sub_nonneg.mpr (reference_first_energy_le_envelope n hn)
  have hA : 0 ≤ referenceSecondWeight n := referenceSecondWeight_nonneg n
  have hpar := competitive_mass_deficit_parity n hn r hr0 (hr.trans hR1) f hf hp hcomp
  have hdenle : 1-curvatureBound n/((n:ℝ)+1) ≤ 1-r*curvatureBound n := by
    have h : r*curvatureBound n ≤ curvatureBound n/((n:ℝ)+1) := by
      simpa only [div_eq_mul_inv,one_mul,mul_comm] using mul_le_mul_of_nonneg_right hr hB
    linarith
  have hnum : r*(centroidEnvelope n-referenceFirstWeight n)+r^2*referenceSecondWeight n+r^3+r^4 ≤
      (1/((n:ℝ)+1))*(centroidEnvelope n-referenceFirstWeight n)+
      (1/((n:ℝ)+1))^2*referenceSecondWeight n+(1/((n:ℝ)+1))^3+(1/((n:ℝ)+1))^4 := by
    gcongr
  have hd := (mul_le_mul_of_nonneg_right hdenle hδ).trans (hpar.trans hnum)
  have hq : massDeficit n f ≤
      ((1/((n:ℝ)+1))*(centroidEnvelope n-referenceFirstWeight n)+
      (1/((n:ℝ)+1))^2*referenceSecondWeight n+(1/((n:ℝ)+1))^3+(1/((n:ℝ)+1))^4)/
      (1-curvatureBound n/((n:ℝ)+1)) :=
    (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hd)
  have hs := mul_le_mul_of_nonneg_left hq (sq_nonneg ((n:ℝ)+2))
  rw [localizationCoefficient_eq_original]
  convert hs using 1 <;> simp only [div_pow,one_pow] <;> ring

theorem mass_window_of_scaled_deficit (n : ℕ) (f : (κ → ℝ) → Fin (n+2) → ℝ)
    (hδ : ((n:ℝ)+2)^2*massDeficit n f ≤ 49/50) (i : Fin (n+2)) :
    assignmentMass f i ∈ Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2)) := by
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hcell : (assignmentMass f i-1/((n:ℝ)+2))^2 ≤ massDeficit n f :=
    by
      unfold massDeficit
      exact Finset.single_le_sum (fun j _ => sq_nonneg (assignmentMass f j-1/((n:ℝ)+2))) (Finset.mem_univ i)
  have hs := (mul_le_mul_of_nonneg_left hcell (sq_nonneg ((n:ℝ)+2))).trans hδ
  have he : ((n:ℝ)+2)*(assignmentMass f i-1/((n:ℝ)+2))=
      ((n:ℝ)+2)*assignmentMass f i-1 := by field_simp <;> ring
  rw [←mul_pow,he] at hs
  have habs : |((n:ℝ)+2)*assignmentMass f i-1| ≤ (99/100:ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤99/100)).mp
    rw [sq_abs]
    nlinarith
  have hb := abs_le.mp habs
  constructor
  · apply (div_le_iff₀ hm).2
    nlinarith
  · apply (le_div_iff₀ hm).2
    nlinarith

/-- One eventual threshold works simultaneously for every finite ambient
coordinate type, every AE fractional assignment, and all admissible r. -/
theorem eventually_uniform_competitive_mass_window :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (f : (κ → ℝ) → Fin (n+2) → ℝ)
      (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
      (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
      (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1))
      (hcomp : gaussianNoiseStability (-r) f ≤
        gaussianNoiseStability (-r) (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)),
      ((n:ℝ)+2)^2*massDeficit n f ≤ 49/50 ∧
      ∀ i, assignmentMass f i ∈ Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2)) := by
  filter_upwards [eventually_denominator_positive,eventually_localizationCoefficient_le,
    eventually_gt_atTop (0:ℕ)] with n hden hc hn
  intro κ _ f hf hp r hr0 hr hcomp
  have hd := (competitive_mass_deficit_coefficient n hn hden r hr0 hr f hf hp hcomp).trans hc
  exact ⟨hd,mass_window_of_scaled_deficit n f hd⟩

end NegativeVotingCompetitiveMassWindow
