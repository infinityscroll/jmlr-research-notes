import GaussianRegularSecondGap

/-! Identification of the actual regular second Hermite energy in every
ambient dimension from actual noise laws and proved third-order tails. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical
namespace NegativeVotingReferenceSecondEnergy
open NegativeVoting NegativeVotingModern NegativeVotingCompetitiveParity
  NegativeVotingRegularScoreLaw NegativeVotingRegularMaximum
  NegativeVotingGaussianMaximumLocalization NegativeVotingRegularSecondGap
  OAI.MinUncut.GaussianHermite

variable {κ κ₂ ι : Type*} [Fintype κ] [Fintype κ₂] [Fintype ι] [Nonempty ι]

/-- The first unmatched coefficient cannot be masked by the proved cubic
Gaussian spectral tail. The two rules may live in different dimensions. -/
theorem secondChaos_eq_of_noise_and_low_modes
    (f : (κ → ℝ) → ι → ℝ) (g : (κ₂ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (hg : ∀ i, AEMeasurable (fun x => g x i) (standardGaussian κ₂))
    (hq : ∀ᵐ x ∂standardGaussian κ₂, SimplexWeights (g x))
    (h0 : chaosEnergy f 0=chaosEnergy g 0) (h1 : chaosEnergy f 1=chaosEnergy g 1)
    (hnoise : ∀ r : ℝ, 0 < r → r ≤ 1 → gaussianNoiseStability (-r) f=gaussianNoiseStability (-r) g) :
    chaosEnergy f 2=chaosEnergy g 2 := by
  have hsf := gaussian_chaosEnergy_summable_of_ae f hf hp
  have hsg := gaussian_chaosEnergy_summable_of_ae g hg hq
  have hef := gaussian_chaosEnergy_le_one_of_ae f hf hp
  have heg := gaussian_chaosEnergy_le_one_of_ae g hg hq
  have hsmall (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
      |chaosEnergy f 2-chaosEnergy g 2| ≤ 2*r := by
    have hρ : |-r| ≤ 1 := by simpa only [abs_neg,abs_of_nonneg hr.le] using hr1
    have he := hnoise r hr hr1
    rw [gaussianNoiseStability_spectral_of_ae (-r) hρ f hf hp,
      gaussianNoiseStability_spectral_of_ae (-r) hρ g hg hq,
      chaos_series_split_three _ (chaosEnergy_nonneg f) hsf (-r) hρ,
      chaos_series_split_three _ (chaosEnergy_nonneg g) hsg (-r) hρ,h0,h1] at he
    have htf := abs_le.mp (bounded_energy_tail _ (chaosEnergy_nonneg f) hsf hef r hr.le hr1 3)
    have htg := abs_le.mp (bounded_energy_tail _ (chaosEnergy_nonneg g) hsg heg r hr.le hr1 3)
    have hr2 : 0 < r^2 := sq_pos_of_pos hr
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_left₀ hr2).mp
      nlinarith
    · apply (mul_le_mul_iff_left₀ hr2).mp
      nlinarith
  by_contra hne
  have hd : 0 < |chaosEnergy f 2-chaosEnergy g 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let r := min 1 (|chaosEnergy f 2-chaosEnergy g 2|/4)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have h := hsmall r hr (min_le_left _ _)
  have hh : r ≤ |chaosEnergy f 2-chaosEnergy g 2|/4 := min_le_right _ _
  linarith

theorem regular_chaosEnergy_zero (n : ℕ) (B : Fin (n+2) → κ → ℝ)
    (hB : RegularSimplexGram B) : chaosEnergy (regularAssignment B) 0=1/((n:ℝ)+2) := by
  rw [chaosEnergy_zero]
  change (∑ i : Fin (n+2), (∫ x, regularAssignment B x i ∂standardGaussian κ)^2)=1/((n:ℝ)+2)
  simp_rw [regularAssignment_mass B hB]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp

/-- The literal reference coefficient agrees with the canonical formula in
any finite ambient realization of the normalized regular Gram matrix. -/
theorem regular_chaosEnergy_two_eq_reference (n : ℕ) (hn : 0 < n)
    (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B) :
    chaosEnergy (regularAssignment B) 2=referenceSecondWeight n := by
  have he := secondChaos_eq_of_noise_and_low_modes (regularAssignment B)
    (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
    (fun i => (regularAssignment_measurable B i).aemeasurable)
    (ae_of_all _ (regularAssignment_simplex B))
    (fun i => (measurable_maxWeights id (fun k => measurable_pi_apply k) i).aemeasurable)
    (ae_of_all _ maxWeights_simplex)
    ((regular_chaosEnergy_zero n B hB).trans (canonical_chaosEnergy_zero n).symm)
    ((regular_chaosEnergy_one_eq_reference n hn B hB).trans (canonical_chaosEnergy_one n hn).symm)
    (fun r _ _ => regularAssignment_noise_eq_canonical n B hB (-r))
  exact he.trans (canonical_chaosEnergy_two n hn)

universe u
/-- The explicit regular gap is valid for the actual reference in every
ambient dimension, with one threshold before the dimension and rows. -/
theorem eventually_uniform_regular_second_gap :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B),
      0 ≤ chaosEnergy (regularAssignment B) 2-referenceJensenFloor n ∧
      chaosEnergy (regularAssignment B) 2-referenceJensenFloor n ≤ 50/((n:ℝ)+2) := by
  filter_upwards [eventually_reference_second_gap,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro κ _ B hB
  rw [regular_chaosEnergy_two_eq_reference n hn0 B hB]
  exact hn

end NegativeVotingReferenceSecondEnergy
