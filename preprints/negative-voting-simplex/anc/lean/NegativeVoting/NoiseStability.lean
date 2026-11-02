import Mathlib
import NegativeVoting.GaussianMoments

/-!
# Concrete finite-dimensional Gaussian noise stability

The second vector is constructed as `rho * x + sqrt (1-rho^2) * y` from
independent finite-product standard Gaussians. All integral statements in this
file concern that actual measure and actual simplex-valued rules. No Gaussian
simplex optimality inequality or Hermite representation is postulated.
-/

namespace NegativeVoting

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable abbrev standardGaussian (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi (fun _ : κ => gaussianReal 0 1)

/-- The independent Gaussian pair is a probability measure. -/
theorem standardGaussian_pair_probability (κ : Type*) [Fintype κ] :
    IsProbabilityMeasure ((standardGaussian κ).prod (standardGaussian κ)) := by
  apply Measure.prod.instIsProbabilityMeasure

/-- The second member of the standard Gaussian noise coupling. -/
noncomputable def correlatedVector {κ : Type*} (ρ : ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) : κ → ℝ :=
  fun j => ρ * z.1 j + Real.sqrt (1 - ρ ^ 2) * z.2 j

/-- Pointwise agreement of two fractional label assignments in the coupling. -/
noncomputable def noiseIntegrand {κ ι : Type*} [Fintype ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ) (z : (κ → ℝ) × (κ → ℝ)) : ℝ :=
  ∑ i, f z.1 i * f (correlatedVector ρ z) i

/-- Actual noise stability on a finite product of standard real Gaussians.
The standard correlation interpretation applies when `|rho| <= 1`. -/
noncomputable def gaussianNoiseStability {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∫ z, noiseIntegrand ρ f z ∂(standardGaussian κ).prod (standardGaussian κ)

/-- The Gaussian coupling map is measurable in every finite dimension. -/
theorem measurable_correlatedVector {κ : Type*} (ρ : ℝ) :
    Measurable (@correlatedVector κ ρ) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_const.mul ((measurable_pi_apply j).comp measurable_fst)).add
    (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))

/-- Coupled fractional agreement is measurable for measurable component rules. -/
theorem measurable_noiseIntegrand {κ ι : Type*} [Fintype ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i)) :
    Measurable (noiseIntegrand ρ f) := by
  exact Finset.measurable_sum _ (fun i _ =>
    ((hf i).comp measurable_fst).mul ((hf i).comp (measurable_correlatedVector ρ)))

/-- Agreement of two simplex vectors always lies in `[0,1]`. -/
theorem simplex_agreement_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (hp : SimplexWeights p) (hq : SimplexWeights q) :
    0 ≤ ∑ i, p i * q i ∧ ∑ i, p i * q i ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (hq.1 i))
  · calc
      ∑ i, p i * q i ≤ ∑ i, p i := by
        apply Finset.sum_le_sum
        intro i _
        simpa using mul_le_mul_of_nonneg_left (simplex_weight_le_one q hq i) (hp.1 i)
      _ = 1 := hp.2

/-- The concrete coupling integrand is integrable. This is proved from the
simplex bound, and is not a hidden assumption of the stability definition. -/
theorem integrable_noiseIntegrand {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    Integrable (noiseIntegrand ρ f) ((standardGaussian κ).prod (standardGaussian κ)) := by
  apply Integrable.of_mem_Icc 0 1 (measurable_noiseIntegrand ρ f hf).aemeasurable
  exact Filter.Eventually.of_forall (fun z =>
    simplex_agreement_bounds (f z.1) (f (correlatedVector ρ z))
      (hsimplex z.1) (hsimplex (correlatedVector ρ z)))

/-- Concrete Gaussian noise stability lies in `[0,1]`. -/
theorem gaussianNoiseStability_bounds {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    0 ≤ gaussianNoiseStability ρ f ∧ gaussianNoiseStability ρ f ≤ 1 := by
  letI := standardGaussian_pair_probability κ
  have hint := integrable_noiseIntegrand ρ f hf hsimplex
  constructor
  · exact integral_nonneg (fun z => (simplex_agreement_bounds _ _
      (hsimplex z.1) (hsimplex (correlatedVector ρ z))).1)
  · have hle := integral_mono hint (integrable_const (1 : ℝ)) (fun z =>
      (simplex_agreement_bounds _ _ (hsimplex z.1)
        (hsimplex (correlatedVector ρ z))).2)
    simpa [gaussianNoiseStability] using hle

/-- At zero correlation the second vector is exactly the independent input. -/
theorem correlatedVector_zero {κ : Type*} (z : (κ → ℝ) × (κ → ℝ)) :
    correlatedVector 0 z = z.2 := by
  funext j
  simp [correlatedVector]

/-- At independence the stability is exactly the sum of squared label masses. -/
theorem gaussianNoiseStability_zero {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    gaussianNoiseStability 0 f =
      ∑ i, (∫ x, f x i ∂standardGaussian κ) ^ 2 := by
  have hi (i : ι) : Integrable (fun x => f x i) (standardGaussian κ) := by
    apply Integrable.of_mem_Icc 0 1 (hf i).aemeasurable
    exact Filter.Eventually.of_forall (fun x =>
      ⟨(hsimplex x).1 i, simplex_weight_le_one (f x) (hsimplex x) i⟩)
  unfold gaussianNoiseStability noiseIntegrand
  simp_rw [correlatedVector_zero]
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).mul_prod (hi i))]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [pow_two] using integral_prod_mul (μ := standardGaussian κ)
    (ν := standardGaussian κ) (fun x => f x i) (fun x => f x i)

/-- A normalized linear combination of two independent standard real Gaussians
has the standard Gaussian law. The law is established from characteristic
functions and product integration. -/
theorem standardGaussian_real_mix_law (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun z : ℝ × ℝ => a * z.1 + b * z.2) = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I)) _ from
      (show Measurable (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I)) by fun_prop).aestronglyMeasurable)]
  have hexp (z : ℝ × ℝ) :
      Complex.exp ((t : ℂ) * (a * z.1 + b * z.2) * Complex.I) =
        Complex.exp (((a * t : ℝ) : ℂ) * z.1 * Complex.I) *
        Complex.exp (((b * t : ℝ) : ℂ) * z.2 * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [Complex.ofReal_add, Complex.ofReal_mul]
  simp_rw [hexp]
  rw [integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ => Complex.exp (((a * t : ℝ) : ℂ) * x * Complex.I))
    (fun x : ℝ => Complex.exp (((b * t : ℝ) : ℂ) * x * Complex.I))]
  rw [← charFun_apply_real (a * t), ← charFun_apply_real (b * t)]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.ofReal_one, one_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have habC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  calc
    _ = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (t : ℂ) ^ 2 / 2 := by ring
    _ = _ := by rw [habC]; ring

/-- Label masses are actual Gaussian integrals of the fractional rule. -/
noncomputable def gaussianLabelMass {κ ι : Type*} [Fintype κ]
    (f : (κ → ℝ) → ι → ℝ) (i : ι) : ℝ := ∫ x, f x i ∂standardGaussian κ

/-- Every measurable simplex-rule coordinate is Gaussian-integrable. -/
theorem integrable_gaussian_simplex_component {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) (i : ι) :
    Integrable (fun x => f x i) (standardGaussian κ) := by
  apply Integrable.of_mem_Icc 0 1 (hf i).aemeasurable
  exact Filter.Eventually.of_forall (fun x =>
    ⟨(hsimplex x).1 i, simplex_weight_le_one (f x) (hsimplex x) i⟩)

/-- The vector of actual Gaussian label masses is itself a simplex vector. -/
theorem gaussianLabelMass_simplex {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    SimplexWeights (gaussianLabelMass f) := by
  constructor
  · intro i
    exact integral_nonneg (fun x => (hsimplex x).1 i)
  · unfold gaussianLabelMass
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      integrable_gaussian_simplex_component f hf hsimplex i)]
    have hsum : (fun x => ∑ i, f x i) = (fun _ => (1 : ℝ)) :=
      funext (fun x => (hsimplex x).2)
    rw [hsum]
    simp

/-- Exact finite mass-defect decomposition around the uniform vector. -/
theorem simplex_mass_square_decomposition {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℝ) (hp : SimplexWeights p) :
    (∑ i, p i ^ 2) = 1 / (Fintype.card ι : ℝ) +
      ∑ i, (p i - 1 / (Fintype.card ι : ℝ)) ^ 2 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcenter (u : ℝ) : (∑ i, (p i - u) ^ 2) =
      (∑ i, p i ^ 2) - 2 * u * (∑ i, p i) + (Fintype.card ι : ℝ) * u ^ 2 := by
    calc
      _ = ∑ i, (p i ^ 2 - (2 * u) * p i + u ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
  rw [hcenter, hp.2]
  field_simp
  ring

/-- The concrete zero-noise value splits into the uniform baseline and the
squared mass imbalance used by the manuscript's localization argument. -/
theorem gaussianNoiseStability_zero_mass_defect {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    gaussianNoiseStability 0 f = 1 / (Fintype.card ι : ℝ) +
      ∑ i, (gaussianLabelMass f i - 1 / (Fintype.card ι : ℝ)) ^ 2 := by
  rw [gaussianNoiseStability_zero f hf hsimplex]
  exact simplex_mass_square_decomposition (gaussianLabelMass f)
    (gaussianLabelMass_simplex f hf hsimplex)

/-- The exact scalar mixing coefficients preserve Gaussian variance throughout
`[-1,1]`, including both endpoints. -/
theorem noise_mixing_coefficients (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    ρ ^ 2 + (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 := by
  have hs : 0 ≤ 1 - ρ ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one ρ).mpr hρ)
  rw [Real.sq_sqrt hs]
  ring

/-- The concrete correlated second vector has the original finite-product
standard Gaussian marginal. This proves the coupling's Gaussian semantics. -/
theorem correlatedVector_measurePreserving {κ : Type*} [Fintype κ]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    MeasurePreserving (@correlatedVector κ ρ)
      ((standardGaussian κ).prod (standardGaussian κ)) (standardGaussian κ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ
  have hsplit : MeasurePreserving e.symm
      ((standardGaussian κ).prod (standardGaussian κ))
      (Measure.pi (fun _ : κ => (gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ
      (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm e
  have hscalar (j : κ) : MeasurePreserving
      (fun z : ℝ × ℝ => ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianReal 0 1) :=
    ⟨by fun_prop, standardGaussian_real_mix_law ρ _ (noise_mixing_coefficients ρ hρ)⟩
  have hpi := measurePreserving_pi
    (fun _ : κ => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : κ => gaussianReal 0 1) hscalar
  exact hpi.comp hsplit

/-- An equivalent explicit marginal-law formulation. -/
theorem correlatedVector_marginal {κ : Type*} [Fintype κ]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    ((standardGaussian κ).prod (standardGaussian κ)).map (correlatedVector ρ) =
      standardGaussian κ := (correlatedVector_measurePreserving ρ hρ).map_eq

/-- The actual Gaussian noise-averaging operator, defined by an ordinary
finite-product Gaussian integral, with no spectral identities postulated. -/
noncomputable def gaussianNoiseOperator {κ ι : Type*} [Fintype κ]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ) (x : κ → ℝ) (i : ι) : ℝ :=
  ∫ y, f (correlatedVector ρ (x, y)) i ∂standardGaussian κ

/-- Each section of the averaging integral is integrable for measurable
simplex-valued assignments. -/
theorem integrable_gaussian_noise_section {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) (x : κ → ℝ) (i : ι) :
    Integrable (fun y => f (correlatedVector ρ (x, y)) i) (standardGaussian κ) := by
  apply Integrable.of_mem_Icc (a := 0) (b := 1)
  · exact ((hf i).comp ((measurable_correlatedVector ρ).comp
      ((measurable_const (a := x)).prodMk measurable_id))).aemeasurable
  · exact Filter.Eventually.of_forall fun y =>
      ⟨(hsimplex _).1 i, simplex_weight_le_one _ (hsimplex _) i⟩

/-- Gaussian averaging preserves the simplex pointwise, including all negative
noise parameters. -/
theorem gaussianNoiseOperator_simplex {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) (x : κ → ℝ) :
    SimplexWeights (gaussianNoiseOperator ρ f x) := by
  constructor
  · intro i
    exact integral_nonneg fun y => (hsimplex _).1 i
  · unfold gaussianNoiseOperator
    rw [← integral_finsetSum _ (fun i _ =>
      integrable_gaussian_noise_section ρ f hf hsimplex x i)]
    have hsum : (fun y => ∑ i, f (correlatedVector ρ (x, y)) i) = fun _ => (1 : ℝ) :=
      funext fun y => (hsimplex _).2
    rw [hsum]
    simp

/-- Fubini identifies the concrete coupling integral with the pairing against
its actual Gaussian noise operator. -/
theorem gaussianNoiseStability_eq_operator_pairing {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) :
    gaussianNoiseStability ρ f =
      ∫ x, ∑ i, f x i * gaussianNoiseOperator ρ f x i ∂standardGaussian κ := by
  unfold gaussianNoiseStability
  rw [integral_prod _ (integrable_noiseIntegrand ρ f hf hsimplex)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  unfold noiseIntegrand gaussianNoiseOperator
  dsimp only
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_gaussian_noise_section ρ f hf hsimplex x i).const_mul (f x i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]

/-- Noise stability depends only on the Gaussian almost-everywhere assignment
class. Both coupling marginals are used; no Borel representative is assumed. -/
theorem gaussianNoiseStability_congr_ae {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (f g : (κ → ℝ) → ι → ℝ)
    (hfg : f =ᵐ[standardGaussian κ] g) :
    gaussianNoiseStability ρ f = gaussianNoiseStability ρ g := by
  have hfirst : (fun z : (κ → ℝ) × (κ → ℝ) => f z.1) =ᵐ[
      (standardGaussian κ).prod (standardGaussian κ)] (fun z => g z.1) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg
  have hsecond := (correlatedVector_measurePreserving ρ hρ).quasiMeasurePreserving.ae_eq_comp hfg
  apply integral_congr_ae
  filter_upwards [hfirst, hsecond] with z hz₁ hz₂
  change f (correlatedVector ρ z) = g (correlatedVector ρ z) at hz₂
  unfold noiseIntegrand
  rw [hz₁, hz₂]

/-- Gaussian averaging of a measurable assignment remains measurable. -/
theorem measurable_gaussianNoiseOperator {κ ι : Type*} [Fintype κ]
    (ρ : ℝ) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i)) (i : ι) :
    Measurable (fun x => gaussianNoiseOperator ρ f x i) := by
  exact (((hf i).comp (measurable_correlatedVector ρ)).stronglyMeasurable.integral_prod_right').measurable

/-- The Gaussian noise operator preserves each actual Gaussian label mass.
This uses the proved second marginal, rather than assuming stationarity. -/
theorem gaussianNoiseOperator_preserves_mass {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, Measurable (fun x => f x i))
    (hsimplex : ∀ x, SimplexWeights (f x)) (i : ι) :
    gaussianLabelMass (gaussianNoiseOperator ρ f) i = gaussianLabelMass f i := by
  have hint : Integrable (fun z => f (correlatedVector ρ z) i)
      ((standardGaussian κ).prod (standardGaussian κ)) := by
    apply Integrable.of_mem_Icc (a := 0) (b := 1)
    · exact ((hf i).comp (measurable_correlatedVector ρ)).aemeasurable
    · exact Filter.Eventually.of_forall fun z =>
        ⟨(hsimplex _).1 i, simplex_weight_le_one _ (hsimplex _) i⟩
  have hmap := integral_map (μ := (standardGaussian κ).prod (standardGaussian κ))
    (φ := correlatedVector ρ) (f := fun x => f x i)
    (measurable_correlatedVector ρ).aemeasurable (hf i).aestronglyMeasurable
  rw [correlatedVector_marginal ρ hρ] at hmap
  unfold gaussianLabelMass gaussianNoiseOperator
  rw [← integral_prod _ hint]
  exact hmap.symm

end NegativeVoting
