import GaussianNormalDerivatives
import GaussianChaosDecay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory GaussianFin NegativeVotingHypercontractivity
open NegativeVotingNormalTrace NegativeVotingNormalDerivatives NegativeVotingChaosDecay
open OAI.MinUncut.GaussianHermite
open scoped ENNReal NNReal

namespace NegativeVotingSmoothingComposition

/-- The checked L² semigroup law transferred to actual integral representatives. -/
theorem ouSemigroupFin_comp_ae {n : ℕ} (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    ouSemigroupFin t (ouSemigroupFin s f) =ᵐ[γFin n] ouSemigroupFin (t + s) f := by
  let F := hf.toLp f
  have hF : (F : (Fin n → ℝ) → ℝ) =ᵐ[γFin n] f := hf.coeFn_toLp
  have hS := (ouSemigroupFinLp_coeFn_ae s hs F).trans
    (ouSemigroupFin_ae_eq_of_aeEq s hs hF)
  have hTS := (ouSemigroupFinLp_coeFn_ae t ht (ouSemigroupFinLp s F)).trans
    (ouSemigroupFin_ae_eq_of_aeEq t ht hS)
  have hsum := (ouSemigroupFinLp_coeFn_ae (t + s) (add_nonneg ht hs) F).trans
    (ouSemigroupFin_ae_eq_of_aeEq (t + s) (add_nonneg ht hs) hF)
  rw [ouSemigroupFinLp_semigroup t s ht hs] at hsum
  exact hTS.symm.trans hsum

/-- Genuine Gaussian OU composition for every Gaussian-L² raw function,
including unbounded and completed-measurable representatives. -/
theorem gaussianAverage_comp_ae {n : ℕ} {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    gaussianAverage τ (gaussianAverage σ f) =ᵐ[γFin n] gaussianAverage (τ * σ) f := by
  rw [gaussianAverage_eq_ouSemigroupFin τ hτ,
    gaussianAverage_eq_ouSemigroupFin σ hσ,
    gaussianAverage_eq_ouSemigroupFin (τ * σ) (mul_pos hτ hσ),
    Real.log_mul (ne_of_gt hτ) (ne_of_gt hσ), neg_add]
  exact ouSemigroupFin_comp_ae _ _ (neg_nonneg.mpr (Real.log_nonpos hτ.le hτ1.le))
    (neg_nonneg.mpr (Real.log_nonpos hσ.le hσ1.le)) f hf

/-- Actual Gaussian smoothing is an L² contraction on raw representatives. -/
theorem gaussianAverage_l2_contraction {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (gaussianAverage τ f) 2 (γFin n) ≤ eLpNorm f 2 (γFin n) := by
  have hp : ENNReal.ofReal (1 + τ ^ 2) ≤ (2 : ℝ≥0∞) := by
    have hh : 1 + τ ^ 2 ≤ (2 : ℝ) := by nlinarith
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hh
  exact (memLp_gaussian_average_l2_hypercontractive τ hτ hτ1 f hf).trans
    (eLpNorm_le_eLpNorm_of_exponent_le hp)

theorem gaussianAverage_memLp_two {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    MemLp (gaussianAverage τ f) 2 (γFin n) :=
  (gaussianAverage_l2_contraction hτ hτ1 f hf).trans_lt hf

/-- Smoothing can be split into a hypercontractive outer part and an inner
L² part, with the exact product correlation. -/
theorem gaussianAverage_factorized_lq_bound {n : ℕ} {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (gaussianAverage (τ * σ) f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      eLpNorm (gaussianAverage σ f) 2 (γFin n) := by
  rw [← eLpNorm_congr_ae (gaussianAverage_comp_ae hτ hτ1 hσ hσ1 f hf)]
  exact memLp_gaussian_average_l2_to_lq τ hτ hτ1 _
    (gaussianAverage_memLp_two hσ hσ1 f hf)

/-- Genuine high-chaos Lq decay: the low coefficients vanish, and both the
spectral contraction and the actual smoothing composition are proved. -/
theorem gaussianAverage_highChaos_lq_bound {n : ℕ} {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    eLpNorm (gaussianAverage (τ * σ) f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (σ ^ k) * eLpNorm f 2 (γFin n) :=
  (gaussianAverage_factorized_lq_bound hτ hτ1 hσ hσ1 f hf).trans
    (gaussianAverage_eLpNorm_decay σ hσ hσ1 f hf k hvanish)

/-- The L32 specialization used for normal traces and face estimates. -/
theorem gaussianAverage_highChaos_l32_bound {n : ℕ} {τ σ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    eLpNorm (gaussianAverage (τ * σ) f) 32 (γFin n) ≤
      ENNReal.ofReal (σ ^ k) * eLpNorm f 2 (γFin n) := by
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  have hq : (32 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
    have hh : 31 ≤ 1 / τ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hτ)).mpr (by nlinarith)
    simpa only [one_div] using (show (32 : ℝ) ≤ 1 + 1 / τ ^ 2 by linarith)
  have hpq : (32 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (τ ^ 2)⁻¹) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hq
  exact (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
    (gaussianAverage_highChaos_lq_bound hτ hτ1 hσ hσ1 f hf k hvanish)

/-- Sharp variable-exponent fixed-normal trace bound. This allows q to grow,
with q=1+tau^(-2), as required by Gaussian weighted-facet estimates. -/
theorem normalTrace_lq_bound_sharp {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (normalTrace τ a f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hsq : τ ^ 2 < 1 := by nlinarith
  exact (memLp_gaussian_average_l2_to_lq τ hτ hτ1 _
    (normalSection_memLp_and_integral_sq_le hsq a f hf).1).trans
    (eLpNorm_normalSection_le_sharp hsq a f hf)

/-- The variable-q estimate for the actual single product-Gaussian integral. -/
theorem actual_product_normalTrace_lq_bound_sharp {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (fun x => ∫ z : (Fin n → ℝ) × ℝ,
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
        τ * a + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1))
      (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  rw [← eLpNorm_congr_ae (normalTrace_eq_product_ae hτ hτ1 a f hf)]
  exact normalTrace_lq_bound_sharp hτ hτ1 a f hf

/-- A common variable-q envelope for the whole normal interval. -/
theorem exists_normalTrace_lq_uniform_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n → ℝ) → ℝ,
      MemLp G (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧ (∀ x, 0 ≤ G x) ∧
      eLpNorm G (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A → ‖normalTrace τ a f x‖ ≤ G x := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) := (memLp_congr_ae hfg).mp hf
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsq : τ ^ 2 < 1 := by nlinarith
  let H := normalFiberNorm g
  have hH := normalFiberNorm_memLp_norm g hg
  have hT : eLpNorm (gaussianAverage τ H) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      eLpNorm H 2 (γFin n) :=
    memLp_gaussian_average_l2_to_lq τ hτ hτ1 H hH.1
  have hTm : MemLp (gaussianAverage τ H) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) := hT.trans_lt hH.1
  let C := Real.sqrt (normalRowSquare τ A)
  refine ⟨fun x => C * gaussianAverage τ H x, hTm.const_mul C, ?_, ?_, ?_⟩
  · intro x
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact integral_nonneg (fun _ => Real.sqrt_nonneg _)
  · change eLpNorm (C • gaussianAverage τ H) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤ _
    rw [eLpNorm_const_smul]
    have hC : ‖C‖ₑ = ENNReal.ofReal C := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hC]
    calc
      ENNReal.ofReal C * eLpNorm (gaussianAverage τ H) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
          ENNReal.ofReal C * eLpNorm H 2 (γFin n) := mul_le_mul_right hT _
      _ = _ := by rw [hH.2, ← eLpNorm_congr_ae hfg]
  · filter_upwards [ae_normalTrace_interval_bound_of_measurable hsq hA g hgm hg,
      normalTrace_congr_ae_all_parameters hsq hfg] with x hx hxx
    intro a ha
    rw [hxx a]
    exact hx a ha

/-- Literal normal supremum in the full variable hypercontractive exponent. -/
theorem normalTraceSup_lq_memLp_and_bound {n : ℕ} {τ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    MemLp (normalTraceSup τ A f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧
      eLpNorm (normalTraceSup τ A f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
        ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
          eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hm := normalTraceSup_aestronglyMeasurable (A := A) hτ hτ1 f hf
  obtain ⟨G, hGm, hGpos, hGn, hG⟩ := exists_normalTrace_lq_uniform_envelope hτ hτ1 hA f hf
  let I := Set.Icc (-A) A
  let a0 : I := ⟨0, by constructor <;> linarith⟩
  let : Nonempty I := ⟨a0⟩
  have hbound : ∀ᵐ x ∂γFin n, ‖normalTraceSup τ A f x‖ ≤ ‖G x‖ := by
    filter_upwards [hG] with x hx
    have hdom (a : I) : ‖normalTrace τ (a : ℝ) f x‖ ≤ G x :=
      hx a (abs_le.mpr a.property)
    have hb : BddAbove (Set.range (fun a : I => ‖normalTrace τ (a : ℝ) f x‖)) :=
      ⟨G x, by rintro _ ⟨a, rfl⟩; exact hdom a⟩
    have hnon : 0 ≤ normalTraceSup τ A f x :=
      (norm_nonneg _).trans (le_ciSup hb a0)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon, Real.norm_eq_abs, abs_of_nonneg (hGpos x)]
    exact ciSup_le hdom
  have hnorm := eLpNorm_mono_ae (p := ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) hm hbound
  exact ⟨hnorm.trans_lt hGm, hnorm.trans hGn⟩

/-- Actual-product normal supremum with variable q=1+tau^(-2). -/
theorem actual_product_normal_sup_lq_memLp_and_bound {n : ℕ} {τ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    let S := fun x => ⨆ a : Set.Icc (-A) A,
      ‖∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * (a : ℝ) + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)‖
    MemLp S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧ eLpNorm S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  intro S
  have hsq : τ ^ 2 < 1 := by nlinarith
  have heq : normalTraceSup τ A f =ᵐ[γFin n] S := by
    filter_upwards [normalTrace_eq_product_ae_all_parameters hsq f hf] with x hx
    exact iSup_congr (fun a => congrArg norm (hx a))
  have hh := normalTraceSup_lq_memLp_and_bound hτ hτ1 hA f hf
  refine ⟨(memLp_congr_ae heq).mp hh.1, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hh.2

/-- Explicit first-coordinate normal/tangent splitting of a finite Gaussian. -/
def normalCoordinates {n : ℕ} : (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
    MeasurableEquiv.prodComm

theorem normalCoordinates_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    normalCoordinates x = ((fun j => x j.succ), x 0) := rfl

theorem normalCoordinates_measurePreserving {n : ℕ} :
    MeasurePreserving (normalCoordinates (n := n)) (γFin (n + 1))
      ((γFin n).prod (gaussianReal 0 1)) := by
  exact Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0)

/-- A function in normal/tangent coordinates, with the coordinate map explicit. -/
def normalLift {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) : (Fin n → ℝ) × ℝ → ℝ :=
  f ∘ normalCoordinates.symm

theorem normalLift_memLp {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    {p : ℝ≥0∞} (hf : MemLp f p (γFin (n + 1))) :
    MemLp (normalLift f) p ((γFin n).prod (gaussianReal 0 1)) :=
  hf.comp_measurePreserving normalCoordinates_measurePreserving.symm

theorem normalLift_eLpNorm {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (γFin (n + 1))) (p : ℝ≥0∞) :
    eLpNorm (normalLift f) p ((γFin n).prod (gaussianReal 0 1)) =
      eLpNorm f p (γFin (n + 1)) :=
  eLpNorm_comp_measurePreserving hf normalCoordinates_measurePreserving.symm

theorem normalCoordinates_mix {n : ℕ} (ρ s : ℝ)
    (x y : Fin (n + 1) → ℝ) :
    normalCoordinates (fun j => ρ * x j + s * y j) =
      ((fun j => ρ * (normalCoordinates x).1 j + s * (normalCoordinates y).1 j),
        ρ * (normalCoordinates x).2 + s * (normalCoordinates y).2) := rfl

theorem normalCoordinates_symm_mix {n : ℕ} (ρ s : ℝ)
    (x y : (Fin n → ℝ) × ℝ) :
    normalCoordinates.symm ((fun j => ρ * x.1 j + s * y.1 j), ρ * x.2 + s * y.2) =
      (fun j => ρ * (normalCoordinates.symm x) j + s * (normalCoordinates.symm y) j) := by
  apply normalCoordinates.injective
  rw [normalCoordinates.apply_symm_apply, normalCoordinates_mix,
    normalCoordinates.apply_symm_apply, normalCoordinates.apply_symm_apply]

/-- The actual Gaussian product-coordinate averaging operator. -/
def productGaussianAverage {n : ℕ} (τ : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (p : (Fin n → ℝ) × ℝ) : ℝ :=
  ∫ z : (Fin n → ℝ) × ℝ,
    f ((fun j => τ * p.1 j + Real.sqrt (1 - τ ^ 2) * z.1 j),
      τ * p.2 + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)

/-- Pointwise coordinate identification of the two actual Gaussian integrals.
It uses a measure-preserving measurable equivalence, with no hidden Fubini premise. -/
theorem gaussianAverage_normalCoordinates {n : ℕ} (τ : ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ) (p : (Fin n → ℝ) × ℝ) :
    gaussianAverage τ f (normalCoordinates.symm p) =
      productGaussianAverage τ (normalLift f) p := by
  calc
    gaussianAverage τ f (normalCoordinates.symm p) =
        ∫ y : Fin (n + 1) → ℝ,
          normalLift f ((fun j => τ * p.1 j + Real.sqrt (1 - τ ^ 2) * (normalCoordinates y).1 j),
            τ * p.2 + Real.sqrt (1 - τ ^ 2) * (normalCoordinates y).2) ∂γFin (n + 1) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [normalLift, Function.comp_apply]
      rw [normalCoordinates_symm_mix, normalCoordinates.symm_apply_apply]
    _ = productGaussianAverage τ (normalLift f) p := by
      simpa only [productGaussianAverage] using
        (normalCoordinates_measurePreserving (n := n)).integral_comp'
          (fun z : (Fin n → ℝ) × ℝ => normalLift f
            ((fun j => τ * p.1 j + Real.sqrt (1 - τ ^ 2) * z.1 j),
              τ * p.2 + Real.sqrt (1 - τ ^ 2) * z.2))

/-- Normal-coordinate values of the actual full-vector smoothing agree with the
checked trace simultaneously for all normal parameters. -/
theorem normalTrace_normalCoordinates_ae_all_parameters {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : MemLp f 2 (γFin (n + 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      normalTrace τ a (normalLift f) x =
        gaussianAverage τ f (normalCoordinates.symm (x, a)) := by
  filter_upwards [normalTrace_eq_product_ae_all_parameters hτ (normalLift f)
    (normalLift_memLp f hf)] with x hx
  intro a
  exact (hx a).trans (gaussianAverage_normalCoordinates τ f (x, a)).symm

/-- Gaussian composition on a normal slice, upgraded from full-space AE
composition using the proved normal continuity and the full-support Gaussian.
The resulting single AE set works for every real normal parameter. -/
theorem normalTrace_smoothing_comp_ae_all_parameters {n : ℕ} {τ σ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : MemLp f 2 (γFin (n + 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      normalTrace τ a (normalLift (gaussianAverage σ f)) x =
        normalTrace (τ * σ) a (normalLift f) x := by
  have hprodpos : 0 < τ * σ := mul_pos hτ hσ
  have hprod1 : τ * σ < 1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  have hτsq : τ ^ 2 < 1 := by nlinarith
  have hprodsq : (τ * σ) ^ 2 < 1 := by nlinarith
  have hg := gaussianAverage_memLp_two hσ hσ1 f hf
  have heqprod := normalCoordinates_measurePreserving.symm.quasiMeasurePreserving.ae
    (gaussianAverage_comp_ae hτ hτ1 hσ hσ1 f hf)
  filter_upwards [Measure.ae_ae_of_ae_prod heqprod,
    normalTrace_normalCoordinates_ae_all_parameters hτsq (gaussianAverage σ f) hg,
    normalTrace_normalCoordinates_ae_all_parameters hprodsq f hf,
    ae_hasDerivAt_normalTrace hτsq (normalLift (gaussianAverage σ f)) (normalLift_memLp _ hg),
    ae_hasDerivAt_normalTrace hprodsq (normalLift f) (normalLift_memLp f hf)]
    with x hx hleft hright hdleft hdright
  have hc1 : Continuous (fun a : ℝ => normalTrace τ a (normalLift (gaussianAverage σ f)) x) :=
    continuous_iff_continuousAt.mpr (fun a => (hdleft a).continuousAt)
  have hc2 : Continuous (fun a : ℝ => normalTrace (τ * σ) a (normalLift f) x) :=
    continuous_iff_continuousAt.mpr (fun a => (hdright a).continuousAt)
  have heq : (fun a => normalTrace τ a (normalLift (gaussianAverage σ f)) x) =ᵐ[gaussianReal 0 1]
      (fun a => normalTrace (τ * σ) a (normalLift f) x) := by
    filter_upwards [hx] with a ha
    rw [hleft a, hright a]
    exact ha
  let : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  have hfun := (Continuous.ae_eq_iff_eq (gaussianReal 0 1) hc1 hc2).mp heq
  intro a
  exact congrFun hfun a

/-- High-chaos normal-supremum decay at the variable exponent q=1+tau^(-2).
Every factor comes from an actual Gaussian identity or proved norm bound. -/
theorem normalTraceSup_highChaos_lq_bound {n : ℕ} {τ σ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : MemLp f 2 (γFin (n + 1))) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    MemLp (normalTraceSup (τ * σ) A (normalLift f))
        (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧
      eLpNorm (normalTraceSup (τ * σ) A (normalLift f))
        (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ A) * σ ^ k) *
        eLpNorm f 2 (γFin (n + 1)) := by
  have hg := gaussianAverage_memLp_two hσ hσ1 f hf
  have hh := normalTraceSup_lq_memLp_and_bound hτ hτ1 hA
    (normalLift (gaussianAverage σ f)) (normalLift_memLp _ hg)
  have heq : normalTraceSup (τ * σ) A (normalLift f) =ᵐ[γFin n]
      normalTraceSup τ A (normalLift (gaussianAverage σ f)) := by
    filter_upwards [normalTrace_smoothing_comp_ae_all_parameters hτ hτ1 hσ hσ1 f hf]
      with x hx
    exact iSup_congr (fun a => congrArg norm (hx a).symm)
  refine ⟨(memLp_congr_ae heq).mpr hh.1, ?_⟩
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm (gaussianAverage σ f) 2 (γFin (n + 1)) := by
      simpa only [normalLift_eLpNorm _ hg.aestronglyMeasurable] using hh.2
    _ ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        (ENNReal.ofReal (σ ^ k) * eLpNorm f 2 (γFin (n + 1))) :=
      mul_le_mul_right (gaussianAverage_eLpNorm_decay σ hσ hσ1 f hf k hvanish) _
    _ = _ := by rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]

/-- The preceding high-chaos boundary directly for actual full-vector Gaussian
averages evaluated on the explicit normal/tangent coordinates. -/
theorem actual_gaussian_normal_sup_highChaos_lq_bound {n : ℕ} {τ σ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : MemLp f 2 (γFin (n + 1))) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    let S := fun x => ⨆ a : Set.Icc (-A) A,
      ‖gaussianAverage (τ * σ) f (normalCoordinates.symm (x, a))‖
    MemLp S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ∧
      eLpNorm S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ A) * σ ^ k) *
        eLpNorm f 2 (γFin (n + 1)) := by
  intro S
  have hp : 0 < τ * σ := mul_pos hτ hσ
  have hp1 : τ * σ < 1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  have hsq : (τ * σ) ^ 2 < 1 := by nlinarith
  have heq : normalTraceSup (τ * σ) A (normalLift f) =ᵐ[γFin n] S := by
    filter_upwards [normalTrace_normalCoordinates_ae_all_parameters hsq f hf] with x hx
    exact iSup_congr (fun a => congrArg norm (hx a))
  have hh := normalTraceSup_highChaos_lq_bound hτ hτ1 hσ hσ1 hA f hf k hvanish
  refine ⟨(memLp_congr_ae heq).mp hh.1, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hh.2

end NegativeVotingSmoothingComposition
