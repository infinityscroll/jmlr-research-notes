import MarkovSemigroups.Instances.WorkInProgress.EuclideanHypercontractive

/-!
# Concrete Gaussian hypercontractivity specialization

The endpoint is obtained from the actual Gaussian OU theorem, not from any
of the legacy abstract axioms present in its imported development.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory GaussianFin
open scoped ENNReal

namespace NegativeVotingHypercontractivity

/-- Exact scalar relation used to specialize Gross's exponent to an L² target. -/
theorem gross_l2_exponent_relation (t : ℝ) :
    1 + ((1 + Real.exp (-2 * t)) - 1) * Real.exp (2 * t) = 2 := by
  rw [add_sub_cancel_left, ← Real.exp_add]
  norm_num

/-- The genuine Gaussian OU hypercontractive bound on its L² carrier. The
source Lp membership follows from L² membership on a probability space. -/
theorem actual_gaussian_ou_l2_hypercontractive {n : ℕ}
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (γFin n)) :
    eLpNorm (ouSemigroupFin t (f : (Fin n → ℝ) → ℝ)) 2 (γFin n) ≤
      eLpNorm (f : (Fin n → ℝ) → ℝ)
        (ENNReal.ofReal (1 + Real.exp (-2 * t))) (γFin n) := by
  have hp : 1 < 1 + Real.exp (-2 * t) := by linarith [Real.exp_pos (-2 * t)]
  have hp2 : 1 + Real.exp (-2 * t) ≤ 2 := by
    have hle : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hfp : MemLp (f : (Fin n → ℝ) → ℝ)
      (ENNReal.ofReal (1 + Real.exp (-2 * t))) (γFin n) :=
    (Lp.memLp f).mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hp2)
  have hrel : 2 ≤ 1 + ((1 + Real.exp (-2 * t)) - 1) * Real.exp (2 * 1 * t) := by
    simpa only [mul_one] using (gross_l2_exponent_relation t).ge
  have hh := (stdGaussianFin_isHypercontractive n).2
    (1 + Real.exp (-2 * t)) 2 t hp hp2 ht hrel f hfp
  change eLpNorm ((ouSemigroupFinLp (n := n) t f) : (Fin n → ℝ) → ℝ)
      (ENNReal.ofReal 2) (γFin n) ≤ _ at hh
  norm_num only [ENNReal.ofReal_ofNat] at hh
  rw [eLpNorm_congr_ae (ouSemigroupFinLp_coeFn_ae t ht.le f)] at hh
  exact hh

/-- The actual finite-product Gaussian averaging operator with correlation tau. -/
def gaussianAverage {n : ℕ} (τ : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * y j) ∂γFin n

/-- The time-to-correlation conversion is exact for every 0<tau<1. -/
theorem gaussianAverage_eq_ouSemigroupFin {n : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : (Fin n → ℝ) → ℝ) :
    gaussianAverage τ f = ouSemigroupFin (-Real.log τ) f := by
  have hpow : Real.exp (-2 * (-Real.log τ)) = τ ^ 2 := by
    rw [show -2 * (-Real.log τ) = Real.log τ + Real.log τ by ring,
      Real.exp_add, Real.exp_log hτ, pow_two]
  funext x
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  funext j
  simp only [ouShiftFin, neg_neg, Real.exp_log hτ, hpow]

/-- The desired L^(1+tau²)-to-L² bound for the actual Gaussian noise integral,
for arbitrary L² representatives; the source Lp membership is derived. -/
theorem actual_gaussian_average_l2_hypercontractive {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : Lp ℝ 2 (γFin n)) :
    eLpNorm (gaussianAverage τ (f : (Fin n → ℝ) → ℝ)) 2 (γFin n) ≤
      eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal (1 + τ ^ 2)) (γFin n) := by
  have ht : 0 < -Real.log τ := neg_pos.mpr (Real.log_neg hτ hτ1)
  have hpow : Real.exp (-2 * (-Real.log τ)) = τ ^ 2 := by
    rw [show -2 * (-Real.log τ) = Real.log τ + Real.log τ by ring,
      Real.exp_add, Real.exp_log hτ, pow_two]
  rw [gaussianAverage_eq_ouSemigroupFin τ hτ]
  simpa only [hpow] using actual_gaussian_ou_l2_hypercontractive
    (-Real.log τ) ht f

/-- Gaussian averaging respects Gaussian almost-everywhere equality. The
measure-preserving/Fubini theorem of the attributed Gaussian dependency is used;
no boundedness or pointwise measurability is needed. -/
theorem gaussianAverage_congr_ae {n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    {f g : (Fin n → ℝ) → ℝ} (hfg : f =ᵐ[γFin n] g) :
    gaussianAverage τ f =ᵐ[γFin n] gaussianAverage τ g := by
  have ht : 0 ≤ -Real.log τ := (neg_pos.mpr (Real.log_neg hτ hτ1)).le
  rw [gaussianAverage_eq_ouSemigroupFin τ hτ,
    gaussianAverage_eq_ouSemigroupFin τ hτ]
  exact GaussianFin.ouSemigroupFin_ae_eq_of_aeEq (-Real.log τ) ht hfg

/-- The actual integral L^(1+tau²)-to-L² inequality for any square-integrable
raw function, including completed-Gaussian-measurable representatives. -/
theorem memLp_gaussian_average_l2_hypercontractive {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (gaussianAverage τ f) 2 (γFin n) ≤
      eLpNorm f (ENNReal.ofReal (1 + τ ^ 2)) (γFin n) := by
  have hh := actual_gaussian_average_l2_hypercontractive τ hτ hτ1 (hf.toLp f)
  rwa [eLpNorm_congr_ae (gaussianAverage_congr_ae τ hτ hτ1 hf.coeFn_toLp),
    eLpNorm_congr_ae hf.coeFn_toLp] at hh

/-- The exact L²-to-L^(1+exp(2t)) inequality for the actual OU integral. -/
theorem actual_gaussian_ou_l2_to_lq {n : ℕ}
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (γFin n)) :
    eLpNorm (ouSemigroupFin t (f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal (1 + Real.exp (2 * t))) (γFin n) ≤
      eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (γFin n) := by
  have h2q : 2 ≤ 1 + Real.exp (2 * t) := by
    have hh : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by linarith)
    linarith
  have hrel : 1 + Real.exp (2 * t) ≤ 1 + (2 - 1) * Real.exp (2 * 1 * t) := by
    norm_num
  have hh := (stdGaussianFin_isHypercontractive n).2
    2 (1 + Real.exp (2 * t)) t (by norm_num) h2q ht hrel f
    (by
      change MemLp (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal 2) (γFin n)
      norm_num only [ENNReal.ofReal_ofNat]
      exact Lp.memLp f)
  change eLpNorm ((ouSemigroupFinLp (n := n) t f) : (Fin n → ℝ) → ℝ)
      (ENNReal.ofReal (1 + Real.exp (2 * t))) (γFin n) ≤
    eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal 2) (γFin n) at hh
  norm_num only [ENNReal.ofReal_ofNat] at hh
  rw [eLpNorm_congr_ae (ouSemigroupFinLp_coeFn_ae t ht.le f)] at hh
  exact hh

/-- The genuine Gaussian L²-to-L^(1+tau^(-2)) inequality on the L² carrier. -/
theorem actual_gaussian_average_l2_to_lq {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (f : Lp ℝ 2 (γFin n)) :
    eLpNorm (gaussianAverage τ (f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (γFin n) := by
  have ht : 0 < -Real.log τ := neg_pos.mpr (Real.log_neg hτ hτ1)
  have hpow : Real.exp (2 * (-Real.log τ)) = (τ ^ 2)⁻¹ := by
    rw [show 2 * (-Real.log τ) = -(Real.log τ + Real.log τ) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hτ, pow_two]
  rw [gaussianAverage_eq_ouSemigroupFin τ hτ]
  simpa only [hpow] using actual_gaussian_ou_l2_to_lq (-Real.log τ) ht f

/-- The actual-integral hypercontractive inequality for every square-integrable
real function. In particular it covers unbounded high-chaos projections. -/
theorem memLp_gaussian_average_l2_to_lq {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (gaussianAverage τ f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) ≤
      eLpNorm f 2 (γFin n) := by
  have hh := actual_gaussian_average_l2_to_lq τ hτ hτ1 (hf.toLp f)
  rwa [eLpNorm_congr_ae (gaussianAverage_congr_ae τ hτ hτ1 hf.coeFn_toLp),
    eLpNorm_congr_ae hf.coeFn_toLp] at hh

/-- Finite higher moment of the smoothed high-chaos projection, derived from
its Gaussian square integrability and the actual hypercontractive bound. -/
theorem memLp_gaussian_average_higher_integrability {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (γFin n)) :
    MemLp (gaussianAverage τ f) (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (γFin n) :=
  lt_of_le_of_lt (memLp_gaussian_average_l2_to_lq τ hτ hτ1 f hf) hf

/-- Hypercontractivity of the actual Gaussian averaging integral for every
bounded measurable real function. This includes fractional-label differences;
no nonnegativity, smoothness, spectral or norm-bound conclusion is assumed. -/
theorem bounded_gaussian_average_l2_hypercontractive {n : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) :
    eLpNorm (gaussianAverage τ f) 2 (γFin n) ≤
      eLpNorm f (ENNReal.ofReal (1 + τ ^ 2)) (γFin n) := by
  exact memLp_gaussian_average_l2_hypercontractive τ hτ hτ1 f
    (MemLp.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hM))

end NegativeVotingHypercontractivity
