import GaussianMassCentroid

/-! Actual weighted Gaussian unions and their one-dimensional projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace NegativeVotingTwoCell
open NegativeVotingCapTail NegativeVotingMassCentroid
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def fractionalGaussian (u : E → ℝ) : Measure E :=
  (stdGaussian E).withDensity (fun x => ENNReal.ofReal (u x))

def projectedFractionalGaussian (u : E → ℝ) (v : E) : Measure ℝ :=
  (fractionalGaussian u).map (fun x => inner ℝ v x)

theorem fractionalGaussian_le (u : E → ℝ)
    (hu : ∀ᵐ x ∂stdGaussian E, u x ≤ 1) : fractionalGaussian u ≤ stdGaussian E := by
  calc
    fractionalGaussian u ≤ (stdGaussian E).withDensity 1 := by
      apply withDensity_mono
      filter_upwards [hu] with x hx
      simpa only [ENNReal.ofReal_one,Pi.one_apply] using ENNReal.ofReal_le_ofReal hx
    _ = stdGaussian E := withDensity_one

theorem fractionalGaussian_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → ℝ) (hu : AEMeasurable u (stdGaussian E))
    (h0 : ∀ᵐ x ∂stdGaussian E, 0 ≤ u x) (g : E → F) :
    ∫ x, g x ∂fractionalGaussian u = ∫ x, u x • g x ∂stdGaussian E := by
  rw [fractionalGaussian,integral_withDensity_eq_integral_toReal_smul₀ hu.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [h0] with x hx
  rw [ENNReal.toReal_ofReal hx]

theorem projectedFractionalGaussian_integral (u : E → ℝ)
    (hu : AEMeasurable u (stdGaussian E)) (h0 : ∀ᵐ x ∂stdGaussian E, 0 ≤ u x)
    (v : E) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ y, g y ∂projectedFractionalGaussian u v =
      ∫ x, u x*g (inner ℝ v x) ∂stdGaussian E := by
  rw [projectedFractionalGaussian,integral_map_of_stronglyMeasurable (by fun_prop) hg.stronglyMeasurable,
    fractionalGaussian_integral u hu h0]
  rfl

theorem projectedFractionalGaussian_total (u : E → ℝ)
    (hu : AEMeasurable u (stdGaussian E)) (h0 : ∀ᵐ x ∂stdGaussian E, 0 ≤ u x)
    (v : E) : (projectedFractionalGaussian u v).real univ=∫ x,u x ∂stdGaussian E := by
  simpa [integral_const,Measure.real] using
    projectedFractionalGaussian_integral u hu h0 v (fun _ => 1) measurable_const

theorem projectedFractionalGaussian_set (u : E → ℝ)
    (hu : AEMeasurable u (stdGaussian E)) (h0 : ∀ᵐ x ∂stdGaussian E, 0 ≤ u x)
    (v : E) (s : Set ℝ) (hs : MeasurableSet s) :
    (projectedFractionalGaussian u v).real s=
      ∫ x,u x*(s.indicator (fun _ => (1:ℝ))) (inner ℝ v x) ∂stdGaussian E := by
  have hh := projectedFractionalGaussian_integral u hu h0 v
    (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  simpa only [integral_indicator hs,integral_const,Measure.real,
    Measure.restrict_apply_univ,smul_eq_mul,mul_one] using hh

theorem gaussianReal_le_density_ceiling :
    gaussianReal 0 1 ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • volume := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  apply ENNReal.ofReal_le_ofReal
  simpa using gaussian_density_le_normalizer 0 1 x

theorem projectedFractionalGaussian_le_gaussian (u : E → ℝ) (v : E) (hv : ‖v‖=1)
    (h1 : ∀ᵐ x ∂stdGaussian E, u x ≤ 1) :
    projectedFractionalGaussian u v ≤ gaussianReal 0 1 := by
  have hh := Measure.map_mono (fractionalGaussian_le u h1) (by fun_prop : Measurable (fun x => inner ℝ v x))
  simpa only [projectedFractionalGaussian,gaussian_inner_map,hv,one_pow,Real.toNNReal_one] using hh

theorem projectedFractionalGaussian_density_bound (u : E → ℝ) (v : E) (hv : ‖v‖=1)
    (h1 : ∀ᵐ x ∂stdGaussian E, u x ≤ 1) :
    projectedFractionalGaussian u v ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • volume :=
  (projectedFractionalGaussian_le_gaussian u v hv h1).trans gaussianReal_le_density_ceiling

theorem projectedFractionalGaussian_finite (u : E → ℝ) (v : E) (hv : ‖v‖=1)
    (h1 : ∀ᵐ x ∂stdGaussian E, u x ≤ 1) : IsFiniteMeasure (projectedFractionalGaussian u v) :=
  isFiniteMeasure_of_le (gaussianReal 0 1) (projectedFractionalGaussian_le_gaussian u v hv h1)

theorem projectedFractionalGaussian_integrable_id (u : E → ℝ) (v : E) (hv : ‖v‖=1)
    (h1 : ∀ᵐ x ∂stdGaussian E, u x ≤ 1) :
    Integrable (fun y : ℝ => y) (projectedFractionalGaussian u v) :=
  (IsGaussian.integrable_id (μ:=gaussianReal 0 1)).mono_measure
    (projectedFractionalGaussian_le_gaussian u v hv h1)

end NegativeVotingTwoCell
