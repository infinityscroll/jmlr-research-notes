import GaussianSmallCap
import NegativeVoting.NoiseStability

/-!
# Actual far-normal cap tails and Gaussian strips

The tail estimate uses an actual L32 moment with no amplitude threshold.
The strip estimate is proved for the actual standard Gaussian measure and
uses the Euclidean norm of the linear coefficient vector.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators

namespace NegativeVotingCapTail
open NegativeVotingSmallCap

/-- Beyond one normal unit, a positive switching reward requires the forcing
to exceed the switching slope. The polynomial bound retains exact scaling. -/
theorem far_reward_pointwise (u z θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 < ell)
    (hz : 1 ≤ z) :
    fibreReward (θ * u) ell z ≤ (θ ^ 32 / ell ^ 31) * |u| ^ 32 := by
  have ht : 0 ≤ θ * |u| := mul_nonneg hθ (abs_nonneg u)
  have hcost : ell ≤ ell * z := by nlinarith
  have hu : θ * u ≤ θ * |u| := mul_le_mul_of_nonneg_left (le_abs_self u) hθ
  by_cases hc : θ * |u| ≤ ell
  · have hr : fibreReward (θ * u) ell z = 0 := by
      apply max_eq_right
      linarith
    rw [hr]
    positivity
  · have he : ell ≤ θ * |u| := (lt_of_not_ge hc).le
    have hp := pow_le_pow_left₀ hell.le he 31
    have hprod := mul_le_mul_of_nonneg_left hp ht
    have hmajor : θ * |u| ≤ (θ * |u|) ^ 32 / ell ^ 31 := by
      apply (le_div_iff₀ (pow_pos hell 31)).mpr
      calc
        _ ≤ (θ * |u|) * (θ * |u|) ^ 31 := hprod
        _ = _ := by ring
    calc
      _ ≤ θ * |u| := max_le (by linarith) ht
      _ ≤ (θ * |u|) ^ 32 / ell ^ 31 := hmajor
      _ = _ := by rw [mul_pow]; ring

/-- The far-normal cap is bounded by the actual 32nd moment, without a small-
amplitude premise. The statement applies to any measure and measurable
normal coordinate, so it applies directly to the ambient Gaussian. -/
theorem far_normal_cap_from_L32 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u z : X → ℝ) (θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 < ell)
    (hu : MemLp u 32 μ) (hz : Measurable z) :
    (∫ x in {x | 1 ≤ z x}, fibreReward (θ * u x) ell (z x) ∂μ) ≤
      (θ ^ 32 / ell ^ 31) * ∫ x, |u x| ^ 32 ∂μ := by
  let C : ℝ := θ ^ 32 / ell ^ 31
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : MeasurableSet {x | 1 ≤ z x} := measurableSet_le measurable_const hz
  have hip : Integrable (fun x => |u x| ^ 32) μ := by
    simpa only [Real.norm_eq_abs] using hu.integrable_norm_pow (by norm_num : (32 : ℕ) ≠ 0)
  have hmeas : AEStronglyMeasurable (fun x => fibreReward (θ * u x) ell (z x)) μ := by
    unfold fibreReward
    exact ((hu.aestronglyMeasurable.const_mul θ).sub
      (hz.aestronglyMeasurable.const_mul ell)).sup aestronglyMeasurable_const
  have hbound : ∀ x ∈ {x | 1 ≤ z x}, fibreReward (θ * u x) ell (z x) ≤ C * |u x| ^ 32 := by
    intro x hx
    exact far_reward_pointwise (u x) (z x) θ ell hθ hell hx
  have hi : IntegrableOn (fun x => fibreReward (θ * u x) ell (z x)) {x | 1 ≤ z x} μ := by
    apply (hip.const_mul C).integrableOn.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem hs] with x hx
    change ‖fibreReward (θ * u x) ell (z x)‖ ≤ C * |u x| ^ 32
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hbound x hx
  have hmono := setIntegral_mono_on hi (hip.const_mul C).integrableOn hs hbound
  have htotal : (∫ x in {x | 1 ≤ z x}, C * |u x| ^ 32 ∂μ) ≤
      ∫ x, C * |u x| ^ 32 ∂μ :=
    setIntegral_le_integral (hip.const_mul C)
      (Filter.Eventually.of_forall fun x => mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
  exact hmono.trans (by simpa only [integral_const_mul, C] using htotal)

/-- Concrete finite-product Gaussian specialization with the actual affine
normal coordinate. The moment is over the full Gaussian space. -/
theorem gaussian_far_normal_cap {κ : Type*} [Fintype κ]
    (u : (κ → ℝ) → ℝ) (normal : κ → ℝ) (offset θ ell : ℝ)
    (hθ : 0 ≤ θ) (hell : 0 < ell) (hu : MemLp u 32 (NegativeVoting.standardGaussian κ)) :
    (∫ x in {x | 1 ≤ (∑ k, normal k * x k) - offset},
      fibreReward (θ * u x) ell ((∑ k, normal k * x k) - offset)
        ∂NegativeVoting.standardGaussian κ) ≤
      (θ ^ 32 / ell ^ 31) * ∫ x, |u x| ^ 32 ∂NegativeVoting.standardGaussian κ := by
  apply far_normal_cap_from_L32 _ _ _ θ ell hθ hell hu
  fun_prop

/-- A scalar Gaussian density never exceeds its normalization factor. -/
theorem gaussian_density_le_normalizer (mean : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal mean v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  have he : Real.exp (-(x - mean) ^ 2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹)

/-- The actual probability of a scalar Gaussian interval is bounded by its
width times the maximum density. -/
theorem gaussianReal_interval_probability (mean : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (a w : ℝ) (hw : 0 ≤ w) :
    (gaussianReal mean v (Icc a (a + w))).toReal ≤ w / Real.sqrt (2 * Real.pi * v) := by
  have hi : IntegrableOn (gaussianPDFReal mean v) (Icc a (a + w)) volume :=
    (integrable_gaussianPDFReal mean v).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹) (Icc a (a + w)) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  have hmono := setIntegral_mono_on hi hc measurableSet_Icc
    (fun x _ => gaussian_density_le_normalizer mean v x)
  rw [gaussianReal_apply_eq_integral mean hv, ENNReal.toReal_ofReal
    (integral_nonneg fun x => gaussianPDFReal_nonneg mean v x)]
  calc
    _ ≤ ∫ x in Icc a (a + w), (Real.sqrt (2 * Real.pi * v))⁻¹ := hmono
    _ = _ := by
      simp only [setIntegral_const, smul_eq_mul]
      simp [hw, div_eq_mul_inv]

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual law of a Gaussian linear functional; its variance is the
squared Euclidean norm, derived from the standard Gaussian covariance. -/
theorem gaussian_inner_map (d : E) :
    (stdGaussian E).map (fun x => inner ℝ d x) = gaussianReal 0 ((‖d‖ ^ 2).toNNReal) := by
  have hh := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ d)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at hh
  exact hh

/-- Actual Gaussian slab probability with its dimension-free sharp density
constant. In particular it applies to the tangent space of a pairwise facet. -/
theorem gaussian_slab_probability (d : E) (hd : d ≠ 0) (a w : ℝ) (hw : 0 ≤ w) :
    (stdGaussian E {x | a ≤ inner ℝ d x ∧ inner ℝ d x ≤ a + w}).toReal ≤
      w / (Real.sqrt (2 * Real.pi) * ‖d‖) := by
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hv : (‖d‖ ^ 2).toNNReal ≠ 0 := by positivity
  have heq : stdGaussian E {x | a ≤ inner ℝ d x ∧ inner ℝ d x ≤ a + w} =
      gaussianReal 0 ((‖d‖ ^ 2).toNNReal) (Icc a (a + w)) := by
    rw [← gaussian_inner_map d, Measure.map_apply (by fun_prop) measurableSet_Icc]
    rfl
  rw [heq]
  have hh := gaussianReal_interval_probability 0 ((‖d‖ ^ 2).toNNReal) hv a w hw
  have hs : Real.sqrt (2 * Real.pi * (↑((‖d‖ ^ 2).toNNReal) : ℝ)) =
      Real.sqrt (2 * Real.pi) * ‖d‖ := by
    rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rw [hs] at hh
  exact hh

end StandardGaussian


section TripleGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard squared singular-value lower bound on the centered label
subspace. This is an operator bound, not a switching-cap hypothesis. -/
def CenteredSingularLowerBound (rows : ι → E) (σ : ℝ) : Prop :=
  ∀ c : ι → ℝ, (∑ q, c q) = 0 →
    σ ^ 2 * (∑ q, c q ^ 2) ≤ ‖∑ q, c q • rows q‖ ^ 2

/-- Every subtraction of the i-j normal from the k-versus-midpoint vector
retains length at least sqrt(3/2) times the centered singular lower bound. -/
theorem triple_difference_lower_bound (rows : ι → E) (σ : ℝ) (hσ : 0 ≤ σ)
    (hlower : CenteredSingularLowerBound rows σ)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    σ * Real.sqrt (3 / 2) ≤
      ‖rows k - (1 / 2 : ℝ) • (rows i + rows j) - t • (rows i - rows j)‖ := by
  let c : ι → ℝ := fun q => (if q = k then 1 else 0) -
    (if q = i then (1 / 2 + t) else 0) - (if q = j then (1 / 2 - t) else 0)
  have hc : (∑ q, c q) = 0 := by
    simp [c, Finset.sum_sub_distrib]
    ring
  have hsquare (q : ι) : c q ^ 2 =
      (if q = k then (1 : ℝ) else 0) + (if q = i then (1 / 2 + t) ^ 2 else 0) +
        (if q = j then (1 / 2 - t) ^ 2 else 0) := by
    by_cases hqk : q = k
    · subst q
      simp [c, hik.symm, hjk.symm]
    · by_cases hqi : q = i
      · subst q
        simp [c, hik, hij]
        ring
      · by_cases hqj : q = j
        · subst q
          simp [c, hjk, hij.symm]
          ring
        · simp [c, hqk, hqi, hqj]
  have hn : (∑ q, c q ^ 2) = (3 / 2 : ℝ) + 2 * t ^ 2 := by
    simp_rw [hsquare]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hv : (∑ q, c q • rows q) =
      rows k - (1 / 2 : ℝ) • (rows i + rows j) - t • (rows i - rows j) := by
    simp only [c, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, one_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [add_smul, smul_add, smul_sub]
    abel
  have hh := hlower c hc
  rw [hn, hv] at hh
  have hsmall : σ ^ 2 * (3 / 2 : ℝ) ≤ σ ^ 2 * ((3 / 2 : ℝ) + 2 * t ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t]) (sq_nonneg σ)
  have heq : (σ * Real.sqrt (3 / 2)) ^ 2 = σ ^ 2 * (3 / 2 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hsq := hsmall.trans hh
  rw [← heq] at hsq
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

/-- Orthogonal projection of the third-label comparison vector onto the
pairwise tangent plane, written with its actual projection coefficient. -/
def tripleTangentVector (a b c : E) : E :=
  (c - (1 / 2 : ℝ) • (a + b)) -
    (inner ℝ (a - b) (c - (1 / 2 : ℝ) • (a + b)) / ‖a - b‖ ^ 2) • (a - b)

theorem tripleTangentVector_orthogonal (a b c : E) :
    inner ℝ (a - b) (tripleTangentVector a b c) = 0 := by
  by_cases hab : a - b = 0
  · simp [hab]
  · unfold tripleTangentVector
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hab)]
    ring

theorem tripleTangentVector_comparison (a b c h : E) (hh : inner ℝ (a - b) h = 0) :
    inner ℝ (tripleTangentVector a b c) h = inner ℝ (c - a) h := by
  have heq : inner ℝ a h = inner ℝ b h := by
    rw [inner_sub_left] at hh
    exact sub_eq_zero.mp hh
  unfold tripleTangentVector
  simp only [inner_sub_left, real_inner_smul_left, inner_add_left, heq, sub_self, mul_zero]
  ring

/-- The audited sqrt(3/2) lower bound holds for the actual tangent projection. -/
theorem triple_tangent_slope_lower_bound (rows : ι → E) (σ : ℝ) (hσ : 0 ≤ σ)
    (hlower : CenteredSingularLowerBound rows σ)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    σ * Real.sqrt (3 / 2) ≤ ‖tripleTangentVector (rows i) (rows j) (rows k)‖ :=
  triple_difference_lower_bound rows σ hσ hlower i j k hij hik hjk _

end TripleGeometry


section TangentStrip
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual third-label strip probability on the pairwise tangent Gaussian
space. The slope bound is derived from the centered singular bound and the
three distinct labels; it is not supplied as an anti-concentration premise. -/
theorem third_label_tangent_strip_probability (rows : ι → E) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a w : ℝ) (hw : 0 ≤ w) :
    (stdGaussian ((ℝ ∙ (rows i - rows j))ᗮ)
      {x | a ≤ inner ℝ (rows k - rows i) (x : E) ∧
        inner ℝ (rows k - rows i) (x : E) ≤ a + w}).toReal ≤
      w / (Real.sqrt (2 * Real.pi) * σ * Real.sqrt (3 / 2)) := by
  let T := (ℝ ∙ (rows i - rows j))ᗮ
  have hdmem : tripleTangentVector (rows i) (rows j) (rows k) ∈ T := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm]
    exact tripleTangentVector_orthogonal _ _ _
  let d : T := ⟨tripleTangentVector (rows i) (rows j) (rows k), hdmem⟩
  have hslope : σ * Real.sqrt (3 / 2) ≤ ‖d‖ :=
    triple_tangent_slope_lower_bound rows σ hσ.le hlower i j k hij hik hjk
  have hpositive : 0 < σ * Real.sqrt (3 / 2) := mul_pos hσ (by positivity)
  have hd : d ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hslope
    linarith
  have hscore (x : T) : inner ℝ d x = inner ℝ (rows k - rows i) (x : E) := by
    change inner ℝ (tripleTangentVector (rows i) (rows j) (rows k)) (x : E) = _
    apply tripleTangentVector_comparison
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.property
  have hprob := gaussian_slab_probability d hd a w hw
  have hfirst : (stdGaussian T
      {x | a ≤ inner ℝ (rows k - rows i) (x : E) ∧
        inner ℝ (rows k - rows i) (x : E) ≤ a + w}).toReal ≤
      w / (Real.sqrt (2 * Real.pi) * ‖d‖) := by
    simpa only [hscore] using hprob
  have hden := mul_le_mul_of_nonneg_left hslope (Real.sqrt_nonneg (2 * Real.pi))
  calc
    _ ≤ w / (Real.sqrt (2 * Real.pi) * ‖d‖) := hfirst
    _ ≤ w / (Real.sqrt (2 * Real.pi) * (σ * Real.sqrt (3 / 2))) :=
      div_le_div_of_nonneg_left hw (by positivity) hden
    _ = _ := by ring

end TangentStrip
end NegativeVotingCapTail
