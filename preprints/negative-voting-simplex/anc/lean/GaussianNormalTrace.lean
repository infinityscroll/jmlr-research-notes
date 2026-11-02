import GaussianHypercontractivityBridge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory GaussianFin NegativeVotingHypercontractivity
open scoped ENNReal NNReal

namespace NegativeVotingNormalTrace

/-- Variance of the one-dimensional normal-coordinate OU kernel. -/
def normalVariance (τ : ℝ) : ℝ≥0 := ⟨max (1 - τ ^ 2) 0, le_max_right _ _⟩

/-- Genuine density ratio of N(tau*a,1-tau²) against the standard real Gaussian. -/
def normalKernel (τ a y : ℝ) : ℝ :=
  gaussianPDFReal (τ * a) (normalVariance τ) y / gaussianPDFReal 0 1 y

/-- A dimension-free kernel-row bound, sufficient for polynomial offset costs. -/
def normalRowBound (τ a : ℝ) : ℝ :=
  (Real.sqrt (1 - τ ^ 2))⁻¹ * Real.exp (a ^ 2 / 2)

theorem normalVariance_coe {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (normalVariance τ : ℝ) = 1 - τ ^ 2 := by
  exact max_eq_left (by linarith)

theorem normalVariance_pos {τ : ℝ} (hτ : τ ^ 2 < 1) :
    0 < normalVariance τ := by
  rw [← NNReal.coe_pos, normalVariance_coe hτ]
  linarith

theorem normalKernel_nonneg (τ a y : ℝ) : 0 ≤ normalKernel τ a y :=
  div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

theorem normalKernel_measurable (τ a : ℝ) : Measurable (normalKernel τ a) :=
  (measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)

/-- Exact exponential expression for the genuine density ratio. -/
theorem normalKernel_exp {τ : ℝ} (hτ : τ ^ 2 < 1) (a y : ℝ) :
    normalKernel τ a y = (Real.sqrt (1 - τ ^ 2))⁻¹ *
      Real.exp (-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) := by
  have hv : 0 < 1 - τ ^ 2 := by linarith
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 < Real.sqrt (1 - τ ^ 2) := Real.sqrt_pos.mpr hv
  simp only [normalKernel, gaussianPDFReal, normalVariance_coe hτ,
    NNReal.coe_one, mul_one, sub_zero]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Real.exp_add, show y ^ 2 / 2 = -(-y ^ 2 / 2) by ring, Real.exp_neg]
  field_simp

/-- Completing the square gives a bound uniform over the integrated coordinate. -/
theorem normalKernel_le_rowBound {τ : ℝ} (hτ : τ ^ 2 < 1) (a y : ℝ) :
    normalKernel τ a y ≤ normalRowBound τ a := by
  rw [normalKernel_exp hτ]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  have hv : 0 < 1 - τ ^ 2 := by linarith
  have hid : a ^ 2 / 2 - (-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) =
      (τ * y - a) ^ 2 / (2 * (1 - τ ^ 2)) := by
    field_simp
    ring
  have hnon : 0 ≤ (τ * y - a) ^ 2 / (2 * (1 - τ ^ 2)) := by positivity
  linarith

theorem normalRowBound_nonneg (τ a : ℝ) : 0 ≤ normalRowBound τ a := by
  unfold normalRowBound
  positivity

/-- The kernel row is square-integrable for every fixed normal coordinate. -/
theorem normalKernel_memLp {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    MemLp (normalKernel τ a) 2 (gaussianReal 0 1) := by
  refine MemLp.of_bound (normalKernel_measurable τ a).aestronglyMeasurable
    (normalRowBound τ a) ?_
  filter_upwards with y
  simpa [Real.norm_eq_abs, abs_of_nonneg (normalKernel_nonneg τ a y)] using
    normalKernel_le_rowBound hτ a y

/-- The kernel ratio really changes Gaussian measures, for the actual integral. -/
theorem integral_normalKernel {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) (f : ℝ → ℝ) :
    (∫ y, normalKernel τ a y * f y ∂gaussianReal 0 1) =
      ∫ y, f y ∂gaussianReal (τ * a) (normalVariance τ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (ne_of_gt (normalVariance_pos hτ))]
  apply integral_congr_ae
  filter_upwards with y
  have hp : gaussianPDFReal 0 1 y ≠ 0 := ne_of_gt (gaussianPDFReal_pos 0 1 y (by norm_num))
  simp only [smul_eq_mul, normalKernel]
  field_simp

/-- Exact probability normalization of each kernel row. -/
theorem integral_normalKernel_one {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (∫ y, normalKernel τ a y ∂gaussianReal 0 1) = 1 := by
  simpa using integral_normalKernel hτ a (fun _ => 1)

/-- The normal kernel row has an explicit dimension-independent L² bound. -/
theorem integral_normalKernel_sq_le {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (∫ y, (normalKernel τ a y) ^ 2 ∂gaussianReal 0 1) ≤ normalRowBound τ a := by
  have hk := normalKernel_memLp hτ a
  have hki : Integrable (normalKernel τ a) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (hk.mono_exponent (by norm_num))
  calc
    (∫ y, (normalKernel τ a y) ^ 2 ∂gaussianReal 0 1) ≤
        ∫ y, normalRowBound τ a * normalKernel τ a y ∂gaussianReal 0 1 := by
      apply integral_mono hk.integrable_sq (hki.const_mul _)
      intro y
      change normalKernel τ a y ^ 2 ≤ normalRowBound τ a * normalKernel τ a y
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (normalKernel_le_rowBound hτ a y)
        (normalKernel_nonneg τ a y)
    _ = normalRowBound τ a := by rw [integral_const_mul, integral_normalKernel_one hτ a, mul_one]

/-- Real L² pairing written as its actual integral, for arbitrary measures. -/
theorem l2_inner_toLp_eq_integral_mul {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [Real.inner_apply, hx, hy]

/-- Genuine Cauchy--Schwarz for the actual kernel pairing. -/
theorem integral_mul_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, (f x) ^ 2 ∂μ) * ∫ x, (g x) ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [l2_inner_toLp_eq_integral_mul hf hg,
    l2_inner_toLp_eq_integral_mul hf hf,
    l2_inner_toLp_eq_integral_mul hg hg] at h
  simpa only [pow_two] using h

/-- The L² seminorm is the square root of the squared integral. -/
theorem eLpNorm_two_eq_sqrt_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, (f x) ^ 2 ∂μ)) := by
  have h := hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    Real.sqrt_eq_rpow, one_div] using h

/-- Explicit L² row-norm estimate at every fixed normal coordinate. -/
theorem eLpNorm_normalKernel_le {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    eLpNorm (normalKernel τ a) 2 (gaussianReal 0 1) ≤
      ENNReal.ofReal (Real.sqrt (normalRowBound τ a)) := by
  rw [eLpNorm_two_eq_sqrt_integral_sq (normalKernel_memLp hτ a)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (integral_normalKernel_sq_le hτ a))

/-- Integrate only the normal coordinate, against the genuine OU row. -/
def normalSection {n : ℕ} (τ a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ y, normalKernel τ a y * f (x, y) ∂gaussianReal 0 1

/-- Fixed-normal-coordinate Gaussian integration maps genuine product-Gaussian
L² inputs to tangential L². No boundedness assumption is made on the input. -/
theorem normalSection_memLp_and_integral_sq_le {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    MemLp (normalSection τ a f) 2 (γFin n) ∧
    (∫ x, (normalSection τ a f x) ^ 2 ∂γFin n) ≤
      normalRowBound τ a * ∫ z, (f z) ^ 2 ∂(γFin n).prod (gaussianReal 0 1) := by
  have hk := normalKernel_memLp hτ a
  have hsm : AEStronglyMeasurable (normalSection τ a f) (γFin n) :=
    (((normalKernel_measurable τ a).comp measurable_snd).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).integral_prod_right'
  have hsec : ∀ᵐ x ∂γFin n, MemLp (fun y => f (x, y)) 2 (gaussianReal 0 1) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      hf.integrable_sq.prod_right_ae] with x hx hx2
    exact (memLp_two_iff_integrable_sq hx).mpr hx2
  have hbound : ∀ᵐ x ∂γFin n, (normalSection τ a f x) ^ 2 ≤
      normalRowBound τ a * ∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1 := by
    filter_upwards [hsec] with x hx
    exact (integral_mul_sq_le hk hx).trans
      (mul_le_mul_of_nonneg_right (integral_normalKernel_sq_le hτ a)
        (integral_nonneg (fun y => sq_nonneg _)))
  have hrhs := hf.integrable_sq.integral_prod_left.const_mul (normalRowBound τ a)
  have hsqint : Integrable (fun x => (normalSection τ a f x) ^ 2) (γFin n) := by
    refine Integrable.mono' hrhs (hsm.pow 2) ?_
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (normalSection τ a f x))] using hx
  refine ⟨(memLp_two_iff_integrable_sq hsm).mpr hsqint, ?_⟩
  calc
    (∫ x, (normalSection τ a f x) ^ 2 ∂γFin n) ≤
        ∫ x, normalRowBound τ a * ∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1 ∂γFin n :=
      integral_mono_ae hsqint hrhs hbound
    _ = normalRowBound τ a * ∫ z, (f z) ^ 2 ∂(γFin n).prod (gaussianReal 0 1) := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod (fun z => f z ^ 2) hf.integrable_sq).symm

/-- Dimension-independent fixed-normal L² trace bound. -/
theorem eLpNorm_normalSection_le {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (normalSection τ a f) 2 (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowBound τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  obtain ⟨hmem, hsq⟩ := normalSection_memLp_and_integral_sq_le hτ a f hf
  rw [eLpNorm_two_eq_sqrt_integral_sq hmem, eLpNorm_two_eq_sqrt_integral_sq hf,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.sqrt (∫ x, (normalSection τ a f x) ^ 2 ∂γFin n) ≤
        Real.sqrt (normalRowBound τ a * ∫ z, (f z) ^ 2 ∂(γFin n).prod (gaussianReal 0 1)) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_mul (normalRowBound_nonneg τ a) _

/-- Actual fixed-normal-coordinate smoothing, factored into one normal row
and genuine tangential Gaussian averaging. -/
def normalTrace {n : ℕ} (τ a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ) : (Fin n → ℝ) → ℝ :=
  gaussianAverage τ (normalSection τ a f)

/-- Tangential hypercontractivity turns the fixed-normal L² trace into L32,
uniformly in the number of tangential coordinates. -/
theorem normalTrace_l32_bound {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (normalTrace τ a f) 32 (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowBound τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hsq : τ ^ 2 < 1 := lt_of_le_of_lt hτ32 (by norm_num)
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  have hq : (32 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
    have hp : 0 < τ ^ 2 := sq_pos_of_pos hτ
    have hi : (31 : ℝ) ≤ 1 / τ ^ 2 := (le_div_iff₀ hp).mpr (by nlinarith)
    simpa only [one_div] using (show (32 : ℝ) ≤ 1 + 1 / τ ^ 2 by linarith)
  have hpq : (32 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (τ ^ 2)⁻¹) := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have hmem := (normalSection_memLp_and_integral_sq_le hsq a f hf).1
  exact (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
    ((memLp_gaussian_average_l2_to_lq τ hτ hτ1 _ hmem).trans
      (eLpNorm_normalSection_le hsq a f hf))

/-- The normal-coordinate affine Gaussian has exactly the required law. -/
theorem normalShift_map {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (gaussianReal 0 1).map (fun y => τ * a + Real.sqrt (1 - τ ^ 2) * y) =
      gaussianReal (τ * a) (normalVariance τ) := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  rw [show (fun y => τ * a + Real.sqrt (1 - τ ^ 2) * y) =
      (fun y => τ * a + y) ∘ (fun y => Real.sqrt (1 - τ ^ 2) * y) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp only [mul_zero, zero_add, mul_one]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mk, normalVariance_coe hτ, Real.sq_sqrt hv]

/-- The density-ratio normal row equals actual Gaussian noise averaging even
for completed-Gaussian-measurable input representatives. -/
theorem integral_normalKernel_eq_shift {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    (∫ y, normalKernel τ a y * f y ∂gaussianReal 0 1) =
      ∫ y, f (τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 := by
  have hac : gaussianReal (τ * a) (normalVariance τ) ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous _ (ne_of_gt (normalVariance_pos hτ))).trans
      (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0))
  have hm : AEStronglyMeasurable f
      ((gaussianReal 0 1).map (fun y => τ * a + Real.sqrt (1 - τ ^ 2) * y)) := by
    rw [normalShift_map hτ a]
    exact AEStronglyMeasurable.mono_ac hac hf
  rw [integral_normalKernel hτ a f, ← normalShift_map hτ a]
  exact integral_map (by fun_prop) hm

/-- The product-L² normal section is the actual affine Gaussian average
for almost every tangential coordinate. -/
theorem normalSection_eq_shift_ae {n : ℕ} {τ : ℝ} (hτ : τ ^ 2 < 1)
    (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    normalSection τ a f =ᵐ[γFin n]
      (fun x => ∫ y, f (x, τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1) := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left] with x hx
  exact integral_normalKernel_eq_shift hτ a (fun y => f (x, y)) hx

/-- The factored trace is the actual iterated Gaussian OU integral at the fixed
normal coordinate; the identity is proved for arbitrary product-L² inputs. -/
theorem normalTrace_eq_iterated_ae {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    normalTrace τ a f =ᵐ[γFin n] (fun x =>
      ∫ z, ∫ y, f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j),
        τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 ∂γFin n) := by
  have hsq : τ ^ 2 < 1 := by nlinarith
  exact gaussianAverage_congr_ae τ hτ hτ1 (normalSection_eq_shift_ae hsq a f hf)

/-- The actual Gaussian integral at a fixed normal coordinate has the L32
bound, with a constant independent of tangential dimension. -/
theorem actual_normalTrace_l32_bound {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (fun x => ∫ z, ∫ y,
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j),
        τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 ∂γFin n)
      32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowBound τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  rw [← eLpNorm_congr_ae (normalTrace_eq_iterated_ae hτ hτ1 a f hf)]
  exact normalTrace_l32_bound hτ hτ32 a f hf

/-- The Gaussian variance appearing after squaring one OU kernel row. -/
def normalSquareVariance (τ : ℝ) : ℝ≥0 :=
  normalVariance τ / (1 + ⟨τ ^ 2, sq_nonneg τ⟩)

/-- Sharp squared row norm; its offset exponent retains the factor tau². -/
def normalRowSquare (τ a : ℝ) : ℝ :=
  (Real.sqrt (1 - τ ^ 2))⁻¹ * (Real.sqrt (1 + τ ^ 2))⁻¹ *
    Real.exp (τ ^ 2 * a ^ 2 / (1 + τ ^ 2))

theorem normalSquareVariance_coe {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (normalSquareVariance τ : ℝ) = (1 - τ ^ 2) / (1 + τ ^ 2) := by
  change (normalVariance τ : ℝ) / (1 + τ ^ 2) = (1 - τ ^ 2) / (1 + τ ^ 2)
  rw [normalVariance_coe hτ]

theorem normalSquareVariance_pos {τ : ℝ} (hτ : τ ^ 2 < 1) :
    0 < normalSquareVariance τ := by
  rw [← NNReal.coe_pos, normalSquareVariance_coe hτ]
  exact div_pos (by linarith) (by positivity)

theorem normalRowSquare_nonneg (τ a : ℝ) : 0 ≤ normalRowSquare τ a := by
  unfold normalRowSquare
  positivity

/-- Exact completion of the square for the squared genuine OU density row. -/
theorem normalKernel_sq_density {τ : ℝ} (hτ : τ ^ 2 < 1) (a y : ℝ) :
    normalKernel τ a y ^ 2 * gaussianPDFReal 0 1 y =
      normalRowSquare τ a *
        gaussianPDFReal (2 * τ * a / (1 + τ ^ 2)) (normalSquareVariance τ) y := by
  have hv : 0 < 1 - τ ^ 2 := by linarith
  have hw : 0 < 1 + τ ^ 2 := by positivity
  have hs : Real.sqrt (1 - τ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have ht : Real.sqrt (1 + τ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  have hc : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsnew : Real.sqrt (2 * Real.pi * ((1 - τ ^ 2) / (1 + τ ^ 2))) =
      Real.sqrt (2 * Real.pi) * (Real.sqrt (1 - τ ^ 2) / Real.sqrt (1 + τ ^ 2)) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), Real.sqrt_div hv.le]
  have hexp :
      (-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) +
      (-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) + (-y ^ 2 / 2) =
      τ ^ 2 * a ^ 2 / (1 + τ ^ 2) +
        (-(y - 2 * τ * a / (1 + τ ^ 2)) ^ 2 / (2 * ((1 - τ ^ 2) / (1 + τ ^ 2)))) := by
    field_simp
    ring
  rw [normalKernel_exp hτ]
  simp only [gaussianPDFReal, normalSquareVariance_coe hτ, NNReal.coe_one, mul_one, sub_zero,
    normalRowSquare, hsnew]
  calc
    _ = (Real.sqrt (1 - τ ^ 2))⁻¹ ^ 2 * (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp ((-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) +
          (-(y - τ * a) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2) + (-y ^ 2 / 2)) := by
      conv_rhs => rw [Real.exp_add, Real.exp_add]
      ring
    _ = _ := by
      rw [hexp, Real.exp_add]
      field_simp

/-- Exact, dimension-independent one-normal-coordinate Gaussian row L² norm. -/
theorem integral_normalKernel_sq_eq {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (∫ y, normalKernel τ a y ^ 2 ∂gaussianReal 0 1) = normalRowSquare τ a := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    (∫ y, gaussianPDFReal 0 1 y * normalKernel τ a y ^ 2) =
        ∫ y, normalRowSquare τ a *
          gaussianPDFReal (2 * τ * a / (1 + τ ^ 2)) (normalSquareVariance τ) y := by
      apply integral_congr_ae
      filter_upwards with y
      simpa only [mul_comm] using normalKernel_sq_density hτ a y
    _ = normalRowSquare τ a := by
      rw [integral_const_mul,
        integral_gaussianPDFReal_eq_one _ (ne_of_gt (normalSquareVariance_pos hτ)), mul_one]

/-- Exact Gaussian row L² seminorm, with the correct small-tau offset scaling. -/
theorem eLpNorm_normalKernel_eq {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    eLpNorm (normalKernel τ a) 2 (gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) := by
  rw [eLpNorm_two_eq_sqrt_integral_sq (normalKernel_memLp hτ a),
    integral_normalKernel_sq_eq hτ a]

/-- The sharp normal-row constant controls the product-L² trace energy. -/
theorem normalSection_integral_sq_le_sharp {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    (∫ x, (normalSection τ a f x) ^ 2 ∂γFin n) ≤
      normalRowSquare τ a * ∫ z, (f z) ^ 2 ∂(γFin n).prod (gaussianReal 0 1) := by
  have hmem := (normalSection_memLp_and_integral_sq_le hτ a f hf).1
  have hsec : ∀ᵐ x ∂γFin n, MemLp (fun y => f (x, y)) 2 (gaussianReal 0 1) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      hf.integrable_sq.prod_right_ae] with x hx hx2
    exact (memLp_two_iff_integrable_sq hx).mpr hx2
  have hbound : ∀ᵐ x ∂γFin n, (normalSection τ a f x) ^ 2 ≤
      normalRowSquare τ a * ∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1 := by
    filter_upwards [hsec] with x hx
    simpa only [normalSection, integral_normalKernel_sq_eq hτ a] using
      integral_mul_sq_le (normalKernel_memLp hτ a) hx
  calc
    _ ≤ ∫ x, normalRowSquare τ a * ∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1 ∂γFin n :=
      integral_mono_ae hmem.integrable_sq
        (hf.integrable_sq.integral_prod_left.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod (fun z => f z ^ 2) hf.integrable_sq).symm

/-- Sharp dimension-independent fixed-normal L² trace bound. -/
theorem eLpNorm_normalSection_le_sharp {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (normalSection τ a f) 2 (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hmem := (normalSection_memLp_and_integral_sq_le hτ a f hf).1
  rw [eLpNorm_two_eq_sqrt_integral_sq hmem, eLpNorm_two_eq_sqrt_integral_sq hf,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.sqrt_le_sqrt (normalSection_integral_sq_le_sharp hτ a f hf)).trans_eq
    (Real.sqrt_mul (normalRowSquare_nonneg τ a) _)

/-- Sharp fixed-normal L32 bound, retaining exp(O(tau²*a²)) offset growth. -/
theorem normalTrace_l32_bound_sharp {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (normalTrace τ a f) 32 (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hsq : τ ^ 2 < 1 := lt_of_le_of_lt hτ32 (by norm_num)
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  have hq : (32 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
    have hp : 0 < τ ^ 2 := sq_pos_of_pos hτ
    have hi : (31 : ℝ) ≤ 1 / τ ^ 2 := (le_div_iff₀ hp).mpr (by nlinarith)
    simpa only [one_div] using (show (32 : ℝ) ≤ 1 + 1 / τ ^ 2 by linarith)
  have hpq : (32 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (τ ^ 2)⁻¹) := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have hmem := (normalSection_memLp_and_integral_sq_le hsq a f hf).1
  exact (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
    ((memLp_gaussian_average_l2_to_lq τ hτ hτ1 _ hmem).trans
      (eLpNorm_normalSection_le_sharp hsq a f hf))

/-- Actual Gaussian integral version of the sharp fixed-normal trace estimate. -/
theorem actual_normalTrace_l32_bound_sharp {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (fun x => ∫ z, ∫ y,
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j),
        τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 ∂γFin n)
      32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  rw [← eLpNorm_congr_ae (normalTrace_eq_iterated_ae hτ hτ1 a f hf)]
  exact normalTrace_l32_bound_sharp hτ hτ32 a f hf

/-- Exact measure-level normal-kernel change of density. -/
theorem normalKernel_withDensity {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (normalKernel τ a y)) =
      gaussianReal (τ * a) (normalVariance τ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← withDensity_mul volume (measurable_gaussianPDF 0 1)
      ((normalKernel_measurable τ a).ennreal_ofReal),
    gaussianReal_of_var_ne_zero _ (ne_of_gt (normalVariance_pos hτ))]
  apply withDensity_congr_ae
  filter_upwards with y
  change ENNReal.ofReal (gaussianPDFReal 0 1 y) * ENNReal.ofReal (normalKernel τ a y) =
    ENNReal.ofReal (gaussianPDFReal (τ * a) (normalVariance τ) y)
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 y)]
  congr 1
  have hp : gaussianPDFReal 0 1 y ≠ 0 := ne_of_gt (gaussianPDFReal_pos 0 1 y (by norm_num))
  unfold normalKernel
  field_simp

/-- Product-L² inputs remain integrable when the normal coordinate is shifted
and contracted. This discharges the Fubini integrability obligation. -/
theorem integrable_shifted_normal_product {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    Integrable f ((γFin n).prod (gaussianReal (τ * a) (normalVariance τ))) := by
  rw [← normalKernel_withDensity hτ a,
    prod_withDensity_right ((normalKernel_measurable τ a).ennreal_ofReal)]
  rw [integrable_withDensity_iff_integrable_smul'
    (f := fun z : (Fin n → ℝ) × ℝ => ENNReal.ofReal (normalKernel τ a z.2))
    (by exact ((normalKernel_measurable τ a).ennreal_ofReal).comp measurable_snd)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (normalKernel_nonneg τ a _), smul_eq_mul]
  have hfi : Integrable f ((γFin n).prod (gaussianReal 0 1)) :=
    memLp_one_iff_integrable.mp (hf.mono_exponent (by norm_num))
  refine hfi.bdd_mul (c := normalRowBound τ a)
    (((normalKernel_measurable τ a).comp measurable_snd).aestronglyMeasurable) ?_
  filter_upwards with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg (normalKernel_nonneg τ a p.2)] using
    normalKernel_le_rowBound hτ a p.2

/-- Integrability of the actual normal/tangential Gaussian product kernel for
almost every tangential base point, proved from the original product-L² input. -/
theorem actual_normal_kernel_integrable_ae {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, Integrable (fun z : (Fin n → ℝ) × ℝ =>
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
        τ * a + Real.sqrt (1 - τ ^ 2) * z.2))
      ((γFin n).prod (gaussianReal 0 1)) := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  have hshift : MeasurePreserving (fun y => τ * a + Real.sqrt (1 - τ ^ 2) * y)
      (gaussianReal 0 1) (gaussianReal (τ * a) (normalVariance τ)) :=
    ⟨by fun_prop, normalShift_map hτ a⟩
  have hmap := (hmix.prod hshift).comp
    (measurePreserving_prodAssoc (γFin n) (γFin n) (gaussianReal 0 1)).symm
  have hi := hmap.integrable_comp_of_integrable
    (integrable_shifted_normal_product hτ a f hf)
  have hsec := hi.prod_right_ae
  change ∀ᵐ x ∂γFin n, Integrable (fun z : (Fin n → ℝ) × ℝ =>
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
        τ * a + Real.sqrt (1 - τ ^ 2) * z.2))
      ((γFin n).prod (gaussianReal 0 1)) at hsec
  exact hsec

/-- Exact identification with the actual Gaussian product integral, with the
Fubini obligation discharged for every product-L² input. -/
theorem normalTrace_eq_product_ae {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    normalTrace τ a f =ᵐ[γFin n] (fun x =>
      ∫ z : (Fin n → ℝ) × ℝ,
        f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
          τ * a + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)) := by
  have hsq : τ ^ 2 < 1 := by nlinarith
  filter_upwards [normalTrace_eq_iterated_ae hτ hτ1 a f hf,
    actual_normal_kernel_integrable_ae hsq a f hf] with x hx hxi
  rw [hx]
  exact (integral_prod _ hxi).symm

/-- Sharp L32 trace bound for the actual product-Gaussian OU integral at a fixed
normal coordinate. All constants are independent of tangential dimension. -/
theorem actual_product_normalTrace_l32_bound_sharp {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    eLpNorm (fun x => ∫ z : (Fin n → ℝ) × ℝ,
      f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
        τ * a + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1))
      32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  rw [← eLpNorm_congr_ae (normalTrace_eq_product_ae hτ hτ1 a f hf)]
  exact normalTrace_l32_bound_sharp hτ hτ32 a f hf

end NegativeVotingNormalTrace
