import GaussianNormalTrace
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory GaussianFin NegativeVotingHypercontractivity
open NegativeVotingNormalTrace
open scoped ENNReal NNReal

namespace NegativeVotingNormalDerivatives

/-- Actual first normal derivative of the Gaussian density-ratio row. -/
def normalKernelDerivative (τ a y : ℝ) : ℝ :=
  (τ * (y - τ * a) / (1 - τ ^ 2)) * normalKernel τ a y

/-- Actual second normal derivative of the Gaussian density-ratio row. -/
def normalKernelSecondDerivative (τ a y : ℝ) : ℝ :=
  ((τ * (y - τ * a) / (1 - τ ^ 2)) ^ 2 - τ ^ 2 / (1 - τ ^ 2)) *
    normalKernel τ a y

/-- Exact squared L² norm of the first normal derivative row. -/
def normalDerivativeRowSquare (τ a : ℝ) : ℝ :=
  normalRowSquare τ a *
    (τ ^ 2 / (1 - τ ^ 4) + τ ^ 4 * a ^ 2 / (1 + τ ^ 2) ^ 2)

/-- The displayed first derivative is proved by differentiating the actual
Gaussian density ratio, rather than introduced as an analytic hypothesis. -/
theorem hasDerivAt_normalKernel {τ : ℝ} (hτ : τ ^ 2 < 1) (a y : ℝ) :
    HasDerivAt (fun b => normalKernel τ b y) (normalKernelDerivative τ a y) a := by
  have hg : HasDerivAt
      (fun b : ℝ => -(y - τ * b) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2)
      (τ * (y - τ * a) / (1 - τ ^ 2)) a := by
    convert (((((hasDerivAt_id a).const_mul τ).const_sub y).pow 2).neg.div_const
      (2 * (1 - τ ^ 2))).add_const (y ^ 2 / 2) using 1
    · ext b
      dsimp
    · dsimp
      field_simp
  have hk := hg.exp.const_mul (Real.sqrt (1 - τ ^ 2))⁻¹
  have heq : (fun b => normalKernel τ b y) =
      (fun b => (Real.sqrt (1 - τ ^ 2))⁻¹ *
        Real.exp (-(y - τ * b) ^ 2 / (2 * (1 - τ ^ 2)) + y ^ 2 / 2)) :=
    funext (fun b => normalKernel_exp hτ b y)
  rw [heq]
  convert hk using 1
  unfold normalKernelDerivative
  rw [normalKernel_exp hτ]
  ring

/-- The second normal derivative is also an actual pointwise derivative. -/
theorem hasDerivAt_normalKernelDerivative {τ : ℝ} (hτ : τ ^ 2 < 1) (a y : ℝ) :
    HasDerivAt (fun b => normalKernelDerivative τ b y)
      (normalKernelSecondDerivative τ a y) a := by
  have hg : HasDerivAt (fun b : ℝ => τ * (y - τ * b) / (1 - τ ^ 2))
      (-τ ^ 2 / (1 - τ ^ 2)) a := by
    convert ((((hasDerivAt_id a).const_mul τ).const_sub y).const_mul τ).div_const
      (1 - τ ^ 2) using 1
    · ext b
      dsimp
    · ring
  convert hg.mul (hasDerivAt_normalKernel hτ a y) using 1
  · ext b
    rfl
  · unfold normalKernelSecondDerivative normalKernelDerivative
    ring

theorem normalKernelDerivative_measurable (τ a : ℝ) :
    Measurable (normalKernelDerivative τ a) := by
  unfold normalKernelDerivative
  exact ((measurable_const.mul (measurable_id.sub measurable_const)).div_const _).mul
    (normalKernel_measurable τ a)

/-- Normal derivative rows are square-integrable; this holds without any
boundedness premise on a function later paired against them. -/
theorem normalKernelDerivative_memLp {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    MemLp (normalKernelDerivative τ a) 2 (gaussianReal 0 1) := by
  have hd : MemLp (fun y : ℝ => τ * (y - τ * a) / (1 - τ ^ 2)) 2
      (gaussianReal 0 1) := by
    convert ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).sub
      (memLp_const (τ * a))).const_mul (τ / (1 - τ ^ 2)) using 1
    · funext y
      dsimp
      ring
    · norm_num
  apply (hd.norm.const_mul (normalRowBound τ a)).mono'
    (normalKernelDerivative_measurable τ a).aestronglyMeasurable
  filter_upwards with y
  rw [normalKernelDerivative, norm_mul]
  have hk : ‖normalKernel τ a y‖ ≤ normalRowBound τ a := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (normalKernel_nonneg τ a y)] using
      normalKernel_le_rowBound hτ a y
  exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- An arbitrary-center Gaussian second moment, including degenerate variance. -/
theorem gaussian_integral_sub_sq (μ : ℝ) (v : ℝ≥0) (b : ℝ) :
    (∫ y : ℝ, (y - b) ^ 2 ∂gaussianReal μ v) = v + (μ - b) ^ 2 := by
  have hi : MemLp (fun y : ℝ => y - b) 2 (gaussianReal μ v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const b)
  have hv := variance_eq_sub hi
  rw [variance_sub_const (X := fun y : ℝ => y) measurable_id.aestronglyMeasurable,
    variance_fun_id_gaussianReal] at hv
  have hm : (∫ y : ℝ, y - b ∂gaussianReal μ v) = μ - b := by
    have hid : Integrable (fun y : ℝ => y) (gaussianReal μ v) :=
      (memLp_id_gaussianReal 2).integrable (by norm_num)
    rw [integral_sub hid (integrable_const b)]
    simp
  rw [hm] at hv
  change (v : ℝ) = (∫ y : ℝ, (y - b) ^ 2 ∂gaussianReal μ v) - (μ - b) ^ 2 at hv
  linarith

/-- Exact change-of-measure formula for a squared Gaussian kernel row. -/
theorem integral_normalKernel_sq_mul {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ)
    (g : ℝ → ℝ) :
    (∫ y, normalKernel τ a y ^ 2 * g y ∂gaussianReal 0 1) =
      normalRowSquare τ a * ∫ y, g y
        ∂gaussianReal (2 * τ * a / (1 + τ ^ 2)) (normalSquareVariance τ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (ne_of_gt (normalSquareVariance_pos hτ)),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  calc
    gaussianPDFReal 0 1 y * (normalKernel τ a y ^ 2 * g y) =
        (normalKernel τ a y ^ 2 * gaussianPDFReal 0 1 y) * g y := by ring
    _ = (normalRowSquare τ a *
        gaussianPDFReal (2 * τ * a / (1 + τ ^ 2)) (normalSquareVariance τ) y) * g y :=
      by rw [normalKernel_sq_density hτ]
    _ = _ := by ring

/-- Exact Gaussian L² norm of the actual first normal derivative row. -/
theorem integral_normalKernelDerivative_sq {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    (∫ y, normalKernelDerivative τ a y ^ 2 ∂gaussianReal 0 1) =
      normalDerivativeRowSquare τ a := by
  have hv : 1 - τ ^ 2 ≠ 0 := by linarith
  have hw : 1 + τ ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + τ ^ 2)
  have h4 : 1 - τ ^ 4 ≠ 0 := by
    rw [show 1 - τ ^ 4 = (1 - τ ^ 2) * (1 + τ ^ 2) by ring]
    exact mul_ne_zero hv hw
  calc
    (∫ y, normalKernelDerivative τ a y ^ 2 ∂gaussianReal 0 1) =
        ∫ y, normalKernel τ a y ^ 2 *
          ((τ / (1 - τ ^ 2)) ^ 2 * (y - τ * a) ^ 2) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards with y
      unfold normalKernelDerivative
      ring
    _ = normalRowSquare τ a *
        ((τ / (1 - τ ^ 2)) ^ 2 *
          ((normalSquareVariance τ : ℝ) +
            (2 * τ * a / (1 + τ ^ 2) - τ * a) ^ 2)) := by
      rw [integral_normalKernel_sq_mul hτ, integral_const_mul, gaussian_integral_sub_sq]
    _ = normalDerivativeRowSquare τ a := by
      rw [normalSquareVariance_coe hτ]
      unfold normalDerivativeRowSquare
      congr 1
      field_simp
      ring

theorem normalDerivativeRowSquare_nonneg {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    0 ≤ normalDerivativeRowSquare τ a := by
  rw [← integral_normalKernelDerivative_sq hτ]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem eLpNorm_normalKernelDerivative_eq {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ) :
    eLpNorm (normalKernelDerivative τ a) 2 (gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt (normalDerivativeRowSquare τ a)) := by
  rw [eLpNorm_two_eq_sqrt_integral_sq (normalKernelDerivative_memLp hτ a),
    integral_normalKernelDerivative_sq hτ a]

/-- An explicit local polynomial envelope for normal derivatives. -/
def normalDerivativeEnvelope (τ A y : ℝ) : ℝ :=
  (|τ| / (1 - τ ^ 2)) * (|y| + |τ| * A) * normalRowBound τ A

theorem normalRowBound_mono_abs {τ a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) :
    normalRowBound τ a ≤ normalRowBound τ A := by
  unfold normalRowBound
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  have hsq : a ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hA).mpr ha
  linarith

/-- The envelope holds simultaneously at all normal parameters in the interval. -/
theorem normalKernelDerivative_le_envelope {τ : ℝ} (hτ : τ ^ 2 < 1)
    {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) (y : ℝ) :
    ‖normalKernelDerivative τ a y‖ ≤ normalDerivativeEnvelope τ A y := by
  have hv : 0 < 1 - τ ^ 2 := by linarith
  have hsub : |y - τ * a| ≤ |y| + |τ| * A := by
    calc
      |y - τ * a| ≤ |y| + |τ * a| := abs_sub _ _
      _ ≤ |y| + |τ| * A := by
        rw [abs_mul]
        linarith [mul_le_mul_of_nonneg_left ha (abs_nonneg τ)]
  have hk : normalKernel τ a y ≤ normalRowBound τ A :=
    (normalKernel_le_rowBound hτ a y).trans (normalRowBound_mono_abs hA ha)
  rw [normalKernelDerivative, norm_mul, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos hv, Real.norm_eq_abs, abs_of_nonneg (normalKernel_nonneg τ a y)]
  unfold normalDerivativeEnvelope
  calc
    |τ| * |y - τ * a| / (1 - τ ^ 2) * normalKernel τ a y ≤
        (|τ| / (1 - τ ^ 2)) * (|y| + |τ| * A) * normalKernel τ a y := by
      apply mul_le_mul_of_nonneg_right _ (normalKernel_nonneg τ a y)
      calc
        |τ| * |y - τ * a| / (1 - τ ^ 2) =
            (|τ| / (1 - τ ^ 2)) * |y - τ * a| := by ring
        _ ≤ (|τ| / (1 - τ ^ 2)) * (|y| + |τ| * A) :=
          mul_le_mul_of_nonneg_left hsub (div_nonneg (abs_nonneg _) hv.le)
    _ ≤ (|τ| / (1 - τ ^ 2)) * (|y| + |τ| * A) * normalRowBound τ A :=
      mul_le_mul_of_nonneg_left hk (by positivity)

theorem normalDerivativeEnvelope_memLp (τ A : ℝ) :
    MemLp (normalDerivativeEnvelope τ A) 2 (gaussianReal 0 1) := by
  have hid : MemLp (fun y : ℝ => |y|) 2 (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs, id_eq, ENNReal.coe_ofNat] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) (2 : ℝ≥0)).norm
  exact ((hid.add (memLp_const (|τ| * A))).const_mul
    (|τ| / (1 - τ ^ 2))).mul_const (normalRowBound τ A)

/-- Differentiation under the actual normal Gaussian integral, for every L²
input. The local dominating function and its integrability are derived above. -/
theorem hasDerivAt_normalIntegral {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ)
    (g : ℝ → ℝ) (hg : MemLp g 2 (gaussianReal 0 1)) :
    HasDerivAt (fun b => ∫ y, normalKernel τ b y * g y ∂gaussianReal 0 1)
      (∫ y, normalKernelDerivative τ a y * g y ∂gaussianReal 0 1) a := by
  let A := |a| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound_int : Integrable
      (fun y => normalDerivativeEnvelope τ A y * ‖g y‖) (gaussianReal 0 1) :=
    (normalDerivativeEnvelope_memLp τ A).integrable_mul hg.norm
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b y => normalKernel τ b y * g y)
    (F' := fun b y => normalKernelDerivative τ b y * g y)
    (s := Metric.ball a 1)
    (bound := fun y => normalDerivativeEnvelope τ A y * ‖g y‖)
    (Metric.ball_mem_nhds a zero_lt_one) ?_
    ((normalKernel_memLp hτ a).integrable_mul hg)
    ((normalKernelDerivative_measurable τ a).aestronglyMeasurable.mul
      hg.aestronglyMeasurable) ?_ hbound_int ?_).2
  · filter_upwards with b
    exact (normalKernel_measurable τ b).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · filter_upwards with y b hb
    have hb' : |b - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
    have hbA : |b| ≤ A := by
      calc
        |b| = |(b - a) + a| := by congr 1; ring
        _ ≤ |b - a| + |a| := abs_add_le _ _
        _ ≤ A := by dsimp [A]; linarith
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (normalKernelDerivative_le_envelope hτ hA hbA y) (norm_nonneg _)
  · filter_upwards with y b _
    exact (hasDerivAt_normalKernel hτ b y).mul_const (g y)

/-- The derivative statement also identifies the actual affine Gaussian average
of the possibly unbounded input, rather than only its density-ratio expression. -/
theorem hasDerivAt_shifted_normalIntegral {τ : ℝ} (hτ : τ ^ 2 < 1) (a : ℝ)
    (g : ℝ → ℝ) (hg : MemLp g 2 (gaussianReal 0 1)) :
    HasDerivAt
      (fun b => ∫ y, g (τ * b + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1)
      (∫ y, normalKernelDerivative τ a y * g y ∂gaussianReal 0 1) a := by
  have heq : (fun b => ∫ y, normalKernel τ b y * g y ∂gaussianReal 0 1) =
      (fun b => ∫ y, g (τ * b + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1) :=
    funext (fun b => integral_normalKernel_eq_shift hτ b g hg.aestronglyMeasurable)
  rw [← heq]
  exact hasDerivAt_normalIntegral hτ a g hg

/-- A single Gaussian-full-measure set of tangential points supports the normal
derivative at every real normal parameter; no uncountable AE interchange is used. -/
theorem ae_hasDerivAt_normalSection {n : ℕ} {τ : ℝ} (hτ : τ ^ 2 < 1)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      HasDerivAt (fun b => normalSection τ b f x)
        (∫ y, normalKernelDerivative τ a y * f (x, y) ∂gaussianReal 0 1) a := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.integrable_sq.prod_right_ae] with x hxm hxi
  have hx : MemLp (fun y => f (x, y)) 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hxm).mpr hxi
  intro a
  exact hasDerivAt_normalIntegral hτ a (fun y => f (x, y)) hx

/-- Gaussian L² norm in the normal fiber. -/
def normalFiberNorm {n : ℕ} (f : (Fin n → ℝ) × ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1)

theorem norm_integral_mul_le_l2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact (Real.sqrt_le_sqrt (integral_mul_sq_le hf hg)).trans_eq
    (Real.sqrt_mul (integral_nonneg (fun _ => sq_nonneg _)) _)

theorem normalRowSquare_mono_abs {τ a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) :
    normalRowSquare τ a ≤ normalRowSquare τ A := by
  unfold normalRowSquare
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : a ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hA).mpr ha
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg τ)) (by positivity)

/-- Fiber L² norms themselves belong to tangential L², with exactly the input
norm. This avoids any dimension or boundedness penalty in the supremum estimate. -/
theorem normalFiberNorm_memLp_norm {n : ℕ} (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    MemLp (normalFiberNorm f) 2 (γFin n) ∧
      eLpNorm (normalFiberNorm f) 2 (γFin n) =
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (normalFiberNorm f) (γFin n) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.pow 2).integral_prod_right'
  have hs : (fun x => normalFiberNorm f x ^ 2) =
      (fun x => ∫ y, f (x, y) ^ 2 ∂gaussianReal 0 1) := by
    funext x
    exact Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))
  have hi : Integrable (fun x => normalFiberNorm f x ^ 2) (γFin n) := by
    rw [hs]
    exact hf.integrable_sq.integral_prod_left
  have hH := (memLp_two_iff_integrable_sq hm).mpr hi
  refine ⟨hH, ?_⟩
  rw [eLpNorm_two_eq_sqrt_integral_sq hH, eLpNorm_two_eq_sqrt_integral_sq hf, hs,
    ← integral_prod (fun z => f z ^ 2) hf.integrable_sq]

theorem normalSection_norm_le_fiber {n : ℕ} {τ : ℝ} (hτ : τ ^ 2 < 1)
    {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ) (x : Fin n → ℝ)
    (hx : MemLp (fun y => f (x, y)) 2 (gaussianReal 0 1)) :
    ‖normalSection τ a f x‖ ≤ Real.sqrt (normalRowSquare τ A) * normalFiberNorm f x := by
  have hh := norm_integral_mul_le_l2 (normalKernel_memLp hτ a) hx
  rw [integral_normalKernel_sq_eq hτ a] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (normalRowSquare_mono_abs hA ha)) (Real.sqrt_nonneg _))

theorem normalSection_measurable_of_measurable {n : ℕ} (τ a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Measurable f) :
    Measurable (normalSection τ a f) := by
  exact (((normalKernel_measurable τ a).comp measurable_snd).mul hf).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- Common pointwise dominator for the whole normal interval. The single AE set
is obtained before quantifying over the real normal parameter. -/
theorem ae_normalTrace_interval_bound_of_measurable {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A →
      ‖normalTrace τ a f x‖ ≤ Real.sqrt (normalRowSquare τ A) *
        gaussianAverage τ (normalFiberNorm f) x := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  have hsec : ∀ᵐ p ∂γFin n, MemLp (fun y => f (p, y)) 2 (gaussianReal 0 1) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      hf.integrable_sq.prod_right_ae] with p hpm hpi
    exact (memLp_two_iff_integrable_sq hpm).mpr hpi
  have hpull := hmix.quasiMeasurePreserving.ae hsec
  have hi := hmix.integrable_comp_of_integrable
    ((normalFiberNorm_memLp_norm f hf).1.integrable (by norm_num))
  filter_upwards [Measure.ae_ae_of_ae_prod hpull, hi.prod_right_ae] with x hx hxi
  intro a ha
  have hb : ∀ᵐ z ∂γFin n,
      ‖normalSection τ a f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)‖ ≤
        Real.sqrt (normalRowSquare τ A) *
          normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) := by
    filter_upwards [hx] with z hz
    exact normalSection_norm_le_fiber hτ hA ha f _ hz
  have hsm : AEStronglyMeasurable
      (fun z : Fin n → ℝ => normalSection τ a f
        (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)) (γFin n) :=
    ((normalSection_measurable_of_measurable τ a f hfm).comp (by fun_prop)).aestronglyMeasurable
  have hright : Integrable (fun z : Fin n → ℝ => Real.sqrt (normalRowSquare τ A) *
      normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)) (γFin n) :=
    hxi.const_mul _
  have hleft := hright.mono' hsm hb
  change ‖∫ z, normalSection τ a f
      (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) ∂γFin n‖ ≤ _
  calc
    _ ≤ ∫ z, ‖normalSection τ a f
      (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ z, Real.sqrt (normalRowSquare τ A) *
      normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) ∂γFin n :=
      integral_mono_ae hleft.norm hright hb
    _ = _ := integral_const_mul _ _

/-- AE-equivalent inputs give equal normal traces simultaneously for every real
normal parameter on one tangential Gaussian-full-measure set. -/
theorem normalTrace_congr_ae_all_parameters {n : ℕ} {τ : ℝ} (hτ : τ ^ 2 < 1)
    {f g : (Fin n → ℝ) × ℝ → ℝ}
    (hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ, normalTrace τ a f x = normalTrace τ a g x := by
  have hs : ∀ᵐ p ∂γFin n, ∀ a : ℝ, normalSection τ a f p = normalSection τ a g p := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with p hp
    intro a
    apply integral_congr_ae
    filter_upwards [hp] with y hy
    rw [hy]
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  filter_upwards [Measure.ae_ae_of_ae_prod (hmix.quasiMeasurePreserving.ae hs)] with x hx
  intro a
  apply integral_congr_ae
  filter_upwards [hx] with z hz
  exact hz a

/-- A genuine L32 dominator for the supremum over an entire normal interval.
The one common AE set is quantified before every real normal parameter. The
input may be unbounded and only completed-Gaussian measurable. -/
theorem exists_normalTrace_l32_uniform_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n → ℝ) → ℝ,
      MemLp G 32 (γFin n) ∧ (∀ x, 0 ≤ G x) ∧
      eLpNorm G 32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A → ‖normalTrace τ a f x‖ ≤ G x := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) := (memLp_congr_ae hfg).mp hf
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsq : τ ^ 2 < 1 := by linarith
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  let H := normalFiberNorm g
  have hH := normalFiberNorm_memLp_norm g hg
  have hq : (32 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
    have ht : 0 < τ ^ 2 := sq_pos_of_pos hτ
    have hh : 31 ≤ 1 / τ ^ 2 := (le_div_iff₀ ht).mpr (by nlinarith)
    simpa only [one_div] using (show (32 : ℝ) ≤ 1 + 1 / τ ^ 2 by linarith)
  have hpq : (32 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (τ ^ 2)⁻¹) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hq
  have hT : eLpNorm (gaussianAverage τ H) 32 (γFin n) ≤ eLpNorm H 2 (γFin n) :=
    (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
      (memLp_gaussian_average_l2_to_lq τ hτ hτ1 H hH.1)
  have hTm : MemLp (gaussianAverage τ H) 32 (γFin n) := hT.trans_lt hH.1
  let C := Real.sqrt (normalRowSquare τ A)
  refine ⟨fun x => C * gaussianAverage τ H x, hTm.const_mul C, ?_, ?_, ?_⟩
  · intro x
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact integral_nonneg (fun _ => Real.sqrt_nonneg _)
  · change eLpNorm (C • gaussianAverage τ H) 32 (γFin n) ≤ _
    rw [eLpNorm_const_smul]
    have hC : ‖C‖ₑ = ENNReal.ofReal C := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hC]
    calc
      ENNReal.ofReal C * eLpNorm (gaussianAverage τ H) 32 (γFin n) ≤
          ENNReal.ofReal C * eLpNorm H 2 (γFin n) := mul_le_mul_right hT _
      _ = _ := by rw [hH.2, ← eLpNorm_congr_ae hfg]
  · filter_upwards [ae_normalTrace_interval_bound_of_measurable hsq hA g hgm hg,
      normalTrace_congr_ae_all_parameters hsq hfg] with x hx hxx
    intro a ha
    rw [hxx a]
    exact hx a ha

/-- The actual product-integral representation holds on one common Gaussian-
full-measure set for all real normal coordinates, not merely separately at each. -/
theorem normalTrace_eq_product_ae_all_parameters {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      normalTrace τ a f x =
        ∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * a + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1) := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  have hpull := hf.comp_measurePreserving
    ((hmix.prod (MeasurePreserving.id (gaussianReal 0 1))).comp
      (measurePreserving_prodAssoc (γFin n) (γFin n) (gaussianReal 0 1)).symm)
  have hsec : ∀ᵐ x ∂γFin n,
      MemLp (fun z : (Fin n → ℝ) × ℝ =>
        f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j), z.2)) 2
        ((γFin n).prod (gaussianReal 0 1)) := by
    filter_upwards [hpull.aestronglyMeasurable.prodMk_left,
      hpull.integrable_sq.prod_right_ae] with x hxm hxi
    exact (memLp_two_iff_integrable_sq hxm).mpr hxi
  have hnormal : ∀ᵐ p ∂γFin n, ∀ a : ℝ,
      normalSection τ a f p =
        ∫ y, f (p, τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left] with p hpm
    intro a
    exact integral_normalKernel_eq_shift hτ a (fun y => f (p, y)) hpm
  filter_upwards [hsec, Measure.ae_ae_of_ae_prod
    (hmix.quasiMeasurePreserving.ae hnormal)] with x hx hxx
  intro a
  have hshift : MeasurePreserving (fun y => τ * a + Real.sqrt (1 - τ ^ 2) * y)
      (gaussianReal 0 1) (gaussianReal (τ * a) (normalVariance τ)) :=
    ⟨by fun_prop, normalShift_map hτ a⟩
  have hi := ((MeasurePreserving.id (γFin n)).prod hshift).integrable_comp_of_integrable
    (integrable_shifted_normal_product hτ a _ hx)
  calc
    normalTrace τ a f x = ∫ z, ∫ y,
        f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j),
          τ * a + Real.sqrt (1 - τ ^ 2) * y) ∂gaussianReal 0 1 ∂γFin n := by
      apply integral_congr_ae
      filter_upwards [hxx] with z hz
      exact hz a
    _ = _ := (integral_prod _ hi).symm

/-- Actual joint-Gaussian OU traces over the entire normal interval admit an
L32 envelope with the sharp dimension-independent row constant. -/
theorem exists_actual_product_trace_l32_uniform_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n → ℝ) → ℝ,
      MemLp G 32 (γFin n) ∧ (∀ x, 0 ≤ G x) ∧
      eLpNorm G 32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A →
        ‖∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * a + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)‖ ≤ G x := by
  obtain ⟨G, hGm, hGpos, hGn, hG⟩ :=
    exists_normalTrace_l32_uniform_envelope hτ hτ32 hA f hf
  refine ⟨G, hGm, hGpos, hGn, ?_⟩
  have hsq : τ ^ 2 < 1 := by linarith
  filter_upwards [hG, normalTrace_eq_product_ae_all_parameters hsq f hf] with x hx hxx
  intro a ha
  rw [← hxx a]
  exact hx a ha

/-- Gaussian normal integration against the actual derivative row. -/
def normalDerivativeSection {n : ℕ} (τ a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ y, normalKernelDerivative τ a y * f (x, y) ∂gaussianReal 0 1

/-- The actual candidate normal derivative of the OU trace. Its derivative
identity is established below by dominated differentiation. -/
def normalDerivativeTrace {n : ℕ} (τ a : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ) :=
  gaussianAverage τ (normalDerivativeSection τ a f)

theorem normalDerivativeRowSquare_mono_abs {τ a A : ℝ} (hτ : τ ^ 2 < 1)
    (hA : 0 ≤ A) (ha : |a| ≤ A) :
    normalDerivativeRowSquare τ a ≤ normalDerivativeRowSquare τ A := by
  have hv : 0 < 1 - τ ^ 2 := by linarith
  have hw : 0 < 1 + τ ^ 2 := by positivity
  have h4 : 0 < 1 - τ ^ 4 := by
    rw [show 1 - τ ^ 4 = (1 - τ ^ 2) * (1 + τ ^ 2) by ring]
    exact mul_pos hv hw
  have hsq : a ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hA).mpr ha
  unfold normalDerivativeRowSquare
  apply mul_le_mul (normalRowSquare_mono_abs hA ha) ?_ (by positivity)
    (normalRowSquare_nonneg τ A)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ τ ^ 4))
    (sq_nonneg (1 + τ ^ 2))
  linarith

theorem normalDerivativeSection_measurable_of_measurable {n : ℕ} (τ a : ℝ)
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Measurable f) :
    Measurable (normalDerivativeSection τ a f) := by
  exact (((normalKernelDerivative_measurable τ a).comp measurable_snd).mul hf).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem normalDerivativeSection_norm_le_fiber {n : ℕ} {τ : ℝ} (hτ : τ ^ 2 < 1)
    {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ) (x : Fin n → ℝ)
    (hx : MemLp (fun y => f (x, y)) 2 (gaussianReal 0 1)) :
    ‖normalDerivativeSection τ a f x‖ ≤
      Real.sqrt (normalDerivativeRowSquare τ A) * normalFiberNorm f x := by
  have hh := norm_integral_mul_le_l2 (normalKernelDerivative_memLp hτ a) hx
  rw [integral_normalKernelDerivative_sq hτ a] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (normalDerivativeRowSquare_mono_abs hτ hA ha)) (Real.sqrt_nonneg _))

/-- Differentiating the tangentially averaged normal trace, for a measurable L²
input. The result holds simultaneously at every real normal parameter. -/
theorem ae_hasDerivAt_normalTrace_of_measurable {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (f : (Fin n → ℝ) × ℝ → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      HasDerivAt (fun b => normalTrace τ b f x) (normalDerivativeTrace τ a f x) a := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  have hsec : ∀ᵐ p ∂γFin n, MemLp (fun y => f (p, y)) 2 (gaussianReal 0 1) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      hf.integrable_sq.prod_right_ae] with p hpm hpi
    exact (memLp_two_iff_integrable_sq hpm).mpr hpi
  have hpull := hmix.quasiMeasurePreserving.ae hsec
  have hi := hmix.integrable_comp_of_integrable
    ((normalFiberNorm_memLp_norm f hf).1.integrable (by norm_num))
  filter_upwards [Measure.ae_ae_of_ae_prod hpull, hi.prod_right_ae] with x hx hxi
  intro a
  let shift := fun z : Fin n → ℝ => fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j
  have hs : Measurable shift := by fun_prop
  have hFint : Integrable (fun z => normalSection τ a f (shift z)) (γFin n) := by
    apply (hxi.const_mul (Real.sqrt (normalRowSquare τ |a|))).mono'
      ((normalSection_measurable_of_measurable τ a f hfm).comp hs).aestronglyMeasurable
    filter_upwards [hx] with z hz
    exact normalSection_norm_le_fiber hτ (abs_nonneg a) le_rfl f _ hz
  let A := |a| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b z => normalSection τ b f (shift z))
    (F' := fun b z => normalDerivativeSection τ b f (shift z))
    (s := Metric.ball a 1)
    (bound := fun z => Real.sqrt (normalDerivativeRowSquare τ A) * normalFiberNorm f (shift z))
    (Metric.ball_mem_nhds a zero_lt_one) ?_ hFint
    ((normalDerivativeSection_measurable_of_measurable τ a f hfm).comp hs).aestronglyMeasurable
    ?_ (hxi.const_mul (Real.sqrt (normalDerivativeRowSquare τ A))) ?_).2
  · filter_upwards with b
    exact ((normalSection_measurable_of_measurable τ b f hfm).comp hs).aestronglyMeasurable
  · filter_upwards [hx] with z hz
    intro b hb
    have hb' : |b - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
    have hbA : |b| ≤ A := by
      calc
        |b| = |(b - a) + a| := by congr 1; ring
        _ ≤ |b - a| + |a| := abs_add_le _ _
        _ ≤ A := by dsimp [A]; linarith
    exact normalDerivativeSection_norm_le_fiber hτ hA hbA f _ hz
  · filter_upwards [hx] with z hz
    intro b _
    exact hasDerivAt_normalIntegral hτ b (fun y => f (shift z, y)) hz

/-- First derivative traces respect completed-Gaussian AE equality on one
common tangential full-measure set for every normal parameter. -/
theorem normalDerivativeTrace_congr_ae_all_parameters {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) {f g : (Fin n → ℝ) × ℝ → ℝ}
    (hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      normalDerivativeTrace τ a f x = normalDerivativeTrace τ a g x := by
  have hs : ∀ᵐ p ∂γFin n, ∀ a : ℝ,
      normalDerivativeSection τ a f p = normalDerivativeSection τ a g p := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with p hp
    intro a
    apply integral_congr_ae
    filter_upwards [hp] with y hy
    rw [hy]
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  filter_upwards [Measure.ae_ae_of_ae_prod (hmix.quasiMeasurePreserving.ae hs)] with x hx
  intro a
  apply integral_congr_ae
  filter_upwards [hx] with z hz
  exact hz a

/-- Actual normal differentiability of the OU trace for every Gaussian-L² input,
including completed-measurable inputs and unbounded high-chaos projections. -/
theorem ae_hasDerivAt_normalTrace {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      HasDerivAt (fun b => normalTrace τ b f x) (normalDerivativeTrace τ a f x) a := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) := (memLp_congr_ae hfg).mp hf
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  filter_upwards [ae_hasDerivAt_normalTrace_of_measurable hτ g hgm hg,
    normalTrace_congr_ae_all_parameters hτ hfg,
    normalDerivativeTrace_congr_ae_all_parameters hτ hfg] with x hx hxx hdx
  intro a
  have heq : (fun b => normalTrace τ b f x) = (fun b => normalTrace τ b g x) := funext hxx
  rw [heq, hdx a]
  exact hx a

/-- Derivative of the actual single joint-Gaussian OU integral on one common AE
set, for all real normal parameters. -/
theorem ae_hasDerivAt_actual_product_trace {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ,
      HasDerivAt (fun b => ∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * b + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1))
        (normalDerivativeTrace τ a f x) a := by
  filter_upwards [ae_hasDerivAt_normalTrace hτ f hf,
    normalTrace_eq_product_ae_all_parameters hτ f hf] with x hx hxx
  intro a
  have heq : (fun b => normalTrace τ b f x) =
      (fun b => ∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * b + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)) := funext hxx
  rw [← heq]
  exact hx a

/-- Uniform derivative-trace domination on one AE set for the entire interval. -/
theorem ae_normalDerivativeTrace_interval_bound_of_measurable {n : ℕ} {τ : ℝ}
    (hτ : τ ^ 2 < 1) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A →
      ‖normalDerivativeTrace τ a f x‖ ≤ Real.sqrt (normalDerivativeRowSquare τ A) *
        gaussianAverage τ (normalFiberNorm f) x := by
  have hv : 0 ≤ 1 - τ ^ 2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) τ (Real.sqrt (1 - τ ^ 2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv]; ring)⟩
  have hsec : ∀ᵐ p ∂γFin n, MemLp (fun y => f (p, y)) 2 (gaussianReal 0 1) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      hf.integrable_sq.prod_right_ae] with p hpm hpi
    exact (memLp_two_iff_integrable_sq hpm).mpr hpi
  have hpull := hmix.quasiMeasurePreserving.ae hsec
  have hi := hmix.integrable_comp_of_integrable
    ((normalFiberNorm_memLp_norm f hf).1.integrable (by norm_num))
  filter_upwards [Measure.ae_ae_of_ae_prod hpull, hi.prod_right_ae] with x hx hxi
  intro a ha
  have hb : ∀ᵐ z ∂γFin n,
      ‖normalDerivativeSection τ a f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)‖ ≤
        Real.sqrt (normalDerivativeRowSquare τ A) *
          normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) := by
    filter_upwards [hx] with z hz
    exact normalDerivativeSection_norm_le_fiber hτ hA ha f _ hz
  have hsm : AEStronglyMeasurable
      (fun z : Fin n → ℝ => normalDerivativeSection τ a f
        (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)) (γFin n) :=
    ((normalDerivativeSection_measurable_of_measurable τ a f hfm).comp (by fun_prop)).aestronglyMeasurable
  have hright : Integrable (fun z : Fin n → ℝ => Real.sqrt (normalDerivativeRowSquare τ A) *
      normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)) (γFin n) :=
    hxi.const_mul _
  have hleft := hright.mono' hsm hb
  change ‖∫ z, normalDerivativeSection τ a f
      (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) ∂γFin n‖ ≤ _
  calc
    _ ≤ ∫ z, ‖normalDerivativeSection τ a f
      (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ z, Real.sqrt (normalDerivativeRowSquare τ A) *
      normalFiberNorm f (fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z j) ∂γFin n :=
      integral_mono_ae hleft.norm hright hb
    _ = _ := integral_const_mul _ _

/-- Uniform L32 envelope for the actual normal derivative trace, with its exact
one-dimensional derivative-row coefficient and no dimension factor. -/
theorem exists_normalDerivativeTrace_l32_uniform_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n → ℝ) → ℝ,
      MemLp G 32 (γFin n) ∧ (∀ x, 0 ≤ G x) ∧
      eLpNorm G 32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalDerivativeRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A → ‖normalDerivativeTrace τ a f x‖ ≤ G x := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[(γFin n).prod (gaussianReal 0 1)] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 ((γFin n).prod (gaussianReal 0 1)) := (memLp_congr_ae hfg).mp hf
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsq : τ ^ 2 < 1 := by linarith
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  let H := normalFiberNorm g
  have hH := normalFiberNorm_memLp_norm g hg
  have hq : (32 : ℝ) ≤ 1 + (τ ^ 2)⁻¹ := by
    have ht : 0 < τ ^ 2 := sq_pos_of_pos hτ
    have hh : 31 ≤ 1 / τ ^ 2 := (le_div_iff₀ ht).mpr (by nlinarith)
    simpa only [one_div] using (show (32 : ℝ) ≤ 1 + 1 / τ ^ 2 by linarith)
  have hpq : (32 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (τ ^ 2)⁻¹) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hq
  have hT : eLpNorm (gaussianAverage τ H) 32 (γFin n) ≤ eLpNorm H 2 (γFin n) :=
    (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
      (memLp_gaussian_average_l2_to_lq τ hτ hτ1 H hH.1)
  have hTm : MemLp (gaussianAverage τ H) 32 (γFin n) := hT.trans_lt hH.1
  let C := Real.sqrt (normalDerivativeRowSquare τ A)
  refine ⟨fun x => C * gaussianAverage τ H x, hTm.const_mul C, ?_, ?_, ?_⟩
  · intro x
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact integral_nonneg (fun _ => Real.sqrt_nonneg _)
  · change eLpNorm (C • gaussianAverage τ H) 32 (γFin n) ≤ _
    rw [eLpNorm_const_smul]
    have hC : ‖C‖ₑ = ENNReal.ofReal C := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hC]
    calc
      ENNReal.ofReal C * eLpNorm (gaussianAverage τ H) 32 (γFin n) ≤
          ENNReal.ofReal C * eLpNorm H 2 (γFin n) := mul_le_mul_right hT _
      _ = _ := by rw [hH.2, ← eLpNorm_congr_ae hfg]
  · filter_upwards [ae_normalDerivativeTrace_interval_bound_of_measurable hsq hA g hgm hg,
      normalDerivativeTrace_congr_ae_all_parameters hsq hfg] with x hx hxx
    intro a ha
    rw [hxx a]
    exact hx a ha

/-- L32 control of the first normal derivative supremum of the actual OU product
integral. The derivative here is Lean's actual derivative of that integral. -/
theorem exists_actual_product_trace_derivative_l32_uniform_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) {A : ℝ} (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n → ℝ) → ℝ,
      MemLp G 32 (γFin n) ∧ (∀ x, 0 ≤ G x) ∧
      eLpNorm G 32 (γFin n) ≤ ENNReal.ofReal (Real.sqrt (normalDerivativeRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ x ∂γFin n, ∀ a : ℝ, |a| ≤ A →
        ‖deriv (fun b => ∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * b + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)) a‖ ≤ G x := by
  obtain ⟨G, hGm, hGpos, hGn, hG⟩ :=
    exists_normalDerivativeTrace_l32_uniform_envelope hτ hτ32 hA f hf
  refine ⟨G, hGm, hGpos, hGn, ?_⟩
  have hsq : τ ^ 2 < 1 := by linarith
  filter_upwards [hG, ae_hasDerivAt_actual_product_trace hsq f hf] with x hx hdx
  intro a ha
  rw [(hdx a).deriv]
  exact hx a ha

/-- The actual real supremum of the absolute normal trace on a compact interval. -/
def normalTraceSup {n : ℕ} (τ A : ℝ) (f : (Fin n → ℝ) × ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨆ a : Set.Icc (-A) A, ‖normalTrace τ a f x‖

/-- The uncountable normal supremum is AE measurable: the previously proved
normal differentiability reduces it to a supremum over a countable dense set. -/
theorem normalTraceSup_aestronglyMeasurable {n : ℕ} {τ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    AEStronglyMeasurable (normalTraceSup τ A f) (γFin n) := by
  have hsq : τ ^ 2 < 1 := by nlinarith
  let I := Set.Icc (-A) A
  obtain ⟨J, hJc, hJd⟩ := TopologicalSpace.exists_countable_dense I
  let : Countable J := hJc.to_subtype
  have hmeas : AEMeasurable
      (fun x => ⨆ a : J, ‖normalTrace τ (a.1 : ℝ) f x‖) (γFin n) := by
    apply AEMeasurable.iSup
    intro a
    have hsec := (normalSection_memLp_and_integral_sq_le hsq (a.1 : ℝ) f hf).1
    exact (memLp_gaussian_average_higher_integrability τ hτ hτ1 _ hsec).aemeasurable.norm
  have heq : (fun x => ⨆ a : J, ‖normalTrace τ (a.1 : ℝ) f x‖) =ᵐ[γFin n]
      normalTraceSup τ A f := by
    filter_upwards [ae_hasDerivAt_normalTrace hsq f hf] with x hx
    have hc : Continuous (fun a : ℝ => normalTrace τ a f x) :=
      continuous_iff_continuousAt.mpr (fun a => (hx a).continuousAt)
    exact hJd.ciSup' (hc.norm.comp continuous_subtype_val)
  exact (hmeas.congr heq).aestronglyMeasurable

/-- Exact L32 bound for the measurable normal supremum, not only separate
fixed-parameter bounds or an unconnected scalar majorant. -/
theorem normalTraceSup_memLp_and_bound {n : ℕ} {τ A : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    MemLp (normalTraceSup τ A f) 32 (γFin n) ∧
      eLpNorm (normalTraceSup τ A f) 32 (γFin n) ≤
        ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
          eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  have hτ1 : τ < 1 := by nlinarith [sq_nonneg τ]
  have hm := normalTraceSup_aestronglyMeasurable (A := A) hτ hτ1 f hf
  obtain ⟨G, hGm, hGpos, hGn, hG⟩ := exists_normalTrace_l32_uniform_envelope hτ hτ32 hA f hf
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
  have hnorm := eLpNorm_mono_ae (p := 32) hm hbound
  exact ⟨hnorm.trans_lt hGm, hnorm.trans hGn⟩

/-- The normal supremum bound for the actual single product-Gaussian integral.
The displayed supremum is over every real coordinate in the interval. -/
theorem actual_product_normal_sup_memLp_and_bound {n : ℕ} {τ A : ℝ}
    (hτ : 0 < τ) (hτ32 : τ ^ 2 ≤ 1 / 31) (hA : 0 ≤ A)
    (f : (Fin n → ℝ) × ℝ → ℝ)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    let S := fun x => ⨆ a : Set.Icc (-A) A,
      ‖∫ z : (Fin n → ℝ) × ℝ,
          f ((fun j => τ * x j + Real.sqrt (1 - τ ^ 2) * z.1 j),
            τ * (a : ℝ) + Real.sqrt (1 - τ ^ 2) * z.2) ∂(γFin n).prod (gaussianReal 0 1)‖
    MemLp S 32 (γFin n) ∧ eLpNorm S 32 (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ A)) *
        eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) := by
  intro S
  have hsq : τ ^ 2 < 1 := by linarith
  have heq : normalTraceSup τ A f =ᵐ[γFin n] S := by
    filter_upwards [normalTrace_eq_product_ae_all_parameters hsq f hf] with x hx
    exact iSup_congr (fun a => congrArg norm (hx a))
  have hh := normalTraceSup_memLp_and_bound hτ hτ32 hA f hf
  refine ⟨(memLp_congr_ae heq).mp hh.1, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hh.2

end NegativeVotingNormalDerivatives
