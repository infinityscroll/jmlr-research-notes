import FSC.Support.Definitions
import FSC.Gaussian.StandardDensity
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Unbounded cap dilation and ambient Gaussian energy. The analytic derivative is developed here. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Pointwise

namespace FSC

/-- Simultaneous positive scaling of the supports scales the whole cap, bounded or not. -/
theorem cap_smul {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ)
    (s : ℝ) (hs : 0 < s) :
    cap w (s • b) = s • cap w b := by
  ext y
  constructor
  · intro hy
    refine ⟨s⁻¹ • y, ?_, smul_inv_smul₀ hs.ne' y⟩
    intro j
    have hj := hy j
    change inner ℝ (w j) y ≤ s * b j at hj
    rw [real_inner_smul_right]
    exact (inv_mul_le_iff₀ hs).2 hj
  · rintro ⟨x, hx, rfl⟩ j
    change inner ℝ (w j) (s • x) ≤ s * b j
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hx j) hs.le

theorem integrable_sq_norm_stdGaussian (d : ℕ) :
    Integrable (fun y : Coord d ↦ ‖y‖ ^ 2) (stdGaussian (Coord d)) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_two_id (μ := stdGaussian (Coord d))).norm.integrable_sq

theorem capEnergy_nonneg {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) :
    0 ≤ capEnergy w b := integral_nonneg fun _ ↦ sq_nonneg _

theorem stdGaussian_null_iff_volume_null {d : ℕ} (A : Set (Coord d)) :
    stdGaussian (Coord d) A = 0 ↔ (volume : Measure (Coord d)) A = 0 := by
  rw [stdGaussian_eq_volume_withDensity,
    withDensity_apply_eq_zero (measurable_standardDensity d)]
  simp [standardDensity_ne_zero]

theorem stdGaussian_pos_of_isOpen {d : ℕ} {A : Set (Coord d)}
    (hA : IsOpen A) (hne : A.Nonempty) : 0 < stdGaussian (Coord d) A := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (hA.measure_pos (μ := volume) hne).ne'
    ((stdGaussian_null_iff_volume_null A).mp hz)

/-- Strict positivity uses the full ambient dimension, including unused directions. -/
theorem capEnergy_pos {d : ℕ} {ι : Type*} [Finite ι]
    (w : ι → Coord d) (b : ι → ℝ) (hd : 1 ≤ d) (hb : ∀ i, 0 < b i) :
    0 < capEnergy w b := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let U : Set (Coord d) := {y | ∀ i, inner ℝ (w i) y < b i}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : Coord d) ∈ U := by simpa [U] using hb
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨x, hx⟩ := exists_norm_eq (Coord d) (by positivity : 0 ≤ r / 2)
  have hx0 : x ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hx
    linarith
  have hxU : x ∈ U := hrU (by simpa [Metric.mem_ball, dist_zero_right, hx] using
    (show r / 2 < r by linarith))
  have hpos : 0 < stdGaussian (Coord d) (U \ {0}) :=
    stdGaussian_pos_of_isOpen (hU.sdiff isClosed_singleton) ⟨x, hxU, hx0⟩
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun y ↦ sq_nonneg ‖y‖)
    ((integrable_sq_norm_stdGaussian d).restrict (s := cap w b))).mpr
  apply lt_of_lt_of_le hpos
  apply measure_mono
  rintro y ⟨hyU, hy0⟩
  exact ⟨by simpa [Function.mem_support, pow_ne_zero_iff] using hy0,
    fun i ↦ (hyU i).le⟩

/-- Gaussian integration as ordinary Lebesgue integration of the explicit standard density. -/
theorem integral_stdGaussian_eq (d : ℕ) (f : Coord d → ℝ) :
    ∫ y, f y ∂stdGaussian (Coord d) =
      ∫ y, (standardDensity y).toReal * f y := by
  rw [stdGaussian_eq_volume_withDensity,
    integral_withDensity_eq_integral_toReal_smul (measurable_standardDensity d)
      (ae_of_all _ fun y ↦ lt_top_iff_ne_top.mpr (standardDensity_ne_top y))]
  rfl

theorem setIntegral_stdGaussian_eq (d : ℕ) (A : Set (Coord d)) (f : Coord d → ℝ) :
    ∫ y in A, f y ∂stdGaussian (Coord d) =
      ∫ y in A, (standardDensity y).toReal * f y := by
  rw [stdGaussian_eq_volume_withDensity,
    setIntegral_withDensity_eq_setIntegral_toReal_smul' A (measurable_standardDensity d)
      (ae_of_all _ fun y ↦ lt_top_iff_ne_top.mpr (standardDensity_ne_top y))]
  rfl

theorem capMass_eq_integral_density {d : ℕ} {ι : Type*}
    (w : ι → Coord d) (b : ι → ℝ) :
    capMass w b = ∫ y in cap w b, (standardDensity y).toReal := by
  simpa [capMass, measureReal_def] using
    setIntegral_stdGaussian_eq d (cap w b) (fun _ ↦ (1 : ℝ))

theorem integrable_standardDensity (d : ℕ) :
    Integrable (fun y : Coord d ↦ (standardDensity y).toReal) := by
  have h : Integrable (fun _ : Coord d ↦ (1 : ℝ)) (stdGaussian (Coord d)) :=
    integrable_const 1
  rw [stdGaussian_eq_volume_withDensity,
    integrable_withDensity_iff (measurable_standardDensity d)
      (ae_of_all _ fun y ↦ lt_top_iff_ne_top.mpr (standardDensity_ne_top y))] at h
  simpa using h

theorem integrable_sq_norm_mul_standardDensity (d : ℕ) :
    Integrable (fun y : Coord d ↦ ‖y‖ ^ 2 * (standardDensity y).toReal) := by
  have h := integrable_sq_norm_stdGaussian d
  rw [stdGaussian_eq_volume_withDensity,
    integrable_withDensity_iff (measurable_standardDensity d)
      (ae_of_all _ fun y ↦ lt_top_iff_ne_top.mpr (standardDensity_ne_top y))] at h
  exact h

theorem integrable_gaussian_majorant (d : ℕ) :
    Integrable (fun y : Coord d ↦ (1 + ‖y‖ ^ 2) * Real.exp (-‖y‖ ^ 2 / 8)) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ d
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne')
  have h0 := (integrable_standardDensity d).comp_smul (R := (1 / 2 : ℝ)) (by norm_num)
  have h2 := (integrable_sq_norm_mul_standardDensity d).comp_smul
    (R := (1 / 2 : ℝ)) (by norm_num)
  have h := (h0.add (h2.const_mul 4)).const_mul c⁻¹
  apply h.congr
  apply ae_of_all
  intro y
  have hdens : (standardDensity ((1 / 2 : ℝ) • y)).toReal =
      c * Real.exp (-‖y‖ ^ 2 / 8) := by
    rw [toReal_standardDensity]
    congr 1
    congr 1
    rw [norm_smul]
    norm_num
    ring
  change c⁻¹ * ((standardDensity ((1 / 2 : ℝ) • y)).toReal +
    4 * (‖(1 / 2 : ℝ) • y‖ ^ 2 * (standardDensity ((1 / 2 : ℝ) • y)).toReal)) = _
  rw [hdens, norm_smul]
  norm_num
  field_simp
  ring

def dilationKernel (d : ℕ) (s : ℝ) (y : Coord d) : ℝ :=
  s ^ d * (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-s ^ 2 * ‖y‖ ^ 2 / 2)

def dilationDerivative (d : ℕ) (s : ℝ) (y : Coord d) : ℝ :=
  ((d : ℝ) * s ^ (d - 1) - s ^ (d + 1) * ‖y‖ ^ 2) *
    (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-s ^ 2 * ‖y‖ ^ 2 / 2)

theorem dilationKernel_eq (d : ℕ) (s : ℝ) (y : Coord d) :
    dilationKernel d s y = s ^ d * (standardDensity (s • y)).toReal := by
  rw [toReal_standardDensity]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, dilationKernel,
    neg_mul, mul_assoc]

theorem hasDerivAt_dilationKernel (d : ℕ) (s : ℝ) (y : Coord d) :
    HasDerivAt (fun r ↦ dilationKernel d r y) (dilationDerivative d s y) s := by
  have hpow := (hasDerivAt_id s).pow d
  have hexp : HasDerivAt (fun r : ℝ ↦ -r ^ 2 * ‖y‖ ^ 2 / 2)
      (-s * ‖y‖ ^ 2) s := by
    exact (((((hasDerivAt_id s).pow 2).neg).mul_const (‖y‖ ^ 2)).div_const 2).congr_deriv
      (by dsimp; ring)
  have h := (hpow.mul_const ((Real.sqrt (2 * Real.pi))⁻¹ ^ d)).mul hexp.exp
  apply h.congr_deriv
  simp only [dilationDerivative, mul_one, pow_succ, id_eq, Pi.pow_apply]
  ring

theorem dilationDerivative_bound (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (y : Coord d),
      s ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) →
      ‖dilationDerivative d s y‖ ≤ C * ((1 + ‖y‖ ^ 2) * Real.exp (-‖y‖ ^ 2 / 8)) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ d
  let a : ℝ := (d : ℝ) * 2 ^ (d - 1)
  let b : ℝ := 2 ^ (d + 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨(a + b) * c, mul_nonneg (add_nonneg ha hb) hc, fun s y hs ↦ ?_⟩
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hs2 : s ≤ 2 := by linarith [hs.2]
  have hN : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hpoly : |(d : ℝ) * s ^ (d - 1) - s ^ (d + 1) * ‖y‖ ^ 2| ≤
      a + b * ‖y‖ ^ 2 := by
    calc
      _ ≤ |(d : ℝ) * s ^ (d - 1)| + |s ^ (d + 1) * ‖y‖ ^ 2| := abs_sub _ _
      _ = (d : ℝ) * s ^ (d - 1) + s ^ (d + 1) * ‖y‖ ^ 2 := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ a + b * ‖y‖ ^ 2 := by
        dsimp [a, b]
        gcongr
  have hexp : Real.exp (-s ^ 2 * ‖y‖ ^ 2 / 2) ≤ Real.exp (-‖y‖ ^ 2 / 8) := by
    apply Real.exp_le_exp.mpr
    have hsq : (1 / 4 : ℝ) ≤ s ^ 2 := by nlinarith [hs.1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hN]
  change ‖((d : ℝ) * s ^ (d - 1) - s ^ (d + 1) * ‖y‖ ^ 2) *
    c * Real.exp (-s ^ 2 * ‖y‖ ^ 2 / 2)‖ ≤ _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hc, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (a + b * ‖y‖ ^ 2) * c * Real.exp (-‖y‖ ^ 2 / 8) := by
      gcongr
    _ ≤ (a + b) * c * ((1 + ‖y‖ ^ 2) * Real.exp (-‖y‖ ^ 2 / 8)) := by
      have hstep : a + b * ‖y‖ ^ 2 ≤ (a + b) * (1 + ‖y‖ ^ 2) := by
        nlinarith [mul_nonneg ha hN]
      have hmul := mul_le_mul_of_nonneg_right hstep
        (mul_nonneg hc (Real.exp_pos (-‖y‖ ^ 2 / 8)).le)
      nlinarith only [hmul]

theorem capMass_dilate_eq_integral {d : ℕ} {ι : Type*}
    (w : ι → Coord d) (b : ι → ℝ) (s : ℝ) (hs : 0 < s) :
    capMass w (s • b) = ∫ y in cap w b, dilationKernel d s y := by
  rw [capMass_eq_integral_density, cap_smul w b s hs]
  simp_rw [dilationKernel_eq]
  rw [integral_const_mul]
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Coord d))
    (fun y : Coord d ↦ (standardDensity y).toReal) (cap w b) hs
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  rw [h]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_mul]

/-- The Gaussian dilation derivative, with no boundedness or independence condition on the cap. -/
theorem hasDerivAt_capMass_dilate {d : ℕ} {ι : Type*}
    (w : ι → Coord d) (b : ι → ℝ) :
    HasDerivAt (fun s : ℝ ↦ capMass w (s • b))
      ((d : ℝ) * capMass w b - capEnergy w b) 1 := by
  obtain ⟨C, hC, hbound⟩ := dilationDerivative_bound d
  have hbase : Integrable (dilationKernel d 1)
      ((volume : Measure (Coord d)).restrict (cap w b)) := by
    change Integrable (fun y ↦ dilationKernel d 1 y)
      ((volume : Measure (Coord d)).restrict (cap w b))
    simpa only [dilationKernel_eq, one_pow, one_smul, one_mul] using
      (integrable_standardDensity d).restrict (s := cap w b)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Coord d)).restrict (cap w b))
    (F := dilationKernel d) (F' := dilationDerivative d)
    (bound := fun y ↦ C * ((1 + ‖y‖ ^ 2) * Real.exp (-‖y‖ ^ 2 / 8)))
    (Icc_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
    (Filter.Eventually.of_forall fun s ↦ by unfold dilationKernel; fun_prop)
    hbase
    (by unfold dilationDerivative; fun_prop)
    (ae_of_all _ fun y s hs ↦ hbound s y hs)
    (((integrable_gaussian_majorant d).const_mul C).restrict)
    (ae_of_all _ fun y s _ ↦ hasDerivAt_dilationKernel d s y)
  have hvalue : (∫ y in cap w b, dilationDerivative d 1 y) =
      (d : ℝ) * capMass w b - capEnergy w b := by
    have heq (y : Coord d) : dilationDerivative d 1 y =
        (d : ℝ) * (standardDensity y).toReal -
          ‖y‖ ^ 2 * (standardDensity y).toReal := by
      rw [toReal_standardDensity]
      simp only [dilationDerivative, one_pow, neg_mul, one_mul]
      ring
    simp_rw [heq]
    rw [integral_sub ((integrable_standardDensity d).const_mul (d : ℝ)).restrict
      ((integrable_sq_norm_mul_standardDensity d).restrict)]
    rw [integral_const_mul, ← capMass_eq_integral_density]
    have he := setIntegral_stdGaussian_eq d (cap w b) (fun y ↦ ‖y‖ ^ 2)
    rw [capEnergy, he]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ mul_comm _ _
  rw [hvalue] at hdiff
  apply hdiff.2.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact capMass_dilate_eq_integral w b s hs

/-- Once the actual support derivative is known, dilation identifies the same canonical energy. -/
theorem capEnergy_eq_of_hasFDerivAt {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) (b : ι → ℝ)
    (h : HasFDerivAt (capMass w) (supportGradient w b) b) :
    capEnergy w b = (d : ℝ) * capMass w b -
      ∑ j, b j * WeakSimplex.normalPDF (b j) * sliceMass w b j := by
  have hline : HasDerivAt (fun s : ℝ ↦ capMass w (s • b)) (supportGradient w b b) 1 := by
    have h' : HasFDerivAt (capMass w) (supportGradient w b) ((1 : ℝ) • b) := by
      simpa only [one_smul] using! h
    simpa only [one_smul] using!
      h'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const b)
  have heq := (hasDerivAt_capMass_dilate w b).unique hline
  have hgrad : supportGradient w b b =
      ∑ j, b j * WeakSimplex.normalPDF (b j) * sliceMass w b j := by
    simp [supportGradient, mul_assoc]
  rw [hgrad] at heq
  linarith

end FSC
