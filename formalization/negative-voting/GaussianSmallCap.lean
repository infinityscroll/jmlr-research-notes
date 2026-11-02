import Mathlib

/-!
# Normal-fibre calculus for the structured Gaussian switching cap

This file concerns actual one-dimensional integrals. The forcing's normal
Lipschitz control is explicit; an Lq bound alone is not substituted for it.
The good-fibre calculus and L32 bad-fibre truncation are proved below.
Multi-facet geometry, third-label strips, weighted trace estimates, and their
full structured-cap assembly remain separate obligations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
namespace NegativeVotingSmallCap

/-- Positive switching reward with linear normal switching cost. -/
def fibreReward (a ell z : ℝ) : ℝ := max (a - ell * z) 0

theorem continuous_fibreReward (a ell : ℝ) : Continuous (fibreReward a ell) := by
  unfold fibreReward
  fun_prop

/-- The exact triangular area, up to its zero crossing. -/
theorem fibreReward_integral_to_crossing (a ell : ℝ) (ha : 0 ≤ a) (hell : 0 < ell) :
    (∫ z in (0 : ℝ)..(a / ell), fibreReward a ell z) = a ^ 2 / (2 * ell) := by
  have hc : 0 ≤ a / ell := div_nonneg ha hell.le
  have heq : (∫ z in (0 : ℝ)..(a / ell), fibreReward a ell z) =
      ∫ z in (0 : ℝ)..(a / ell), a - ell * z := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc
    intro z hz
    unfold fibreReward
    apply max_eq_left
    have h : ell * z ≤ a := by
      have hh := (le_div_iff₀ hell).mp hz.2.le
      nlinarith
    linarith
  have hlin : IntervalIntegrable (fun z : ℝ => ell * z) volume 0 (a / ell) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [heq, intervalIntegral.integral_sub (f := fun _ : ℝ => a) intervalIntegrable_const hlin,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, smul_eq_mul]
  field_simp
  ring

/-- Any endpoint beyond the crossing gives exactly the same triangular area. -/
theorem fibreReward_integral (a ell η : ℝ) (ha : 0 ≤ a) (hell : 0 < ell)
    (hη : a / ell ≤ η) :
    (∫ z in (0 : ℝ)..η, fibreReward a ell z) = a ^ 2 / (2 * ell) := by
  have htail : (∫ z in (a / ell)..η, fibreReward a ell z) = 0 := by
    calc
      _ = ∫ z in (a / ell)..η, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hη
        intro z hz
        unfold fibreReward
        apply max_eq_right
        have hh := (div_le_iff₀ hell).mp hz.1.le
        nlinarith
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((continuous_fibreReward a ell).intervalIntegrable (μ := volume) (a := 0) (b := a / ell))
    ((continuous_fibreReward a ell).intervalIntegrable (μ := volume) (a := a / ell) (b := η))
  rw [fibreReward_integral_to_crossing a ell ha hell, htail, add_zero] at h
  exact h.symm

/-- Exact half-line fibre integral, with vanishing beyond the crossing proved. -/
theorem fibreReward_halfline_integral (a ell : ℝ) (ha : 0 ≤ a) (hell : 0 < ell) :
    (∫ z in Ioi (0 : ℝ), fibreReward a ell z) = a ^ 2 / (2 * ell) := by
  have hc : 0 ≤ a / ell := div_nonneg ha hell.le
  have hset : Ioc (0 : ℝ) (a / ell) ∪ Ioi (a / ell) = Ioi (0 : ℝ) := by
    ext z
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hc.trans_lt h
    · intro h
      by_cases hz : z ≤ a / ell
      · exact Or.inl ⟨h, hz⟩
      · exact Or.inr (lt_of_not_ge hz)
  rw [← hset, integral_union_eq_left_of_forall measurableSet_Ioi]
  · rw [← intervalIntegral.integral_of_le hc]
    exact fibreReward_integral_to_crossing a ell ha hell
  · intro z hz
    unfold fibreReward
    apply max_eq_right
    have hh := (div_le_iff₀ hell).mp hz.le
    nlinarith

/-- Positive part is 1-Lipschitz in the reward height. -/
theorem fibreReward_height_lipschitz (a b ell z : ℝ) :
    |fibreReward a ell z - fibreReward b ell z| ≤ |a - b| := by
  simpa only [fibreReward, sub_sub_sub_cancel_right] using
    abs_max_sub_max_le_abs (a - ell * z) (b - ell * z) 0

/-- Actual unweighted normal-fibre replacement error. The normal variation
bound is a sufficient consequence of a Lipschitz bound on the forcing. -/
theorem fibre_lipschitz_replacement (u : ℝ → ℝ) (θ M ell η : ℝ)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hu : ContinuousOn u (Icc 0 η))
    (hlip : ∀ z ∈ Icc 0 η, |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..η, fibreReward (θ * u z) ell z) -
      (∫ z in (0 : ℝ)..η, fibreReward (θ * u 0) ell z)| ≤ θ * M * η ^ 2 / 2 := by
  have hiu : IntervalIntegrable (fun z => fibreReward (θ * u z) ell z) volume 0 η := by
    apply ContinuousOn.intervalIntegrable_of_Icc hη
    unfold fibreReward
    exact ((continuousOn_const.mul hu).sub (continuousOn_const.mul continuousOn_id)).sup continuousOn_const
  have hic := (continuous_fibreReward (θ * u 0) ell).intervalIntegrable (μ := volume) (a := 0) (b := η)
  rw [← intervalIntegral.integral_sub hiu hic]
  have hb : ∀ᵐ z ∂volume, z ∈ Ioc (0 : ℝ) η →
      ‖fibreReward (θ * u z) ell z - fibreReward (θ * u 0) ell z‖ ≤ θ * M * z := by
    filter_upwards [] with z hz
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |θ * u z - θ * u 0| := fibreReward_height_lipschitz _ _ _ _
      _ = θ * |u z - u 0| := by rw [← mul_sub, abs_mul, abs_of_nonneg hθ]
      _ ≤ θ * (M * z) := mul_le_mul_of_nonneg_left (hlip z ⟨hz.1.le, hz.2⟩) hθ
      _ = _ := by ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le hη hb
    ((continuous_const.mul continuous_id).intervalIntegrable (μ := volume) (a := 0) (b := η))
  rw [intervalIntegral.integral_const_mul, integral_id] at hh
  simpa only [Real.norm_eq_abs, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_div_assoc] using hh

/-- The exact Gaussian normal-density ratio, retaining the affine offset. -/
theorem gaussian_density_shift (a z : ℝ) :
    gaussianPDFReal 0 1 (a + z) = gaussianPDFReal 0 1 a * Real.exp (-a * z - z ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A local relative density bound with explicit constants and no dependence
on the ambient dimension of the containing Gaussian space. -/
theorem gaussian_density_relative_error (a z η : ℝ)
    (hz : 0 ≤ z) (hzη : z ≤ η) (hη : η ≤ 1)
    (hsmall : (1 + |a|) * η ≤ 1 / 2) :
    |gaussianPDFReal 0 1 (a + z) - gaussianPDFReal 0 1 a| ≤
      2 * gaussianPDFReal 0 1 a * (1 + |a|) * z := by
  have hbound : |-a * z - z ^ 2 / 2| ≤ (1 + |a|) * z := by
    calc
      _ ≤ |-a * z| + |z ^ 2 / 2| := abs_sub _ _
      _ = |a| * z + z ^ 2 / 2 := by
        rw [abs_mul, abs_neg, abs_of_nonneg hz, abs_of_nonneg (by positivity : 0 ≤ z ^ 2 / 2)]
      _ ≤ _ := by nlinarith [mul_nonneg hz (sub_nonneg.mpr (hzη.trans hη))]
  have hexp : |-a * z - z ^ 2 / 2| ≤ 1 := by
    have hh : (1 + |a|) * z ≤ (1 + |a|) * η :=
      mul_le_mul_of_nonneg_left hzη (by positivity)
    linarith
  have heq : gaussianPDFReal 0 1 (a + z) - gaussianPDFReal 0 1 a =
      gaussianPDFReal 0 1 a * (Real.exp (-a * z - z ^ 2 / 2) - 1) := by
    rw [gaussian_density_shift]
    ring
  rw [heq, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 a)]
  calc
    _ ≤ gaussianPDFReal 0 1 a * (2 * |-a * z - z ^ 2 / 2|) :=
      mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hexp) (gaussianPDFReal_nonneg 0 1 a)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hbound (gaussianPDFReal_nonneg 0 1 a)
      nlinarith only [hh]



/-- Replacing the boundary value of a normally Lipschitz forcing under an
actual bounded, nonnegative density. -/
theorem weighted_fibre_lipschitz_replacement (u w : ℝ → ℝ) (θ M ell η D : ℝ)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hD : 0 ≤ D)
    (hu : ContinuousOn u (Icc 0 η)) (hw : ContinuousOn w (Icc 0 η))
    (hwb : ∀ z ∈ Icc 0 η, 0 ≤ w z ∧ w z ≤ D)
    (hlip : ∀ z ∈ Icc 0 η, |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..η, w z * fibreReward (θ * u z) ell z) -
      (∫ z in (0 : ℝ)..η, w z * fibreReward (θ * u 0) ell z)| ≤
      D * θ * M * η ^ 2 / 2 := by
  have hcu : ContinuousOn (fun z => fibreReward (θ * u z) ell z) (Icc 0 η) := by
    unfold fibreReward
    exact ((continuousOn_const.mul hu).sub
      (continuousOn_const.mul continuousOn_id)).sup continuousOn_const
  have hiu : IntervalIntegrable (fun z => w z * fibreReward (θ * u z) ell z) volume 0 η :=
    (hw.mul hcu).intervalIntegrable_of_Icc hη
  have hic : IntervalIntegrable (fun z => w z * fibreReward (θ * u 0) ell z) volume 0 η :=
    (hw.mul (continuous_fibreReward (θ * u 0) ell).continuousOn).intervalIntegrable_of_Icc hη
  rw [← intervalIntegral.integral_sub hiu hic]
  have hb : ∀ᵐ z ∂volume, z ∈ Ioc (0 : ℝ) η →
      ‖w z * fibreReward (θ * u z) ell z - w z * fibreReward (θ * u 0) ell z‖ ≤
      (D * θ * M) * z := by
    filter_upwards [] with z hz
    have hzi : z ∈ Icc 0 η := ⟨hz.1.le, hz.2⟩
    have hr : |fibreReward (θ * u z) ell z - fibreReward (θ * u 0) ell z| ≤ θ * M * z := by
      calc
        _ ≤ |θ * u z - θ * u 0| := fibreReward_height_lipschitz _ _ _ _
        _ = θ * |u z - u 0| := by rw [← mul_sub, abs_mul, abs_of_nonneg hθ]
        _ ≤ θ * (M * z) := mul_le_mul_of_nonneg_left (hlip z hzi) hθ
        _ = _ := by ring
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hwb z hzi).1]
    calc
      _ ≤ D * (θ * M * z) := mul_le_mul (hwb z hzi).2 hr (abs_nonneg _) hD
      _ = _ := by ring
  have hmajor : IntervalIntegrable (fun z : ℝ => (D * θ * M) * z) volume 0 η :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le hη hb hmajor
  rw [intervalIntegral.integral_const_mul, integral_id] at hh
  simpa only [Real.norm_eq_abs, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_div_assoc] using hh

/-- Freezing a continuous density at a boundary value, with the triangular
fibre integral evaluated rather than assumed. -/
theorem fibre_density_freezing (w : ℝ → ℝ) (a ell η c δ : ℝ)
    (ha : 0 ≤ a) (hell : 0 < ell) (hcross : a / ell ≤ η)
    (hw : ContinuousOn w (Icc 0 η))
    (hvariation : ∀ z ∈ Icc 0 η, |w z - c| ≤ δ) :
    |(∫ z in (0 : ℝ)..η, w z * fibreReward a ell z) -
      c * (a ^ 2 / (2 * ell))| ≤ δ * (a ^ 2 / (2 * ell)) := by
  have hη : 0 ≤ η := (div_nonneg ha hell.le).trans hcross
  have hc := (continuous_fibreReward a ell).intervalIntegrable (μ := volume) 0 η
  have hiw : IntervalIntegrable (fun z => w z * fibreReward a ell z) volume 0 η :=
    (hw.mul (continuous_fibreReward a ell).continuousOn).intervalIntegrable_of_Icc hη
  have hid : (∫ z in (0 : ℝ)..η, w z * fibreReward a ell z) -
      c * (a ^ 2 / (2 * ell)) =
      ∫ z in (0 : ℝ)..η, (w z - c) * fibreReward a ell z := by
    rw [← fibreReward_integral a ell η ha hell hcross,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hiw (hc.const_mul c)]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  rw [hid]
  have hb : ∀ᵐ z ∂volume, z ∈ Ioc (0 : ℝ) η →
      ‖(w z - c) * fibreReward a ell z‖ ≤ δ * fibreReward a ell z := by
    filter_upwards [] with z hz
    have hr : 0 ≤ fibreReward a ell z := le_max_right _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_right (hvariation z ⟨hz.1.le, hz.2⟩) hr
  have hh := intervalIntegral.norm_integral_le_of_norm_le hη hb (hc.const_mul δ)
  rw [intervalIntegral.integral_const_mul, fibreReward_integral a ell η ha hell hcross] at hh
  simpa only [Real.norm_eq_abs] using hh

/-- On the good normal tube the shifted Gaussian density is at most twice
its boundary density. -/
theorem gaussian_density_le_twice (a z η : ℝ) (hz : 0 ≤ z) (hzη : z ≤ η)
    (hη : η ≤ 1) (hsmall : (1 + |a|) * η ≤ 1 / 2) :
    gaussianPDFReal 0 1 (a + z) ≤ 2 * gaussianPDFReal 0 1 a := by
  have hh := gaussian_density_relative_error a z η hz hzη hη hsmall
  have hp := gaussianPDFReal_nonneg 0 1 a
  have hs := mul_le_mul_of_nonneg_left hzη (show 0 ≤ 1 + |a| by positivity)
  have hs' : (1 + |a|) * z ≤ 1 / 2 := hs.trans hsmall
  have hmul := mul_le_mul_of_nonneg_left hs' hp
  have hab := le_abs_self (gaussianPDFReal 0 1 (a + z) - gaussianPDFReal 0 1 a)
  nlinarith only [hh, hmul, hab]

/-- The Gaussian good-fibre error, with the leading boundary term explicit.
The two error terms are cubic after the audited choice η = θ M / ell.
No dimension, facet-count, or global cap estimate occurs as a hypothesis. -/
theorem gaussian_good_fibre_error (u : ℝ → ℝ) (a θ M ell η : ℝ)
    (hθ : 0 ≤ θ) (hu0 : 0 ≤ u 0) (hell : 0 < ell) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (hsmall : (1 + |a|) * η ≤ 1 / 2)
    (hcross : θ * u 0 / ell ≤ η)
    (hu : ContinuousOn u (Icc 0 η))
    (hlip : ∀ z ∈ Icc 0 η, |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..η, gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) -
      gaussianPDFReal 0 1 a * ((θ * u 0) ^ 2 / (2 * ell))| ≤
      gaussianPDFReal 0 1 a * θ * M * η ^ 2 +
        gaussianPDFReal 0 1 a * (1 + |a|) * η * (θ * u 0) ^ 2 / ell := by
  have hp := gaussianPDFReal_nonneg 0 1 a
  have hw : ContinuousOn (fun z : ℝ => gaussianPDFReal 0 1 (a + z)) (Icc 0 η) := by
    apply Continuous.continuousOn
    unfold gaussianPDFReal
    fun_prop
  have hwb : ∀ z ∈ Icc 0 η, 0 ≤ gaussianPDFReal 0 1 (a + z) ∧
      gaussianPDFReal 0 1 (a + z) ≤ 2 * gaussianPDFReal 0 1 a := by
    intro z hz
    exact ⟨gaussianPDFReal_nonneg _ _ _, gaussian_density_le_twice a z η hz.1 hz.2 hη1 hsmall⟩
  have hv : ∀ z ∈ Icc 0 η, |gaussianPDFReal 0 1 (a + z) - gaussianPDFReal 0 1 a| ≤
      2 * gaussianPDFReal 0 1 a * (1 + |a|) * η := by
    intro z hz
    exact (gaussian_density_relative_error a z η hz.1 hz.2 hη1 hsmall).trans
      (mul_le_mul_of_nonneg_left hz.2 (by positivity))
  have hrep := weighted_fibre_lipschitz_replacement u (fun z => gaussianPDFReal 0 1 (a + z))
    θ M ell η (2 * gaussianPDFReal 0 1 a) hθ hη0 (by positivity) hu hw hwb hlip
  have hfreeze := fibre_density_freezing (fun z => gaussianPDFReal 0 1 (a + z))
    (θ * u 0) ell η (gaussianPDFReal 0 1 a)
    (2 * gaussianPDFReal 0 1 a * (1 + |a|) * η) (mul_nonneg hθ hu0) hell hcross hw hv
  have htriangle := abs_sub_le
    (∫ z in (0 : ℝ)..η, gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z)
    (∫ z in (0 : ℝ)..η, gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u 0) ell z)
    (gaussianPDFReal 0 1 a * ((θ * u 0) ^ 2 / (2 * ell)))
  have hrhs : (2 * gaussianPDFReal 0 1 a) * θ * M * η ^ 2 / 2 +
      (2 * gaussianPDFReal 0 1 a * (1 + |a|) * η) * ((θ * u 0) ^ 2 / (2 * ell)) =
      gaussianPDFReal 0 1 a * θ * M * η ^ 2 +
        gaussianPDFReal 0 1 a * (1 + |a|) * η * (θ * u 0) ^ 2 / ell := by ring
  exact (htriangle.trans (add_le_add hrep hfreeze)).trans_eq hrhs



/-- The short-fibre error is genuinely cubic at η = θ M / ell, uniformly down
to θ = 0. The normal Lipschitz constant and boundary height share the same cutoff M. -/
theorem gaussian_good_fibre_cubic (u : ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hu0 : 0 ≤ u 0) (huM : u 0 ≤ M) (hell : 0 < ell)
    (hη1 : θ * M / ell ≤ 1) (hsmall : (1 + |a|) * (θ * M / ell) ≤ 1 / 2)
    (hu : ContinuousOn u (Icc 0 (θ * M / ell)))
    (hlip : ∀ z ∈ Icc 0 (θ * M / ell), |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..(θ * M / ell), gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) -
      gaussianPDFReal 0 1 a * ((θ * u 0) ^ 2 / (2 * ell))| ≤
      gaussianPDFReal 0 1 a * (2 + |a|) * θ ^ 3 * M ^ 3 / ell ^ 2 := by
  have hη0 : 0 ≤ θ * M / ell := div_nonneg (mul_nonneg hθ hM) hell.le
  have hcross : θ * u 0 / ell ≤ θ * M / ell :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left huM hθ) hell.le
  have hh := gaussian_good_fibre_error u a θ M ell (θ * M / ell)
    hθ hu0 hell hη0 hη1 hsmall hcross hu hlip
  have hsquare : (θ * u 0) ^ 2 ≤ (θ * M) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hθ hu0) (mul_le_mul_of_nonneg_left huM hθ) 2
  have hp := gaussianPDFReal_nonneg 0 1 a
  have hterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ gaussianPDFReal 0 1 a * (1 + |a|) * (θ * M / ell) by positivity)) hell.le
  calc
    _ ≤ gaussianPDFReal 0 1 a * θ * M * (θ * M / ell) ^ 2 +
        gaussianPDFReal 0 1 a * (1 + |a|) * (θ * M / ell) * (θ * u 0) ^ 2 / ell := hh
    _ ≤ gaussianPDFReal 0 1 a * θ * M * (θ * M / ell) ^ 2 +
        gaussianPDFReal 0 1 a * (1 + |a|) * (θ * M / ell) * (θ * M) ^ 2 / ell :=
      add_le_add le_rfl hterm
    _ = _ := by ring

/-- The cutoff radius follows from a normal supremum bound, rather than from
an arbitrary truncation of the switching reward. -/
theorem fibreReward_zero_past_cutoff (u : ℝ → ℝ) (θ M ell z : ℝ)
    (hθ : 0 ≤ θ) (hell : 0 < ell) (hu : u z ≤ M) (hz : θ * M / ell ≤ z) :
    fibreReward (θ * u z) ell z = 0 := by
  apply max_eq_right
  have hh := (div_le_iff₀ hell).mp hz
  have hbound := mul_le_mul_of_nonneg_left hu hθ
  nlinarith only [hh, hbound]

/-- The bad-set contribution to the first moment is controlled by the actual
L32 moment. This is a tail estimate, not an Lq-only global switching-cap claim. -/
theorem bad_set_first_moment_from_L32 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (W : X → ℝ) (M : ℝ) (hM : 0 < M)
    (hW : MemLp W 32 μ) (hW0 : ∀ x, 0 ≤ W x) :
    (∫ x in {x | M < W x}, W x ∂μ) ≤ (M ^ 31)⁻¹ * ∫ x, W x ^ 32 ∂μ := by
  have hi : Integrable W μ := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 32) hW
  have hip : Integrable (fun x => W x ^ 32) μ := by
    have hh : Integrable (fun x => ‖W x‖ ^ 32) μ := hW.integrable_norm_pow'
    exact hh.congr (Filter.Eventually.of_forall fun x => by
      change ‖W x‖ ^ 32 = W x ^ 32
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 x)])
  have hs : NullMeasurableSet {x | M < W x} μ :=
    nullMeasurableSet_lt aemeasurable_const hW.aestronglyMeasurable.aemeasurable
  have hbound : ∀ x ∈ {x | M < W x}, W x ≤ (M ^ 31)⁻¹ * W x ^ 32 := by
    intro x hx
    have hp : M ^ 31 ≤ W x ^ 31 := pow_le_pow_left₀ hM.le hx.le 31
    have hh := mul_le_mul_of_nonneg_left hp (hW0 x)
    have hmp : 0 < M ^ 31 := pow_pos hM _
    rw [mul_comm ((M ^ 31)⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ hmp).mpr
    calc
      _ ≤ W x * W x ^ 31 := hh
      _ = W x ^ 32 := by ring
  have hmono := setIntegral_mono_on₀ hi.integrableOn (hip.const_mul ((M ^ 31)⁻¹)).integrableOn hs hbound
  have htotal : (∫ x in {x | M < W x}, (M ^ 31)⁻¹ * W x ^ 32 ∂μ) ≤
      ∫ x, (M ^ 31)⁻¹ * W x ^ 32 ∂μ :=
    setIntegral_le_integral (hip.const_mul ((M ^ 31)⁻¹))
    (Filter.Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr (pow_nonneg hM.le _))
      (pow_nonneg (hW0 x) _))
  exact hmono.trans (by simpa only [integral_const_mul] using htotal)



/-- Fractional reassignment earns at most the positive switching reward;
this is valid for every fractional weight, including the endpoints. -/
theorem fractional_gain_le_fibreReward (p a ell z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (a - ell * z) ≤ fibreReward a ell z := by
  unfold fibreReward
  by_cases hs : 0 ≤ a - ell * z
  · rw [max_eq_left hs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hs
  · rw [max_eq_right (le_of_not_ge hs)]
    exact mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_not_ge hs)

/-- Along a nonnegative normal coordinate, only the positive boundary height
can contribute to the switching reward. -/
theorem fibreReward_positive_height (a ell z : ℝ) (hell : 0 ≤ ell) (hz : 0 ≤ z) :
    fibreReward a ell z = fibreReward (max a 0) ell z := by
  unfold fibreReward
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hc := mul_nonneg hell hz
    rw [max_eq_right ha', max_eq_right (by linarith : a - ell * z ≤ 0),
      max_eq_right (by linarith : 0 - ell * z ≤ 0)]

/-- Signed forcing is permitted: the leading fibre energy uses the positive
part of its boundary value, while normal Lipschitz control is preserved. -/
theorem gaussian_good_fibre_signed_cubic (u : ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (huM : u 0 ≤ M) (hell : 0 < ell)
    (hη1 : θ * M / ell ≤ 1) (hsmall : (1 + |a|) * (θ * M / ell) ≤ 1 / 2)
    (hu : ContinuousOn u (Icc 0 (θ * M / ell)))
    (hlip : ∀ z ∈ Icc 0 (θ * M / ell), |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..(θ * M / ell), gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) -
      gaussianPDFReal 0 1 a * ((θ * max (u 0) 0) ^ 2 / (2 * ell))| ≤
      gaussianPDFReal 0 1 a * (2 + |a|) * θ ^ 3 * M ^ 3 / ell ^ 2 := by
  have hη0 : 0 ≤ θ * M / ell := div_nonneg (mul_nonneg hθ hM) hell.le
  have huplus : ContinuousOn (fun z => max (u z) 0) (Icc 0 (θ * M / ell)) :=
    hu.sup continuousOn_const
  have hlipplus : ∀ z ∈ Icc 0 (θ * M / ell),
      |max (u z) 0 - max (u 0) 0| ≤ M * z := by
    intro z hz
    exact (abs_max_sub_max_le_abs (u z) (u 0) 0).trans (hlip z hz)
  have hh := gaussian_good_fibre_cubic (fun z => max (u z) 0) a θ M ell
    hθ hM (le_max_right _ _) (max_le huM hM) hell hη1 hsmall huplus hlipplus
  have heq : (∫ z in (0 : ℝ)..(θ * M / ell), gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) =
      ∫ z in (0 : ℝ)..(θ * M / ell), gaussianPDFReal 0 1 (a + z) * fibreReward (θ * max (u z) 0) ell z := by
    apply intervalIntegral.integral_congr_Ioo_of_le hη0
    intro z hz
    dsimp only
    rw [fibreReward_positive_height (θ * u z) ell z hell.le hz.1.le]
    have hm : θ * max (u z) 0 = max (θ * u z) 0 := by
      rw [mul_max_of_nonneg _ _ hθ, mul_zero]
    rw [hm]
  rw [heq]
  exact hh

/-- A normal supremum bound makes the short-fibre cutoff exact on the full
unit normal tube. This is the good-fibre estimate used before facet integration. -/
theorem gaussian_unit_fibre_cubic (u : ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hell : 0 < ell)
    (hη1 : θ * M / ell ≤ 1) (hsmall : (1 + |a|) * (θ * M / ell) ≤ 1 / 2)
    (hu : ContinuousOn u (Icc 0 1))
    (hsup : ∀ z ∈ Icc 0 1, u z ≤ M)
    (hlip : ∀ z ∈ Icc 0 (θ * M / ell), |u z - u 0| ≤ M * z) :
    |(∫ z in (0 : ℝ)..1, gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) -
      gaussianPDFReal 0 1 a * ((θ * max (u 0) 0) ^ 2 / (2 * ell))| ≤
      gaussianPDFReal 0 1 a * (2 + |a|) * θ ^ 3 * M ^ 3 / ell ^ 2 := by
  let F : ℝ → ℝ := fun z => gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z
  have hη0 : 0 ≤ θ * M / ell := div_nonneg (mul_nonneg hθ hM) hell.le
  have hcf : ContinuousOn F (Icc 0 1) := by
    have hw : ContinuousOn (fun z : ℝ => gaussianPDFReal 0 1 (a + z)) (Icc 0 1) := by
      apply Continuous.continuousOn
      unfold gaussianPDFReal
      fun_prop
    exact hw.mul (((continuousOn_const.mul hu).sub
      (continuousOn_const.mul continuousOn_id)).sup continuousOn_const)
  have hshort : IntervalIntegrable F volume 0 (θ * M / ell) :=
    (hcf.mono (fun z hz => ⟨hz.1, hz.2.trans hη1⟩)).intervalIntegrable_of_Icc hη0
  have htail : IntervalIntegrable F volume (θ * M / ell) 1 :=
    (hcf.mono (fun z hz => ⟨hη0.trans hz.1, hz.2⟩)).intervalIntegrable_of_Icc hη1
  have hzero : (∫ z in (θ * M / ell)..1, F z) = 0 := by
    calc
      _ = ∫ z in (θ * M / ell)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hη1
        intro z hz
        have hcut := fibreReward_zero_past_cutoff u θ M ell z hθ hell
          (hsup z ⟨hη0.trans hz.1.le, hz.2.le⟩) hz.1.le
        simp only [F, hcut, mul_zero]
      _ = 0 := by simp
  have hunit := intervalIntegral.integral_add_adjacent_intervals hshort htail
  rw [hzero, add_zero] at hunit
  change |(∫ z in (0 : ℝ)..1, F z) - _| ≤ _
  rw [← hunit]
  exact gaussian_good_fibre_signed_cubic u a θ M ell hθ hM (hsup 0 ⟨le_rfl, by norm_num⟩)
    hell hη1 hsmall (hu.mono (fun z hz => ⟨hz.1, hz.2.trans hη1⟩)) hlip



/-- On a bad fibre one uses the linear normal-supremum bound. Gaussian mass
normalization makes its constant independent of the affine offset. -/
theorem gaussian_unit_fibre_le_supremum (u : ℝ → ℝ) (a θ W ell : ℝ)
    (hθ : 0 ≤ θ) (hW : 0 ≤ W) (hell : 0 ≤ ell)
    (hu : ContinuousOn u (Icc 0 1)) (hsup : ∀ z ∈ Icc 0 1, u z ≤ W) :
    (∫ z in (0 : ℝ)..1, gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) ≤ θ * W := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hiphi : Integrable (fun z : ℝ => gaussianPDFReal 0 1 (a + z)) volume :=
    (integrable_gaussianPDFReal 0 1).comp_add_left a
  have himajor : IntervalIntegrable (fun z : ℝ => gaussianPDFReal 0 1 (a + z) * (θ * W)) volume 0 1 :=
    (hiphi.mul_const (θ * W)).intervalIntegrable
  have hw : ContinuousOn (fun z : ℝ => gaussianPDFReal 0 1 (a + z)) (Icc 0 1) := by
    apply Continuous.continuousOn
    unfold gaussianPDFReal
    fun_prop
  have hif : IntervalIntegrable (fun z => gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z) volume 0 1 := by
    exact (hw.mul (((continuousOn_const.mul hu).sub
      (continuousOn_const.mul continuousOn_id)).sup continuousOn_const)).intervalIntegrable_of_Icc h01
  have hbound : ∀ z ∈ Icc (0 : ℝ) 1,
      gaussianPDFReal 0 1 (a + z) * fibreReward (θ * u z) ell z ≤
      gaussianPDFReal 0 1 (a + z) * (θ * W) := by
    intro z hz
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
    apply max_le
    · have hh := mul_le_mul_of_nonneg_left (hsup z hz) hθ
      have hc := mul_nonneg hell hz.1
      linarith
    · exact mul_nonneg hθ hW
  have hmass : (∫ z in (0 : ℝ)..1, gaussianPDFReal 0 1 (a + z)) ≤ 1 := by
    rw [intervalIntegral.integral_of_le h01]
    have hh := setIntegral_le_integral (s := Ioc (0 : ℝ) 1) hiphi
      (Filter.Eventually.of_forall fun z => gaussianPDFReal_nonneg 0 1 (a + z))
    rw [integral_add_left_eq_self (μ := volume) (gaussianPDFReal 0 1) a, integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)] at hh
    exact hh
  calc
    _ ≤ ∫ z in (0 : ℝ)..1, gaussianPDFReal 0 1 (a + z) * (θ * W) :=
      intervalIntegral.integral_mono_on h01 hif himajor hbound
    _ = (∫ z in (0 : ℝ)..1, gaussianPDFReal 0 1 (a + z)) * (θ * W) :=
      intervalIntegral.integral_mul_const (θ * W) _
    _ ≤ 1 * (θ * W) := mul_le_mul_of_nonneg_right hmass (mul_nonneg hθ hW)
    _ = _ := one_mul _

/-- Actual iterated Gaussian-fibre contribution over the bad normal-supremum
set. Its measurability is explicit; integrability and the θ M⁻³¹ bound follow
from the L32 hypothesis and the just-proved normal-fibre estimate. -/
theorem bad_fibre_cap_from_L32 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (u : X → ℝ → ℝ) (a W : X → ℝ)
    (θ M ell : ℝ) (hθ : 0 ≤ θ) (hM : 0 < M) (hell : 0 ≤ ell)
    (hW : MemLp W 32 μ) (hW0 : ∀ x, 0 ≤ W x)
    (hu : ∀ x, ContinuousOn (u x) (Icc 0 1))
    (hsup : ∀ x z, z ∈ Icc 0 1 → u x z ≤ W x)
    (hmeas : AEStronglyMeasurable
      (fun x => ∫ z in (0 : ℝ)..1,
        gaussianPDFReal 0 1 (a x + z) * fibreReward (θ * u x z) ell z) μ) :
    (∫ x in {x | M < W x}, (∫ z in (0 : ℝ)..1,
      gaussianPDFReal 0 1 (a x + z) * fibreReward (θ * u x z) ell z) ∂μ) ≤
      θ * ((M ^ 31)⁻¹ * ∫ x, W x ^ 32 ∂μ) := by
  let F : X → ℝ := fun x => ∫ z in (0 : ℝ)..1,
    gaussianPDFReal 0 1 (a x + z) * fibreReward (θ * u x z) ell z
  have hnonneg : ∀ x, 0 ≤ F x := by
    intro x
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
    intro z
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (le_max_right _ _)
  have hbound : ∀ x, F x ≤ θ * W x := by
    intro x
    exact gaussian_unit_fibre_le_supremum (u x) (a x) θ (W x) ell hθ (hW0 x) hell (hu x) (hsup x)
  have hiW : Integrable W μ := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 32) hW
  have hiF : Integrable F μ := (hiW.const_mul θ).mono' hmeas
    (Filter.Eventually.of_forall fun x => by
      change ‖F x‖ ≤ θ * W x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
      exact hbound x)
  have hs : NullMeasurableSet {x | M < W x} μ :=
    nullMeasurableSet_lt aemeasurable_const hW.aestronglyMeasurable.aemeasurable
  have hmono := setIntegral_mono_on₀ hiF.integrableOn (hiW.const_mul θ).integrableOn hs
    (fun x _ => hbound x)
  change (∫ x in {x | M < W x}, F x ∂μ) ≤ _
  calc
    _ ≤ ∫ x in {x | M < W x}, θ * W x ∂μ := hmono
    _ = θ * ∫ x in {x | M < W x}, W x ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (bad_set_first_moment_from_L32 μ W M hM hW hW0) hθ

end NegativeVotingSmallCap
