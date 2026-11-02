import GaussianSwitchingTinyScale

/-! A finite-Lq positive-reward estimate for the moderate-amplitude argument.
The cost sublevel probability is explicit; it is not a supplied cap bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace NegativeVotingSwitchingLp
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem set_integral_abs_le_lq (F : Set X) (q : ℝ) (hq : 1 ≤ q)
    {v : X → ℝ} (hv : MemLp v (ENNReal.ofReal q) μ) :
    (∫ x in F, |v x| ∂μ) ≤
      (eLpNorm v (ENNReal.ofReal q) μ).toReal * (μ F).toReal^(1-1/q) := by
  have hq0 : 0 ≤ q := by linarith
  have hexp : 0 ≤ 1-q⁻¹ := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1) hq
    norm_num at hh
    linarith
  have hq1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal q := by exact_mod_cast ENNReal.ofReal_le_ofReal hq
  have hv1 : MemLp v 1 (μ.restrict F) := (hv.restrict F).mono_exponent hq1
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq1
    (hv.restrict F).aestronglyMeasurable
  have hb := hh.trans (mul_le_mul'
    (eLpNorm_mono_measure v (Measure.restrict_le_self (μ:=μ) (s:=F))) le_rfl)
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal hq0,
    Measure.restrict_apply_univ, one_div] at hb
  have hfin : eLpNorm v (ENNReal.ofReal q) μ * μ F^(1-q⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top hv.eLpNorm_ne_top
      (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hexp (measure_ne_top μ F)))
  have hr := ENNReal.toReal_mono hfin hb
  have he := hv1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs] at he
  rw [he, ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
  simpa only [one_div] using hr

theorem integral_abs_rpow_eq_norm (q : ℝ) (hq : 0 < q)
    {v : X → ℝ} (hv : MemLp v (ENNReal.ofReal q) μ) :
    (∫ x, |v x|^q ∂μ) = (eLpNorm v (ENNReal.ofReal q) μ).toReal^q := by
  have he := hv.eLpNorm_eq_integral_rpow_norm
    (by positivity) ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] at he
  rw [he, ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _),
    ← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _),
    inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]

theorem reward_far_rpow (v c a q : ℝ) (ha : 0 < a) (hq : 1 ≤ q) (hc : a ≤ c) :
    max (v-c) 0 ≤ |v|^q / a^(q-1) := by
  by_cases hv : v ≤ c
  · rw [max_eq_right (sub_nonpos.mpr hv)]
    positivity
  · have hv0 : 0 < v := ha.trans_le (hc.trans (lt_of_not_ge hv).le)
    have hav : a ≤ |v| := by rw [abs_of_pos hv0]; exact hc.trans (lt_of_not_ge hv).le
    have hp := Real.rpow_le_rpow ha.le hav (sub_nonneg.mpr hq)
    have hid : |v| * |v|^(q-1) = |v|^q := by
      have hh := Real.rpow_add (abs_pos.mpr (ne_of_gt hv0)) (1:ℝ) (q-1)
      rw [Real.rpow_one, show (1:ℝ)+(q-1)=q by ring] at hh
      exact hh.symm
    have hm : |v| ≤ |v|^q / a^(q-1) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr
      simpa only [hid] using mul_le_mul_of_nonneg_left hp (abs_nonneg v)
    exact (max_le (by linarith [le_abs_self v]) (abs_nonneg v)).trans hm

/-- Split at a genuine positive cost cutoff.  The near contribution uses
restriction Holder and the far contribution uses the same actual Lq moment. -/
theorem integral_reward_cutoff (v c : X → ℝ) (q a : ℝ) (hq : 1 ≤ q) (ha : 0 < a)
    (hv : MemLp v (ENNReal.ofReal q) μ) (hcM : Measurable c) (hc : ∀ x, 0 ≤ c x) :
    (∫ x, max (v x-c x) 0 ∂μ) ≤
      (eLpNorm v (ENNReal.ofReal q) μ).toReal *
        (μ {x | c x ≤ a}).toReal^(1-1/q) +
      (eLpNorm v (ENNReal.ofReal q) μ).toReal^q / a^(q-1) := by
  let F := {x | c x ≤ a}
  have hF : MeasurableSet F := measurableSet_le hcM measurable_const
  have hq0 : 0 < q := by linarith
  have hq1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal q := by exact_mod_cast ENNReal.ofReal_le_ofReal hq
  have hi : Integrable (fun x => |v x|) μ := by
    simpa only [Real.norm_eq_abs] using (hv.integrable hq1).norm
  have hip : Integrable (fun x => |v x|^q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using hv.integrable_norm_rpow'
  have hrM : AEStronglyMeasurable (fun x => max (v x-c x) 0) μ :=
    (hv.aestronglyMeasurable.sub hcM.aestronglyMeasurable).sup aestronglyMeasurable_const
  have hr : Integrable (fun x => max (v x-c x) 0) μ := by
    apply hi.mono' hrM
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self (v x),hc x]) (abs_nonneg _)
  have hp (x : X) : max (v x-c x) 0 ≤ F.indicator (fun y => |v y|) x +
      |v x|^q / a^(q-1) := by
    by_cases hx : x ∈ F
    · rw [Set.indicator_of_mem hx]
      have hb : max (v x-c x) 0 ≤ |v x| :=
        max_le (by linarith [le_abs_self (v x),hc x]) (abs_nonneg _)
      exact hb.trans (le_add_of_nonneg_right (by positivity))
    · rw [Set.indicator_of_notMem hx,zero_add]
      exact reward_far_rpow _ _ _ _ ha hq (le_of_lt (lt_of_not_ge hx))
  have hb := integral_mono hr ((hi.indicator hF).add (hip.div_const _)) hp
  simp only [Pi.add_apply] at hb
  rw [integral_add (hi.indicator hF) (hip.div_const _), integral_indicator hF,
    integral_div, integral_abs_rpow_eq_norm q hq0 hv] at hb
  exact hb.trans (add_le_add (set_integral_abs_le_lq F q hq hv) le_rfl)

/-- A linear sublevel-measure estimate is sufficient.  No smoothness of the
perturbation or interface of its maximizer is assumed. -/
theorem integral_reward_cutoff_of_sublevel (v c : X → ℝ) (q a C W : ℝ)
    (hq : 1 ≤ q) (ha : 0 < a) (_hC : 0 ≤ C) (hW : 0 ≤ W)
    (hv : MemLp v (ENNReal.ofReal q) μ) (hcM : Measurable c) (hc : ∀ x, 0 ≤ c x)
    (hsublevel : (μ {x | c x ≤ a}).toReal ≤ C*a)
    (hnorm : eLpNorm v (ENNReal.ofReal q) μ ≤ ENNReal.ofReal W) :
    (∫ x, max (v x-c x) 0 ∂μ) ≤ W*(C*a)^(1-1/q) + W^q/a^(q-1) := by
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal hW] at hn
  have he : 0 ≤ 1-1/q := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1) hq
    norm_num at hh
    simpa only [one_div] using sub_nonneg.mpr hh
  refine (integral_reward_cutoff v c q a hq ha hv hcM hc).trans ?_
  apply add_le_add
  · exact mul_le_mul hn (Real.rpow_le_rpow ENNReal.toReal_nonneg hsublevel he)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _) hW
  · exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hn (by linarith)) (by positivity)

theorem optimal_cutoff_identities (W q : ℝ) (hW : 0 < W) (hq : 1 ≤ q) :
    W*(W^(q/(q+1)))^(1-1/q) = W^(2*q/(q+1)) ∧
    W^q/(W^(q/(q+1)))^(q-1) = W^(2*q/(q+1)) := by
  have hq0 : q ≠ 0 := by linarith
  have hqp : q+1 ≠ 0 := by linarith
  constructor
  · rw [←Real.rpow_mul hW.le]
    have he : (1:ℝ)+q/(q+1)*(1-1/q)=2*q/(q+1) := by field_simp; ring
    simpa only [Real.rpow_one,he] using (Real.rpow_add hW 1 (q/(q+1)*(1-1/q))).symm
  · rw [←Real.rpow_mul hW.le, ←Real.rpow_sub hW]
    congr 1
    field_simp
    ring

/-- The moderate-amplitude scalar estimate, derived by optimizing an actual
cost cutoff.  The same constant works for every q≥2. -/
theorem integral_reward_lq (v c : X → ℝ) (q aStar C W : ℝ)
    (hq : 2 ≤ q) (haStar : 0 < aStar) (hC : 1 ≤ C) (hW : 0 ≤ W)
    (hv : MemLp v (ENNReal.ofReal q) μ) (hcM : Measurable c) (hc : ∀ x, 0 ≤ c x)
    (hsublevel : ∀ a : ℝ, 0 < a → a ≤ aStar → (μ {x | c x ≤ a}).toReal ≤ C*a)
    (hnorm : eLpNorm v (ENNReal.ofReal q) μ ≤ ENNReal.ofReal W) :
    (∫ x, max (v x-c x) 0 ∂μ) ≤
      (C+1)*W^(2*q/(q+1)) + W^q/aStar^(q-1) := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hbeta : 0 ≤ 1-1/q := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1) hq1
    norm_num at hh
    simpa only [one_div] using sub_nonneg.mpr hh
  have hbeta1 : 1-1/q ≤ 1 := by linarith [one_div_nonneg.mpr hq0.le]
  have hCp : C^(1-1/q) ≤ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hC hbeta1
  rcases hW.eq_or_lt with hW | hW
  · subst W
    have hb := integral_reward_cutoff_of_sublevel v c q aStar C 0 hq1 haStar hC0
      le_rfl hv hcM hc (hsublevel aStar haStar le_rfl) hnorm
    have hp : 0 < 2*q/(q+1) := by positivity
    simpa only [zero_mul,Real.zero_rpow (ne_of_gt hq0),
      Real.zero_rpow (ne_of_gt hp),zero_div,add_zero,mul_zero] using hb
  · let a0 := W^(q/(q+1))
    have ha0 : 0 < a0 := Real.rpow_pos_of_pos hW _
    have hides := optimal_cutoff_identities W q hW hq1
    have hnear : W*(C*a0)^(1-1/q) ≤ C*W^(2*q/(q+1)) := by
      rw [Real.mul_rpow hC0 ha0.le]
      calc
        _ = C^(1-1/q)*(W*a0^(1-1/q)) := by ring
        _ = C^(1-1/q)*W^(2*q/(q+1)) := by rw [hides.1]
        _ ≤ _ := mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg hW.le _)
    by_cases hcut : a0 ≤ aStar
    · have hb := integral_reward_cutoff_of_sublevel v c q a0 C W hq1 ha0 hC0
        hW.le hv hcM hc (hsublevel a0 ha0 hcut) hnorm
      rw [hides.2] at hb
      have ht : 0 ≤ W^q/aStar^(q-1) := by positivity
      nlinarith
    · have hb := integral_reward_cutoff_of_sublevel v c q aStar C W hq1 haStar hC0
        hW.le hv hcM hc (hsublevel aStar haStar le_rfl) hnorm
      have ha : W*(C*aStar)^(1-1/q) ≤ W*(C*a0)^(1-1/q) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hC0 haStar.le)
          (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hcut)) hC0) hbeta) hW.le
      have hp : 0 ≤ W^(2*q/(q+1)) := Real.rpow_nonneg hW.le _
      linarith [ha.trans hnear]

end NegativeVotingSwitchingLp
