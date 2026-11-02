import Mathlib

/-! Bounded-density splitting estimates for a genuine finite measure on the line.
The final Gaussian application derives this domination from a fractional union. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace NegativeVotingTwoCell

variable (ν : Measure ℝ) [IsFiniteMeasure ν]

theorem bounded_density_interval (c : ℝ) (hc : 0 ≤ c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) (x y : ℝ) (hxy : x ≤ y) :
    ν.real (Ioc x y) ≤ c*(y-x) := by
  have hh := hdom (Ioc x y)
  have hfin : (ENNReal.ofReal c • volume) (Ioc x y) ≠ ⊤ := by
    simp only [Measure.smul_apply,smul_eq_mul,Real.volume_Ioc]
    finiteness
  have hr := ENNReal.toReal_mono hfin hh
  simpa [Measure.real,Measure.smul_apply,Real.volume_Ioc,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] using hr

theorem bounded_density_cumulative_lipschitz (c : ℝ) (hc : 0 ≤ c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) :
    LipschitzWith c.toNNReal (fun x => ν.real (Iic x)) := by
  have hinc (x y : ℝ) (hxy : x ≤ y) :
      ν.real (Iic y)-ν.real (Iic x) ≤ c*(y-x) := by
    have hs : Iic y \ Iic x = Ioc x y := by
      ext z
      simp only [Set.mem_sdiff,mem_Iic,mem_Ioc,not_le,and_comm]
    rw [← measureReal_sdiff (Iic_subset_Iic.mpr hxy) measurableSet_Iic,hs]
    exact bounded_density_interval ν c hc hdom x y hxy
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ hc]
  by_cases hxy : x ≤ y
  · have hf := measureReal_mono (μ:=ν) (Iic_subset_Iic.mpr hxy)
    simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr hf),neg_sub] using hinc x y hxy
  · have hyx := le_of_not_ge hxy
    have hf := measureReal_mono (μ:=ν) (Iic_subset_Iic.mpr hyx)
    simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr hf)] using hinc y x hyx

/-- A bounded-density finite measure admits every strictly intermediate mass
as a literal half-line cut. No atomlessness or quantile is supplied. -/
theorem bounded_density_threshold (c : ℝ) (hc : 0 ≤ c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) (b : ℝ)
    (hb : 0 < b) (hbP : b < ν.real univ) :
    ∃ t : ℝ, ν.real (Iic t)=b := by
  have hcont := (bounded_density_cumulative_lipschitz ν c hc hdom).continuous
  have hlo : Tendsto (fun t : ℝ => ν.real (Iic t)) atBot (𝓝 0) := by
    simpa [integral_const,Measure.real] using
      (tendsto_integral_Iic_zero (μ:=ν) (f:=fun _ : ℝ => (1:ℝ)) tendsto_id)
  have hhi : Tendsto (fun t : ℝ => ν.real (Iic t)) atTop (𝓝 (ν.real univ)) :=
    (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp (tendsto_measure_Iic_atTop ν)
  obtain ⟨x,hx⟩ := (hlo.eventually (gt_mem_nhds hb)).exists
  obtain ⟨y,hy⟩ := (hhi.eventually (lt_mem_nhds hbP)).exists
  exact intermediate_value_univ x y hcont ⟨hx.le,hy.le⟩

/-- Literal upper triangular ramp and its exact Lebesgue integral. -/
def upperTriangle (t s x : ℝ) : ℝ :=
  (Ioc t (t+s)).indicator (fun x => t+s-x) x

theorem upperTriangle_integrable (t s : ℝ) : Integrable (upperTriangle t s) volume := by
  exact ((continuous_const.sub continuous_id : Continuous (fun x : ℝ => t+s-x)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

theorem upperTriangle_integral (t s : ℝ) (hs : 0 ≤ s) :
    ∫ x, upperTriangle t s x = s^2/2 := by
  change (∫ x, (Ioc t (t+s)).indicator (fun x : ℝ => t+s-x) x)=_
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : t ≤ t+s),
    intervalIntegral.integral_sub (f:=fun _ : ℝ => t+s) (g:=fun x : ℝ => x) (intervalIntegrable_const) (continuous_id.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const,integral_id]
  simp only [smul_eq_mul]
  ring

theorem upperTriangle_nonneg (t s x : ℝ) : 0 ≤ upperTriangle t s x := by
  unfold upperTriangle
  by_cases hx : x ∈ Ioc t (t+s)
  · simp only [indicator_of_mem hx]
    linarith [hx.2]
  · simp [hx]

/-- The one-sided first moment forced by a density ceiling. -/
theorem bounded_density_upper_moment (c : ℝ) (hc : 0 < c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) (hid : Integrable (fun x : ℝ => x) ν)
    (t : ℝ) :
    (ν.real (Ioi t))^2/(2*c) ≤ ∫ x in Ioi t, x-t ∂ν := by
  let a := ν.real (Ioi t)
  let s := a/c
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hs : 0 ≤ s := div_nonneg ha hc.le
  have hrV := upperTriangle_integrable t s
  have hr := (hrV.smul_measure (ENNReal.ofReal_ne_top)).mono_measure hdom
  have hrbd : (∫ x, upperTriangle t s x ∂ν) ≤ c*(s^2/2) := by
    have hm := integral_mono_measure hdom
      (Filter.Eventually.of_forall (upperTriangle_nonneg t s))
      (hrV.smul_measure (ENNReal.ofReal_ne_top))
    simpa [integral_smul_measure,ENNReal.toReal_ofReal hc.le,
      upperTriangle_integral t s hs] using hm
  have htail : Integrable ((Ioi t).indicator (fun x : ℝ => x-t)) ν := (hid.sub (integrable_const t)).integrableOn.integrable_indicator measurableSet_Ioi
  have hcut : Integrable ((Ioi t).indicator (fun _ : ℝ => (1:ℝ))) ν :=
    (integrable_const 1).integrableOn.integrable_indicator measurableSet_Ioi
  have hpoint (x : ℝ) : s*((Ioi t).indicator (fun _ : ℝ => (1:ℝ)) x) ≤
      (Ioi t).indicator (fun x => x-t) x + upperTriangle t s x := by
    by_cases hx : t < x
    · simp only [indicator_of_mem (s:=Ioi t) hx,mul_one]
      by_cases hx' : x ≤ t+s
      · simp only [upperTriangle,indicator_of_mem (show x ∈ Ioc t (t+s) from ⟨hx,hx'⟩)]
        linarith
      · have hnot : x ∉ Ioc t (t+s) := by simpa [mem_Ioc,hx] using hx'
        simp only [upperTriangle,indicator_of_notMem hnot,add_zero]
        linarith
    · have hnot : x ∉ Ioi t := hx
      have hnot' : x ∉ Ioc t (t+s) := fun h => hx h.1
      simp only [indicator_of_notMem hnot,mul_zero,upperTriangle,
        indicator_of_notMem hnot',add_zero,le_refl]
  have hi := integral_mono (hcut.const_mul s) (htail.add hr) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add htail hr] at hi
  simp only [integral_indicator measurableSet_Ioi,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hi
  have heq : a^2/(2*c)=s*a-c*(s^2/2) := by
    dsimp [s]
    field_simp
    ring
  rw [heq]
  change s*a-c*(s^2/2) ≤ _
  change s*a ≤ (∫ x in Ioi t, x-t ∂ν)+(∫ x, upperTriangle t s x ∂ν) at hi
  linarith

/-- The reflected triangular ramp, including its upper endpoint. -/
def lowerTriangle (t s x : ℝ) : ℝ :=
  (Ioc (t-s) t).indicator (fun x => x-(t-s)) x

theorem lowerTriangle_integrable (t s : ℝ) : Integrable (lowerTriangle t s) volume := by
  exact ((continuous_id.sub continuous_const : Continuous (fun x : ℝ => x-(t-s))).integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

theorem lowerTriangle_integral (t s : ℝ) (hs : 0 ≤ s) :
    ∫ x, lowerTriangle t s x = s^2/2 := by
  change (∫ x, (Ioc (t-s) t).indicator (fun x : ℝ => x-(t-s)) x)=_
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : t-s ≤ t),
    intervalIntegral.integral_sub (f:=fun x : ℝ => x) (g:=fun _ : ℝ => t-s) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
  rw [intervalIntegral.integral_const,integral_id]
  simp only [smul_eq_mul]
  ring

theorem lowerTriangle_nonneg (t s x : ℝ) : 0 ≤ lowerTriangle t s x := by
  unfold lowerTriangle
  by_cases hx : x ∈ Ioc (t-s) t
  · simp only [indicator_of_mem hx]
    linarith [hx.1]
  · simp [hx]

theorem bounded_density_lower_moment (c : ℝ) (hc : 0 < c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) (hid : Integrable (fun x : ℝ => x) ν)
    (t : ℝ) :
    (ν.real (Iic t))^2/(2*c) ≤ ∫ x in Iic t, t-x ∂ν := by
  let a := ν.real (Iic t)
  let s := a/c
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hs : 0 ≤ s := div_nonneg ha hc.le
  have hrV := lowerTriangle_integrable t s
  have hr := (hrV.smul_measure (ENNReal.ofReal_ne_top)).mono_measure hdom
  have hrbd : (∫ x, lowerTriangle t s x ∂ν) ≤ c*(s^2/2) := by
    have hm := integral_mono_measure hdom
      (Filter.Eventually.of_forall (lowerTriangle_nonneg t s))
      (hrV.smul_measure (ENNReal.ofReal_ne_top))
    simpa [integral_smul_measure,ENNReal.toReal_ofReal hc.le,
      lowerTriangle_integral t s hs] using hm
  have htail : Integrable ((Iic t).indicator (fun x : ℝ => t-x)) ν := ((integrable_const t).sub hid).integrableOn.integrable_indicator measurableSet_Iic
  have hcut : Integrable ((Iic t).indicator (fun _ : ℝ => (1:ℝ))) ν :=
    (integrable_const 1).integrableOn.integrable_indicator measurableSet_Iic
  have hpoint (x : ℝ) : s*((Iic t).indicator (fun _ : ℝ => (1:ℝ)) x) ≤
      (Iic t).indicator (fun x => t-x) x + lowerTriangle t s x := by
    by_cases hx : x ≤ t
    · simp only [indicator_of_mem (s:=Iic t) hx,mul_one]
      by_cases hx' : t-s < x
      · simp only [lowerTriangle,indicator_of_mem (show x ∈ Ioc (t-s) t from ⟨hx',hx⟩)]
        linarith
      · have hnot : x ∉ Ioc (t-s) t := fun h => hx' h.1
        simp only [lowerTriangle,indicator_of_notMem hnot,add_zero]
        linarith
    · have hnot : x ∉ Iic t := hx
      have hnot' : x ∉ Ioc (t-s) t := fun h => hx h.2
      simp only [indicator_of_notMem hnot,mul_zero,lowerTriangle,
        indicator_of_notMem hnot',add_zero,le_refl]
  have hi := integral_mono (hcut.const_mul s) (htail.add hr) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add htail hr] at hi
  simp only [integral_indicator measurableSet_Iic,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hi
  have heq : a^2/(2*c)=s*a-c*(s^2/2) := by
    dsimp [s]
    field_simp
    ring
  rw [heq]
  change s*a-c*(s^2/2) ≤ _
  change s*a ≤ (∫ x in Iic t, t-x ∂ν)+(∫ x, lowerTriangle t s x ∂ν) at hi
  linarith

/-- A threshold split of a centered bounded-density measure has a quantitative
unnormalized centroid separation. Both moments are literal set integrals. -/
theorem bounded_density_split_separation (c : ℝ) (hc : 0 < c)
    (hdom : ν ≤ ENNReal.ofReal c • volume) (hid : Integrable (fun x : ℝ => x) ν)
    (hmean : ∫ x, x ∂ν=0) (t : ℝ)
    (ha : 0 < ν.real (Ioi t)) (hb : 0 < ν.real (Iic t)) :
    ν.real (Ioi t)*ν.real (Iic t)/c ≤
      (∫ x in Ioi t, x ∂ν)-(∫ x in Iic t, x ∂ν) := by
  have hu := bounded_density_upper_moment ν c hc hdom hid t
  have hl := bounded_density_lower_moment ν c hc hdom hid t
  rw [integral_sub hid.integrableOn (integrable_const t)] at hu
  rw [integral_sub (integrable_const t) hid.integrableOn] at hl
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hu hl
  have hc2 : 0 < 2*c := by positivity
  have hu' := (div_le_iff₀ hc2).mp hu
  have hl' := (div_le_iff₀ hc2).mp hl
  have hs := integral_add_compl (s:=Iic t) measurableSet_Iic hid
  simp only [compl_Iic,hmean] at hs
  have hlow : (∫ x in Iic t,x ∂ν)= -(∫ x in Ioi t,x ∂ν) := by linarith [hs]
  have hcomb := add_le_add (mul_le_mul_of_nonneg_left hu' hb.le)
    (mul_le_mul_of_nonneg_left hl' ha.le)
  have hp : (ν.real (Ioi t)+ν.real (Iic t)) *
      (ν.real (Ioi t)*ν.real (Iic t)-c*
        ((∫ x in Ioi t,x ∂ν)-(∫ x in Iic t,x ∂ν))) ≤ 0 := by
    rw [hlow] at hcomb ⊢
    dsimp only [Measure.real] at *
    nlinarith
  have hgap := nonpos_of_mul_nonpos_right hp (add_pos ha hb)
  apply (div_le_iff₀ hc).mpr
  linarith

end NegativeVotingTwoCell
