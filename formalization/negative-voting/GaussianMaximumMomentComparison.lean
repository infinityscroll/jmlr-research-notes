import GaussianMaximumSecondMoment

/-! Exact first- and second-moment consequences of common-threshold CDF
comparison. A squared-shortfall identity needs only the upper tail of the
larger random variable. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace NegativeVotingMaximumMomentComparison
variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
variable (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem integral_le_of_superlevel_le
    (f : Ω→ℝ) (g : Ψ→ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g ν)
    (hf0 : ∀ x,0 ≤ f x) (hg0 : ∀ x,0 ≤ g x)
    (ht : ∀ t,0 < t→μ {x | t ≤ f x} ≤ ν {x | t ≤ g x}) :
    (∫ x,f x ∂μ) ≤ ∫ x,g x ∂ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
  apply ENNReal.toReal_mono hgi.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hf0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le ν (ae_of_all _ hg0) hg.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
  exact ht t ht0

private theorem integral_le_of_strict_superlevel_le
    (f : Ω→ℝ) (g : Ψ→ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g ν)
    (hf0 : ∀ x,0 ≤ f x) (hg0 : ∀ x,0 ≤ g x)
    (ht : ∀ t,0 < t→μ {x | t < f x} ≤ ν {x | t < g x}) :
    (∫ x,f x ∂μ) ≤ ∫ x,g x ∂ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
  apply ENNReal.toReal_mono hgi.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hf0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (ae_of_all _ hg0) hg.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
  exact ht t ht0

/-- CDF order in the direction supplied by Mulgund implies actual mean order. -/
theorem integral_le_of_cdf_ge
    (X : Ω→ℝ) (Y : Ψ→ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (hcdf : ∀ t,ν {y | Y y ≤ t} ≤ μ {x | X x ≤ t}) :
    (∫ x,X x ∂μ) ≤ ∫ y,Y y ∂ν := by
  have hp : (∫ x,max (X x) 0 ∂μ) ≤ ∫ y,max (Y y) 0 ∂ν := by
    apply integral_le_of_strict_superlevel_le μ ν _ _ (hX.max measurable_const)
      (hY.max measurable_const) (hXi.sup (integrable_const _)) (hYi.sup (integrable_const _))
      (fun _=>le_max_right _ _) (fun _=>le_max_right _ _)
    intro t ht
    have hx : {x | t < max (X x) 0}=({x | X x ≤ t})ᶜ := by ext x;simp only [mem_setOf_eq,mem_compl_iff,not_le,lt_max_iff];simp [not_lt.mpr ht.le]
    have hy : {y | t < max (Y y) 0}=({y | Y y ≤ t})ᶜ := by ext y;simp only [mem_setOf_eq,mem_compl_iff,not_le,lt_max_iff];simp [not_lt.mpr ht.le]
    rw [hx,hy,measure_compl (measurableSet_le hX measurable_const) (measure_ne_top _ _),
      measure_compl (measurableSet_le hY measurable_const) (measure_ne_top _ _),measure_univ,measure_univ]
    exact tsub_le_tsub_left (hcdf t) 1
  have hn : (∫ y,max (-Y y) 0 ∂ν) ≤ ∫ x,max (-X x) 0 ∂μ := by
    apply integral_le_of_superlevel_le ν μ _ _ (hY.neg.max measurable_const)
      (hX.neg.max measurable_const) (hYi.neg.sup (integrable_const _)) (hXi.neg.sup (integrable_const _))
      (fun _=>le_max_right _ _) (fun _=>le_max_right _ _)
    intro t ht
    have hx : {x | t ≤ max (-X x) 0}={x | X x ≤ -t} := by
      ext x
      simp only [mem_setOf_eq,le_max_iff,not_le.mpr ht,or_false]
      constructor <;> intro hh <;> linarith
    have hy : {y | t ≤ max (-Y y) 0}={y | Y y ≤ -t} := by
      ext y
      simp only [mem_setOf_eq,le_max_iff,not_le.mpr ht,or_false]
      constructor <;> intro hh <;> linarith
    change ν {y | t ≤ max (-Y y) 0} ≤ μ {x | t ≤ max (-X x) 0}
    rw [hx,hy]
    exact hcdf (-t)
  have hx := integral_eq_integral_pos_part_sub_integral_neg_part hXi
  have hy := integral_eq_integral_pos_part_sub_integral_neg_part hYi
  simp only [Real.coe_toNNReal',max_comm (0:ℝ)] at hx hy
  linarith

private theorem shortfall_level (T x t : ℝ) (ht : 0 < t) :
    t ≤ (max (T-x) 0)^2 ↔ x ≤ T-Real.sqrt t := by
  have hs := Real.sq_sqrt ht.le
  have hs0 := Real.sqrt_pos.mpr ht
  by_cases hx : x ≤ T
  · rw [max_eq_left (by linarith)]
    constructor <;> intro hh <;> nlinarith
  · rw [max_eq_right (by linarith)]
    constructor <;> intro hh <;> nlinarith

/-- Squared shortfall reverses CDF order, with no continuity assumption on the
laws. Non-strict layer cake matches the exact common-threshold events. -/
theorem shortfall_sq_integral_ge
    (X : Ω→ℝ) (Y : Ψ→ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 ν)
    (hcdf : ∀ t,ν {y | Y y ≤ t} ≤ μ {x | X x ≤ t}) (T : ℝ) :
    (∫ y,(max (T-Y y) 0)^2 ∂ν) ≤ ∫ x,(max (T-X x) 0)^2 ∂μ := by
  apply integral_le_of_superlevel_le ν μ _ _
    (((measurable_const.sub hY).max measurable_const).pow_const 2)
    (((measurable_const.sub hX).max measurable_const).pow_const 2)
    (((memLp_const T).sub hY2).sup (memLp_const 0)).integrable_sq
    (((memLp_const T).sub hX2).sup (memLp_const 0)).integrable_sq
    (fun _=>sq_nonneg _) (fun _=>sq_nonneg _)
  intro t ht
  change ν {y | t ≤ (max (T-Y y) 0)^2} ≤ μ {x | t ≤ (max (T-X x) 0)^2}
  simp_rw [shortfall_level T _ t ht]
  exact hcdf (T-Real.sqrt t)

private theorem square_split (T x : ℝ) :
    x^2=2*T*x-T^2+(max (T-x) 0)^2+(max (x-T) 0)^2 := by
  rcases le_total x T with h | h
  · rw [max_eq_left (by linarith : 0 ≤ T-x),max_eq_right (by linarith : x-T ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : T-x ≤ 0),max_eq_left (by linarith : 0 ≤ x-T)]
    ring

private theorem integral_square_split
    (X : Ω→ℝ) (hX2 : MemLp X 2 μ) (T : ℝ) :
    (∫ x,X x^2 ∂μ)=2*T*(∫ x,X x ∂μ)-T^2+
      (∫ x,(max (T-X x) 0)^2 ∂μ)+(∫ x,(max (X x-T) 0)^2 ∂μ) := by
  have hi : Integrable X μ := hX2.integrable (by norm_num)
  have hlo : Integrable (fun x=>(max (T-X x) 0)^2) μ :=
    (((memLp_const T).sub hX2).sup (memLp_const 0)).integrable_sq
  have hhi : Integrable (fun x=>(max (X x-T) 0)^2) μ :=
    ((hX2.sub (memLp_const T)).sup (memLp_const 0)).integrable_sq
  have hbase : Integrable (fun x=>2*T*X x-T^2) μ :=
    (hi.const_mul (2*T)).sub (integrable_const (T^2))
  have hadd : Integrable (fun x=>2*T*X x-T^2+(max (T-X x) 0)^2) μ :=
    hbase.add hlo
  calc
    _ = ∫ x,2*T*X x-T^2+(max (T-X x) 0)^2+(max (X x-T) 0)^2 ∂μ :=
      integral_congr_ae (ae_of_all _ (fun x=>square_split T (X x)))
    _ = _ := by
      rw [integral_add hadd hhi,
        integral_add hbase hlo,
        integral_sub (hi.const_mul (2*T)) (integrable_const (T^2)),integral_const_mul]
      simp

/-- The exact second-moment comparison has only the larger variable's upper
shortfall as an error. In particular no deficit-relative tail estimate is
smuggled into this statement. -/
theorem second_moment_difference_le
    (X : Ω→ℝ) (Y : Ψ→ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 ν)
    (hcdf : ∀ t,ν {y | Y y ≤ t} ≤ μ {x | X x ≤ t}) (T : ℝ) :
    (∫ y,Y y^2 ∂ν)-(∫ x,X x^2 ∂μ) ≤
      2*T*((∫ y,Y y ∂ν)-(∫ x,X x ∂μ))+(∫ y,(max (Y y-T) 0)^2 ∂ν) := by
  have hlo := shortfall_sq_integral_ge μ ν X Y hX hY hX2 hY2 hcdf T
  have hx := integral_square_split μ X hX2 T
  have hy := integral_square_split ν Y hY2 T
  have hnon : 0 ≤ ∫ x,(max (X x-T) 0)^2 ∂μ := integral_nonneg (fun _=>sq_nonneg _)
  linarith

end NegativeVotingMaximumMomentComparison
