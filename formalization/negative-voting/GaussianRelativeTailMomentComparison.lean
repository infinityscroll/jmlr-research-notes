import GaussianMaximumMomentComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Relative CDF tails give relative second-moment remainders. The covariance
amplitude is retained as an arbitrary nonnegative A, never discarded. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace NegativeVotingRelativeTailMomentComparison
open NegativeVotingMaximumMomentComparison
variable {Ω Ψ:Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
variable (μ:Measure Ω) (ν:Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma tail_integrable (f:Ω→ℝ) (hf:Integrable f μ) (h0:∀x,0 ≤ f x) :
    IntegrableOn (fun u:ℝ=>μ.real {x|u<f x}) (Ioi 0) := by
  have hmeas:Measurable (fun u:ℝ=>μ.real {x|u<f x}):=by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun a b hab=>measure_mono fun x hx=>lt_of_le_of_lt hab hx
  refine ⟨hmeas.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have he:=lintegral_eq_lintegral_meas_lt μ (ae_of_all _ h0) hf.aemeasurable
  have hfinite:∀u:ℝ,μ {x|u<f x}≠∞:=fun u=>measure_ne_top _ _
  simp_rw [Real.norm_eq_abs,Measure.real_def,abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hfinite _)]
  rw [←he]
  exact hf.lintegral_lt_top

lemma strict_shortfall_level (T x u:ℝ) (hu:0<u) :
    u<(max (x-T) 0)^2 ↔ T+Real.sqrt u<x := by
  have hs:=Real.sq_sqrt hu.le
  have hs0:=Real.sqrt_pos.mpr hu
  by_cases hx:T ≤ x
  · rw [max_eq_left (by linarith)]
    constructor <;> intro hh <;> nlinarith
  · rw [max_eq_right (by linarith)]
    constructor <;> intro hh <;> nlinarith

lemma sqrt_tail_exponential (T u:ℝ) (hT:0 ≤ T) (hu:0 ≤ u) :
    Real.exp (-(T+Real.sqrt u)^2/4) ≤ Real.exp (-T^2/8)*Real.exp (-(1/8:ℝ)*u) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh:=Real.sq_sqrt hu
  nlinarith [mul_nonneg hT (Real.sqrt_nonneg u),sq_nonneg T]

/-- Difference of upper squared shortfalls, with a Gaussian CDF-difference
amplitude A. Both tail integrals are actual integrable functions. -/
theorem upper_shortfall_difference_le (X:Ω→ℝ) (Y:Ψ→ℝ)
    (hX:Measurable X) (hY:Measurable Y) (hX2:MemLp X 2 μ) (hY2:MemLp Y 2 ν)
    (T A:ℝ) (hT:0 ≤ T) (hA:0 ≤ A)
    (hrelative:∀t:ℝ,T ≤ t → μ.real {x|X x ≤ t}-ν.real {y|Y y ≤ t} ≤ A*Real.exp (-t^2/4)) :
    (∫y,(max (Y y-T) 0)^2 ∂ν)-(∫x,(max (X x-T) 0)^2 ∂μ) ≤
      8*A*Real.exp (-T^2/8) := by
  let f:Ω→ℝ:=fun x=>(max (X x-T) 0)^2
  let g:Ψ→ℝ:=fun y=>(max (Y y-T) 0)^2
  have hf:Integrable f μ:=((hX2.sub (memLp_const T)).sup (memLp_const 0)).integrable_sq
  have hg:Integrable g ν:=((hY2.sub (memLp_const T)).sup (memLp_const 0)).integrable_sq
  have hfx:=tail_integrable μ f hf (fun _=>sq_nonneg _)
  have hgy:=tail_integrable ν g hg (fun _=>sq_nonneg _)
  have hdom:IntegrableOn (fun u:ℝ=>A*Real.exp (-T^2/8)*Real.exp (-(1/8:ℝ)*u)) (Ioi 0):=
    (integrableOn_exp_mul_Ioi (a:=-(1/8:ℝ)) (by norm_num) 0).const_mul _
  have hpoint:∀ᵐu:ℝ ∂(volume.restrict (Ioi 0)),
      ν.real {y|u<g y}-μ.real {x|u<f x} ≤ A*Real.exp (-T^2/8)*Real.exp (-(1/8:ℝ)*u):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have ht:T ≤ T+Real.sqrt u:=by linarith [Real.sqrt_nonneg u]
    have hx:{x|u<f x}=({x|X x ≤ T+Real.sqrt u})ᶜ:=by
      ext x;simpa only [f,mem_setOf_eq,mem_compl_iff,not_le] using strict_shortfall_level T (X x) u hu
    have hy:{y|u<g y}=({y|Y y ≤ T+Real.sqrt u})ᶜ:=by
      ext y;simpa only [g,mem_setOf_eq,mem_compl_iff,not_le] using strict_shortfall_level T (Y y) u hu
    rw [hx,hy,measureReal_compl (measurableSet_le hX measurable_const),
      measureReal_compl (measurableSet_le hY measurable_const),probReal_univ,probReal_univ]
    have hb:=(hrelative _ ht).trans (mul_le_mul_of_nonneg_left (sqrt_tail_exponential T u hT hu.le) hA)
    nlinarith only [hb]
  have hb:=integral_mono_ae (hgy.sub hfx) hdom hpoint
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hgy hfx,integral_const_mul] at hb
  have hexp:(∫u:ℝ in Ioi 0,Real.exp (-(1/8:ℝ)*u))=8:=by
    rw [integral_exp_mul_Ioi (by norm_num : -(1/8:ℝ)<0)]
    norm_num
  rw [hexp,←hg.integral_eq_integral_meas_lt (ae_of_all _ (fun _=>sq_nonneg _)),
    ←hf.integral_eq_integral_meas_lt (ae_of_all _ (fun _=>sq_nonneg _))] at hb
  change (∫y,g y ∂ν)-(∫x,f x ∂μ) ≤ _
  nlinarith only [hb]

lemma square_split (T x:ℝ) :
    x^2=2*T*x-T^2+(max (T-x) 0)^2+(max (x-T) 0)^2 := by
  rcases le_total x T with h|h
  · rw [max_eq_left (by linarith : 0 ≤ T-x),max_eq_right (by linarith : x-T ≤ 0)];ring
  · rw [max_eq_right (by linarith : T-x ≤ 0),max_eq_left (by linarith : 0 ≤ x-T)];ring

lemma integral_square_split (X:Ω→ℝ) (hX2:MemLp X 2 μ) (T:ℝ) :
    (∫x,X x^2 ∂μ)=2*T*(∫x,X x ∂μ)-T^2+
      (∫x,(max (T-X x) 0)^2 ∂μ)+(∫x,(max (X x-T) 0)^2 ∂μ) := by
  have hi:=hX2.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hlo : Integrable (fun x=>(max (T-X x) 0)^2) μ :=
    (((memLp_const T).sub hX2).sup (memLp_const 0)).integrable_sq
  have hhi : Integrable (fun x=>(max (X x-T) 0)^2) μ :=
    ((hX2.sub (memLp_const T)).sup (memLp_const 0)).integrable_sq
  have hbase:Integrable (fun x=>2*T*X x-T^2) μ:=(hi.const_mul _).sub (integrable_const _)
  have hadd : Integrable (fun x=>2*T*X x-T^2+(max (T-X x) 0)^2) μ := hbase.add hlo
  calc
    _ = ∫x,2*T*X x-T^2+(max (T-X x) 0)^2+(max (X x-T) 0)^2 ∂μ:=
      integral_congr_ae (ae_of_all _ fun x=>square_split T (X x))
    _ = _:=by
      rw [integral_add hadd hhi,integral_add hbase hlo,
        integral_sub (hi.const_mul _) (integrable_const _),integral_const_mul]
      simp

/-- CDF ordering plus a relative upper CDF tail gives the desired relative
moment remainder. This retains zero amplitude exactly. -/
theorem second_moment_difference_relative (X:Ω→ℝ) (Y:Ψ→ℝ)
    (hX:Measurable X) (hY:Measurable Y) (hX2:MemLp X 2 μ) (hY2:MemLp Y 2 ν)
    (hcdf:∀t:ℝ,ν {y|Y y ≤ t} ≤ μ {x|X x ≤ t})
    (T A:ℝ) (hT:0 ≤ T) (hA:0 ≤ A)
    (hrelative:∀t:ℝ,T ≤ t → μ.real {x|X x ≤ t}-ν.real {y|Y y ≤ t} ≤ A*Real.exp (-t^2/4)) :
    (∫y,Y y^2 ∂ν)-(∫x,X x^2 ∂μ) ≤
      2*T*((∫y,Y y ∂ν)-(∫x,X x ∂μ))+8*A*Real.exp (-T^2/8) := by
  have hlo:=shortfall_sq_integral_ge μ ν X Y hX hY hX2 hY2 hcdf T
  have hx:=integral_square_split μ X hX2 T
  have hy:=integral_square_split ν Y hY2 T
  have ht:=upper_shortfall_difference_le μ ν X Y hX hY hX2 hY2 T A hT hA hrelative
  linarith

end NegativeVotingRelativeTailMomentComparison
