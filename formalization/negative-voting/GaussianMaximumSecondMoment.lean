import GaussianMaximumMeanBounds

/-! Actual second-moment bounds for the normalized finite Gaussian maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianMaximumSecondMoment
open NegativeVotingGaussianMaximum NegativeVotingGaussianTail NegativeVotingGaussianMaximumMargins
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianEnvelopeIntegral NegativeVoting WeakSimplex

/-- Weighted layer cake for the literal square of a measurable real random variable. -/
theorem integral_sq_eq_weighted_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    (∫ x, f x^2 ∂μ) = ∫ t in Ioi 0, 2*t*μ.real {x | t < |f x|} := by
  have htail : Measurable (fun t : ℝ => μ.real {x | t < |f x|}) := by
    apply Antitone.measurable
    intro a b hab
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    exact lt_of_le_of_lt hab hx
  have hint (x : Ω) : (∫ t in (0:ℝ)..|f x|, 2*t)=f x^2 := by
    rw [intervalIntegral.integral_const_mul,integral_id]
    nlinarith [sq_abs (f x)]
  have hG : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ 2*t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    positivity
  have hLC := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun x => abs_nonneg (f x))) hf.abs.aemeasurable
    (g := fun t : ℝ => 2*t) (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t) hG
  simp_rw [hint] at hLC
  have hR : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun t : ℝ => 2*t*μ.real {x | t < |f x|}) := by
    filter_upwards [hG] with t ht
    exact mul_nonneg ht measureReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg (f x))) (hf.pow_const 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hR ((measurable_const.mul measurable_id).mul htail).aestronglyMeasurable,hLC]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hG] with t ht
  rw [ENNReal.ofReal_mul ht,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact mul_comm _ _

theorem scaledMaximum_measurable (n : ℕ) : Measurable (scaledMaximum n) := by
  unfold scaledMaximum
  exact (maximum_measurable.sub_const _).const_mul _

theorem scaledMaximum_abs_tail (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (standardGaussian (Fin (n+2))).real {x | t < |scaledMaximum n x|} =
      positiveTail n t+negativeTail n t := by
  have he : {x : Fin (n+2) → ℝ | t < |scaledMaximum n x|} =
      {x | t < scaledMaximum n x} ∪ {x | scaledMaximum n x < -t} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_union,lt_abs]
    constructor
    · rintro (h|h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h|h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [he,measureReal_union]
  · rfl
  · rw [Set.disjoint_left]
    intro x hx hy
    change t < scaledMaximum n x at hx
    change scaledMaximum n x < -t at hy
    linarith
  · exact measurableSet_lt (scaledMaximum_measurable n) measurable_const

theorem scaledMaximum_square_layercake (n : ℕ) :
    (∫ x, scaledMaximum n x^2 ∂standardGaussian (Fin (n+2))) =
      ∫ t in Ioi 0, 2*t*(positiveTail n t+negativeTail n t) := by
  rw [integral_sq_eq_weighted_tail _ _ (scaledMaximum_measurable n)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [scaledMaximum_abs_tail n t ht.le]

theorem weighted_exponential_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => 2*t*Real.exp (-c*t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := (1:ℝ))
    (b := c) (by norm_num) (by norm_num) hc
  have h' : Integrable (fun t : ℝ => t*Real.exp (-c*t)) (volume.restrict (Ioi 0)) := by
    simpa only [IntegrableOn,Real.rpow_one] using h
  exact (h'.const_mul (2:ℝ)).congr (ae_of_all _ (fun _ => by ring))

theorem weighted_exponential_integral (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi 0, 2*t*Real.exp (-c*t))=2/c^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c) (by norm_num) hc
  norm_num only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.Gamma_two] at h
  calc
    _ = 2*(∫ t in Ioi 0, t*Real.exp (-(c*t))) := by rw [← integral_const_mul];congr 1;funext t;ring
    _ = 2/c^2 := by rw [h];rw [Real.rpow_two];ring

/-- Exact elementary Gaussian row moment on the positive half-line. -/
theorem weighted_gaussian_integral (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi 0, 2*t*Real.exp (-c*t^2))=1/c := by
  have h := integral_mul_cexp_neg_mul_sq (b := (c:ℂ)) (by simpa using hc)
  have hr : (∫ t in Ioi 0, t*Real.exp (-c*t^2))=(2*c)⁻¹ := by
    apply Complex.ofReal_injective
    simpa only [← integral_complex_ofReal,Complex.ofReal_mul,Complex.ofReal_exp,
      Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_ofNat] using h
  calc
    _ = 2*(∫ t in Ioi 0, t*Real.exp (-c*t^2)) := by rw [← integral_const_mul];congr 1;funext t;ring
    _ = 1/c := by rw [hr];field_simp <;> ring

def weightedMiddle (n : ℕ) (t : ℝ) : ℝ :=
  (Ioc (upperQuantile n^2/50) (2*upperQuantile n^2)).indicator
    (fun u => 2*u*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))) t

def weightedFar (n : ℕ) (t : ℝ) : ℝ :=
  (1/2:ℝ)^(n+2)*(2*t*Real.exp (-(1/(8*upperQuantile n^2))*t^2))

theorem weightedMiddle_nonneg (n : ℕ) (t : ℝ) : 0 ≤ weightedMiddle n t := by
  classical
  by_cases ht : t ∈ Ioc (upperQuantile n^2/50) (2*upperQuantile n^2)
  · have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht.1
    simp only [weightedMiddle,indicator_of_mem ht]
    positivity
  · simp [weightedMiddle,ht]

theorem weightedFar_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ weightedFar n t := by
  unfold weightedFar
  positivity

theorem weightedMiddle_integrable (n : ℕ) : Integrable (weightedMiddle n) := by
  have h : IntegrableOn (fun t : ℝ => 2*t*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))))
      (Ioc (upperQuantile n^2/50) (2*upperQuantile n^2)) :=
    ((continuous_const.mul continuous_id).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact h.integrable_indicator measurableSet_Ioc

theorem weightedMiddle_integral_bound (n : ℕ) :
    (∫ t in Ioi 0, weightedMiddle n t) ≤
      4*upperQuantile n^4*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))) := by
  apply (setIntegral_le_integral (weightedMiddle_integrable n) (ae_of_all _ (weightedMiddle_nonneg n))).trans
  unfold weightedMiddle
  rw [integral_indicator measurableSet_Ioc]
  have hab : upperQuantile n^2/50 ≤ 2*upperQuantile n^2 := by nlinarith [sq_nonneg (upperQuantile n)]
  rw [← intervalIntegral.integral_of_le hab,intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul,integral_id]
  nlinarith [mul_nonneg (sq_nonneg (upperQuantile n^2/50))
    (Real.exp_pos (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))).le]

theorem weightedFar_integrable (n : ℕ) (hn : 0 < n) : Integrable (weightedFar n) := by
  have hb := upperQuantile_pos hn
  have h := (integrable_mul_exp_neg_mul_sq (show 0 < 1/(8*upperQuantile n^2) by positivity)).const_mul (2:ℝ)
  convert h.const_mul ((1/2:ℝ)^(n+2)) using 1
  funext t
  unfold weightedFar
  ring

theorem weightedFar_integral (n : ℕ) (hn : 0 < n) :
    (∫ t in Ioi 0, weightedFar n t)=8*upperQuantile n^2*(1/2:ℝ)^(n+2) := by
  have hb := upperQuantile_pos hn
  unfold weightedFar
  rw [integral_const_mul,weighted_gaussian_integral _ (by positivity)]
  field_simp <;> ring

/-- A weighted negative-tail majorant with a shrinking far-region remainder. -/
theorem weighted_negativeTail_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    2*t*negativeTail n t ≤ 2*t*Real.exp (-(99/100:ℝ)*t)+weightedMiddle n t+weightedFar n t := by
  have hm := weightedMiddle_nonneg n t
  have hf := weightedFar_nonneg n t ht.le
  have hbase : 0 ≤ 2*t*Real.exp (-(99/100:ℝ)*t) := by positivity
  have hcoef : 0 ≤ 2*t := by positivity
  by_cases htc : t ≤ upperQuantile n^2/50
  · have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real {x | scaledMaximum n x ≤ -t} := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      change scaledMaximum n x < -t at hx
      exact hx.le
    have he : Real.exp (-Real.exp ((99/100:ℝ)*t)) ≤ Real.exp (-(99/100:ℝ)*t) := by
      apply Real.exp_le_exp.mpr
      linarith [Real.add_one_le_exp ((99/100:ℝ)*t)]
    have h := mul_le_mul_of_nonneg_left ((hsub.trans (scaledMaximum_negative_tail n hn t ht.le htc)).trans he) hcoef
    linarith
  · by_cases htu : t ≤ 2*upperQuantile n^2
    · have hcut : upperQuantile n^2/50 < t := lt_of_not_ge htc
      have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real
          {x | scaledMaximum n x ≤ -(upperQuantile n^2/50)} := by
        refine measureReal_mono ?_ (by finiteness)
        intro x hx
        change scaledMaximum n x < -t at hx
        change scaledMaximum n x ≤ -(upperQuantile n^2/50)
        linarith
      have h := mul_le_mul_of_nonneg_left (hsub.trans
        (scaledMaximum_negative_tail n hn (upperQuantile n^2/50) (by positivity) le_rfl)) hcoef
      have hmid : weightedMiddle n t=2*t*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))) := by
        simp [weightedMiddle,hcut,htu]
      rw [← hmid] at h
      linarith
    · let b := upperQuantile n
      let z := (t-b^2)/b
      have hb : 0 < b := upperQuantile_pos hn
      have htu' : 2*b^2 < t := lt_of_not_ge htu
      have hz : 0 ≤ z := div_nonneg (by nlinarith [sq_nonneg b]) hb.le
      have hbz : b*z=t-b^2 := by dsimp [z];field_simp
      have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real {x | maximum x ≤ -z} := by
        refine measureReal_mono ?_ (by finiteness)
        intro x hx
        change b*(maximum x-b) < -t at hx
        change maximum x ≤ -z
        nlinarith
      have hsq : t^2 ≤ (2*b*z)^2 := pow_le_pow_left₀ ht.le (by nlinarith) 2
      have hdiv : t^2/(8*b^2) ≤ z^2/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith [hsq])
      have he : -(Fintype.card (Fin (n+2)):ℝ)*z^2/2 ≤ -(1/(8*b^2))*t^2 := by
        calc
          _ ≤ -z^2/2 := by
            simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
            nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg z),sq_nonneg z]
          _ ≤ -t^2/(8*b^2) := by simpa only [neg_div] using neg_le_neg hdiv
          _ = _ := by ring
      have hfar := hsub.trans (maximum_far_negative_tail (ι := Fin (n+2)) z hz)
      have hfar' : negativeTail n t ≤ (1/2:ℝ)^(n+2)*Real.exp (-(1/(8*b^2))*t^2) := by
        apply hfar.trans
        simp only [Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa only [Fintype.card_fin] using he)) (by positivity)
      have h := mul_le_mul_of_nonneg_left hfar' hcoef
      have heq : 2*t*((1/2:ℝ)^(n+2)*Real.exp (-(1/(8*b^2))*t^2))=weightedFar n t := by
        unfold weightedFar
        change 2*t*((1/2:ℝ)^(n+2)*Real.exp (-(1/(8*b^2))*t^2))=
          (1/2:ℝ)^(n+2)*(2*t*Real.exp (-(1/(8*b^2))*t^2))
        ring
      rw [heq] at h
      linarith

/-- A finite quantitative bound on the actual normalized maximum's second moment. -/
theorem scaledMaximum_second_moment_bound (n : ℕ) (hn : 0 < n) :
    (∫ x, scaledMaximum n x^2 ∂standardGaussian (Fin (n+2))) ≤ 5+
      4*upperQuantile n^4*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))+
      8*upperQuantile n^2*(1/2:ℝ)^(n+2) := by
  have hp := weighted_exponential_integrable 1 (by norm_num)
  have hd := weighted_exponential_integrable (99/100) (by norm_num)
  have hm := (weightedMiddle_integrable n).integrableOn (s := Ioi 0)
  have hf := (weightedFar_integrable n hn).integrableOn (s := Ioi 0)
  rw [scaledMaximum_square_layercake]
  calc
    _ ≤ ∫ t in Ioi 0, (2*t*Real.exp (-(1:ℝ)*t)+2*t*Real.exp (-(99/100:ℝ)*t))+weightedMiddle n t+weightedFar n t := by
      apply integral_mono_of_nonneg ?_ (((hp.add hd).add hm).add hf) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hp0 := positiveTail_nonneg n t
        have hn0 := negativeTail_nonneg n t
        change 0 < t at ht
        positivity
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < t at ht
        have hneg := weighted_negativeTail_bound n hn t ht
        have hpos := mul_le_mul_of_nonneg_left (scaledMaximum_positive_tail n hn t ht.le) (show 0 ≤ 2*t by positivity)
        change 2*t*positiveTail n t ≤ 2*t*Real.exp (-t) at hpos
        simp only [Pi.add_apply,neg_mul,one_mul] at *
        linarith
    _ = (∫ t in Ioi 0, 2*t*Real.exp (-(1:ℝ)*t))+(∫ t in Ioi 0, 2*t*Real.exp (-(99/100:ℝ)*t))+
        (∫ t in Ioi 0, weightedMiddle n t)+(∫ t in Ioi 0, weightedFar n t) := by
      have h1 := integral_add ((hp.add hd).add hm) hf
      have h2 := integral_add (hp.add hd) hm
      have h3 := integral_add hp hd
      simp only [Pi.add_apply] at h1 h2 h3
      linarith
    _ ≤ _ := by
      rw [weighted_exponential_integral 1 (by norm_num),weighted_exponential_integral (99/100) (by norm_num),weightedFar_integral n hn]
      have hmid := weightedMiddle_integral_bound n
      norm_num
      linarith

theorem second_middle_remainder_tendsto :
    Tendsto (fun n => 4*upperQuantile n^4*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (99/5000) (by norm_num)
  have hmajor : Tendsto (fun n => 4*upperQuantile n^4*Real.exp (-(99/5000:ℝ)*upperQuantile n^2)) atTop (𝓝 0) := by
    convert (hbase.comp upperQuantile_sq_tendsto).const_mul (4:ℝ) using 1
    · funext n
      dsimp only [Function.comp_def]
      rw [Real.rpow_two]
      ring
    · norm_num
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hmajor
  filter_upwards with n
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp ((99/100:ℝ)*(upperQuantile n^2/50))]

theorem second_far_remainder_tendsto :
    Tendsto (fun n => 8*upperQuantile n^2*(1/2:ℝ)^(n+2)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)^2*(1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num) (by norm_num)
  have hshift : Tendsto (fun n : ℕ => 8*((n:ℝ)+2)^2*(1/2:ℝ)^(n+2)) atTop (𝓝 0) := by
    simpa [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using ((tendsto_add_atTop_iff_nat 2).mpr hbase).const_mul 8
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hshift
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpow := pow_le_pow_left₀ (upperQuantile_pos hn).le (upperQuantile_le_size n hn) 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)

/-- Uniform boundedness of the actual normalized maximum second moment. -/
theorem eventually_scaledMaximum_second_moment_le_six :
    ∀ᶠ n in atTop, (∫ x, scaledMaximum n x^2 ∂standardGaussian (Fin (n+2))) ≤ (6:ℝ) := by
  have hr := (second_middle_remainder_tendsto.add second_far_remainder_tendsto).eventually
    (gt_mem_nhds (show (0:ℝ)+0 < 1 by norm_num))
  filter_upwards [eventually_gt_atTop 0,hr] with n hn hrn
  have h := scaledMaximum_second_moment_bound n hn
  linarith

def maximumVariance (n : ℕ) : ℝ := variance (maximum : (Fin (n+2) → ℝ) → ℝ) (standardGaussian (Fin (n+2)))
def maximumSecondMoment (n : ℕ) : ℝ := ∫ x, maximum x^2 ∂standardGaussian (Fin (n+2))

theorem maximumVariance_eq_centered_integral (n : ℕ) :
    maximumVariance n = ∫ x, (maximum x-maximumMean n)^2 ∂standardGaussian (Fin (n+2)) :=
  variance_eq_integral maximum_measurable.aemeasurable

theorem maximumVariance_eq_second_sub_mean_sq (n : ℕ) :
    maximumVariance n=maximumSecondMoment n-maximumMean n^2 :=
  variance_eq_sub maximum_memLp_two

theorem scaledMaximum_variance (n : ℕ) :
    variance (scaledMaximum n) (standardGaussian (Fin (n+2))) = upperQuantile n^2*maximumVariance n := by
  unfold scaledMaximum maximumVariance
  rw [variance_const_mul,variance_sub_const maximum_memLp_two.aestronglyMeasurable]

theorem eventually_maximum_variance_bound :
    ∀ᶠ n in atTop, maximumVariance n ≤ 6/upperQuantile n^2 := by
  filter_upwards [eventually_gt_atTop 0,eventually_scaledMaximum_second_moment_le_six] with n hn hs
  have hv := variance_le_expectation_sq (scaledMaximum_memLp_two n).aestronglyMeasurable
  rw [scaledMaximum_variance n] at hv
  apply (le_div_iff₀ (sq_pos_of_pos (upperQuantile_pos hn))).mpr
  simp only [Pi.pow_apply] at hv
  nlinarith

theorem maximum_variance_tendsto_zero : Tendsto maximumVariance atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => variance_nonneg _ _)) eventually_maximum_variance_bound
  exact upperQuantile_sq_tendsto.const_div_atTop 6

/-- The second moment is controlled by the actual normalized centered moment. -/
theorem maximum_second_moment_comparison (n : ℕ) :
    upperQuantile n^2*maximumSecondMoment n ≤ 2*upperQuantile n^4+
      2*(∫ x, scaledMaximum n x^2 ∂standardGaussian (Fin (n+2))) := by
  have hcenter : Integrable (fun x : Fin (n+2) → ℝ => (maximum x-upperQuantile n)^2)
      (standardGaussian (Fin (n+2))) := by
    simpa only [Pi.sub_apply] using ((maximum_memLp_two (ι := Fin (n+2))).sub (memLp_const (upperQuantile n))).integrable_sq
  have he : (∫ x, scaledMaximum n x^2 ∂standardGaussian (Fin (n+2)))=
      upperQuantile n^2*(∫ x, (maximum x-upperQuantile n)^2 ∂standardGaussian (Fin (n+2))) := by
    unfold scaledMaximum
    simp_rw [mul_pow]
    rw [integral_const_mul]
  have hm : maximumSecondMoment n ≤ 2*(∫ x, (maximum x-upperQuantile n)^2 ∂standardGaussian (Fin (n+2)))+
      2*upperQuantile n^2 := by
    calc
      _ ≤ ∫ x, 2*(maximum x-upperQuantile n)^2+2*upperQuantile n^2 ∂standardGaussian (Fin (n+2)) := by
        apply integral_mono maximum_square_integrable ((hcenter.const_mul (2:ℝ)).add (integrable_const _))
        intro x
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (maximum x-2*upperQuantile n)]
      _ = _ := by
        rw [integral_add (hcenter.const_mul (2:ℝ)) (integrable_const _),integral_const_mul]
        simp
  have hscaled := mul_le_mul_of_nonneg_left hm (sq_nonneg (upperQuantile n))
  nlinarith

theorem size_tendsto : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop := by
  simpa only [Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_add_atTop_iff_nat 2).mpr (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Genuine logarithmic growth bound for the actual finite Gaussian maximum. -/
theorem eventually_maximum_second_moment_log_bound :
    ∀ᶠ (n : ℕ) in atTop, maximumSecondMoment n ≤ 5*Real.log ((n:ℝ)+2) := by
  filter_upwards [eventually_gt_atTop 0,eventually_scaledMaximum_second_moment_le_six,
    upperQuantile_sq_tendsto.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 12] with n hn hs hb hl
  have h := maximum_second_moment_comparison n
  have hu := upperQuantile_sq_le_log n hn
  have hm : maximumSecondMoment n ≤ 2*upperQuantile n^2+12 := by nlinarith
  change 12 ≤ Real.log ((n:ℝ)+2) at hl
  linarith

end NegativeVotingGaussianMaximumSecondMoment
