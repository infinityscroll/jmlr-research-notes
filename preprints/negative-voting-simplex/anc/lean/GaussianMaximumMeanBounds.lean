import GaussianMaximumTailMargins
import GaussianDoubleExponentialIntegral

/-! Actual tail-integral assembly for Gaussian maximum means. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianMaximumMean
open NegativeVotingGaussianMaximum NegativeVotingGaussianTail NegativeVotingGaussianMaximumMargins
  NegativeVotingGaussianEnvelopeIntegral NegativeVotingMassCentroid NegativeVoting WeakSimplex

def positiveTail (n : ℕ) (t : ℝ) : ℝ :=
  (standardGaussian (Fin (n+2))).real {x | t < scaledMaximum n x}
def negativeTail (n : ℕ) (t : ℝ) : ℝ :=
  (standardGaussian (Fin (n+2))).real {x | scaledMaximum n x < -t}

theorem positiveTail_nonneg (n : ℕ) (t : ℝ) : 0 ≤ positiveTail n t := measureReal_nonneg
 theorem negativeTail_nonneg (n : ℕ) (t : ℝ) : 0 ≤ negativeTail n t := measureReal_nonneg

theorem positiveTail_measurable (n : ℕ) : Measurable (positiveTail n) := by
  apply Antitone.measurable
  intro a b hab
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  exact hab.trans_lt hx

theorem negativeTail_measurable (n : ℕ) : Measurable (negativeTail n) := by
  apply Antitone.measurable
  intro a b hab
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  exact hx.trans_le (neg_le_neg hab)

/-- Signed layer-cake identity for the actual centered maximum. -/
theorem scaledMaximum_mean_tail_difference (n : ℕ) :
    (∫ x, scaledMaximum n x ∂standardGaussian (Fin (n+2)))=
      (∫ t in Ioi 0, positiveTail n t)-(∫ t in Ioi 0, negativeTail n t) := by
  have hp : Integrable (fun x => max (scaledMaximum n x) 0) (standardGaussian (Fin (n+2))) :=
    (scaledMaximum_integrable n).sup (integrable_const 0)
  have hm : Integrable (fun x => max (-scaledMaximum n x) 0) (standardGaussian (Fin (n+2))) :=
    (scaledMaximum_integrable n).neg.sup (integrable_const 0)
  have he : scaledMaximum n=(fun x => max (scaledMaximum n x) 0-max (-scaledMaximum n x) 0) := by
    funext x
    rcases le_total 0 (scaledMaximum n x) with hx | hx
    · simp [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)]
    · simp [max_eq_right hx,max_eq_left (neg_nonneg.mpr hx)]
  rw [he,integral_sub hp hm]
  rw [hp.integral_eq_integral_meas_lt (ae_of_all _ (fun x => le_max_right _ _)),
    hm.integral_eq_integral_meas_lt (ae_of_all _ (fun x => le_max_right _ _))]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold positiveTail
    apply congrArg (fun s : Set (Fin (n+2) → ℝ) => (standardGaussian (Fin (n+2))).real s)
    ext x
    simp only [mem_setOf_eq,lt_max_iff]
    constructor
    · rintro (h|h)
      · exact h
      · exact (not_lt_of_ge ht.le h).elim
    · exact Or.inl
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold negativeTail
    apply congrArg (fun s : Set (Fin (n+2) → ℝ) => (standardGaussian (Fin (n+2))).real s)
    ext x
    simp only [mem_setOf_eq,lt_max_iff]
    constructor
    · rintro (h|h)
      · linarith
      · exact (not_lt_of_ge ht.le h).elim
    · intro h
      left
      linarith

theorem positiveTail_integrable (n : ℕ) (hn : 0 < n) : IntegrableOn (positiveTail n) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono' (positiveTail_measurable n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (positiveTail_nonneg n t)]
  exact scaledMaximum_positive_tail n hn t ht.le

/-- The elementary positive-envelope integral has a strict rational margin. -/
theorem positive_envelope_integral_lower :
    (187/250:ℝ) ≤ ∫ t in (0:ℝ)..8, (999/1000:ℝ)*Real.exp (-t)-Real.exp (-2*t)/2 := by
  have hd (t : ℝ) : HasDerivAt
      (fun x => -(999/1000:ℝ)*Real.exp (-x)+(1/4:ℝ)*Real.exp (-2*x))
      ((999/1000:ℝ)*Real.exp (-t)-Real.exp (-2*t)/2) t := by
    convert (((hasDerivAt_id t).neg.exp).const_mul (-(999/1000:ℝ))).add
      ((((hasDerivAt_id t).const_mul (-2)).exp).const_mul (1/4:ℝ)) using 1
    · funext x
      simp <;> ring
    · simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (by apply Continuous.intervalIntegrable;fun_prop)]
  have h1 : Real.exp (-1) ≤ 46/125 := by linarith [Real.exp_neg_one_lt_d9]
  have h8 : Real.exp (-8) ≤ 1/1000 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos (-1)).le h1 8
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    linarith
  norm_num
  linarith [Real.exp_pos (-16)]

/-- An actual positive-tail integral lower bound, with explicit quantile threshold. -/
theorem positiveTail_integral_lower (n : ℕ) (hn : 0 < n) (hb : 1000000 ≤ upperQuantile n^2) :
    (187/250:ℝ) ≤ ∫ t in Ioi 0, positiveTail n t := by
  have hi : IntervalIntegrable (positiveTail n) volume 0 8 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    exact (positiveTail_integrable n hn).mono_set Ioc_subset_Ioi_self
  have hpart : (∫ t in (0:ℝ)..8, positiveTail n t) ≤ ∫ t in Ioi 0, positiveTail n t := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set (positiveTail_integrable n hn)
      (ae_of_all _ (positiveTail_nonneg n)) (ae_of_all _ (fun _ h => Ioc_subset_Ioi_self h))
  apply positive_envelope_integral_lower.trans
  apply le_trans _ hpart
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable;fun_prop) hi
  intro t ht
  exact scaledMaximum_positive_tail_lower n hn hb t ht.1 ht.2

def farEnvelope (n : ℕ) (t : ℝ) : ℝ :=
  (1/2:ℝ)^(n+2)*Real.exp (-((t-upperQuantile n^2)/upperQuantile n)^2/2)

private theorem integrable_base_gaussian : Integrable (fun t : ℝ => Real.exp (-t^2/2)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2) using 1
  funext t
  congr 1
  ring

theorem farEnvelope_integrable (n : ℕ) (hn : 0 < n) : Integrable (farEnvelope n) := by
  exact ((integrable_base_gaussian.comp_div (upperQuantile_pos hn).ne').comp_sub_right
    (upperQuantile n^2)).const_mul ((1/2:ℝ)^(n+2))

theorem farEnvelope_integral (n : ℕ) (hn : 0 < n) :
    (∫ t, farEnvelope n t)=(1/2:ℝ)^(n+2)*upperQuantile n*Real.sqrt (2*Real.pi) := by
  unfold farEnvelope
  rw [integral_const_mul,integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(t/upperQuantile n)^2/2))]
  rw [Measure.integral_comp_div (fun t : ℝ => Real.exp (-t^2/2)),abs_of_pos (upperQuantile_pos hn),smul_eq_mul]
  have hi : (∫ t : ℝ, Real.exp (-t^2/2))=Real.sqrt (2*Real.pi) := by
    have he : (fun t : ℝ => Real.exp (-t^2/2))=fun t => Real.exp (-(1/2:ℝ)*t^2) := by
      funext t
      congr 1
      ring
    rw [he,integral_gaussian]
    congr 1
    ring
  rw [hi]
  ring

theorem farEnvelope_integral_bound (n : ℕ) (hn : 0 < n) :
    (∫ t in Ioi 0, farEnvelope n t) ≤ 3*upperQuantile n*(1/2:ℝ)^(n+2) := by
  apply (setIntegral_le_integral (farEnvelope_integrable n hn) (ae_of_all _ (by intro t;unfold farEnvelope;positivity))).trans
  rw [farEnvelope_integral n hn]
  have hs : Real.sqrt (2*Real.pi) ≤ 3 := by
    have hh := Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)
    nlinarith [Real.pi_lt_four,Real.sqrt_nonneg (2*Real.pi)]
  have hb := (upperQuantile_pos hn).le
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (1/2:ℝ)^(n+2)*upperQuantile n)
  nlinarith

def middleEnvelope (n : ℕ) (t : ℝ) : ℝ :=
  (Ioc (upperQuantile n^2/50) (upperQuantile n^2)).indicator
    (fun _ => Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))) t

theorem middleEnvelope_nonneg (n : ℕ) (t : ℝ) : 0 ≤ middleEnvelope n t := by
  classical
  by_cases ht : t ∈ Ioc (upperQuantile n^2/50) (upperQuantile n^2)
  · simp only [middleEnvelope,indicator_of_mem ht]
    positivity
  · simp [middleEnvelope,ht]

theorem farEnvelope_nonneg (n : ℕ) (t : ℝ) : 0 ≤ farEnvelope n t := by
  unfold farEnvelope
  positivity

theorem middleEnvelope_integrable (n : ℕ) : Integrable (middleEnvelope n) := by
  exact (integrableOn_const (s := Ioc (upperQuantile n^2/50) (upperQuantile n^2))
    (C := Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))))
    (μ := volume) (hs := by rw [Real.volume_Ioc];exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioc

theorem middleEnvelope_integral_bound (n : ℕ) :
    (∫ t in Ioi 0, middleEnvelope n t) ≤
      upperQuantile n^2*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))) := by
  apply (setIntegral_le_integral (middleEnvelope_integrable n) (ae_of_all _ (middleEnvelope_nonneg n))).trans
  unfold middleEnvelope
  rw [integral_indicator measurableSet_Ioc,setIntegral_const]
  have hu : 0 ≤ upperQuantile n^2-upperQuantile n^2/50 := by nlinarith [sq_nonneg (upperQuantile n)]
  simp only [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hu,smul_eq_mul]
  nlinarith [sq_nonneg (upperQuantile n),Real.exp_pos (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))]

/-- One explicit integrable envelope covers all negative-tail regions. -/
theorem negativeTail_envelope (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    negativeTail n t ≤ Real.exp (-Real.exp ((99/100:ℝ)*t))+middleEnvelope n t+farEnvelope n t := by
  have hd : 0 ≤ Real.exp (-Real.exp ((99/100:ℝ)*t)) := (Real.exp_pos _).le
  have hm := middleEnvelope_nonneg n t
  have hf := farEnvelope_nonneg n t
  by_cases htc : t ≤ upperQuantile n^2/50
  · have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real {x | scaledMaximum n x ≤ -t} := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      change scaledMaximum n x < -t at hx
      exact hx.le
    have hb := hsub.trans (scaledMaximum_negative_tail n hn t ht.le htc)
    linarith
  · by_cases htu : t ≤ upperQuantile n^2
    · have hcut : upperQuantile n^2/50 < t := lt_of_not_ge htc
      have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real
          {x | scaledMaximum n x ≤ -(upperQuantile n^2/50)} := by
        refine measureReal_mono ?_ (by finiteness)
        intro x hx
        change scaledMaximum n x < -t at hx
        change scaledMaximum n x ≤ -(upperQuantile n^2/50)
        linarith
      have hb := hsub.trans (scaledMaximum_negative_tail n hn (upperQuantile n^2/50) (by positivity) le_rfl)
      have hmid : middleEnvelope n t=Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50))) := by
        simp [middleEnvelope,hcut,htu]
      rw [← hmid] at hb
      linarith
    · let b := upperQuantile n
      let s := (t-b^2)/b
      have hb : 0 < b := upperQuantile_pos hn
      have htu' : b^2 < t := lt_of_not_ge htu
      have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr htu'.le) hb.le
      have hbs : b*s=t-b^2 := by dsimp [s];field_simp
      have hsub : negativeTail n t ≤ (standardGaussian (Fin (n+2))).real {x | maximum x ≤ -s} := by
        refine measureReal_mono ?_ (by finiteness)
        intro x hx
        change b*(maximum x-b) < -t at hx
        change maximum x ≤ -s
        nlinarith
      have hfar := hsub.trans (maximum_far_negative_tail (ι := Fin (n+2)) s hs)
      have he : -(Fintype.card (Fin (n+2)):ℝ)*s^2/2 ≤ -s^2/2 := by
        simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg s),sq_nonneg s]
      have hfar' : negativeTail n t ≤ farEnvelope n t := by
        apply hfar.trans
        unfold farEnvelope
        change (1/2:ℝ)^Fintype.card (Fin (n+2))*Real.exp (-(Fintype.card (Fin (n+2)):ℝ)*s^2/2) ≤
          (1/2:ℝ)^(n+2)*Real.exp (-s^2/2)
        simp only [Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa only [Fintype.card_fin] using he)) (by positivity)
      linarith

theorem scaled_doubleExp_integrable :
    IntegrableOn (fun t : ℝ => Real.exp (-Real.exp ((99/100:ℝ)*t))) (Ioi 0) := by
  apply (integrableOn_exp_mul_Ioi (a := -(99/100:ℝ)) (by norm_num) 0).mono' (by fun_prop)
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp ((99/100:ℝ)*t)]

/-- Actual negative tail integral, with both discarded regions quantified. -/
theorem negativeTail_integral_bound (n : ℕ) (hn : 0 < n) :
    (∫ t in Ioi 0, negativeTail n t) ≤ (23/99:ℝ)+
      upperQuantile n^2*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))+
      3*upperQuantile n*(1/2:ℝ)^(n+2) := by
  have hm := (middleEnvelope_integrable n).integrableOn (s := Ioi 0)
  have hf := (farEnvelope_integrable n hn).integrableOn (s := Ioi 0)
  calc
    _ ≤ ∫ t in Ioi 0, Real.exp (-Real.exp ((99/100:ℝ)*t))+middleEnvelope n t+farEnvelope n t := by
      apply integral_mono_of_nonneg (ae_of_all _ (negativeTail_nonneg n)) ((scaled_doubleExp_integrable.add hm).add hf)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact negativeTail_envelope n hn t ht
    _ = (∫ t in Ioi 0, Real.exp (-Real.exp ((99/100:ℝ)*t)))+
        (∫ t in Ioi 0, middleEnvelope n t)+(∫ t in Ioi 0, farEnvelope n t) := by
      have h1 := integral_add (scaled_doubleExp_integrable.add hm) hf
      have h2 := integral_add scaled_doubleExp_integrable hm
      simp only [Pi.add_apply] at h1 h2
      linarith
    _ ≤ _ := by linarith [scaled_doubleExp_integral_lt,middleEnvelope_integral_bound n,farEnvelope_integral_bound n hn]

/-- A completely finite actual Gaussian mean inequality. -/
theorem scaledMaximum_mean_lower (n : ℕ) (hn : 0 < n) (hb : 1000000 ≤ upperQuantile n^2) :
    (187/250:ℝ)-(23/99)-
      (upperQuantile n^2*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))+
      3*upperQuantile n*(1/2:ℝ)^(n+2)) ≤
      upperQuantile n*(maximumMean n-upperQuantile n) := by
  rw [← scaledMaximum_mean n,scaledMaximum_mean_tail_difference n]
  linarith [positiveTail_integral_lower n hn hb,negativeTail_integral_bound n hn]

theorem upperQuantile_sq_tendsto :
    Tendsto (fun n => upperQuantile n^2) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp upperQuantile_tendsto

theorem middle_remainder_tendsto :
    Tendsto (fun n => upperQuantile n^2*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun u : ℝ => u*Real.exp (-(99/5000:ℝ)*u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (99/5000) (by norm_num)
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ (hbase.comp upperQuantile_sq_tendsto)
  filter_upwards with n
  apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp ((99/100:ℝ)*(upperQuantile n^2/50))]

theorem upperQuantile_le_size (n : ℕ) (hn : 0 < n) : upperQuantile n ≤ (n:ℝ)+2 := by
  have hb := upperQuantile_pos hn
  have hsq := upperQuantile_sq_le_log n hn
  have hl := Real.log_le_sub_one_of_pos (show 0 < (n:ℝ)+2 by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n,sq_nonneg ((n:ℝ)+1)]

theorem far_remainder_tendsto :
    Tendsto (fun n => 3*upperQuantile n*(1/2:ℝ)^(n+2)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)*(1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hshift : Tendsto (fun n : ℕ => 3*((n:ℝ)+2)*(1/2:ℝ)^(n+2)) atTop (𝓝 0) := by
    simpa [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using ((tendsto_add_atTop_iff_nat 2).mpr hbase).const_mul 3
  apply squeeze_zero' ?_ ?_ hshift
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hb := (upperQuantile_pos hn).le
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (upperQuantile_le_size n hn) (by norm_num)) (by positivity)

theorem total_remainder_tendsto :
    Tendsto (fun n => upperQuantile n^2*Real.exp (-Real.exp ((99/100:ℝ)*(upperQuantile n^2/50)))+
      3*upperQuantile n*(1/2:ℝ)^(n+2)) atTop (𝓝 0) := by
  simpa using middle_remainder_tendsto.add far_remainder_tendsto

/-- Numerical eventual mean/quantile separation for the actual finite Gaussian maximum. -/
theorem eventually_scaledMaximum_mean_lower :
    ∀ᶠ n in atTop, (103/200:ℝ) ≤ upperQuantile n*(maximumMean n-upperQuantile n) := by
  have hr := total_remainder_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2000))
  filter_upwards [eventually_gt_atTop 0,upperQuantile_sq_tendsto.eventually_ge_atTop 1000000,hr] with n hn hb hrn
  have hm := scaledMaximum_mean_lower n hn hb
  norm_num at hrn
  linarith

theorem normal_mills_ratio_bound (b : ℝ) (hb : 0 < b) :
    normalPDF b/normalCDF (-b) ≤ b+1/b := by
  have h := mul_le_mul_of_nonneg_left (mills_lower b hb) (show 0 ≤ (1+b^2)/b by positivity)
  have hleft : (1+b^2)/b*(b/(1+b^2)*normalPDF b)=normalPDF b := by field_simp
  have hright : (1+b^2)/b*normalCDF (-b)=(b+1/b)*normalCDF (-b) := by field_simp <;> ring
  rw [hleft,hright] at h
  exact (div_le_iff₀ (normalCDF_pos (-b))).mpr h

theorem upperQuantile_density_bound (n : ℕ) (hn : 0 < n) :
    ((n:ℝ)+2)*normalPDF (upperQuantile n) ≤ upperQuantile n+1/upperQuantile n := by
  have h := normal_mills_ratio_bound (upperQuantile n) (upperQuantile_pos hn)
  rw [upperQuantile_tail] at h
  simpa only [one_div,div_inv_eq_mul,mul_comm] using h

/-- The literal Gaussian density upper envelope appearing in mass localization. -/
def centroidEnvelope (n : ℕ) : ℝ := ((n:ℝ)+2)*normalPDF (upperQuantile n)^2
/-- The literal first Hermite-weight expression of the regular simplex comparator. -/
def referenceFirstWeight (n : ℕ) : ℝ := maximumMean n^2/((n:ℝ)+1)

theorem reference_gap_bound (n : ℕ) (hn : 0 < n)
    (hm : (103/200:ℝ) ≤ upperQuantile n*(maximumMean n-upperQuantile n)) :
    ((n:ℝ)+2)*(centroidEnvelope n-referenceFirstWeight n) ≤ (97/100:ℝ)+1/upperQuantile n^2 := by
  have hb := upperQuantile_pos hn
  have hfirst : maximumMean n^2 ≤ ((n:ℝ)+2)*referenceFirstWeight n := by
    unfold referenceFirstWeight
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (maximumMean n)]
  have hsq : (((n:ℝ)+2)*normalPDF (upperQuantile n))^2 ≤ (upperQuantile n+1/upperQuantile n)^2 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) (normalPDF_pos _).le) (upperQuantile_density_bound n hn) 2
  have he : (upperQuantile n+1/upperQuantile n)^2=upperQuantile n^2+2+1/upperQuantile n^2 := by
    field_simp <;> ring
  rw [he] at hsq
  unfold centroidEnvelope
  nlinarith [sq_nonneg (maximumMean n-upperQuantile n)]

/-- Actual eventual coefficient gap; no extremal-value limit is assumed. -/
theorem eventually_reference_gap_bound :
    ∀ᶠ (n : ℕ) in atTop, ((n:ℝ)+2)*(centroidEnvelope n-referenceFirstWeight n) ≤ (97/100:ℝ)+1/upperQuantile n^2 := by
  filter_upwards [eventually_gt_atTop 0,eventually_scaledMaximum_mean_lower] with n hn hm
  exact reference_gap_bound n hn hm

/-- A fixed strict numerical margin below one for the actual Gaussian quantities. -/
theorem eventually_reference_gap_lt_one :
    ∀ᶠ (n : ℕ) in atTop, ((n:ℝ)+2)*(centroidEnvelope n-referenceFirstWeight n) ≤ (39/40:ℝ) := by
  filter_upwards [eventually_reference_gap_bound,upperQuantile_sq_tendsto.eventually_ge_atTop 400] with n hg hb
  have hbpos : 0 < upperQuantile n^2 := by linarith
  have hi : 1/upperQuantile n^2 ≤ (1/400:ℝ) := (div_le_iff₀ hbpos).mpr (by linarith)
  linarith

end NegativeVotingGaussianMaximumMean
