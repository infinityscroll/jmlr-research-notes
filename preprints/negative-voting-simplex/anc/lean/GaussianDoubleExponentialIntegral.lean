import GaussianTailRatio

/-! A proved numerical integral bound for the actual double-exponential
negative-tail envelope. No Gumbel moment identity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianEnvelopeIntegral

def expOverSelf (u : ℝ) : ℝ := Real.exp (-u)/u

theorem expOverSelf_integrable : IntegrableOn expOverSelf (Ioi 1) := by
  apply (integrableOn_exp_neg_Ioi 1).mono'
    ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  rw [Real.norm_eq_abs,abs_of_nonneg (by change 0 ≤ Real.exp (-u)/u;positivity)]
  exact div_le_self (Real.exp_pos _).le hu.le

theorem expOverSelf_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable expOverSelf volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
    (fun u hu => ne_of_gt (ha.trans_le hu.1))

/-- Reciprocal lies below its secant on a positive interval. -/
theorem reciprocal_chord {a b u : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hau : a ≤ u) (hub : u ≤ b) : 1/u ≤ (a+b-u)/(a*b) := by
  have hb : 0 < b := ha.trans_le hab
  have hu : 0 < u := ha.trans_le hau
  apply (div_le_div_iff₀ hu (mul_pos ha hb)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hau) (sub_nonneg.mpr hub)]

theorem integral_exp_chord (a b : ℝ) :
    (∫ u in a..b, (a+b-u)*Real.exp (-u)/(a*b)) =
      ((b-1)*Real.exp (-a)-(a-1)*Real.exp (-b))/(a*b) := by
  have hd (u : ℝ) : HasDerivAt (fun x => (x+1-a-b)*Real.exp (-x)/(a*b))
      ((a+b-u)*Real.exp (-u)/(a*b)) u := by
    convert (((((hasDerivAt_id u).add_const 1).sub_const a).sub_const b).mul
      ((hasDerivAt_id u).neg.exp)).div_const (a*b) using 1 <;> simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable;fun_prop)]
  ring

/-- Explicit finite-interval integral bound from the proved secant. -/
theorem expOverSelf_chord_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, expOverSelf u) ≤
      ((b-1)*Real.exp (-a)-(a-1)*Real.exp (-b))/(a*b) := by
  rw [← integral_exp_chord a b]
  apply intervalIntegral.integral_mono_on hab (expOverSelf_intervalIntegrable ha hab)
    (by apply Continuous.intervalIntegrable;fun_prop)
  intro u hu
  have hc := mul_le_mul_of_nonneg_left (reciprocal_chord ha hab hu.1 hu.2) (Real.exp_pos (-u)).le
  dsimp [expOverSelf]
  convert hc using 1 <;> ring

theorem expOverSelf_tail_bound {a : ℝ} (ha : 1 ≤ a) :
    (∫ u in Ioi a, expOverSelf u) ≤ Real.exp (-a)/a := by
  have hi := expOverSelf_integrable.mono_set (Ioi_subset_Ioi ha)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hu : (∫ u in Ioi a, expOverSelf u) ≤ ∫ u in Ioi a, Real.exp (-u)/a := by
    apply integral_mono_ae hi ((integrableOn_exp_neg_Ioi a).div_const a)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact div_le_div_of_nonneg_left (Real.exp_pos (-u)).le ha0 hu.le
  simpa only [integral_div,integral_exp_neg_Ioi] using hu

/-- Three rational secants and a constant tail bound yield an explicit
upper bound for the exponential integral at one. -/
theorem expOverSelf_integral_le_chords :
    (∫ u in Ioi 1, expOverSelf u) ≤ Real.exp (-1)/3+Real.exp (-(3/2))/3+
      Real.exp (-2)/6+Real.exp (-3)/6 := by
  have h1 := expOverSelf_chord_bound (a := 1) (b := 3/2) (by norm_num) (by norm_num)
  have h2 := expOverSelf_chord_bound (a := 3/2) (b := 2) (by norm_num) (by norm_num)
  have h3 := expOverSelf_chord_bound (a := 2) (b := 3) (by norm_num) (by norm_num)
  have ht := expOverSelf_tail_bound (a := 3) (by norm_num)
  have hs1 := intervalIntegral.integral_Ioi_sub_Ioi expOverSelf_integrable (b := 3/2) (by norm_num)
  have hs2 := intervalIntegral.integral_Ioi_sub_Ioi
    (expOverSelf_integrable.mono_set (Ioi_subset_Ioi (by norm_num : (1:ℝ) ≤ 3/2))) (b := 2) (by norm_num)
  have hs3 := intervalIntegral.integral_Ioi_sub_Ioi
    (expOverSelf_integrable.mono_set (Ioi_subset_Ioi (by norm_num : (1:ℝ) ≤ 2))) (b := 3) (by norm_num)
  norm_num at h1 h2 h3
  linarith

/-- A rational numerical upper bound, proved from certified exponential bounds. -/
theorem expOverSelf_integral_lt : (∫ u in Ioi 1, expOverSelf u) < (23/100:ℝ) := by
  have h1 : Real.exp (-1) ≤ 46/125 := by linarith [Real.exp_neg_one_lt_d9]
  have h2 : Real.exp (-2) ≤ 17/125 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le h1 2
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have h3 : Real.exp (-3) ≤ 1/20 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le h1 3
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hs : Real.exp (-(3/2))^2=Real.exp (-3) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have h15 : Real.exp (-(3/2)) ≤ 9/40 := by nlinarith [Real.exp_pos (-(3/2))]
  linarith [expOverSelf_integral_le_chords]

theorem doubleExp_integrable : IntegrableOn (fun t : ℝ => Real.exp (-Real.exp t)) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono' (by fun_prop)
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp t]

/-- Actual half-line change of variables u=exp(t). -/
theorem doubleExp_integral_eq :
    (∫ t in Ioi 0, Real.exp (-Real.exp t)) = ∫ u in Ioi 1, expOverSelf u := by
  have hg : ContinuousOn expOverSelf (Real.exp '' Ioi 0) := by
    apply (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
    rintro u ⟨t,ht,rfl⟩
    exact (Real.exp_pos t).ne'
  have hgi : IntegrableOn expOverSelf (Real.exp '' Ici 0) := by
    have hi : IntegrableOn expOverSelf (Ici 1) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact expOverSelf_integrable
    apply hi.mono_set
    rintro u ⟨t,ht,rfl⟩
    simpa only [Set.mem_Ici,Real.exp_zero] using Real.exp_le_exp.mpr ht
  have he (t : ℝ) : (expOverSelf ∘ Real.exp) t*Real.exp t=Real.exp (-Real.exp t) := by
    simp [expOverSelf,Function.comp_def,Real.exp_ne_zero]
  have hcomp : IntegrableOn (fun t : ℝ => (expOverSelf ∘ Real.exp) t*Real.exp t) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [he] using doubleExp_integrable
  have hi := integral_comp_mul_deriv_Ioi Real.continuous_exp.continuousOn Real.tendsto_exp_atTop
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) hg hgi hcomp
  simpa only [he,Real.exp_zero] using hi

/-- The precise scalar negative-tail constant needed by mass localization. -/
theorem scaled_doubleExp_integral_lt :
    (∫ t in Ioi 0, Real.exp (-Real.exp ((99/100:ℝ)*t))) < (23/99:ℝ) := by
  rw [integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-Real.exp t)) 0 (by norm_num : (0:ℝ)<99/100)]
  simp only [mul_zero,smul_eq_mul]
  rw [doubleExp_integral_eq]
  have h := mul_lt_mul_of_pos_left expOverSelf_integral_lt (by norm_num : (0:ℝ)<(99/100:ℝ)⁻¹)
  norm_num at h ⊢
  linarith

end NegativeVotingGaussianEnvelopeIntegral
