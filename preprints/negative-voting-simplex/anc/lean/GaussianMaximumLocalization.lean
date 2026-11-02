import GaussianMaximumSecondMoment

/-! Actual Gaussian maximum coefficients entering the mass-localization certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianMaximumLocalization
open NegativeVotingGaussianMaximum NegativeVotingGaussianTail NegativeVotingGaussianMaximumMargins
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumSecondMoment
  NegativeVoting WeakSimplex

/-- An elementary lower tail estimate sufficient for logarithmic quantile control. -/
theorem normalTail_lower_three_quarters (b : ℝ) (hb : 1 ≤ b) :
    (normalPDF 0/2)*Real.exp (-(3/4:ℝ)*b^2) ≤ normalCDF (-b) := by
  have hbpos : 0 < b := by linarith
  have hfac : 1/(2*b) ≤ b/(1+b^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hexp : Real.exp (-b^2/4) ≤ 1/b := by
    have he : b ≤ Real.exp (b^2/4) := by nlinarith [Real.add_one_le_exp (b^2/4),sq_nonneg (b-2)]
    have hi := one_div_le_one_div_of_le hbpos he
    simpa only [Real.exp_neg,one_div,neg_div] using hi
  have hfac' : (1/2:ℝ)*Real.exp (-b^2/4) ≤ b/(1+b^2) := by
    calc
      _ ≤ (1/2:ℝ)*(1/b) := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 1/(2*b) := by ring
      _ ≤ _ := hfac
  have hp := (mul_le_mul_of_nonneg_right hfac' (normalPDF_pos b).le).trans (mills_lower b hbpos)
  have he : (normalPDF 0/2)*Real.exp (-(3/4:ℝ)*b^2)=
      ((1/2:ℝ)*Real.exp (-b^2/4))*normalPDF b := by
    rw [normalPDF_ratio 0 b]
    have hx : Real.exp (-(3/4:ℝ)*b^2)=Real.exp (-b^2/4)*Real.exp (-b^2/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hx]
    ring
  rw [he]
  exact hp

theorem eventually_quantile_sq_ge_log :
    ∀ᶠ (n : ℕ) in atTop, Real.log ((n:ℝ)+2) ≤ upperQuantile n^2 := by
  have hc : 0 < normalPDF 0/2 := div_pos (normalPDF_pos 0) (by norm_num)
  filter_upwards [upperQuantile_tendsto.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop (-4*Real.log (normalPDF 0/2))] with n hb hl
  have ht := normalTail_lower_three_quarters (upperQuantile n) hb
  rw [upperQuantile_tail] at ht
  have hlog := Real.log_le_log (mul_pos hc (Real.exp_pos _)) ht
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp,one_div,Real.log_inv] at hlog
  change -4*Real.log (normalPDF 0/2) ≤ Real.log ((n:ℝ)+2) at hl
  linarith

/-- Actual logarithmic variance decay, rather than an unproved extreme-value heuristic. -/
theorem eventually_maximum_variance_log_bound :
    ∀ᶠ (n : ℕ) in atTop, maximumVariance n ≤ 6/Real.log ((n:ℝ)+2) := by
  filter_upwards [eventually_quantile_sq_ge_log,eventually_maximum_variance_bound] with n hq hv
  have hl : 0 < Real.log ((n:ℝ)+2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact hv.trans (div_le_div_of_nonneg_left (by norm_num) hl hq)

/-- Literal regular-comparator second-weight expression in the localization ledger.
Its separate identification with regular-simplex chaos is not asserted by this definition. -/
def referenceSecondWeight (n : ℕ) : ℝ :=
  ((n:ℝ)+2)*(maximumSecondMoment n-1)^2/(2*((n:ℝ)+1)*(n:ℝ))

theorem referenceSecondWeight_nonneg (n : ℕ) : 0 ≤ referenceSecondWeight n := by
  unfold referenceSecondWeight
  positivity

theorem referenceSecondWeight_log_bound (n : ℕ) (hn : 0 < n)
    (hl : 1 ≤ Real.log ((n:ℝ)+2))
    (hs : maximumSecondMoment n ≤ 5*Real.log ((n:ℝ)+2)) :
    referenceSecondWeight n ≤ 36*(Real.log ((n:ℝ)+2))^2/(n:ℝ) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs0 : 0 ≤ maximumSecondMoment n := integral_nonneg (fun _ => sq_nonneg _)
  have ha : |maximumSecondMoment n-1| ≤ 6*Real.log ((n:ℝ)+2) := abs_le.mpr ⟨by linarith,by linarith⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg (maximumSecondMoment n-1)) ha 2
  simp only [sq_abs] at hsq
  unfold referenceSecondWeight
  apply (div_le_iff₀ (by positivity)).mpr
  have he : (36*Real.log ((n:ℝ)+2)^2/(n:ℝ))*(2*((n:ℝ)+1)*(n:ℝ))=
      72*((n:ℝ)+1)*Real.log ((n:ℝ)+2)^2 := by field_simp <;> ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (n:ℝ)+2 by positivity)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (Real.log ((n:ℝ)+2))),sq_nonneg (Real.log ((n:ℝ)+2))]

theorem referenceSecondWeight_tendsto_zero : Tendsto referenceSecondWeight atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero
  have hmajor : Tendsto (fun n : ℕ => 36*Real.log ((n:ℝ)+2)^2/(n:ℝ)) atTop (𝓝 0) := by
    convert (hbase.comp size_tendsto).const_mul (36:ℝ) using 1
    · funext n
      dsimp only [Function.comp_def]
      ring
    · norm_num
  apply squeeze_zero' (Eventually.of_forall referenceSecondWeight_nonneg) ?_ hmajor
  filter_upwards [eventually_gt_atTop 0,eventually_maximum_second_moment_log_bound,
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1] with n hn hs hl
  exact referenceSecondWeight_log_bound n hn hl hs

def curvatureBound (n : ℕ) : ℝ := max (2*Real.log ((n:ℝ)+2)+1) 6
def sizeRatio (n : ℕ) : ℝ := ((n:ℝ)+2)/((n:ℝ)+1)

theorem inverse_size_minus_one_tendsto :
    Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem sizeRatio_tendsto_one : Tendsto sizeRatio atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1+1/((n:ℝ)+1)) atTop (𝓝 ((1:ℝ)+0)) :=
    tendsto_const_nhds.add inverse_size_minus_one_tendsto
  convert h using 1
  · funext n
    unfold sizeRatio
    field_simp <;> ring
  · norm_num

theorem curvature_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => curvatureBound n/((n:ℝ)+1)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+2)/((n:ℝ)+1)) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp size_tendsto using 1
    funext n
    dsimp only [Function.comp_def]
    rw [pow_one]
    congr 1
    ring
  have hbase : Tendsto (fun n : ℕ => (2*Real.log ((n:ℝ)+2)+1)/((n:ℝ)+1)) atTop (𝓝 0) := by
    convert (hlog.const_mul (2:ℝ)).add inverse_size_minus_one_tendsto using 1
    · funext n
      ring
    · norm_num
  apply hbase.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 3] with n hn
  change 3 ≤ Real.log ((n:ℝ)+2) at hn
  unfold curvatureBound
  rw [max_eq_left (by linarith)]

theorem eventually_denominator_positive :
    ∀ᶠ (n : ℕ) in atTop, 0 < 1-curvatureBound n/((n:ℝ)+1) := by
  filter_upwards [curvature_ratio_tendsto_zero.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
  linarith

/-- The finite localization coefficient expressed using the actual Gaussian
maximum moments. The competitor-to-coefficient inequality is a separate step. -/
def localizationCoefficient (n : ℕ) : ℝ :=
  (sizeRatio n*(((n:ℝ)+2)*(centroidEnvelope n-referenceFirstWeight n))+
    sizeRatio n^2*referenceSecondWeight n+sizeRatio n^2*(1/((n:ℝ)+1))+
    sizeRatio n^2*(1/((n:ℝ)+1))^2)/(1-curvatureBound n/((n:ℝ)+1))

def localizationMajorant (n : ℕ) : ℝ :=
  (sizeRatio n*(39/40:ℝ)+sizeRatio n^2*referenceSecondWeight n+
    sizeRatio n^2*(1/((n:ℝ)+1))+sizeRatio n^2*(1/((n:ℝ)+1))^2)/
    (1-curvatureBound n/((n:ℝ)+1))

theorem localizationCoefficient_eq_original (n : ℕ) :
    localizationCoefficient n = ((n:ℝ)+2)^2/(1-curvatureBound n/((n:ℝ)+1))*
      ((centroidEnvelope n-referenceFirstWeight n)/((n:ℝ)+1)+
       referenceSecondWeight n/((n:ℝ)+1)^2+1/((n:ℝ)+1)^3+1/((n:ℝ)+1)^4) := by
  unfold localizationCoefficient sizeRatio
  by_cases hd : 1-curvatureBound n/((n:ℝ)+1)=0
  · simp [hd]
  · have hn : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp <;> ring

theorem localizationMajorant_tendsto : Tendsto localizationMajorant atTop (𝓝 (39/40:ℝ)) := by
  have hnum := (((sizeRatio_tendsto_one.mul_const (39/40:ℝ)).add
    ((sizeRatio_tendsto_one.pow 2).mul referenceSecondWeight_tendsto_zero)).add
    ((sizeRatio_tendsto_one.pow 2).mul inverse_size_minus_one_tendsto)).add
    ((sizeRatio_tendsto_one.pow 2).mul (inverse_size_minus_one_tendsto.pow 2))
  have hden : Tendsto (fun n : ℕ => 1-curvatureBound n/((n:ℝ)+1)) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.sub curvature_ratio_tendsto_zero
  convert hnum.div hden (by norm_num) using 1
  · funext n
    rfl
  · norm_num

/-- Actual strict first-window coefficient bound, with all Gaussian moment
and tail inputs discharged. No fractional-competitor localization is assumed. -/
theorem eventually_localizationCoefficient_le :
    ∀ᶠ n in atTop, localizationCoefficient n ≤ (49/50:ℝ) := by
  have hm := localizationMajorant_tendsto.eventually
    (gt_mem_nhds (show (39/40:ℝ) < 49/50 by norm_num))
  filter_upwards [eventually_reference_gap_lt_one,eventually_denominator_positive,hm] with n hg hd hm
  have hr : 0 ≤ sizeRatio n := by unfold sizeRatio;positivity
  have hN := mul_le_mul_of_nonneg_left hg hr
  have hbound : localizationCoefficient n ≤ localizationMajorant n := by
    unfold localizationCoefficient localizationMajorant
    apply div_le_div_of_nonneg_right ?_ hd.le
    linarith
  exact hbound.trans hm.le

end NegativeVotingGaussianMaximumLocalization
