import GaussianTailRatio

/-! Explicit finite Gaussian tail margins used for the eventual mean/quantile gap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianMaximumMargins
open NegativeVotingGaussianMaximum NegativeVotingGaussianTail NegativeVotingMassCentroid
  NegativeVoting WeakSimplex

theorem normalTail_ratio_le_exp (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    normalCDF (-(b+t/b))/normalCDF (-b) ≤ Real.exp (-t) := by
  have hu := normalTail_le_shift b (b+t/b) (le_add_of_nonneg_right (div_nonneg ht hb.le))
  have hexp : (b^2-(b+t/b)^2)/2 ≤ -t := by
    have he : (b^2-(b+t/b)^2)/2 = -t-t^2/(2*b^2) := by field_simp <;> ring
    rw [he]
    exact sub_le_self _ (by positivity)
  apply (div_le_iff₀ (normalCDF_pos (-b))).mpr
  have hh := hu.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (normalCDF_pos (-b)).le)
  simpa only [mul_comm] using hh

/-- A fully finite lower ratio on the fixed interval [0,8]. The deliberately
large threshold makes the numerical margin elementary and explicit. -/
theorem normalTail_ratio_lower_bounded (b t : ℝ) (hb : 0 < b) (hb2 : 1000000 ≤ b^2)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) :
    (999/1000:ℝ)*Real.exp (-t) ≤ normalCDF (-(b+t/b))/normalCDF (-b) := by
  have hb1000 : 1000 ≤ b := by nlinarith
  have hr0 : 0 ≤ t/b := div_nonneg ht hb.le
  have hr1 : t/b ≤ 1/100 := (div_le_iff₀ hb).mpr (by nlinarith)
  have hr2 : (t/b)^2 ≤ 1/10000 := by nlinarith
  have hbt : b*(t/b)=t := by field_simp
  have hc : (9999/10000:ℝ) ≤ b*(b+t/b)/(1+(b+t/b)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (9999/10000:ℝ) ≤ Real.exp (-(t/b)^2/2) := by
    have hh := Real.add_one_le_exp (-(t/b)^2/2)
    linarith
  have heq : (b^2-(b+t/b)^2)/2 = -t-(t/b)^2/2 := by nlinarith
  have hp : (9999/10000:ℝ)*(9999/10000) ≤
      (b*(b+t/b)/(1+(b+t/b)^2))*Real.exp (-(t/b)^2/2) :=
    mul_le_mul hc he (by norm_num) (by positivity)
  calc
    _ ≤ ((9999/10000:ℝ)*(9999/10000))*Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ ≤ ((b*(b+t/b)/(1+(b+t/b)^2))*Real.exp (-(t/b)^2/2))*Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (b*(b+t/b)/(1+(b+t/b)^2))*Real.exp ((b^2-(b+t/b)^2)/2) := by
      rw [heq,sub_eq_add_neg,Real.exp_add]
      ring
    _ ≤ _ := normalTail_ratio_lower b (b+t/b) hb (by positivity)

/-- The actual scaled maximum has an explicit finite-interval lower tail
margin. No limiting distribution or moment-convergence premise is used. -/
theorem scaledMaximum_positive_tail_lower (n : ℕ) (hn : 0 < n)
    (hb2 : 1000000 ≤ upperQuantile n^2) (t : ℝ) (ht : 0 ≤ t) (ht8 : t ≤ 8) :
    (999/1000:ℝ)*Real.exp (-t)-Real.exp (-2*t)/2 ≤
      (standardGaussian (Fin (n+2))).real {x | t < scaledMaximum n x} := by
  let b := upperQuantile n
  have hb : 0 < b := upperQuantile_pos hn
  let lam := (Fintype.card (Fin (n+2)):ℝ)*normalCDF (-(b+t/b))
  have hq : normalCDF (-(b+t/b))/normalCDF (-b)=lam := by
    simp only [lam,b,upperQuantile_tail,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
    field_simp
  have hl := normalTail_ratio_lower_bounded b t hb hb2 ht ht8
  have hu := normalTail_ratio_le_exp b t hb ht
  rw [hq] at hl hu
  have hlam : 0 ≤ lam := mul_nonneg (Nat.cast_nonneg _) (normalCDF_pos _).le
  have hs : {x : Fin (n+2) → ℝ | t < scaledMaximum n x}={x | b+t/b < maximum x} := by
    ext x
    change t < b*(maximum x-b) ↔ b+t/b < maximum x
    rw [mul_comm b,← div_lt_iff₀ hb,lt_sub_iff_add_lt,add_comm (t/b) b]
  rw [hs]
  have hg := (maximum_survival_bounds (ι := Fin (n+2)) (b+t/b)).1
  change lam-lam^2/2 ≤ _ at hg
  have hsquare : lam^2 ≤ Real.exp (-2*t) := by
    have he : Real.exp (-t)^2=Real.exp (-2*t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num <;> ring
    rw [← he]
    exact pow_le_pow_left₀ hlam hu 2
  linarith

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The far lower tail is controlled by the actual all-coordinates event. -/
theorem maximum_far_negative_tail (s : ℝ) (hs : 0 ≤ s) :
    (standardGaussian ι).real {x | maximum x ≤ -s} ≤
      (1/2:ℝ)^Fintype.card ι*Real.exp (-(Fintype.card ι:ℝ)*s^2/2) := by
  rw [maximum_cdf]
  have hh := pow_le_pow_left₀ (normalCDF_pos (-s)).le (normalTail_le_half_exp s hs) (Fintype.card ι)
  rw [mul_pow,← Real.exp_nat_mul] at hh
  convert hh using 1
  congr 2
  ring

end NegativeVotingGaussianMaximumMargins
