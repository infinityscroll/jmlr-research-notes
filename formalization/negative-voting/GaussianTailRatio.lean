import GaussianMaximum

/-! Exact Gaussian tail-ratio and actual maximum-tail estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace NegativeVotingGaussianTail
open NegativeVotingGaussianMaximum NegativeVotingMassCentroid NegativeVoting WeakSimplex

def correctedLogTail (x : ℝ) : ℝ := Real.log (normalCDF (-x))+x^2/2

theorem correctedLogTail_hasDerivAt (x : ℝ) :
    HasDerivAt correctedLogTail (x-normalPDF x/normalCDF (-x)) x := by
  have hc := (hasDerivAt_normalCDF (-x)).comp x (hasDerivAt_id x).neg
  rw [normalPDF_even] at hc
  have hd := (hc.log (normalCDF_pos (-x)).ne').add (((hasDerivAt_id x).pow 2).div_const 2)
  convert hd using 1
  · funext y
    simp [correctedLogTail,div_eq_mul_inv]
  · simp
    ring

/-- An exact global monotonicity consequence of the proved Gaussian Mills bound. -/
theorem correctedLogTail_antitone : Antitone correctedLogTail := by
  apply antitone_of_hasDerivAt_nonpos correctedLogTail_hasDerivAt
  intro x
  change x-normalPDF x/normalCDF (-x) ≤ 0
  by_cases hx : 0 < x
  · have hu := (mills_upper x hx)
    have hmul : normalCDF (-x)*x ≤ normalPDF x := (le_div_iff₀ hx).mp hu
    have hh : x ≤ normalPDF x/normalCDF (-x) :=
      (le_div_iff₀ (normalCDF_pos (-x))).mpr (by nlinarith)
    linarith
  · have hh := div_pos (normalPDF_pos x) (normalCDF_pos (-x))
    linarith

/-- Exact upper ratio, with the quadratic exponent retained. -/
theorem normalTail_le_shift (a b : ℝ) (hab : a ≤ b) :
    normalCDF (-b) ≤ normalCDF (-a)*Real.exp ((a^2-b^2)/2) := by
  have hh := correctedLogTail_antitone hab
  unfold correctedLogTail at hh
  have he : Real.log (normalCDF (-b)) ≤ Real.log (normalCDF (-a))+(a^2-b^2)/2 := by linarith
  have he' := Real.exp_le_exp.mpr he
  simpa only [Real.exp_add,Real.exp_log (normalCDF_pos (-a)),
    Real.exp_log (normalCDF_pos (-b))] using he'

/-- Equivalent exact lower ratio, useful for the lower maximum tail. -/
theorem normalTail_ge_shift (a b : ℝ) (hab : a ≤ b) :
    normalCDF (-b)*Real.exp ((b^2-a^2)/2) ≤ normalCDF (-a) := by
  have hh := correctedLogTail_antitone hab
  unfold correctedLogTail at hh
  have he : Real.log (normalCDF (-b))+(b^2-a^2)/2 ≤ Real.log (normalCDF (-a)) := by linarith
  have he' := Real.exp_le_exp.mpr he
  simpa only [Real.exp_add,Real.exp_log (normalCDF_pos (-a)),
    Real.exp_log (normalCDF_pos (-b))] using he'

theorem normalTail_le_half_exp (x : ℝ) (hx : 0 ≤ x) :
    normalCDF (-x) ≤ (1/2)*Real.exp (-x^2/2) := by
  simpa only [neg_zero,normalCDF_zero,zero_pow (by norm_num : 2≠0),zero_sub] using
    normalTail_le_shift 0 x hx

theorem normalPDF_ratio (a b : ℝ) :
    normalPDF b=normalPDF a*Real.exp ((a^2-b^2)/2) := by
  have hp (x : ℝ) : normalPDF x=(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
    norm_num [normalPDF,gaussianPDFReal]
  rw [hp,hp,mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- Matching elementary lower ratio from both actual Mills inequalities. -/
theorem normalTail_ratio_lower (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a*b/(1+b^2))*Real.exp ((a^2-b^2)/2) ≤ normalCDF (-b)/normalCDF (-a) := by
  have hu := mills_upper a ha
  have hl := mills_lower b hb
  rw [normalPDF_ratio a b] at hl
  apply (le_div_iff₀ (normalCDF_pos (-a))).mpr
  have hfac : 0 ≤ a*b/(1+b^2)*Real.exp ((a^2-b^2)/2) := by positivity
  calc
    _ ≤ (a*b/(1+b^2)*Real.exp ((a^2-b^2)/2))*(normalPDF a/a) :=
      mul_le_mul_of_nonneg_left hu hfac
    _ = (b/(1+b^2))*(normalPDF a*Real.exp ((a^2-b^2)/2)) := by field_simp <;> ring
    _ ≤ _ := hl

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Actual lower-tail CDF of the independent maximum has the exponential bound. -/
theorem maximum_cdf_le_exp (x : ℝ) :
    (standardGaussian ι).real {z | maximum z ≤ x} ≤
      Real.exp (-(Fintype.card ι:ℝ)*normalCDF (-x)) := by
  rw [maximum_cdf]
  have hbase : normalCDF x ≤ Real.exp (-normalCDF (-x)) := by
    have hh := Real.add_one_le_exp (-normalCDF (-x))
    have hs := normalCDF_neg x
    linarith
  have hp := pow_le_pow_left₀ (normalCDF_pos x).le hbase (Fintype.card ι)
  simpa only [← Real.exp_nat_mul,neg_mul,mul_neg] using hp

/-- Positive centered-maximum tails have an exact exponential bound, for
all t≥0, rather than merely a bounded-interval limit. -/
theorem scaledMaximum_positive_tail (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    (standardGaussian (Fin (n+2))).real {x | t < scaledMaximum n x} ≤ Real.exp (-t) := by
  let b := upperQuantile n
  have hb : 0 < b := upperQuantile_pos hn
  have hbe : b ≤ b+t/b := le_add_of_nonneg_right (div_nonneg ht hb.le)
  have hs : {x : Fin (n+2) → ℝ | t < scaledMaximum n x}={x | b+t/b < maximum x} := by
    ext x
    change t < b*(maximum x-b) ↔ b+t/b < maximum x
    rw [mul_comm b,← div_lt_iff₀ hb,lt_sub_iff_add_lt,add_comm (t/b) b]
  rw [hs]
  apply (maximum_survival_bounds (ι := Fin (n+2)) (b+t/b)).2.trans
  have hu := normalTail_le_shift b (b+t/b) hbe
  have hexp : (b^2-(b+t/b)^2)/2 ≤ -t := by
    have he : (b^2-(b+t/b)^2)/2 = -t-t^2/(2*b^2) := by field_simp <;> ring
    rw [he]
    exact sub_le_self _ (by positivity)
  have huc : normalCDF (-(b+t/b)) ≤ normalCDF (-b)*Real.exp (-t) :=
    hu.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (normalCDF_pos (-b)).le)
  have hh := mul_le_mul_of_nonneg_left huc (Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin (n+2))))
  have he : (Fintype.card (Fin (n+2)):ℝ)*normalCDF (-b)=1 := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,b,upperQuantile_tail]
    field_simp
  rw [← mul_assoc,he,one_mul] at hh
  exact hh

/-- The lower centered-maximum tail has a dimension-free double-exponential
bound up to b²/50. All laws and quantile identities are the actual Gaussian ones. -/
theorem scaledMaximum_negative_tail (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : 0 ≤ t) (htb : t ≤ upperQuantile n^2/50) :
    (standardGaussian (Fin (n+2))).real {x | scaledMaximum n x ≤ -t} ≤
      Real.exp (-Real.exp ((99/100:ℝ)*t)) := by
  let b := upperQuantile n
  have hb : 0 < b := upperQuantile_pos hn
  have ha : b-t/b ≤ b := sub_le_self _ (div_nonneg ht hb.le)
  have hs : {x : Fin (n+2) → ℝ | scaledMaximum n x ≤ -t}={x | maximum x ≤ b-t/b} := by
    ext x
    change b*(maximum x-b) ≤ -t ↔ maximum x ≤ b-t/b
    rw [mul_comm b,← le_div_iff₀ hb,neg_div]
    constructor <;> intro hx <;> linarith
  rw [hs]
  apply (maximum_cdf_le_exp (ι := Fin (n+2)) (b-t/b)).trans
  apply Real.exp_le_exp.mpr
  have hu := normalTail_ge_shift (b-t/b) b ha
  have he : (Fintype.card (Fin (n+2)):ℝ)*normalCDF (-b)=1 := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,b,upperQuantile_tail]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin (n+2))))
  rw [← mul_assoc,he,one_mul] at hh
  have hexp : (99/100:ℝ)*t ≤ (b^2-(b-t/b)^2)/2 := by
    have heq : (b^2-(b-t/b)^2)/2=t-t^2/(2*b^2) := by field_simp <;> ring
    rw [heq]
    have htb' : t ≤ b^2/50 := htb
    have ht2 : t^2 ≤ t*b^2/50 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr htb')]
    have hdiv : t^2/(2*b^2) ≤ t/100 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hl := (Real.exp_le_exp.mpr hexp).trans hh
  linarith

/-- The normal quantile has the elementary logarithmic square bound. -/
theorem upperQuantile_sq_le_log (n : ℕ) (hn : 0 < n) :
    upperQuantile n ^ 2 ≤ 2*Real.log ((n:ℝ)+2) := by
  have hb := upperQuantile_pos hn
  have ht := normalTail_le_half_exp (upperQuantile n) hb.le
  rw [upperQuantile_tail] at ht
  have hhalf : (1/2:ℝ)*Real.exp (-upperQuantile n^2/2) ≤ Real.exp (-upperQuantile n^2/2) := by
    nlinarith [Real.exp_pos (-upperQuantile n^2/2)]
  have he := Real.log_le_log (by positivity : 0 < 1/((n:ℝ)+2)) (ht.trans hhalf)
  rw [Real.log_exp,one_div,Real.log_inv] at he
  linarith

end NegativeVotingGaussianTail
