import GaussianHazardMomentEnvelope
import GaussianMaximumLocalization

/-! Quantile-scale bounds for the full threshold split. These use the actual
Gaussian quantile, its exact tail probability and Mills inequalities. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingHazardQuantileBounds
open WeakSimplex NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianTail NegativeVotingHazardThresholdBounds
  NegativeVotingHazardMomentEnvelope NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingMassCentroid

lemma quantile_density_lower (n : ℕ) (hn : 0 < n) :
    upperQuantile n/((n:ℝ)+2) ≤ normalPDF (upperQuantile n) := by
  have hh := mills_upper (upperQuantile n) (upperQuantile_pos hn)
  rw [upperQuantile_tail] at hh
  have ht := (le_div_iff₀ (upperQuantile_pos hn)).mp hh
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using ht

lemma quantile_density_upper (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n) :
    normalPDF (upperQuantile n) ≤ 2*upperQuantile n/((n:ℝ)+2) := by
  have hh := upperQuantile_density_bound n hn
  have hi : 1/upperQuantile n ≤ upperQuantile n := by
    apply (div_le_iff₀ (upperQuantile_pos hn)).mpr
    nlinarith
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+2)).mpr
  nlinarith

lemma scaled_quantile_tail_upper (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    ((n:ℝ)+2)*normalCDF (-((1+a)*upperQuantile n)) ≤
      Real.exp (-(a+a^2/2)*(upperQuantile n)^2) := by
  have hb := upperQuantile_pos hn
  have hh := normalTail_le_shift (upperQuantile n) ((1+a)*upperQuantile n) (by nlinarith)
  rw [upperQuantile_tail] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (n:ℝ)+2)
  convert hh' using 1 <;> field_simp <;> congr 1 <;> ring

lemma scaled_quantile_tail_lower (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp ((a-a^2/2)*(upperQuantile n)^2) ≤
      ((n:ℝ)+2)*normalCDF (-((1-a)*upperQuantile n)) := by
  have hb := upperQuantile_pos hn
  have hh := normalTail_ge_shift ((1-a)*upperQuantile n) (upperQuantile n) (by nlinarith)
  rw [upperQuantile_tail] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (n:ℝ)+2)
  convert hh' using 1 <;> field_simp <;> congr 1 <;> ring

/-- The lower region is doubly exponentially small in the quantile squared. -/
lemma low_threshold_CDF_power (n : ℕ) (hn : 0 < n) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1/16) :
    normalCDF ((((1-4*a)*upperQuantile n)+a*upperQuantile n)/(1-a))^(n+1) ≤
      Real.exp (-(1/2:ℝ)*Real.exp (a*(upperQuantile n)^2/2)) := by
  have hb := upperQuantile_pos hn
  have hs : 0 < 1-a := by linarith
  have hu : (((1-4*a)*upperQuantile n)+a*upperQuantile n)/(1-a) ≤ (1-a)*upperQuantile n := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg (sq_nonneg a) hb.le]
  have hpow := pow_le_pow_left₀ (normalCDF_pos _).le (strictMono_normalCDF.monotone hu) (n+1)
  refine hpow.trans ((cdf_power_exponential ((1-a)*upperQuantile n) (n+1)).trans ?_)
  have htail := scaled_quantile_tail_lower n hn a ha.le
  have hexp : Real.exp (a*(upperQuantile n)^2/2) ≤ Real.exp ((a-a^2/2)*(upperQuantile n)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ a-a^2 by nlinarith) (sq_nonneg (upperQuantile n))]
  have hhalf : (1/2:ℝ)*(((n:ℝ)+2)*normalCDF (-((1-a)*upperQuantile n))) ≤
      ((n+1:ℕ):ℝ)*normalCDF (-((1-a)*upperQuantile n)) := by
    push_cast
    nlinarith [normalCDF_pos (-((1-a)*upperQuantile n)),Nat.cast_nonneg (α:=ℝ) n,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (normalCDF_pos (-((1-a)*upperQuantile n))).le]
  have hfull := (mul_le_mul_of_nonneg_left (hexp.trans htail) (by norm_num : (0:ℝ) ≤ 1/2)).trans hhalf
  exact Real.exp_le_exp.mpr (by linarith)

lemma high_threshold_standardized (b a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    (1-6*a)*b ≤ (((1-4*a)*b)-a*b)/(1+a) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+a)).mpr
  nlinarith [mul_nonneg (sq_nonneg a) hb]

lemma upper_interval_standardized (b a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (ha1 : a ≤ 1/16) :
    (((1+5*a)*b)+a*b)/(1-a) ≤ (1+8*a)*b := by
  apply (div_le_iff₀ (by linarith : (0:ℝ) < 1-a)).mpr
  have hh : 0 ≤ 2*a-8*a^2 := by nlinarith
  nlinarith [mul_nonneg hh hb]

lemma upper_interval_tail (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/16) :
    ((n:ℝ)+2)*normalCDF (-((((1+4*a)*upperQuantile n)-a*upperQuantile n)/(1+a))) ≤
      Real.exp (-a*(upperQuantile n)^2) := by
  have hb := upperQuantile_pos hn
  have hu : (1+a)*upperQuantile n ≤ (((1+4*a)*upperQuantile n)-a*upperQuantile n)/(1+a) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+a)).mpr
    nlinarith [mul_nonneg (show 0 ≤ a-a^2 by nlinarith) hb.le]
  have hc := strictMono_normalCDF.monotone (neg_le_neg hu)
  have hh := (mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ (n:ℝ)+2)).trans
    (scaled_quantile_tail_upper n hn a ha.le)
  exact hh.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (upperQuantile n))]))

/-- The exact Gaussian density factor after peeling off an integrable
exponential. All label powers still cancel against the quantile density. -/
lemma high_density_factor (n : ℕ) (hn : 0 < n) (hb : 1 ≤ upperQuantile n)
    (a lam : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/16) (hlam0 : 0 ≤ lam)
    (k : ℕ) (hlam : lam ≤ k) :
    normalPDF 0^k*Real.exp (-((k:ℝ)-lam)*
      ((((1-4*a)*upperQuantile n)-a*upperQuantile n)/(1+a))^2/2) ≤
      (2*upperQuantile n/((n:ℝ)+2))^k*
        Real.exp ((12*a*(k:ℝ)+lam)*(upperQuantile n)^2/2) := by
  let b := upperQuantile n
  let z := (((1-4*a)*b)-a*b)/(1+a)
  have hb0 : 0 ≤ b := (upperQuantile_pos hn).le
  have ha0 : 0 ≤ (1-6*a)*b := mul_nonneg (by linarith) hb0
  have hz : (1-6*a)*b ≤ z := high_threshold_standardized b a hb0 ha
  have hzsq := pow_le_pow_left₀ ha0 hz 2
  have hksq := mul_le_mul_of_nonneg_left hzsq (sub_nonneg.mpr hlam)
  have hrest : 0 ≤ (12*a*lam+36*a^2*((k:ℝ)-lam))*b^2 := by positivity
  have hexp : -((k:ℝ)-lam)*z^2/2 ≤ -(k:ℝ)*b^2/2+(12*a*(k:ℝ)+lam)*b^2/2 := by
    nlinarith [hrest]
  have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (pow_nonneg (normalPDF_pos 0).le k)
  have hid : normalPDF 0^k*Real.exp (-(k:ℝ)*b^2/2+(12*a*(k:ℝ)+lam)*b^2/2)=
      normalPDF b^k*Real.exp ((12*a*(k:ℝ)+lam)*b^2/2) := by
    rw [normalPDF_ratio 0 b,mul_pow,←Real.exp_nat_mul]
    have he : (k:ℝ)*((0^2-b^2)/2)=-(k:ℝ)*b^2/2 := by ring
    rw [he,Real.exp_add]
    ring
  rw [hid] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (normalPDF_pos b).le (quantile_density_upper n hn hb) k) (Real.exp_pos _).le)

end NegativeVotingHazardQuantileBounds
