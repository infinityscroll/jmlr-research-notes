import GaussianMaximumLocalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Scalar quantile absorptions used by Gaussian hazard envelopes. Thresholds
depend only on the displayed scalar constants. No assertion about a hazard
integral or a conditional Gaussian moment is an assumption or conclusion. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set Asymptotics
open scoped Topology
namespace NegativeVotingHazardQuantileAsymptotics
open NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianMaximumLocalization NegativeVotingGaussianTail
  NegativeVotingGaussianMaximumSecondMoment

/-- Direct upper quantile exponential comparison; no asymptotic remainder. -/
theorem quantile_exp_sq_half_le_rpow (n : ℕ) (hn : 0 < n)
    (d : ℝ) (hd : 0 ≤ d) :
    Real.exp (d*(upperQuantile n)^2/2) ≤ ((n:ℝ)+2)^d := by
  have hm : 0 < (n:ℝ)+2 := by positivity
  rw [Real.rpow_def_of_pos hm]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (upperQuantile_sq_le_log n hn) hd
  nlinarith

/-- The corresponding lower bound for the decaying exponential. -/
theorem rpow_neg_twice_le_quantile_exp_neg_sq (n : ℕ) (hn : 0 < n)
    (d : ℝ) (hd : 0 ≤ d) :
    ((n:ℝ)+2)^(-2*d) ≤ Real.exp (-d*(upperQuantile n)^2) := by
  have hm : 0 < (n:ℝ)+2 := by positivity
  rw [Real.rpow_def_of_pos hm]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (upperQuantile_sq_le_log n hn) hd
  nlinarith

/-- A polynomial in log(m) is absorbed by every positive power of m. -/
theorem eventually_const_log_pow_le_rpow (C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log ((n:ℝ)+2))^q ≤ ((n:ℝ)+2)^η := by
  have ho := ((isLittleO_log_rpow_rpow_atTop (q:ℝ) hη).const_mul_left C).comp_tendsto size_tendsto
  filter_upwards [ho.def (show (0:ℝ) < 1 by norm_num)] with n hn
  have hm : 0 ≤ (n:ℝ)+2 := by positivity
  have hl : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (pow_nonneg hl q)),
    abs_of_nonneg (Real.rpow_nonneg hm η),one_mul] using hn

/-- Actual quantiles grow more slowly than every fixed positive power of the
alphabet size, including the constant factor and degree-zero case. -/
theorem eventually_quantile_polynomial_le_rpow (C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      C*(1+upperQuantile n)^q ≤ ((n:ℝ)+2)^η := by
  filter_upwards [eventually_gt_atTop (0:ℕ),upperQuantile_tendsto.eventually_ge_atTop 1,
    eventually_const_log_pow_le_rpow (C*4^q) (by positivity) q η hη] with n hn hb hlog
  have hq := upperQuantile_sq_le_log n hn
  have hb' : 0 ≤ 1+upperQuantile n := by linarith
  have hbase : 1+upperQuantile n ≤ 4*Real.log ((n:ℝ)+2) := by nlinarith
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb' hbase q) hC
  have he : C*(4*Real.log ((n:ℝ)+2))^q=(C*4^q)*(Real.log ((n:ℝ)+2))^q := by rw [mul_pow]; ring
  exact (hp.trans_eq he).trans hlog

/-- Strict real-power separation absorbs every fixed quantile polynomial. -/
theorem eventually_rpow_quantile_polynomial_le (C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) (u v : ℝ) (huv : u < v) :
    ∀ᶠ n : ℕ in atTop,
      C*((n:ℝ)+2)^u*(1+upperQuantile n)^q ≤ ((n:ℝ)+2)^v := by
  filter_upwards [eventually_quantile_polynomial_le_rpow C hC q (v-u) (sub_pos.mpr huv)] with n hn
  have hm : 0 < (n:ℝ)+2 := by positivity
  calc
    _ = ((n:ℝ)+2)^u*(C*(1+upperQuantile n)^q) := by ring
    _ ≤ ((n:ℝ)+2)^u*((n:ℝ)+2)^(v-u) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hm.le u)
    _ = ((n:ℝ)+2)^(u+(v-u)) := (Real.rpow_add hm u (v-u)).symm
    _ = _ := by congr 1; ring

/-- Stretched exponential decay beats any prescribed real power. -/
theorem eventually_exp_neg_rpow_le_rpow (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (v : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-a*((n:ℝ)+2)^c) ≤ ((n:ℝ)+2)^v := by
  have ht := (tendsto_rpow_atTop hc).comp size_tendsto
  have ho := (isLittleO_exp_neg_mul_rpow_atTop ha (v/c)).comp_tendsto ht
  filter_upwards [ho.def (show (0:ℝ) < 1 by norm_num)] with n hn
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hpos := Real.rpow_pos_of_pos hm c
  have he : (((n:ℝ)+2)^c)^(v/c)=((n:ℝ)+2)^v := by
    rw [←Real.rpow_mul hm.le]
    congr 1
    field_simp
  have hh : Real.exp (-a*((n:ℝ)+2)^c) ≤ (((n:ℝ)+2)^c)^(v/c) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg hpos.le (v/c)),one_mul] using hn
  exact hh.trans_eq he

/-- The quantile double-exponential remainder absorbs any fixed polynomial
alphabet growth, any quantile polynomial, and any requested inverse power. -/
theorem eventually_quantile_double_exp_le (C : ℝ) (hC : 0 ≤ C)
    (p q A : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      C*((n:ℝ)+2)^p*(1+upperQuantile n)^q*
        Real.exp (-(1/2:ℝ)*Real.exp (c*(upperQuantile n)^2)) ≤ ((n:ℝ)+2)^(-(A:ℝ)) := by
  filter_upwards [eventually_quantile_polynomial_le_rpow C hC q 1 (by norm_num),
    eventually_quantile_sq_ge_log,
    eventually_exp_neg_rpow_le_rpow (1/2) c (by norm_num) hc (-(A:ℝ)-(p:ℝ)-1),
    upperQuantile_tendsto.eventually_ge_atTop 1] with n hpoly hsq hexp hb
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hinner : ((n:ℝ)+2)^c ≤ Real.exp (c*(upperQuantile n)^2) := by
    rw [Real.rpow_def_of_pos hm]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdec : Real.exp (-(1/2:ℝ)*Real.exp (c*(upperQuantile n)^2)) ≤
      ((n:ℝ)+2)^(-(A:ℝ)-(p:ℝ)-1) := by
    apply le_trans _ hexp
    apply Real.exp_le_exp.mpr
    linarith
  have hcoef : 0 ≤ C*(1+upperQuantile n)^q := by
    apply mul_nonneg hC
    apply pow_nonneg
    linarith
  calc
    _ = ((n:ℝ)+2)^p*(C*(1+upperQuantile n)^q)*
        Real.exp (-(1/2:ℝ)*Real.exp (c*(upperQuantile n)^2)) := by ring
    _ ≤ ((n:ℝ)+2)^p*((n:ℝ)+2)^(1:ℝ)*((n:ℝ)+2)^(-(A:ℝ)-(p:ℝ)-1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (pow_nonneg hm.le p)) hdec
        (Real.exp_pos _).le (mul_nonneg (pow_nonneg hm.le p) (Real.rpow_nonneg hm.le 1))
    _ = ((n:ℝ)+2)^(-(A:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hm,←Real.rpow_add hm]
      congr 1
      ring

end NegativeVotingHazardQuantileAsymptotics
