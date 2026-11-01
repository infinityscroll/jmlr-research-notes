import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Uniform decay of the scalar remainder rates

This proves a calculus ingredient used when choosing a sufficiently large alphabet.
It does not supply the analytic constants, their uniformity in dimension/noise, or
the earlier localization hypotheses of the Gaussian theorem.
-/

namespace NegativeVoting

open Filter
open scoped Topology

/-- Every fixed nonnegative power of `1 + log x` is dominated by a positive
power of `x`. This includes the two remainder rates in the exterior assembly. -/
theorem logarithmic_remainder_tendsto_zero (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ p / x ^ q) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => (Real.log x) ^ p / x ^ q) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop p hq).tendsto_div_nhds_zero
  have hmajor : Tendsto (fun x : ℝ => (2 : ℝ) ^ p * ((Real.log x) ^ p / x ^ q))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbase
  apply squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    exact div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) p)
      (Real.rpow_nonneg hx0 q)
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hlog : 0 ≤ Real.log x := by linarith
    have hL : 1 + Real.log x ≤ 2 * Real.log x := by linarith
    have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + Real.log x) hL hp
    calc
      (1 + Real.log x) ^ p / x ^ q ≤ (2 * Real.log x) ^ p / x ^ q :=
        div_le_div_of_nonneg_right hpow (Real.rpow_nonneg (le_of_lt hxpos) q)
      _ = (2 : ℝ) ^ p * ((Real.log x) ^ p / x ^ q) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlog]
        ring

/-- The two concrete exterior rates have a single eventual natural-number
threshold for any fixed real coefficients. The threshold is existential. -/
theorem exists_uniform_remainder_threshold (A B : ℝ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      A * ((1 + Real.log (m : ℝ)) ^ (3 : ℕ) / (m : ℝ)) +
      B * ((1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2) /
        (m : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / 2 := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hfirst := (logarithmic_remainder_tendsto_zero (3 : ℕ) 1 (by norm_num) (by norm_num)).comp hnat
  have hsecond := (logarithmic_remainder_tendsto_zero (7 / 2) (1 / 4)
    (by norm_num) (by norm_num)).comp hnat
  have htotal := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A)).mul hfirst).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B)).mul hsecond)
  have htotal' : Tendsto (fun m : ℕ =>
      A * ((1 + Real.log (m : ℝ)) ^ (3 : ℕ) / (m : ℝ)) +
      B * ((1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2) /
        (m : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero, add_zero, Real.rpow_natCast] using htotal
  have hevent := htotal'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  exact Filter.eventually_atTop.mp (hevent.mono (fun _ hm => le_of_lt hm))

end NegativeVoting
