import GaussianRegularQuadraticRepresentation

/-! Logarithmic bound for the actual regular quadratic moment coefficient.
The only asymptotic input is the already proved Gaussian maximum estimate. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace NegativeVotingRegularCoefficientBound
open NegativeVotingRegularQuadraticRepresentation NegativeVotingRegularQuadratic
  NegativeVotingGaussianMaximumSecondMoment

theorem momentCoefficient_eq (n : ℕ) (hn : 1 ≤ n) :
    momentCoefficient n = ((n:ℝ)+2)*(maximumSecondMoment n-1)/(((n:ℝ)+1)*(n:ℝ)) := by
  rw [momentCoefficient,moment_distinguished]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  have h : (n:ℝ)+2≠0 := by positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by linarith
  have hn1 : (n:ℝ)+1≠0 := by linarith
  have hn1' : 1+(n:ℝ)≠0 := by linarith
  rw [show (n:ℝ)+2-1=(n:ℝ)+1 by ring,show (n:ℝ)+2-2=(n:ℝ) by ring]
  field_simp [h,hn0,hn1]
  <;> ring

theorem momentCoefficient_log_bound (n : ℕ) (hn : 1 ≤ n)
    (hs : maximumSecondMoment n ≤ 5*Real.log ((n:ℝ)+2)) :
    |momentCoefficient n| ≤ 30*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) := by
  let m : ℝ := (n:ℝ)+2
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm : 3 ≤ m := by dsimp [m];linarith
  have hm0 : 0 < m := by linarith
  have hd : 0 < (m-1)*(m-2) := mul_pos (by linarith) (by linarith)
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hs0 : 0 ≤ maximumSecondMoment n := integral_nonneg fun _=>sq_nonneg _
  have hsa : |maximumSecondMoment n-1| ≤ 6*(1+Real.log m) := by
    apply abs_le.mpr
    change maximumSecondMoment n ≤ 5*Real.log m at hs
    constructor <;> linarith
  have hratio : m^2 ≤ 5*((m-1)*(m-2)) := by
    nlinarith [mul_nonneg (show 0 ≤ m-3 by linarith) (show 0 ≤ 4*m-3 by linarith)]
  have he : momentCoefficient n=m*(maximumSecondMoment n-1)/((m-1)*(m-2)) := by
    rw [momentCoefficient_eq n hn]
    dsimp [m]
    congr 1 <;> ring
  rw [he,abs_div,abs_mul,abs_of_pos hm0,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  apply le_trans (mul_le_mul_of_nonneg_left hsa hm0.le)
  change m*(6*(1+Real.log m)) ≤ 30*(1+Real.log m)/m*((m-1)*(m-2))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm0).mpr
  convert mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 6*(1+Real.log m)) using 1 <;> ring

theorem eventually_momentCoefficient_log_bound :
    ∀ᶠ n : ℕ in atTop,
      |momentCoefficient n| ≤ 30*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) := by
  filter_upwards [eventually_ge_atTop 1,eventually_maximum_second_moment_log_bound] with n hn hs
  exact momentCoefficient_log_bound n hn hs
end NegativeVotingRegularCoefficientBound
