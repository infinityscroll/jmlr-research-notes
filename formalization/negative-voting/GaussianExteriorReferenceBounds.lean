import GaussianUniformMassBound
import GaussianProcrustesDistance
import GaussianFacetMeanBound

/-! Actual reference-scale and competitive row-energy bounds used by the
exterior covariance remainder. Every eventual threshold precedes the ambient
space, reference orientation, fractional assignment and negative correlation. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
universe u
namespace NegativeVotingExteriorReference
open NegativeVoting WeakSimplex NegativeVotingGaussianMaximum NegativeVotingGaussianTail
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumSecondMoment
  NegativeVotingBalancedReference NegativeVotingMovingCap NegativeVotingFractionalMass
  NegativeVotingUniformMassBound NegativeVotingCompetitiveDeficit NegativeVotingRegularSecondGap
  NegativeVotingAssignmentCoordinateBridge NegativeVotingCentroidOptimization
  NegativeVotingAssignmentDuality

/-- Mills' actual lower tail bound supplies the lower logarithmic quantile
scale. No asymptotic quantile formula is an input. -/
theorem quantile_logarithmic_lower (n:ℕ) (hb1:1≤ upperQuantile n)
    (hb2:4*(2+|Real.log (normalPDF 0)|)≤(upperQuantile n)^2):
    1+Real.log ((n:ℝ)+2)≤(upperQuantile n)^2:=by
  let b:=upperQuantile n
  have hb:0< b:=by change 1≤ b at hb1;linarith
  have hm:0<(n:ℝ)+2:=by positivity
  have hratio:1/(2*b)≤ b/(1+b^2):=by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    change 1≤ b at hb1
    nlinarith
  have ht:= (mul_le_mul_of_nonneg_right hratio (normalPDF_pos b).le).trans (mills_lower b hb)
  change (1/(2*b))*normalPDF b≤ normalCDF (-upperQuantile n) at ht
  rw [upperQuantile_tail] at ht
  have hlog:=Real.log_le_log (mul_pos (by positivity) (normalPDF_pos b)) ht
  have hpdf:Real.log (normalPDF b)=Real.log (normalPDF 0)-b^2/2:=by
    rw [normalPDF_factor,Real.log_mul (ne_of_gt (normalPDF_pos 0)) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    ring
  rw [Real.log_mul (by positivity) (ne_of_gt (normalPDF_pos b)),
    Real.log_div (by norm_num) (by positivity),Real.log_one,
    Real.log_mul (by norm_num) (ne_of_gt hb),hpdf,
    Real.log_div (by norm_num) (ne_of_gt hm),Real.log_one] at hlog
  have hlb:Real.log b≤ b^2/4:=by
    have hh:=Real.log_le_sub_one_of_pos hb
    nlinarith [sq_nonneg (b-2)]
  have hl2:Real.log (2:ℝ)≤1:=by
    have hh:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    linarith
  have hc:-(Real.log (normalPDF 0))≤|Real.log (normalPDF 0)|:=neg_le_abs _
  change 4*(2+|Real.log (normalPDF 0)|)≤ b^2 at hb2
  change 1+Real.log ((n:ℝ)+2)≤ b^2
  nlinarith

/-- The physical regular scale has the actual logarithmic size with explicit
universal constants. -/
theorem eventually_reference_scale_bounds:
    ∀ᶠ n:ℕ in atTop,
      (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)^2≤(referenceScale n)^2 ∧
      (referenceScale n)^2≤20*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)^2:=by
  filter_upwards [upperQuantile_tendsto.eventually_ge_atTop 1,
    upperQuantile_sq_tendsto.eventually_ge_atTop (4*(2+|Real.log (normalPDF 0)|)),
    eventually_scaledMaximum_mean_lower,eventually_maximum_second_moment_log_bound]
    with n hb1 hb2 hmean hsecond
  have hb:0< upperQuantile n:=by linarith
  have hμ:upperQuantile n≤ maximumMean n:=by
    have hh:0≤ upperQuantile n*(maximumMean n-upperQuantile n):=by linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hb).mp hh)
  have hlo:=quantile_logarithmic_lower n hb1 hb2
  have hμ2:(upperQuantile n)^2≤(maximumMean n)^2:=
    pow_le_pow_left₀ hb.le hμ 2
  have hV:0≤ maximumVariance n:=variance_nonneg _ _
  rw [maximumVariance_eq_second_sub_mean_sq] at hV
  have hL:0≤1+Real.log ((n:ℝ)+2):=by
    have hh:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  have ha:referenceScale n*((n:ℝ)+1)=maximumMean n:=by dsimp [referenceScale];field_simp
  have ham:maximumMean n≤ referenceScale n*((n:ℝ)+2):=by nlinarith [referenceScale_pos n]
  have ham2:referenceScale n*((n:ℝ)+2)≤2*maximumMean n:=by
    nlinarith [mul_nonneg (referenceScale_pos n).le (Nat.cast_nonneg (α:=ℝ) n)]
  have hapos:=referenceScale_pos n
  have hlow:=pow_le_pow_left₀ (maximumMean_pos n).le ham 2
  have hupp:=pow_le_pow_left₀ (show 0≤ referenceScale n*((n:ℝ)+2) by positivity) ham2 2
  constructor
  · apply (div_le_iff₀ (show 0<((n:ℝ)+2)^2 by positivity)).mpr
    nlinarith
  · apply (le_div_iff₀ (show 0<((n:ℝ)+2)^2 by positivity)).mpr
    nlinarith

/-- The actual competitive first-chaos bound is uniform over all finite
ambient coordinate types. Strict negative correlation is explicit. -/
theorem eventually_uniform_competitive_row_energy_bound:
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (B:Fin (n+2)→κ→ℝ) (hB:RegularSimplexGram B)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0< r) (hr:r≤1/((n:ℝ)+1)),
      gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment B) →
      assignmentFirstEnergy f≤2*referenceFirstWeight n:=by
  filter_upwards [NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds,
    eventually_maximum_mean_sq_ge_one,eventually_ge_atTop (256:ℕ)] with n hdef hmean hn
  intro κ _ B hB f hf hp r hr0 hr hcomp
  have hd:=hdef κ B hB f hf hp r hr0.le hr hcomp
  have hm:0<(n:ℝ)+2:=by positivity
  have hm1:0<(n:ℝ)+1:=by positivity
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hn256:(256:ℝ)≤(n:ℝ):=by exact_mod_cast hn
  have hr1:r≤1:=hr.trans ((div_le_one hm1).mpr (by linarith))
  have hrm:r*((n:ℝ)+1)≤1:=(le_div_iff₀ hm1).mp hr
  have hr2:r≤2/((n:ℝ)+2):=(le_div_iff₀ hm).mpr (by nlinarith)
  have habs:|assignmentFirstEnergy f-referenceFirstWeight n|≤128*r/((n:ℝ)+2):=by
    apply (mul_le_mul_iff_right₀ hr0).mp
    have hh:=hd.2.2.1.trans hd.2.2.2
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  have h128:128*r/((n:ℝ)+2)≤256/((n:ℝ)+2)^2:=by
    apply (div_le_div_iff₀ hm (sq_pos_of_pos hm)).mpr
    have hh:128*r*((n:ℝ)+2)≤256:=by nlinarith [(le_div_iff₀ hm).mp hr2]
    nlinarith [mul_le_mul_of_nonneg_right hh hm.le]
  have hsmall:256/((n:ℝ)+2)^2≤1/((n:ℝ)+2):=by
    apply (div_le_div_iff₀ (sq_pos_of_pos hm) hm).mpr
    nlinarith
  have hw:1/((n:ℝ)+2)≤ referenceFirstWeight n:=by
    unfold referenceFirstWeight
    apply (div_le_div_iff₀ hm hm1).mpr
    nlinarith [hmean]
  have hh:assignmentFirstEnergy f-referenceFirstWeight n≤ referenceFirstWeight n:=
    (le_abs_self _).trans (habs.trans (h128.trans (hsmall.trans hw)))
  linarith

end NegativeVotingExteriorReference
