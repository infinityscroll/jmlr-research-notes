import GaussianAffineMassComparison

/-! A dimension-independent finite Gaussian affine mass comparison with the
explicit linear-HS and square-root-logarithmic translation scales. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffinePolynomialComparison
open NegativeVotingAffineLogScale NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingAffineMassComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lineMass_zero (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    lineMass w b A z 0=FSC.capMass w b := by
  simp [lineMass,NegativeVotingAffinePathDerivative.affineMass,nearIdentityMap,FSC.capMass]

theorem lineLogScale_zero (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    lineLogScale w b A z 0=Real.sqrt (1+Real.log (1/FSC.capMass w b)) := by
  rw [lineLogScale,lineLogMass,lineMass_zero]
  simp only [one_div,Real.log_inv,sub_eq_add_neg]

private theorem polynomial_entropy_ratio_bound (e a z F G : ℝ)
    (he : 1 ≤ e) (ha : 0 ≤ a) (hz : 0 ≤ z) (hF : 0 ≤ F) (hG0 : 0 ≤ G)
    (hK : 4*e*a ≤ 1) (hFG : F ≤ G) (hG : G ≤ e*(F+3*z)) :
    (4*e*a*G+3*z)*(G+F) ≤ 64*e^3*(a*F^2+z*F+z^2) := by
  have he0 : 0 ≤ e := by linarith
  have hsum : G+F ≤ 2*G := by linarith
  have hstart := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 4*e*a*G+3*z by positivity)
  have hsq : G^2 ≤ e^2*(F+3*z)^2 := by
    have hh := (sq_le_sq₀ hG0 (by positivity : 0 ≤ e*(F+3*z))).mpr hG
    nlinarith
  have hsimp : (F+3*z)^2 ≤ 2*F^2+18*z^2 := by nlinarith [sq_nonneg (F-3*z)]
  have hsq' : G^2 ≤ 2*e^2*F^2+18*e^2*z^2 := by
    have hh := mul_le_mul_of_nonneg_left hsimp (sq_nonneg e)
    nlinarith
  have hmain := mul_le_mul_of_nonneg_left hsq' (show 0 ≤ 8*e*a by positivity)
  have htrans := mul_le_mul_of_nonneg_left hG (show 0 ≤ 6*z by positivity)
  have hKz := mul_le_mul_of_nonneg_right hK (show 0 ≤ 36*e^2*z^2 by positivity)
  have he2 : e ≤ e^2 := by nlinarith [mul_nonneg he0 (sub_nonneg.mpr he)]
  have he3 : e^2 ≤ e^3 := by nlinarith [mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he)]
  have he31 : e ≤ e^3 := he2.trans he3
  have hzz2 := mul_le_mul_of_nonneg_right he3 (sq_nonneg z)
  have hzz1 := mul_le_mul_of_nonneg_right he31 (sq_nonneg z)
  have hzf := mul_le_mul_of_nonneg_right he31 (mul_nonneg hz hF)
  have hpos1 : 0 ≤ e^3*(a*F^2) := by positivity
  have hpos2 : 0 ≤ e^3*(z*F) := by positivity
  have hpos3 : 0 ≤ e^3*z^2 := by positivity
  nlinarith

/-- A literal finite Gaussian probability ratio. The constants are absolute;
there is no dependence on dimension or the number of cap constraints. -/
theorem affine_mass_polynomial_log_ratio_bound (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (hp : 0 < FSC.capMass w b) (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : 4*Real.exp 1*operatorHilbertSchmidt A ≤ 1) (z : FSC.Coord d) :
    |Real.log (lineMass w b A z 1/FSC.capMass w b)| ≤
      64*(Real.exp 1)^3*(operatorHilbertSchmidt A*(1+Real.log (1/FSC.capMass w b))+
        ‖z‖*Real.sqrt (1+Real.log (1/FSC.capMass w b))+‖z‖^2) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have ha := operatorHilbertSchmidt_nonneg A
  have hnorm : ‖A‖ ≤ 1/2 := by
    have hmul := mul_le_mul_of_nonneg_right he ha
    have hh := operator_norm_le_HilbertSchmidt A
    nlinarith
  have hK : 0 ≤ 4*Real.exp 1*operatorHilbertSchmidt A := by positivity
  let G := gronwallBound (lineLogScale w b A z 0)
    (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) 1
  have hF : 0 ≤ lineLogScale w b A z 0 := zero_le_one.trans (one_le_lineLogScale w b A z 0)
  have hFG : lineLogScale w b A z 0 ≤ G := by
    have hh := gronwallBound_mono hF (by positivity : 0 ≤ 3*‖z‖) hK (show (0:ℝ) ≤ 1 by norm_num)
    simpa only [gronwallBound_x0] using hh
  have hG0 : 0 ≤ G := hF.trans hFG
  have hG : G ≤ Real.exp 1*(lineLogScale w b A z 0+3*‖z‖) := by
    have hh := gronwall_one_le_exponential (lineLogScale w b A z 0)
      (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) hK (by positivity)
    have heK := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA)
      (show 0 ≤ lineLogScale w b A z 0+3*‖z‖ by positivity)
    dsimp only [G]
    nlinarith
  have hpoly := polynomial_entropy_ratio_bound (Real.exp 1) (operatorHilbertSchmidt A)
    ‖z‖ (lineLogScale w b A z 0) G he ha (norm_nonneg z) hF hG0 hA hFG hG
  have hh := (affine_mass_log_ratio_bound w hw b hb hp A hnorm z).trans hpoly
  rw [lineMass_zero] at hh
  rw [lineLogScale_sq,lineLogMass,lineMass_zero,lineLogScale_zero] at hh
  simpa only [one_div,Real.log_inv,sub_eq_add_neg] using hh

end NegativeVotingAffinePolynomialComparison
