import GaussianAffineLogScale

/-! Finite actual Gaussian affine mass comparison from the derived logarithmic
rate. The interval estimate has no supplied derivative or path-positivity input. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffineMassComparison
open NegativeVotingAffineLogScale NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lineLogScale_gronwall (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : t∈Icc 0 1) :
    lineLogScale w b A z t ≤
      gronwallBound (lineLogScale w b A z 0)
        (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) t := by
  have hi (x : ℝ) (hx : x∈Icc 0 1) : |x|≤1 := by
    rw [abs_of_nonneg hx.1]; exact hx.2
  have hdiff (x : ℝ) (hx : x∈Icc 0 1) :=
    (hasDerivAt_lineLogScale w hw b hb hp A hA z x (hi x hx)).differentiableAt
  have hcont : ContinuousOn (lineLogScale w b A z) (Icc 0 1) :=
    fun x hx=>(hdiff x hx).continuousAt.continuousWithinAt
  have hpos (x : ℝ) : 0 ≤ lineLogScale w b A z x :=
    (zero_le_one.trans (one_le_lineLogScale w b A z x))
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    (f' := deriv (lineLogScale w b A z)) hcont
    (fun x hx=>(hdiff x ⟨hx.1,hx.2.le⟩).hasDerivAt.hasDerivWithinAt)
    (show ‖lineLogScale w b A z 0‖ ≤ lineLogScale w b A z 0 by
      rw [Real.norm_eq_abs,abs_of_nonneg (hpos 0)])
    (fun x hx=>by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hpos x)]
      exact lineLogScale_derivative_bound w hw b hb hp A hA z x (hi x ⟨hx.1,hx.2.le⟩))
    t ht
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos t),sub_zero] using hG

theorem lineLogScale_difference_bound (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) :
    |lineLogScale w b A z 1-lineLogScale w b A z 0| ≤
      (4*Real.exp 1*operatorHilbertSchmidt A)*
        gronwallBound (lineLogScale w b A z 0)
          (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) 1+3*‖z‖ := by
  have hK : 0 ≤ 4*Real.exp 1*operatorHilbertSchmidt A := by
    have := operatorHilbertSchmidt_nonneg A; positivity
  have hgmono := gronwallBound_mono
    (zero_le_one.trans (one_le_lineLogScale w b A z 0)) (by positivity : 0 ≤ 3*‖z‖) hK
  have hi (x : ℝ) (hx : x∈Icc 0 1) : |x|≤1 := by
    rw [abs_of_nonneg hx.1]; exact hx.2
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f' := deriv (lineLogScale w b A z))
    (fun x hx=>(hasDerivAt_lineLogScale w hw b hb hp A hA z x
      (hi x hx)).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun x hx=>by
      rw [Real.norm_eq_abs]
      exact (lineLogScale_derivative_bound w hw b hb hp A hA z x (hi x ⟨hx.1,hx.2.le⟩)).trans
        (add_le_add (mul_le_mul_of_nonneg_left
          ((lineLogScale_gronwall w hw b hb hp A hA z x ⟨hx.1,hx.2.le⟩).trans
            (hgmono hx.2.le)) hK) (le_refl (3*‖z‖))))
  simpa only [Real.norm_eq_abs] using hh

/-- Elementary majorant, including zero linear velocity. -/
theorem gronwall_one_le_exponential (δ K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε 1 ≤ (δ+ε)*Real.exp K := by
  by_cases hk : K=0
  · simp [hk,gronwallBound_K0]
  have hkpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hk)
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-K)) (Real.exp_pos K).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at he
  have hex : Real.exp K-1 ≤ K*Real.exp K := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hex (div_nonneg hε hK)
  have hc : ε/K*(K*Real.exp K)=ε*Real.exp K := by field_simp
  rw [hc] at hm
  simp only [gronwallBound_of_K_ne_0 hk,mul_one]
  nlinarith

/-- Actual two-sided logarithmic probability comparison. The explicit Grönwall
factor retains the separate linear deformation and translation scales. -/
theorem affine_mass_log_ratio_bound (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) :
    |Real.log (lineMass w b A z 1/lineMass w b A z 0)| ≤
      ((4*Real.exp 1*operatorHilbertSchmidt A)*
        gronwallBound (lineLogScale w b A z 0)
          (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) 1+3*‖z‖)*
      (gronwallBound (lineLogScale w b A z 0)
          (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) 1+lineLogScale w b A z 0) := by
  have hp0 : 0 < lineMass w b A z 0 :=
    NegativeVotingAffinePositiveMass.nearIdentity_affineMass_pos w hw b hp A hA z 0 (by norm_num)
  have hp1 : 0 < lineMass w b A z 1 :=
    NegativeVotingAffinePositiveMass.nearIdentity_affineMass_pos w hw b hp A hA z 1 (by norm_num)
  have hF0 := one_le_lineLogScale w b A z 0
  have hF1 := one_le_lineLogScale w b A z 1
  have hs0 := lineLogScale_sq w b A z 0
  have hs1 := lineLogScale_sq w b A z 1
  have hg := lineLogScale_gronwall w hw b hb hp A hA z 1 (by norm_num)
  have hd := lineLogScale_difference_bound w hw b hb hp A hA z
  have hK : 0 ≤ 4*Real.exp 1*operatorHilbertSchmidt A := by
    have := operatorHilbertSchmidt_nonneg A; positivity
  have hG : 0 ≤ gronwallBound (lineLogScale w b A z 0)
      (4*Real.exp 1*operatorHilbertSchmidt A) (3*‖z‖) 1 := by linarith
  rw [Real.log_div hp1.ne' hp0.ne']
  change |lineLogMass w b A z 1-lineLogMass w b A z 0| ≤ _
  have he : lineLogMass w b A z 1-lineLogMass w b A z 0=
      -(lineLogScale w b A z 1-lineLogScale w b A z 0)*
        (lineLogScale w b A z 1+lineLogScale w b A z 0) := by nlinarith
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by linarith :
    0 ≤ lineLogScale w b A z 1+lineLogScale w b A z 0)]
  exact mul_le_mul hd (add_le_add hg (le_refl (lineLogScale w b A z 0))) (by linarith) (by positivity)

end NegativeVotingAffineMassComparison
