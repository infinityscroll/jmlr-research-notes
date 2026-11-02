import GaussianCapShiftLower

/-! Actual Gaussian halfspace tails and a dimension-free union lower bound
for polyhedra whose thresholds have a common positive margin. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators ENNReal
namespace NegativeVotingCapUnionLower
open NegativeVotingCapShiftLower NegativeVotingPolyhedral
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem inner_strict_tail (w : FSC.Coord d) (s t : ℝ) (ht : 0 ≤ t) :
    (stdGaussian (FSC.Coord d)).real {x | s < inner ℝ w x} ≤
      Real.exp (t^2*‖w‖^2/2-t*s) := by
  let S := {x : FSC.Coord d | s < inner ℝ w x}
  have hS : MeasurableSet S := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ))) (stdGaussian (FSC.Coord d)) :=
    (integrable_const _).indicator hS
  have hg := (integrable_exp_inner w t).const_mul (Real.exp (-t*s))
  have hp (x : FSC.Coord d) : S.indicator (fun _ => (1 : ℝ)) x ≤
      Real.exp (-t*s)*Real.exp (t*inner ℝ w x) := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx,← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hh : s ≤ inner ℝ w x := (show s < inner ℝ w x from hx).le
      nlinarith [mul_le_mul_of_nonneg_left hh ht]
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hh := integral_mono hi hg hp
  rw [integral_indicator hS,integral_const,integral_const_mul,integral_exp_inner] at hh
  simpa only [smul_eq_mul,mul_one,← Real.exp_add,sub_eq_add_neg,neg_mul,
    add_comm,S,Measure.real,Measure.restrict_apply_univ] using hh

theorem inner_strict_tail_norm_bound (w : FSC.Coord d) (D s t : ℝ)
    (hD : 0 ≤ D) (hw : ‖w‖ ≤ D) (ht : 0 ≤ t) :
    (stdGaussian (FSC.Coord d)).real {x | s < inner ℝ w x} ≤
      Real.exp (t^2*D^2/2-t*s) := by
  apply (inner_strict_tail w s t ht).trans
  apply Real.exp_le_exp.mpr
  have hsq := (sq_le_sq₀ (norm_nonneg w) hD).mpr hw
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg t)]

theorem cap_mass_lower_of_uniform_margin (w : ι → FSC.Coord d) (b : ι → ℝ)
    (D s t : ℝ) (hD : 0 ≤ D) (hw : ∀ i, ‖w i‖ ≤ D)
    (hb : ∀ i, s ≤ b i) (ht : 0 ≤ t) :
    1-(Fintype.card ι : ℝ)*Real.exp (t^2*D^2/2-t*s) ≤ FSC.capMass w b := by
  let μ := stdGaussian (FSC.Coord d)
  have hsub : (FSC.cap w b)ᶜ ⊆ ⋃ i, {x | s < inner ℝ (w i) x} := by
    intro x hx
    have hh : ∃ i, b i < inner ℝ (w i) x := by
      simpa only [FSC.cap,mem_compl_iff,mem_setOf_eq,not_forall,not_le] using hx
    obtain ⟨i,hi⟩ := hh
    exact mem_iUnion.mpr ⟨i,lt_of_le_of_lt (hb i) hi⟩
  have hc : μ.real (FSC.cap w b)ᶜ ≤
      (Fintype.card ι : ℝ)*Real.exp (t^2*D^2/2-t*s) := by
    calc
      _ ≤ μ.real (⋃ i, {x | s < inner ℝ (w i) x}) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ i, μ.real {x | s < inner ℝ (w i) x} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : ι, Real.exp (t^2*D^2/2-t*s) :=
        Finset.sum_le_sum fun i _ => inner_strict_tail_norm_bound (w i) D s t hD (hw i) ht
      _ = _ := by simp
  have htotal := measureReal_add_measureReal_compl (μ := μ) (FSC.measurableSet_cap w b)
  have htotal' : FSC.capMass w b + μ.real (FSC.cap w b)ᶜ = 1 := by
    simpa [μ,FSC.capMass,Measure.real] using htotal
  linarith

theorem cap_mass_half_of_margin (w : ι → FSC.Coord d) (b : ι → ℝ)
    (D : ℝ) (hD : 0 < D) (hw : ∀ i, ‖w i‖ ≤ D)
    (hb : ∀ i, D*Real.sqrt (2*Real.log (2*((Fintype.card ι : ℝ)+1))) ≤ b i) :
    (1/2 : ℝ) ≤ FSC.capMass w b := by
  let c : ℝ := Fintype.card ι
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hc1 : 0 < 2*(c+1) := by positivity
  have hlog : 0 ≤ Real.log (2*(c+1)) := Real.log_nonneg (by linarith)
  let L := Real.log (2*(c+1))
  let q := Real.sqrt (2*L)
  have hq : q^2 = 2*L := Real.sq_sqrt (by dsimp [L];positivity)
  have he : (q/D)^2*D^2/2-(q/D)*(D*q) = -L := by
    field_simp
    <;> nlinarith [hq]
  have hh := cap_mass_lower_of_uniform_margin w b D (D*q) (q/D) hD.le hw hb
    (div_nonneg (Real.sqrt_nonneg _) hD.le)
  rw [he] at hh
  have hex : Real.exp (-L) = 1/(2*(c+1)) := by
    rw [Real.exp_neg]
    simp only [L,Real.exp_log hc1,one_div]
  rw [hex] at hh
  have hfrac : c*(1/(2*(c+1))) ≤ 1/2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hc1).mpr
    linarith
  change 1-c*(1/(2*(c+1))) ≤ FSC.capMass w b at hh
  linarith

end NegativeVotingCapUnionLower
