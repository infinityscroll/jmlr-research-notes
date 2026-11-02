import GaussianConditionedFacetLower
import GaussianBoundedCoherentLift

/-! Actual conditioned-facet lower bounds in arbitrary ambient dimension.
The bounded coherent score lift replaces the affine-basis restriction. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingConditionedFacetGeneral
open NegativeVotingFan NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingConditionedFacet NegativeVotingFacetScoreWitness
  NegativeVotingBoundedCoherentLift
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A bounded two-high-score witness needs only score differences. No
spanning or centering assumption on the rows is necessary. -/
theorem exists_dominant_point
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i j : ι) (hij : i≠j) (h : ι→ℝ) (H a : ℝ)
    (hH : ∀ k,|h k| ≤ H) (ha : 0 ≤ a) :
    ∃ x : FSC.Coord d,
      (∀ k,k≠i→k≠j→a-2*H ≤
        (inner ℝ (B i) x-h i)-(inner ℝ (B k) x-h k)) ∧
      inner ℝ (B i-B j) x=h i-h j ∧
      ‖x‖^2 ≤ (6*a^2+(h i-h j)^2/2)/σ^2 := by
  let q := twoHighScores i j a (h i-h j)
  let x := boundedScoreLift B σ hσ hlower i q
  have hx (l k : ι) : inner ℝ (B l-B k) x=q l-q k :=
    boundedScoreLift_coherent B σ hσ hlower i q l k
  have hn : ‖x‖^2 ≤ (∑ k,q k^2)/σ^2 := by
    simpa only [sub_zero] using boundedScoreLift_norm_sq B σ hσ hlower i q 0
  refine ⟨x,?_,?_,hn.trans (div_le_div_of_nonneg_right
    (twoHighScores_sq_sum hm i j hij a (h i-h j)) (sq_nonneg σ))⟩
  · intro k hki hkj
    have he := hx i k
    simp only [inner_sub_left] at he
    have hi : q i=a+(h i-h j)/2 := by simp [q,twoHighScores]
    have hk : q k= -2*a/((Fintype.card ι : ℝ)-2) := by
      simp [q,twoHighScores,hki,hkj]
    rw [hi,hk] at he
    have hhi := (abs_le.mp (hH i)).2
    have hhj := (abs_le.mp (hH j)).2
    have hhk := (abs_le.mp (hH k)).1
    have hm' : (3:ℝ) ≤ Fintype.card ι := by exact_mod_cast hm
    have ht : 0 ≤ 2*a/((Fintype.card ι : ℝ)-2) :=
      div_nonneg (mul_nonneg (by norm_num) ha) (by linarith)
    rw [neg_mul,neg_div] at he
    linarith
  · have he := hx i j
    simpa [q,twoHighScores,hij,hij.symm] using he

theorem intrinsicProbability_exp_lower_of_offsets
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ D H : ℝ) (hσ : 0<σ) (hD : 0<D) (hH : 0 ≤ H)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀ i j,‖B i-B j‖ ≤ D) (h : ι→ℝ) (hoff : ∀ i,|h i| ≤ H)
    (i j : ι) (hij : i≠j) :
    (1/4:ℝ)*Real.exp (-(6*(2*H+unionRadius (V:=ι) D)^2+(h i-h j)^2/2)/σ^2) ≤
      intrinsicProbability B h i j := by
  let a := 2*H+unionRadius (V:=ι) D
  have ha : 0 ≤ a := by dsimp [a,unionRadius]; positivity
  obtain ⟨x,hgap,hplane,hx⟩ := exists_dominant_point B hm σ hσ hlower i j hij
    (fun k=>-h k) H a (fun k=>by simpa only [abs_neg] using hoff k) ha
  have hxplane : inner ℝ (B i-B j) x=h j-h i := by simpa only [neg_sub_neg] using hplane
  have hmargin : ∀ k : OtherLabels i j,
      D*Real.sqrt (2*Real.log (2*((Fintype.card (OtherLabels i j) : ℝ)+1))) ≤
        affineScore B h i x-affineScore B h k x := by
    intro k
    have hh := hgap k k.property.1 k.property.2
    simp only [sub_neg_eq_add] at hh
    have hr := otherLabel_margin_le (V:=ι) D hD.le i j
    change a-2*H ≤ affineScore B h i x-affineScore B h k x at hh
    dsimp only [a] at hh
    linarith
  have hp := intrinsicProbability_lower_of_point B h i j
    (centered_singular_rows_ne B σ hσ hlower i j hij) D hD (fun k=>hrow k i)
    x hxplane hmargin
  refine le_trans ?_ hp
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hx' : ‖x‖^2 ≤ (6*a^2+(h i-h j)^2/2)/σ^2 := by convert hx using 1 <;> ring
  simpa only [neg_div] using neg_le_neg hx'

theorem intrinsicProbability_exp_lower_uniform
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ D H : ℝ) (hσ : 0<σ) (hD : 0<D) (hH : 0 ≤ H)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀ i j,‖B i-B j‖ ≤ D) (h : ι→ℝ) (hoff : ∀ i,|h i| ≤ H)
    (i j : ι) (hij : i≠j) :
    (1/4:ℝ)*Real.exp (-(6*(2*H+unionRadius (V:=ι) D)^2+2*H^2)/σ^2) ≤
      intrinsicProbability B h i j := by
  refine le_trans ?_ (intrinsicProbability_exp_lower_of_offsets B hm σ D H hσ hD hH
    hlower hrow h hoff i j hij)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hd : |h i-h j| ≤ 2*H := (abs_sub (h i) (h j)).trans (by linarith [hoff i,hoff j])
  have hs := pow_le_pow_left₀ (abs_nonneg _) hd 2
  rw [sq_abs] at hs
  apply div_le_div_of_nonneg_right _ (sq_nonneg σ)
  nlinarith

/-- Uniform positive winning-cell masses and a fixed conditioning ratio imply
the actual polynomial facet lower bound, including all spectator dimensions. -/
theorem intrinsicProbability_polynomial_lower
    (B : ι→FSC.Coord d) (hm : 3 ≤ Fintype.card ι)
    (σ D : ℝ) (hσ : 0<σ) (hD : 0<D)
    (hlower : CenteredSingularLowerBound B σ) (hrow : ∀ i j,‖B i-B j‖ ≤ D)
    (hcond : D/σ ≤ 4) (h : ι→ℝ) (hs : ∑ i,h i=0)
    (hmass : ∀ i,1/(2*(Fintype.card ι : ℝ)) ≤ mass B h i)
    (i j : ι) (hij : i≠j) :
    (Fintype.card ι : ℝ)^(-4096:ℝ) ≤ intrinsicProbability B h i j := by
  let m : ℝ := Fintype.card ι
  let E := (6*(2*offsetRadius (V:=ι) D+unionRadius (V:=ι) D)^2+
    2*(offsetRadius (V:=ι) D)^2)/σ^2
  have hm3 : (3:ℝ) ≤ m := by dsimp only [m]; exact_mod_cast hm
  have hmpos : 0 < m := by linarith
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hE : E ≤ 3584*Real.log m := witness_exponent_le_log hm σ D hσ hD hcond
  have hquarter : Real.exp (-(2*Real.log m)) ≤ 1/4 := by
    have he : Real.exp (-(2*Real.log m))=(m^2)⁻¹ := by
      have hlp : Real.log (m^2)=2*Real.log m := Real.log_pow m 2
      rw [←hlp,Real.exp_neg,Real.exp_log (sq_pos_of_pos hmpos)]
    rw [he]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4)
      (show (4:ℝ) ≤ m^2 by nlinarith)
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hp : (1/4:ℝ)*Real.exp (-E) ≤ intrinsicProbability B h i j := by
    simpa only [E,neg_div] using intrinsicProbability_exp_lower_uniform B hm σ D
      (offsetRadius (V:=ι) D) hσ hD (offsetRadius_nonneg D hD.le) hlower hrow h
      (centered_offsets_le_of_cell_masses B h hinj D hD.le hrow hs hmass) i j hij
  calc
    (Fintype.card ι : ℝ)^(-4096:ℝ)=Real.exp (-(4096*Real.log m)) := by
      rw [Real.rpow_def_of_pos hmpos]
      congr 1
      ring
    _ ≤ Real.exp (-(2*Real.log m))*Real.exp (-E) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ (1/4:ℝ)*Real.exp (-E) :=
      mul_le_mul_of_nonneg_right hquarter (Real.exp_pos _).le
    _ ≤ intrinsicProbability B h i j := hp

end NegativeVotingConditionedFacetGeneral
