import GaussianConditionedFacetCap
import GaussianFacetScoreWitness

/-! An actual score-space witness gives an explicit exponential lower bound
for every facet of a centered quantitatively independent affine simplex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace NegativeVotingConditionedFacet
open NegativeVotingFan NegativeVotingCapTail NegativeVotingFacetScoreWitness
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def unionRadius (D : ℝ) : ℝ :=
  D*Real.sqrt (2*Real.log (2*((Fintype.card V : ℝ)+1)))

theorem otherLabel_margin_le (D : ℝ) (hD : 0 ≤ D) (i j : V) :
    D*Real.sqrt (2*Real.log (2*((Fintype.card (OtherLabels i j) : ℝ)+1))) ≤
      unionRadius (V:=V) D := by
  have hc : (Fintype.card (OtherLabels i j) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_subtype_le (fun k : V => k≠i ∧ k≠j)
  have hp : 0 < 2*((Fintype.card (OtherLabels i j) : ℝ)+1) := by positivity
  apply mul_le_mul_of_nonneg_left _ hD
  apply Real.sqrt_le_sqrt
  have hl := Real.log_le_log hp (show 2*((Fintype.card (OtherLabels i j) : ℝ)+1) ≤
    2*((Fintype.card V : ℝ)+1) by linarith)
  linarith

/-- The witness is constructed from actual centered score coordinates.
Offsets enter the existing fan with the plus sign. -/
theorem intrinsicProbability_exp_lower_of_offsets
    (B : AffineBasis V ℝ (FSC.Coord d)) (hB : ∑i,B i=0)
    (hm : 3 ≤ Fintype.card V) (σ D H : ℝ) (hσ : 0 < σ) (hD : 0 < D) (hH : 0 ≤ H)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i j,‖B i-B j‖ ≤ D) (h : V → ℝ) (hoff : ∀i,|h i| ≤ H)
    (i j : V) (hij : i≠j) :
    (1/4:ℝ)*Real.exp (-(6*(2*H+unionRadius (V:=V) D)^2+(h i-h j)^2/2)/σ^2) ≤
      intrinsicProbability B h i j := by
  let a := 2*H+unionRadius (V:=V) D
  have ha : 0 ≤ a := by dsimp [a,unionRadius];positivity
  have hneg : ∀k,|-h k| ≤ H := by intro k;simpa only [abs_neg] using hoff k
  obtain ⟨x,_,hgap,hplane,hx⟩ := exists_dominant_facet_point B hB hm σ hσ hlower
    i j hij (fun k => -h k) H a hneg ha
  have hxplane : inner ℝ (B i-B j) x=h j-h i := by simpa only [neg_sub_neg] using hplane
  have hmargin : ∀k : OtherLabels i j,
      D*Real.sqrt (2*Real.log (2*((Fintype.card (OtherLabels i j) : ℝ)+1))) ≤
        affineScore B h i x-affineScore B h k x := by
    intro k
    have hh := hgap k k.property.1 k.property.2
    simp only [sub_neg_eq_add] at hh
    have hrad := otherLabel_margin_le (V:=V) D hD.le i j
    change a-2*H ≤ affineScore B h i x-affineScore B h k x at hh
    dsimp only [a] at hh
    linarith
  have hp := intrinsicProbability_lower_of_point B h i j (B.ind.injective.ne hij)
    D hD (fun k => hrow k i) x hxplane hmargin
  have hx' : ‖x‖^2 ≤ (6*a^2+(h i-h j)^2/2)/σ^2 := by
    convert hx using 1 <;> ring
  apply (le_trans _ hp)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  change -(6*a^2+(h i-h j)^2/2)/σ^2 ≤ -‖x‖^2
  simpa only [neg_div] using neg_le_neg hx'

/-- A uniform explicit exponential bound, independent of the selected pair. -/
theorem intrinsicProbability_exp_lower_uniform
    (B : AffineBasis V ℝ (FSC.Coord d)) (hB : ∑i,B i=0)
    (hm : 3 ≤ Fintype.card V) (σ D H : ℝ) (hσ : 0 < σ) (hD : 0 < D) (hH : 0 ≤ H)
    (hlower : CenteredSingularLowerBound B σ)
    (hrow : ∀i j,‖B i-B j‖ ≤ D) (h : V → ℝ) (hoff : ∀i,|h i| ≤ H)
    (i j : V) (hij : i≠j) :
    (1/4:ℝ)*Real.exp (-(6*(2*H+unionRadius (V:=V) D)^2+2*H^2)/σ^2) ≤
      intrinsicProbability B h i j := by
  apply (le_trans _ (intrinsicProbability_exp_lower_of_offsets B hB hm σ D H hσ hD hH
    hlower hrow h hoff i j hij))
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hdiff : |h i-h j| ≤ 2*H := (abs_sub (h i) (h j)).trans (by linarith [hoff i,hoff j])
  have hsq : (h i-h j)^2 ≤ 4*H^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*H)).mpr hdiff
    rw [sq_abs] at hh
    nlinarith
  apply div_le_div_of_nonneg_right _ (sq_nonneg σ)
  linarith

end NegativeVotingConditionedFacet
