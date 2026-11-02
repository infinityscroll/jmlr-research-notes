import GaussianRegularCapProbability

/-! Actual regular-facet geometry reducing arbitrary score shifts to two
one-direction shifts controlled by the score range, independent of dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetRange
open NegativeVoting NegativeVotingFacetConditionalPlane NegativeVotingRegularCapProbability
  NegativeVotingAffinePathDerivative NegativeVotingBalancedReference

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def utilityRange (u : ι → ℝ) : ℝ := maxScore u+maxScore (fun i => -u i)

theorem utilityRange_nonneg (u : ι → ℝ) : 0 ≤ utilityRange u := by
  let i := chosenWinner u
  have h1 : u i ≤ maxScore u := Finset.le_sup' u (Finset.mem_univ i)
  have h2 : -u i ≤ maxScore (fun j => -u j) :=
    Finset.le_sup' (fun j => -u j) (Finset.mem_univ i)
  unfold utilityRange
  linarith

theorem abs_sub_le_utilityRange (u : ι → ℝ) (i j : ι) :
    |u i-u j| ≤ utilityRange u := by
  have hi : u i ≤ maxScore u := Finset.le_sup' u (Finset.mem_univ i)
  have hj : u j ≤ maxScore u := Finset.le_sup' u (Finset.mem_univ j)
  have hni : -u i ≤ maxScore (fun k => -u k) :=
    Finset.le_sup' (fun k => -u k) (Finset.mem_univ i)
  have hnj : -u j ≤ maxScore (fun k => -u k) :=
    Finset.le_sup' (fun k => -u k) (Finset.mem_univ j)
  unfold utilityRange
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem midpoint_difference_le_range (u : ι → ℝ) (i j k : ι) :
    |u k-(u i+u j)/2| ≤ utilityRange u := by
  have hi := abs_le.mp (abs_sub_le_utilityRange u k i)
  have hj := abs_le.mp (abs_sub_le_utilityRange u k j)
  exact abs_le.mpr ⟨by linarith [hi.1,hj.1],by linarith [hi.2,hj.2]⟩

end Finite

variable {n d : ℕ}

def commonRangeDirection (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2)) : FSC.Coord d :=
  -(B i+B j)

def facetRangeShift (B : Fin (n+2) → FSC.Coord d) (h : FSC.Coord d)
    (i j : Fin (n+2)) : FSC.Coord d :=
  utilityRange (scoreOffsets B h) • commonRangeDirection B i j

theorem commonRangeDirection_norm_sq (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    ‖commonRangeDirection B i j‖^2=2-4/((n:ℝ)+2) := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [commonRangeDirection,inner_neg_left,inner_neg_right,neg_neg,
    inner_add_left,inner_add_right,hG,ite_true,if_neg hij,if_neg (Ne.symm hij)]
  ring

theorem commonRangeDirection_norm_le (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) : ‖commonRangeDirection B i j‖ ≤ 2 := by
  have hh := commonRangeDirection_norm_sq B hG i j hij
  have hp : 0 ≤ 4/((n:ℝ)+2) := by positivity
  nlinarith [norm_nonneg (commonRangeDirection B i j)]

theorem regularFacetNormal_inner_commonRangeDirection (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (k : FacetLabels i j) :
    inner ℝ (regularFacetNormal B i j k) (commonRangeDirection B i j)=
      (Real.sqrt (3/2:ℝ))⁻¹ := by
  simp only [regularFacetNormal,real_inner_smul_left,commonRangeDirection,
    inner_neg_right,regularFacetRawNormal,inner_sub_left,inner_add_right,
    inner_add_left,hG,ite_true,if_neg k.property.1,if_neg k.property.2,
    if_neg hij,if_neg (Ne.symm hij)]
  ring

theorem regularFacetNormal_inner_scores (B : Fin (n+2) → FSC.Coord d)
    (h : FSC.Coord d) (i j : Fin (n+2)) (k : FacetLabels i j) :
    inner ℝ (regularFacetNormal B i j k) h=
      (Real.sqrt (3/2:ℝ))⁻¹*(scoreOffsets B h k-(scoreOffsets B h i+scoreOffsets B h j)/2) := by
  simp only [regularFacetNormal,regularFacetRawNormal,real_inner_smul_left,
    inner_sub_left,inner_add_left,scoreOffsets]
  ring

theorem facetRangeShift_dominates_normals (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) (k : FacetLabels i j) :
    |inner ℝ (regularFacetNormal B i j k) h| ≤
      inner ℝ (regularFacetNormal B i j k) (facetRangeShift B h i j) := by
  have hp : 0<(Real.sqrt (3/2:ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  rw [regularFacetNormal_inner_scores,abs_mul,abs_of_pos hp,facetRangeShift,
    real_inner_smul_right,regularFacetNormal_inner_commonRangeDirection B hG i j hij]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (midpoint_difference_le_range (scoreOffsets B h) i j k) hp.le

theorem facetRangeShift_norm_le (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    ‖facetRangeShift B h i j‖ ≤ 2*utilityRange (scoreOffsets B h) := by
  rw [facetRangeShift,norm_smul,Real.norm_eq_abs,abs_of_nonneg (utilityRange_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (commonRangeDirection_norm_le B hG i j hij) (utilityRange_nonneg (scoreOffsets B h))

theorem common_shift_cap_sandwich (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    ((fun x => x+facetRangeShift B h i j) ⁻¹' FSC.cap (regularFacetNormal B i j) 0) ⊆
      ((fun x => x+h) ⁻¹' FSC.cap (regularFacetNormal B i j) 0) ∧
    ((fun x => x+h) ⁻¹' FSC.cap (regularFacetNormal B i j) 0) ⊆
      ((fun x => x-facetRangeShift B h i j) ⁻¹' FSC.cap (regularFacetNormal B i j) 0) := by
  constructor
  · intro x hx k
    have hxk := hx k
    have hh := (abs_le.mp (facetRangeShift_dominates_normals B hG h i j hij k)).2
    simp only [inner_add_right,Pi.zero_apply] at hxk ⊢
    linarith
  · intro x hx k
    have hxk := hx k
    have hh := (abs_le.mp (facetRangeShift_dominates_normals B hG h i j hij k)).1
    simp only [inner_add_right,inner_sub_right,Pi.zero_apply] at hxk ⊢
    linarith

theorem common_shift_mass_sandwich (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : FSC.Coord d) (i j : Fin (n+2)) (hij : i≠j) :
    affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) (facetRangeShift B h i j) ≤
      affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h ∧
    affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) h ≤
      affineMass (regularFacetNormal B i j) 0 (ContinuousLinearMap.id ℝ _) (-facetRangeShift B h i j) := by
  obtain ⟨hlo,hhi⟩ := common_shift_cap_sandwich B hG h i j hij
  constructor
  · exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hlo)
  · simpa only [affineMass,ContinuousLinearMap.id_apply,sub_eq_add_neg] using
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hhi)

end NegativeVotingRegularFacetRange
