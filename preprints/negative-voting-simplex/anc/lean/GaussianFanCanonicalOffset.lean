import GaussianFanOffsetMinimization
import GaussianFanJacobianPseudoInverse

/-! The actual canonical mass-preserving offset response and exact
pseudoinverse elimination of the Gaussian surface quadratic form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped InnerProductSpace BigOperators
namespace NegativeVotingFanCanonicalOffset
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingFanOffsetMinimization NegativeVotingFanJacobian NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingFanInverse NegativeVotingFanPseudoInverse
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The actual row-only first variation of each cell's Gaussian mass. -/
def rowMassVariation (B : ι → FSC.Coord d) (h : ι → ℝ) (D : ι → FSC.Coord d) (i : ι) : ℝ :=
  mixedForm B h D 0 0 (Pi.single i 1)

/-- The canonical centered offset, constructed from the actual Jacobian. -/
def canonicalOffsetVariation (B : ι → FSC.Coord d) (h : ι → ℝ) (D : ι → FSC.Coord d) : ι → ℝ :=
  -((offsetJacobian B h).covariancePseudoInverse *ᵥ rowMassVariation B h D)

/-- Direct analytic meaning of g: the derivative of the actual row-only
Gaussian cell mass, with the offsets held fixed. -/
theorem hasDerivAt_mass_row_only (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    HasDerivAt (fun t : ℝ => mass (B+t•D) h i) (rowMassVariation B h D i) 0 := by
  simpa only [smul_zero,add_zero,rowMassVariation] using hasDerivAt_mass_line B D h 0 σ hσ hlower i

theorem rowMassVariation_sum (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∑ i, rowMassVariation B h D i=0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_mass_line B D h 0 σ hσ hlower i)
  have he : (fun t : ℝ => ∑ i, mass (B+t•D) (h+t•0) i) = fun _ : ℝ => (1:ℝ) := by
    funext t
    exact mass_sum _ _
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (1:ℝ))

/-- The offset block is identified through two actual derivatives of cell
mass, independently of a supplied Hessian block. -/
theorem massVariation_offsets (B : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    mixedForm B h 0 v 0 (Pi.single i 1)=(offsetJacobian B h *ᵥ v) i := by
  have hline : HasDerivAt (fun t : ℝ => h+t•v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add h
  have hmass : HasFDerivAt (fun z => mass B z i) (massDerivative B h i) (h+(0:ℝ)•v) := by
    simpa using hasFDerivAt_mass B σ hσ hlower h i
  have hd := hmass.comp_hasDerivAt 0 hline
  have hg := hasDerivAt_mass_line B 0 h v σ hσ hlower i
  simp only [smul_zero,add_zero] at hg
  rw [← massDerivative_eq_offsetJacobian B σ hσ hlower h v i]
  exact hg.unique hd

theorem massVariation_add_offsets (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    mixedForm B h D v 0 (Pi.single i 1)=rowMassVariation B h D i+(offsetJacobian B h *ᵥ v) i := by
  have he := mixedForm_add_left B D 0 0 h 0 v (Pi.single i 1) σ hσ hlower
  simpa only [add_zero,zero_add,rowMassVariation,massVariation_offsets B h v σ hσ hlower] using he

/-- The actual canonical response solves Jv=-g. -/
theorem jacobian_canonicalOffsetVariation (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    offsetJacobian B h *ᵥ canonicalOffsetVariation B h D = -rowMassVariation B h D := by
  have hB := affineIndependent_of_centered_lower B σ hσ hlower
  have hc : (centering (rowMassVariation B h D) : ι → ℝ)=rowMassVariation B h D :=
    congrArg Subtype.val (centering_centered
      (⟨rowMassVariation B h D,rowMassVariation_sum B D h σ hσ hlower⟩ : centeredGauge ι))
  unfold canonicalOffsetVariation
  rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,offsetJacobian_pseudoinverse_mulVec B hB h,hc]

theorem canonicalOffsetVariation_centered (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∑ i, canonicalOffsetVariation B h D i=0 := by
  simp only [canonicalOffsetVariation,Pi.neg_apply,Finset.sum_neg_distrib]
  rw [pseudoinverse_sum_mulVec B (affineIndependent_of_centered_lower B σ hσ hlower),neg_zero]

/-- Every actual cell mass has zero first derivative under the constructed
row/offset response. No stationarity or existence premise remains. -/
theorem hasDerivAt_mass_line_canonical (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•canonicalOffsetVariation B h D) i) 0 0 := by
  have hd := hasDerivAt_mass_line B D h (canonicalOffsetVariation B h D) σ hσ hlower i
  rw [massVariation_add_offsets B D h _ σ hσ hlower i,
    jacobian_canonicalOffsetVariation B D h σ hσ hlower] at hd
  simpa using hd

theorem canonicalOffset_minimizes (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (w : ι → ℝ) :
    quadraticForm B h D (canonicalOffsetVariation B h D) ≤ quadraticForm B h D w :=
  quadraticForm_offset_minimizes B D h _ σ hσ hlower
    (hasDerivAt_mass_line_canonical B D h σ hσ hlower) w

theorem canonicalOffset_remainder (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (w : ι → ℝ) :
    quadraticForm B h D w=quadraticForm B h D (canonicalOffsetVariation B h D)+
      (w-canonicalOffsetVariation B h D) ⬝ᵥ
        (offsetJacobian B h *ᵥ (w-canonicalOffsetVariation B h D)) :=
  quadraticForm_offset_remainder_jacobian B D h _ w σ hσ hlower
    (hasDerivAt_mass_line_canonical B D h σ hσ hlower)

theorem canonicalOffset_unique_centered (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (w : ι → ℝ) (hw : ∑ i, w i=0) :
    quadraticForm B h D w=quadraticForm B h D (canonicalOffsetVariation B h D) ↔
      w=canonicalOffsetVariation B h D :=
  quadraticForm_offset_eq_iff_of_centered B D h _ w σ hσ hlower
    (hasDerivAt_mass_line_canonical B D h σ hσ hlower)
    (canonicalOffsetVariation_centered B D h σ hσ hlower) hw

/-- The cross term is the actual row-mass derivative paired with the one
global offset vector. -/
theorem mixedForm_row_offset_pairing (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    mixedForm B h D 0 0 v = rowMassVariation B h D ⬝ᵥ v := by
  have hg := hasDerivAt_jointDerivative_line_mixedForm B D 0 h 0 v σ hσ hlower
  have he : (fun t : ℝ => jointDerivative (B+t•D) (h+t•0) (0,v)) =
      fun t : ℝ => ∑ i, mass (B+t•D) (h+t•0) i*v i := by
    funext t
    simp only [jointDerivative_apply,Pi.zero_apply,inner_zero_left,zero_add]
  rw [he] at hg
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_mass_line B D h 0 σ hσ hlower i).mul_const (v i))
  exact hg.unique hd

/-- Exact canonical elimination formula for the literal Gaussian form. -/
theorem canonicalOffset_elimination_formula (B D : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    quadraticForm B h D (canonicalOffsetVariation B h D) = quadraticForm B h D 0-
      rowMassVariation B h D ⬝ᵥ
        ((offsetJacobian B h).covariancePseudoInverse *ᵥ rowMassVariation B h D) := by
  have he := quadraticForm_add B D 0 h 0 (canonicalOffsetVariation B h D) σ hσ hlower
  simp only [add_zero,zero_add] at he
  rw [mixedForm_row_offset_pairing B D h _ σ hσ hlower,quadraticForm_offsets] at he
  change quadraticForm B h D (canonicalOffsetVariation B h D)=quadraticForm B h D 0+
    2*(rowMassVariation B h D ⬝ᵥ canonicalOffsetVariation B h D)+
    canonicalOffsetVariation B h D ⬝ᵥ (offsetJacobian B h *ᵥ canonicalOffsetVariation B h D) at he
  rw [jacobian_canonicalOffsetVariation B D h σ hσ hlower] at he
  simp only [canonicalOffsetVariation,dotProduct_neg,neg_dotProduct,neg_neg] at he
  rw [dotProduct_comm ((offsetJacobian B h).covariancePseudoInverse *ᵥ rowMassVariation B h D)] at he
  unfold canonicalOffsetVariation
  linarith

/-- Any actual mass-preserving tangent has the same surface energy as the
canonical offset, even if its offset gauge is not fixed. -/
theorem mass_preserving_offset_value_eq_canonical (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    quadraticForm B h D v=quadraticForm B h D (canonicalOffsetVariation B h D) :=
  le_antisymm (quadraticForm_offset_minimizes B D h v σ hσ hlower hm _)
    (canonicalOffset_minimizes B D h σ hσ hlower v)

/-- The exact elimination identity applies directly to every actual
mass-preserving tangent, without a centered-offset premise. -/
theorem mass_preserving_offset_elimination_formula (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    quadraticForm B h D v=quadraticForm B h D 0-rowMassVariation B h D ⬝ᵥ
      ((offsetJacobian B h).covariancePseudoInverse *ᵥ rowMassVariation B h D) := by
  rw [mass_preserving_offset_value_eq_canonical B D h v σ hσ hlower hm]
  exact canonicalOffset_elimination_formula B D h σ hσ hlower

end NegativeVotingFanCanonicalOffset
