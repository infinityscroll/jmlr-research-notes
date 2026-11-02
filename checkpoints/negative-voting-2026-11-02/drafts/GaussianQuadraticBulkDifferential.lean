import GaussianFanQuarticMoments
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The actual quartic transport integral is Frechet differentiable as a
functional of the affine-field coefficients, using a finite dual basis. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingQuadraticBulkDifferential
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingQuadraticAffineTransport NegativeVotingFanQuarticMoments NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev Fields (d : ℕ) := (FSC.Coord d→L[ℝ] FSC.Coord d)×FSC.Coord d

 theorem affineBulk_add (v y : FSC.Coord d) (p q : Fields d) (x : FSC.Coord d) :
    affineBulk v y (p+q).1 (p+q).2 x=affineBulk v y p.1 p.2 x+affineBulk v y q.1 q.2 x := by
  simp [affineBulk,inner_add_left,inner_add_right,map_add]
  ring

 theorem affineBulk_smul (v y : FSC.Coord d) (c : ℝ) (p : Fields d) (x : FSC.Coord d) :
    affineBulk v y (c•p).1 (c•p).2 x=c*affineBulk v y p.1 p.2 x := by
  simp [affineBulk,inner_add_right,real_inner_smul_left,real_inner_smul_right,map_smul]
  ring

 def bulkFunctionalLinear (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (v y : FSC.Coord d) :
    Fields d→ₗ[ℝ] ℝ where
   toFun p := ∫ x in winningCell B h i,affineBulk v y p.1 p.2 x ∂stdGaussian (FSC.Coord d)
   map_add' p q := by
     simp_rw [affineBulk_add]
     exact integral_add (affineBulk_integrable (stdGaussian (FSC.Coord d)) v y p.1 p.2).restrict
       (affineBulk_integrable (stdGaussian (FSC.Coord d)) v y q.1 q.2).restrict
   map_smul' c p := by
     change (∫ x in winningCell B h i,affineBulk v y (c•p).1 (c•p).2 x ∂stdGaussian (FSC.Coord d))=_
     simp_rw [affineBulk_smul]
     rw [integral_const_mul]
     rfl

 def bulkFunctional (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (v y : FSC.Coord d) :
    Fields d→L[ℝ] ℝ := (bulkFunctionalLinear B h i v y).toContinuousLinearMap

 @[simp] theorem bulkFunctional_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (i : ι) (v y : FSC.Coord d) (q : Fields d) :
    bulkFunctional B h i v y q=
      ∫ x in winningCell B h i,affineBulk v y q.1 q.2 x ∂stdGaussian (FSC.Coord d) := rfl

private def fieldBasis (d : ℕ) := Module.finBasis ℝ (Fields d)
private def dualCoord (j : Fin (Module.finrank ℝ (Fields d))) : Fields d→L[ℝ] ℝ :=
  ((fieldBasis d).coord j).toContinuousLinearMap

private theorem dual_reconstruction (L : Fields d→L[ℝ] ℝ) :
    L=∑ j,L (fieldBasis d j)•dualCoord (d:=d) j := by
  apply ContinuousLinearMap.coe_injective
  apply (fieldBasis d).ext
  intro j
  simp [dualCoord,Finsupp.single_apply]

 def bulkFunctionalDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (i : ι) (v y : FSC.Coord d) : Parameters d ι→L[ℝ] Fields d→L[ℝ] ℝ :=
   ∑ j,(testedCellDerivative B h i (affineBulk v y (fieldBasis d j).1 (fieldBasis d j).2)).smulRight
     (dualCoord (d:=d) j)

/-- All coefficient directions are differentiated together; this is an
operator-valued Frechet derivative of the literal Gaussian bulk integral. -/
 theorem hasFDerivAt_bulkFunctional (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i : ι) (v y : FSC.Coord d) :
    HasFDerivAt (fun p:Parameters d ι=>bulkFunctional p.1 p.2 i v y)
      (bulkFunctionalDerivative B h i v y) (B,h) := by
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) fun j _=>
    (hasFDerivAt_affineBulk_testedCell B h σ hσ hlower i v y
      (fieldBasis d j).1 (fieldBasis d j).2).smul_const (dualCoord (d:=d) j)
  change HasFDerivAt
    (fun p:Parameters d ι=>∑ j,bulkFunctional p.1 p.2 i v y (fieldBasis d j)•dualCoord (d:=d) j)
    (bulkFunctionalDerivative B h i v y) (B,h) at hs
  simpa only [←dual_reconstruction] using hs

 theorem bulkFunctionalDerivative_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i : ι) (v y : FSC.Coord d) (δ : Parameters d ι) (q : Fields d) :
    bulkFunctionalDerivative B h i v y δ q=
      testedCellDerivative B h i (affineBulk v y q.1 q.2) δ := by
  let ev : (Fields d→L[ℝ] ℝ)→L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ q
  have hd := ev.hasFDerivAt.comp (B,h) (hasFDerivAt_bulkFunctional B h σ hσ hlower i v y)
  have he := hasFDerivAt_affineBulk_testedCell B h σ hσ hlower i v y q.1 q.2
  have hid : ev.comp (bulkFunctionalDerivative B h i v y)=
      testedCellDerivative B h i (affineBulk v y q.1 q.2) := hd.unique he
  exact congrArg (fun L:Parameters d ι→L[ℝ] ℝ=>L δ) hid

end NegativeVotingQuadraticBulkDifferential
