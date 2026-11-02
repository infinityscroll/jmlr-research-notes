import GaussianGlobalTensorTransport

/-! The actual centered second-moment tensor as a symmetric finite-dimensional
operator, and its exact contraction with the actual fan Hessian. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingActualMomentOperator
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanQuadraticMoments
  NegativeVotingAffineLogMassBound NegativeVotingQuadraticBulkNorm
  NegativeVotingTensorHessianContraction NegativeVotingGlobalTensorTransport
  NegativeVotingCoherentLiftHessian NegativeVotingFanMovingCells NegativeVotingCapTail
  NegativeVotingSecondChaosFacetGradient NegativeVotingOperatorHS
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A completely explicit finite-rank operator with the literal moment entries. -/
def momentOperator (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) : FSC.Coord d→L[ℝ] FSC.Coord d :=
  ∑ j,∑ k,secondMomentTensor B h i j k •
    (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)).smulRight
      (EuclideanSpace.basisFun (Fin d) ℝ k)

theorem momentOperator_apply (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    momentOperator B h i x=∑ j,∑ k,(secondMomentTensor B h i j k*x j) •
      (EuclideanSpace.basisFun (Fin d) ℝ k) := by
  have he (j:Fin d) : innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) x=x j :=
    EuclideanSpace.basisFun_inner _ _ x j
  simp only [momentOperator,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,he,smul_smul]

theorem momentOperator_entries (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (j k : Fin d) :
    operatorEntries (momentOperator B h i) j k=secondMomentTensor B h i j k := by
  rw [operatorEntries,momentOperator_apply]
  simp [EuclideanSpace.basisFun_apply,PiLp.single_apply,Pi.single_apply]

theorem secondMomentTensor_symm (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (j k : Fin d) :
    secondMomentTensor B h i j k=secondMomentTensor B h i k j := by
  unfold secondMomentTensor
  congr 1
  funext x
  simp only [tensorTest,mul_comm,eq_comm]

theorem momentOperator_symmetric (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    (momentOperator B h i).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (momentOperator B h i x) y=inner ℝ x (momentOperator B h i y)
  rw [←bilinear_entries,←real_inner_comm x (momentOperator B h i y),←bilinear_entries]
  simp only [momentOperator_entries]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [secondMomentTensor_symm B h i k j]
  ring

theorem momentOperator_quadraticScore (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    quadraticScore (momentOperator B h i)=quadraticLabelTest B h i := by
  funext x
  change inner ℝ x (momentOperator B h i x)-LinearMap.trace ℝ (FSC.Coord d) (momentOperator B h i).toLinearMap=_
  rw [quadratic_score_eq_entries]
  simp only [momentOperator_entries,quadraticLabelTest,tensorTest]

/-- No coordinate triangle inequality: the exact energy Hessian separates
into the squared first moment response and one corrected tensor contraction. -/
theorem energyHessian_corrected_eq (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (c : ι→ℝ) (δ : Parameters d ι) :
    energyHessian B h L δ δ-∑ i,c i*constantHessian B h L i δ δ=
      (∑ i,∑ j,∑ k,(testedCellDerivative B h i (tensorTest j k) δ)^2)+
      ∑ i,correctedTensorHessian B h L i (momentOperator B h i) (c i) δ δ := by
  simp only [energyHessian,sum_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,correctedTensorHessian,momentOperator_entries]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

end NegativeVotingActualMomentOperator
