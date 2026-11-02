import GaussianQuadraticAffineTransport
import GaussianFanCoherentChart
import GaussianFanQuadraticMoments

/-! The actual fan quadratic-test derivative expressed through one coherent
linear-plus-translation field. The score-difference lifting condition is
algebraic; the final instance supplies the constructed fan lift. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingFanQuadraticTransport
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingMovingCap NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingQuadraticAffineTransport NegativeVotingAffineOperatorDerivative
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

 def velocityMap (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    Parameters d ι→L[ℝ] ((FSC.Coord d→L[ℝ] FSC.Coord d)×FSC.Coord d) :=
   ((ContinuousLinearMap.compL ℝ (FSC.Coord d) (ι→ℝ) (FSC.Coord d) L).comp
     (rowScoreOperator.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _))).prod
       (L.comp (ContinuousLinearMap.snd ℝ _ _))

 @[simp] theorem velocityMap_first (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (δ : Parameters d ι) (x : FSC.Coord d) :
    (velocityMap L δ).1 x=L (fun j=>inner ℝ (δ.1 j) x) := rfl

 @[simp] theorem velocityMap_second (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (δ : Parameters d ι) : (velocityMap L δ).2=L δ.2 := rfl

 theorem fanParameterMap_eq_affineVelocity (B : ι→FSC.Coord d)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (hL : ∀ (q:ι→ℝ) (i j:ι),inner ℝ (B i-B j) (L q)=q i-q j)
    (i : ι) (δ : Parameters d ι) :
    fanParameterMap B i δ=affineVelocity (cellNormals B i) (velocityMap L δ).1 (velocityMap L δ).2 := by
  apply Prod.ext
  · funext j
    apply ext_inner_right ℝ
    intro x
    have hh := hL (fun k=>inner ℝ (δ.1 k) x) j.1 i
    change inner ℝ (‖B j.1-B i‖⁻¹ • (δ.1 j.1-δ.1 i)) x=
      inner ℝ ((velocityMap L δ).1.adjoint (‖B j.1-B i‖⁻¹ • (B j.1-B i))) x
    rw [ContinuousLinearMap.adjoint_inner_left,velocityMap_first,real_inner_smul_left,
      real_inner_smul_left,inner_sub_left,hh]
  · funext j
    have hh := hL δ.2 j.1 i
    change ‖B j.1-B i‖⁻¹*(δ.2 i-δ.2 j.1)=
      -inner ℝ (‖B j.1-B i‖⁻¹ • (B j.1-B i)) (L δ.2)
    rw [real_inner_smul_left,hh]
    ring

/-- The actual quadratic cell derivative for any coherent lifting field.
No Gaussian transport conclusion or differentiation premise is assumed. -/
 theorem testedCellDerivative_bilinear_bulk (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (hL : ∀ (q:ι→ℝ) (i j:ι),inner ℝ (B i-B j) (L q)=q i-q j)
    (i : ι) (v y : FSC.Coord d) (δ : Parameters d ι) :
    testedCellDerivative B h i (fun x=>inner ℝ v x*inner ℝ y x) δ=
      ∫ x in winningCell B h i,affineBulk v y (velocityMap L δ).1 (velocityMap L δ).2 x
        ∂stdGaussian (FSC.Coord d) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i)
    (fun x=>inner ℝ v x*inner ℝ y x) (fanParameterMap B i δ)=_
  rw [fanParameterMap_eq_affineVelocity B L hL,
    capJointDerivative_bilinear_affine_bulk _ (cellNormals_unit B σ hσ hlower i) _
      (cellNormals_noCoincident B h σ hσ hlower i)]
  have hB : Function.Injective B := fun j k he=>by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have he := normalized_cap_eq_winningCell B hB i (B,h)
  rw [fanParameterMap_base] at he
  rw [he]

/-- A fully derived coherent field for every actual nondegenerate fan. -/
 theorem testedCellDerivative_constructed_bulk (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) (δ : Parameters d ι) :
    testedCellDerivative B h i (fun x=>inner ℝ v x*inner ℝ y x) δ=
      ∫ x in winningCell B h i,affineBulk v y
        (velocityMap (scoreLiftCLM B (NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower) i₀) δ).1
        (velocityMap (scoreLiftCLM B (NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower) i₀) δ).2 x
        ∂stdGaussian (FSC.Coord d) := by
  apply testedCellDerivative_bilinear_bulk B h σ hσ hlower
  exact scoreLiftCLM_pair B _ i₀

end NegativeVotingFanQuadraticTransport
