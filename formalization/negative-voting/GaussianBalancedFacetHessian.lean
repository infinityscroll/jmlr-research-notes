import GaussianBalancedSecondChaosDerivative
import GaussianMomentResponseBound

/-! The literal balanced second-chaos second derivative equals the first
response energy plus the exact signed corrected facet transport formula. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedFacetHessian
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingCoherentLiftHessian
  NegativeVotingFanQuadraticTransport NegativeVotingFanQuadraticMoments
  NegativeVotingActualMomentOperator NegativeVotingGlobalTensorTransport
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingMomentResponseBound
  NegativeVotingFanHessian NegativeVotingSecondChaosMassAdjoint
  NegativeVotingFanSelectedOffsets NegativeVotingModern
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Literal first-response energy and three-term corrected material derivative,
written in its unexpanded signed form to retain label cancellation. -/
def balancedFacetHessianValue (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (c : ι→ℝ) (δ : Parameters d ι) : ℝ :=
  responseEnergy B h δ+(1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j (fun x=>
    (correctedLabelBulk (momentOperator B h i) (c i) (velocityMap L δ).1 (velocityMap L δ).2 x-
      correctedLabelBulk (momentOperator B h j) (c j) (velocityMap L δ).1 (velocityMap L δ).2 x)*
        (affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)-
    (correctedLabelValue (momentOperator B h i) (c i) x-
      correctedLabelValue (momentOperator B h j) (c j) x)*
        inner ℝ (δ.1 i-δ.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2))

theorem frozenCorrectedHessian_eq_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (c : ι→ℝ)
    (δ : Parameters d ι) :
    frozenCorrectedHessian c B h L δ δ=balancedFacetHessianValue B h L c δ := by
  simp only [frozenCorrectedHessian,sub_apply,sum_apply,smul_apply,smul_eq_mul]
  rw [energyHessian_corrected_eq,global_correctedTensorHessian_surface B h σ hσ hlower L hL
    (fun i=>momentOperator B h i) (momentOperator_symmetric B h)]
  rfl

/-- The actual selected balanced energy has the full corrected facet Hessian.
The correction is the derived mass adjoint, the velocity is canonical, and
no path acceleration, scalar Hessian, or surface formula is assumed. -/
theorem hasDerivAt_selected_actual_chaos_surface (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    let h : ι→ℝ := selectedOffsets B p
    let δ : Parameters d ι := (D,NegativeVotingFanCanonicalOffset.canonicalOffsetVariation B h D)
    HasDerivAt (deriv (fun t:ℝ=>chaosEnergy
      (fun x:Fin d→ℝ=>weights (B+t•D) (selectedRowOffsets B D p t)
        (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2))
      (balancedFacetHessianValue B h L (massAdjoint B h) δ) 0 := by
  dsimp only
  rw [←frozenCorrectedHessian_eq_surface B _ σ hσ hlower L hL]
  exact hasDerivAt_selected_actual_chaos_deriv B D σ hσ hlower p hp hs L hL

end NegativeVotingBalancedFacetHessian
