import GaussianFanCycleAnalyticBridge
import GaussianFanCycleResidual
import GaussianFanJointMass
import GaussianFanCanonicalOffset

/-! The actual optimizer creates the literal divergence-free cycle used in
the geometric energy identity. No cycle condition is assumed for that optimizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanCycleFlux
open NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingFan
  NegativeVotingFanHessian NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanJointMass NegativeVotingFanCanonicalOffset NegativeVotingCapTail
  NegativeVotingWeightedFacet
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The derivative of each actual cell mass is its outgoing geometric flux. -/
theorem jointMassDerivativeAt_eq_flux (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (z : V → FSC.Coord d) (beta : V → ℝ) (i : V) :
    jointMassDerivativeAt b h i (z,beta) = ∑ j, cycleFlux b h z beta i j := by
  rw [jointMassDerivativeAt_eq_tested b h σ hσ hlower i,
    testedCellDerivative_apply_ambient b h σ hσ hlower i (fun _ => 1) continuous_const
      1 (by norm_num) (fun x => by simp)]
  have hterm (j : {j : V // j ≠ i}) :
      ProbabilityTheory.gaussianPDFReal 0 1 (pairOffset b h j.1 i) / ‖b j.1-b i‖ *
        ∫ x in affineFacet b h j.1 i,
          (1:ℝ) * (inner ℝ (z i-z j.1) x + beta i-beta j.1)
          ∂FSC.sliceLaw (pairNormal b j.1 i) (pairOffset b h j.1 i) =
      cycleFlux b h z beta i j.1 := by
    change surfaceIntegral b h j.1 i (fun x => (1:ℝ)*(inner ℝ (z i-z j.1) x+beta i-beta j.1)) = _
    rw [surfaceIntegral_reverse]
    have he : (fun x : FSC.Coord d => (1:ℝ)*(inner ℝ (z i-z j.1) x+beta i-beta j.1)) =
        (fun x => inner ℝ (z i-z j.1) x+(beta i-beta j.1)) := by funext x; ring
    rw [he,surfaceIntegral_affine b h i j.1 (Ne.symm j.property)]
    unfold cycleFlux cycleMeanEdge
    ring
  simp only [hterm]
  have hsub := Finset.sum_subtype (p := fun j : V => j ≠ i)
    (F := inferInstance) (Finset.univ.erase i) (by intro j; simp) (fun j => cycleFlux b h z beta i j)
  rw [← hsub]
  have hz : cycleFlux b h z beta i i = 0 := by
    simp [cycleFlux,cycleMeanEdge,stratumMeanPairing]
  simpa only [hz,add_zero] using
    (Finset.sum_erase_add Finset.univ (fun j => cycleFlux b h z beta i j) (Finset.mem_univ i))

/-- Incoming graph divergence is minus the literal cell-mass derivative. -/
theorem edgeBoundary_cycleFlux_eq (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (z : V → FSC.Coord d) (beta : V → ℝ) (i : V) :
    edgeBoundary (cycleFlux b h z beta) i = -jointMassDerivativeAt b h i (z,beta) := by
  rw [jointMassDerivativeAt_eq_flux b h σ hσ hlower,edgeBoundary]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact cycleFlux_skew b h z beta j i

/-- Zero derivatives of actual masses provide the geometric cycle condition. -/
theorem edgeBoundary_zero_of_mass_derivatives (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (z : V → FSC.Coord d) (beta : V → ℝ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass ((b : V → FSC.Coord d)+t•z) (h+t•beta) i) 0 0) :
    ∀ i, edgeBoundary (cycleFlux b h z beta) i = 0 := by
  have hline : HasDerivAt (fun t : ℝ => ((b : V → FSC.Coord d)+t•z,h+t•beta)) (z,beta) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).smul_const z).const_add (b : V → FSC.Coord d)).prodMk
      (((hasDerivAt_id (0:ℝ)).smul_const beta).const_add h)
  intro i
  have hD : HasFDerivAt (fun q : Parameters d V => mass q.1 q.2 i)
      (jointMassDerivativeAt b h i) ((b : V → FSC.Coord d)+(0:ℝ)•z,h+(0:ℝ)•beta) := by
    simpa using hasFDerivAt_mass_joint_component b h σ hσ hlower i
  have hd : HasDerivAt (fun t : ℝ => mass ((b : V → FSC.Coord d)+t•z) (h+t•beta) i)
      (jointMassDerivativeAt b h i (z,beta)) 0 := by
    simpa only [Function.comp_def] using hD.comp_hasDerivAt 0 hline
  have hz := hd.unique (hm i)
  rw [edgeBoundary_cycleFlux_eq b h σ hσ hlower,hz,neg_zero]

/-- The canonical global offset minimizer supplies an actual cycle without
any imposed divergence condition. -/
theorem canonicalOffset_cycle (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ) (z : V → FSC.Coord d) :
    ∀ i, edgeBoundary (cycleFlux b h z (canonicalOffsetVariation b h z)) i = 0 :=
  edgeBoundary_zero_of_mass_derivatives b h σ hσ hlower z _
    (hasDerivAt_mass_line_canonical b z h σ hσ hlower)

end NegativeVotingFanCycleFlux
