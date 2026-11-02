import GaussianMovingFaceQuadraticMoments
import GaussianFanJointMass
import GaussianFanGradientDerivative

/-! Continuity of the literal Gaussian fan Hessian and genuine joint C2 regularity. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingFanHessianContinuity
open NegativeVotingFan NegativeVotingFanScore NegativeVotingMovingCap
  NegativeVotingMovingFaceQuadratic NegativeVotingFanJointMass
  NegativeVotingFanMovingCells NegativeVotingFacetDegree NegativeVotingCapTail
  NegativeVotingFanHessian NegativeVotingFanGradient
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuousAt_fintypeSum {κ X M : Type*} [Fintype κ] [TopologicalSpace X]
    [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
    {f : X→κ→M} {x : X} (hf : ∀ i,ContinuousAt (fun p=>f p i) x) :
    ContinuousAt (fun p=>∑ i,f p i) x := by
  exact (show Continuous (fun a:κ→M=>∑ i,a i) from
    continuous_finsetSum Finset.univ (fun i _=>continuous_apply i)).continuousAt.comp
      (continuousAt_pi.mpr hf)

/-- Actual boundary pairing in one fixed cap-parameter direction. -/
def capAffineValue (w : ι→FSC.Coord d) (b : ι→ℝ) (u : FSC.Coord d) (a : ℝ)
    (δ : Parameters d ι) : ℝ :=
  ∑ j,WeakSimplex.normalPDF (b j)*sliceTest w b j
    (fun x=>(inner ℝ u x+a)*(inner ℝ (-δ.1 j) x+δ.2 j))

theorem capJointDerivative_affine_apply (w : ι→FSC.Coord d)
    (hw : ∀ k,‖w k‖=1) (b : ι→ℝ) (u : FSC.Coord d) (a : ℝ)
    (δ : Parameters d ι) :
    capJointDerivative w b (fun x=>inner ℝ u x+a) δ=capAffineValue w b u a δ := by
  rw [capJointDerivative_apply w hw b _ (by fun_prop) (‖u‖+|a|) (by positivity)
    (fun x=>affine_abs_bound u x a)]
  unfold capAffineValue
  apply Finset.sum_congr rfl
  intro j _
  rw [tangentFace_integral_eq_restFace w hw b j
    (fun x=>(inner ℝ u x+a)*(δ.2 j-inner ℝ (δ.1 j) x)) (by fun_prop)]
  congr 1
  unfold sliceTest
  congr 1
  funext x
  simp only [inner_neg_left]
  ring

theorem continuousAt_capAffineValue (w : ι→FSC.Coord d)
    (hw : ∀ k,‖w k‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (u : FSC.Coord d) (a : ℝ) (δ : Parameters d ι) :
    ContinuousAt (fun p : Parameters d ι=>capAffineValue p.1 p.2 u a δ) (w,b) := by
  unfold capAffineValue
  apply continuousAt_fintypeSum
  intro j
  have hpdf : ContinuousAt (fun p : Parameters d ι=>WeakSimplex.normalPDF (p.2 j)) (w,b) := by
    unfold WeakSimplex.normalPDF gaussianPDFReal
    fun_prop
  exact hpdf.mul (continuousAt_slice_affine_product w hw b hb j u (-δ.1 j) a (δ.2 j))

private def capBasis (d : ℕ) (ι : Type*) [Fintype ι] := Module.finBasis ℝ (Parameters d ι)
private def capDual (k : Fin (Module.finrank ℝ (Parameters d ι))) : Parameters d ι→L[ℝ]ℝ :=
  ((capBasis d ι).coord k).toContinuousLinearMap

/-- Finite reconstruction from actual affine-test boundary integrals. -/
def capAffineLinear (w : ι→FSC.Coord d) (b : ι→ℝ) (u : FSC.Coord d) (a : ℝ) :
    Parameters d ι→L[ℝ]ℝ :=
  ∑ k,capAffineValue w b u a (capBasis d ι k) • capDual k

theorem capAffineLinear_eq (w : ι→FSC.Coord d) (hw : ∀ k,‖w k‖=1)
    (b : ι→ℝ) (u : FSC.Coord d) (a : ℝ) :
    capAffineLinear w b u a=capJointDerivative w b (fun x=>inner ℝ u x+a) := by
  apply ContinuousLinearMap.coe_injective
  apply (capBasis d ι).ext
  intro k
  change capAffineLinear w b u a (capBasis d ι k)=_
  simpa [capAffineLinear,capDual,Finsupp.single_apply] using
    (capJointDerivative_affine_apply w hw b u a (capBasis d ι k)).symm

theorem continuousAt_capAffineLinear (w : ι→FSC.Coord d) (hw : ∀ k,‖w k‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u : FSC.Coord d) (a : ℝ) :
    ContinuousAt (fun p : Parameters d ι=>capAffineLinear p.1 p.2 u a) (w,b) := by
  unfold capAffineLinear
  apply continuousAt_fintypeSum
  intro k
  exact (continuousAt_capAffineValue w hw b hb u a _).smul continuousAt_const

section Fan
variable [Nonempty ι]

theorem continuousAt_testedCellDerivative_affine (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (u : FSC.Coord d) (a : ℝ) :
    ContinuousAt (fun p : Parameters d ι=>testedCellDerivative p.1 p.2 i
      (fun x=>inner ℝ u x+a)) (B,h) := by
  have hB : Function.Injective B:=fun j k he=>by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hc : ContinuousAt (fun p : Parameters d ι=>
      capAffineLinear (cellNormals p.1 i) (cellSupports p.1 p.2 i) u a) (B,h) :=
    (continuousAt_capAffineLinear (cellNormals B i) (cellNormals_unit B σ hσ hlower i)
      (cellSupports B h i) (cellNormals_noCoincident B h σ hσ hlower i) u a).comp
        (f:=fun p:Parameters d ι=>(cellNormals p.1 i,cellSupports p.1 p.2 i))
        (x:=(B,h)) (continuousAt_cellData B h hB i)
  have hcomp:=hc.clm_comp (continuousAt_fanParameterMap B h hB i)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower] with p hp
  unfold testedCellDerivative
  rw [capAffineLinear_eq _ (cellNormals_unit p.1 (σ/2) (by positivity) hp i)]

theorem continuousAt_secondDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (D : ι→FSC.Coord d) (v : ι→ℝ) :
    ContinuousAt (fun p : Parameters d ι=>secondDerivative p.1 p.2 D v) (B,h) := by
  unfold secondDerivative
  apply continuousAt_fintypeSum
  intro i
  exact continuousAt_testedCellDerivative_affine B h σ hσ hlower i (D i) (v i)

theorem continuousAt_jointHessian (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ContinuousAt (fun p : Parameters d ι=>jointHessian p.1 p.2) (B,h) := by
  letI : ContinuousAdd (Parameters d ι→L[ℝ]Parameters d ι→L[ℝ]ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd
      (Parameters d ι→L[ℝ]Parameters d ι→L[ℝ]ℝ) inferInstance inferInstance
      ContinuousLinearMap.isTopologicalAddGroup
  unfold jointHessian
  change ContinuousAt (fun p : Parameters d ι =>
    (∑ k, (secondDerivative p.1 p.2 _ _).smulRight _ :
      Parameters d ι→L[ℝ]Parameters d ι→L[ℝ]ℝ)) (B,h)
  apply continuousAt_fintypeSum
  intro k
  exact (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous.continuousAt.comp
    ((continuousAt_secondDerivative B h σ hσ hlower _ _).prodMk continuousAt_const)

theorem contDiffAt_jointGradient_one (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun p : Parameters d ι=>jointDerivative p.1 p.2) (B,h) := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun p=>jointHessian p.1 p.2,
    {p : Parameters d ι | CenteredSingularLowerBound p.1 (σ/2)},
    eventually_centeredSingularLowerBound B h σ hσ hlower,?_,?_⟩
  · intro p hp
    exact (continuousAt_jointHessian p.1 p.2 (σ/2) (by positivity) hp).continuousWithinAt
  · intro p hp
    exact hasFDerivAt_jointGradient p.1 p.2 (σ/2) (by positivity) hp

/-- Actual joint C2 regularity in all rows and offsets, with the genuine
Gaussian facet Hessian proved continuous in operator norm. -/
theorem contDiffAt_expectedMax_two (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 2 (fun p : Parameters d ι=>expectedMax p.1 p.2) (B,h) := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n:=1)).mpr
  refine ⟨fun p=>jointDerivative p.1 p.2,?_,contDiffAt_jointGradient_one B h σ hσ hlower⟩
  refine ⟨{p : Parameters d ι | CenteredSingularLowerBound p.1 (σ/2)},
    eventually_centeredSingularLowerBound B h σ hσ hlower,?_⟩
  intro p hp
  apply hasFDerivAt_expectedMax_joint
  intro i j he
  by_contra hij
  exact centered_singular_rows_ne p.1 (σ/2) (by positivity) hp i j hij he

end Fan
end NegativeVotingFanHessianContinuity
