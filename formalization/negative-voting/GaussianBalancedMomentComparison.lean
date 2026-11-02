import GaussianBalancedSecondChaosDerivative
import GaussianMomentResponseBound
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite comparison of the literal balanced centered moment tensors.
Uniform facet geometry and edge-energy bounds remain explicit hypotheses;
all differentiation and integration steps are derived for selectedOffsets. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedMomentComparison
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingFanQuadraticMoments
  NegativeVotingFanSelectedOffsets NegativeVotingFanCanonicalOffset
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingMomentResponseBound
  NegativeVotingTensorFacetAggregation NegativeVotingWeightedFacet NegativeVotingDisintegration
  NegativeVotingPolynomialFacetLogBound NegativeVotingFanJacobian
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite tensor is encoded in its genuine Euclidean norm, not a sum of
coordinatewise estimates. -/
def momentVector (B : ι→FSC.Coord d) (h : ι→ℝ) : EuclideanSpace ℝ (ι×Fin d×Fin d) :=
  ∑ q:ι×Fin d×Fin d,secondMomentTensor B h q.1 q.2.1 q.2.2 •
    (EuclideanSpace.basisFun (ι×Fin d×Fin d) ℝ q)

def responseVector (B : ι→FSC.Coord d) (h : ι→ℝ) (δ : Parameters d ι) :
    EuclideanSpace ℝ (ι×Fin d×Fin d) :=
  ∑ q:ι×Fin d×Fin d,testedCellDerivative B h q.1 (tensorTest q.2.1 q.2.2) δ •
    (EuclideanSpace.basisFun (ι×Fin d×Fin d) ℝ q)

theorem momentVector_coordinate (B : ι→FSC.Coord d) (h : ι→ℝ) (q : ι×Fin d×Fin d) :
    momentVector B h q=secondMomentTensor B h q.1 q.2.1 q.2.2 := by
  simp [momentVector,EuclideanSpace.basisFun_apply,PiLp.single_apply,Pi.single_apply]

theorem responseVector_coordinate (B : ι→FSC.Coord d) (h : ι→ℝ)
    (δ : Parameters d ι) (q : ι×Fin d×Fin d) :
    responseVector B h δ q=testedCellDerivative B h q.1 (tensorTest q.2.1 q.2.2) δ := by
  simp [responseVector,EuclideanSpace.basisFun_apply,PiLp.single_apply,Pi.single_apply]

theorem responseVector_norm_sq (B : ι→FSC.Coord d) (h : ι→ℝ) (δ : Parameters d ι) :
    ‖responseVector B h δ‖^2=responseEnergy B h δ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [responseVector_coordinate,Fintype.sum_prod_type,responseEnergy]

theorem momentVector_difference_norm_sq (B C : ι→FSC.Coord d) (h k : ι→ℝ) :
    ‖momentVector C k-momentVector B h‖^2=
      ∑ i,∑ j,∑ l,(secondMomentTensor C k i j l-secondMomentTensor B h i j l)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply,momentVector_coordinate,Fintype.sum_prod_type]

/-- The actual selected-offset derivative at an arbitrary point on the row
line is its canonical balanced response. -/
theorem selectedRowOffsets_hasDerivAt (B D : ι→FSC.Coord d) (t : ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound (B+t•D) σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    HasDerivAt (selectedRowOffsets B D p)
      (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D) t := by
  let a := selectedRowOffsets (B+t•D) D p
  have ha := selectedRowOffsets_contDiffAt (B+t•D) D σ hσ hlower p hp hs
  have hm := selectedRowOffsets_balanced (B+t•D) D σ hσ hlower p hp hs
  have hm0 : mass (B+t•D) (a 0)=p := by
    have hh := hm.self_of_nhds
    simpa only [zero_smul,add_zero,a] using hh
  have hm' : ∀ᶠ s in 𝓝 (0:ℝ),mass ((B+t•D)+s•D) (a s)=mass (B+t•D) (a 0) := by
    simpa only [hm0,a] using hm
  have hc (s : ℝ) : ∑ i,a s i=0 := (selectedOffsets ((B+t•D)+s•D) p).property
  have hv := balanced_offset_deriv_eq_canonical (B+t•D) D a σ hσ hlower ha hc hm'
  have hd : HasDerivAt a (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D) 0 := by
    have hh := (ha.differentiableAt (by norm_num)).hasDerivAt
    rw [hv] at hh
    simpa only [a,selectedRowOffsets,zero_smul,add_zero] using hh
  have hd' : HasDerivAt a (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D) (t-t) := by
    simpa only [sub_self] using hd
  have hh := hd'.scomp (h:=fun s:ℝ=>s-t) t ((hasDerivAt_id t).sub_const t)
  have he : (fun s=>a (s-t))=selectedRowOffsets B D p := by
    funext s
    dsimp only [a,selectedRowOffsets]
    have hr : (B+t•D)+(s-t)•D=B+s•D := by rw [sub_smul]; abel
    rw [hr]
  simpa only [Function.comp_def,one_smul,he] using hh

/-- The actual full tensor derivative is the assembled facet response. -/
theorem selected_momentVector_hasDerivAt (B D : ι→FSC.Coord d) (t : ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound (B+t•D) σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    HasDerivAt (fun s:ℝ=>momentVector (B+s•D) (selectedRowOffsets B D p s))
      (responseVector (B+t•D) (selectedRowOffsets B D p t)
        (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)) t := by
  have ha := selectedRowOffsets_hasDerivAt B D t σ hσ hlower p hp hs
  have hr : HasDerivAt (fun s:ℝ=>B+s•D) D t := by
    simpa using ((hasDerivAt_id t).smul_const D).const_add B
  have hh := HasDerivAt.fun_sum (u:=Finset.univ) (fun q:ι×Fin d×Fin d=>fun _=>
    ((hasFDerivAt_secondMomentTensor (B+t•D) (selectedRowOffsets B D p t) σ hσ hlower
      q.1 q.2.1 q.2.2).comp_hasDerivAt t (hr.prodMk ha)).smul_const
        (EuclideanSpace.basisFun (ι×Fin d×Fin d) ℝ q))
  convert! hh using 1

/-- Finite tensor comparison along the actual selected balanced row segment.
The only quantitative inputs are uniform literal facet geometry and an
upper bound R for the actual balanced edge-score energy. -/
theorem selected_moment_difference_sq_le (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (B+t•D) σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (a m degree R : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree) (hR : 0 ≤ R)
    (hprob : ∀ t∈Ico (0:ℝ) 1,∀ i j,i≠j→m^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal (B+t•D) i j))
        (intrinsicFacet (B+t•D) (selectedRowOffsets B D p t) i j)).toReal)
    (ha : ∀ t∈Ico (0:ℝ) 1,∀ i j,i≠j→
      |pairOffset (B+t•D) (selectedRowOffsets B D p t) i j| ≤ a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ t∈Ico (0:ℝ) 1,∀ i,
      (∑ j∈Finset.univ.erase i,facetWeight (B+t•D) (selectedRowOffsets B D p t) i j) ≤ degree)
    (hedge : ∀ t∈Ico (0:ℝ) 1,
      affineWeightedEdgeScoreEnergy (B+t•D) D (selectedRowOffsets B D p t)
        (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D) ≤ R) :
    (∑ i,∑ j,∑ k,
      (secondMomentTensor (B+D) (selectedOffsets (B+D) p) i j k-
       secondMomentTensor B (selectedOffsets B p) i j k)^2) ≤
      2*degree*quarticLogConstant a*(1+Real.log m)^4*R := by
  let C := 2*degree*quarticLogConstant a*(1+Real.log m)^4
  have hC : 0 ≤ C := by unfold C quarticLogConstant; positivity
  let f := fun t:ℝ=>momentVector (B+t•D) (selectedRowOffsets B D p t)
  let f' := fun t:ℝ=>responseVector (B+t•D) (selectedRowOffsets B D p t)
    (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t :=
    (selected_momentVector_hasDerivAt B D t σ hσ (hlower t ht) p hp hs).hasDerivWithinAt
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖f' t‖ ≤ Real.sqrt (C*R) := by
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hh := responseEnergy_log_le (B+t•D) (selectedRowOffsets B D p t) σ hσ (hlower t ht')
      (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)
      a m degree hm hdegree0 (hprob t ht) (ha t ht) (hdegree t ht)
    have hsquare : ‖f' t‖^2 ≤ C*R := by
      rw [responseVector_norm_sq]
      exact hh.trans (mul_le_mul_of_nonneg_left (hedge t ht) hC)
    nlinarith [Real.sq_sqrt (mul_nonneg hC hR),Real.sqrt_nonneg (C*R),norm_nonneg (f' t)]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  have hh2 := pow_le_pow_left₀ (norm_nonneg (f 1-f 0)) hh 2
  rw [Real.sq_sqrt (mul_nonneg hC hR)] at hh2
  dsimp only [f] at hh2
  rw [momentVector_difference_norm_sq] at hh2
  simpa only [selectedRowOffsets,one_smul,zero_smul,add_zero] using hh2

end NegativeVotingBalancedMomentComparison
