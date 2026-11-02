import GaussianBalancedMomentGeometry
import GaussianRegularReferenceJumpBound

/-! Finite Euclidean offset comparison along the actual selected balanced
row segment. The actual graph gap and geometric bounds are explicit. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingBalancedOffsetComparison
open NegativeVotingFan NegativeVotingFanHessian NegativeVotingFanCanonicalOffset
  NegativeVotingFanJacobian NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingBalancedMomentGeometry NegativeVotingTensorFacetAggregation
  NegativeVotingPolynomialFacetLogBound NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingFanSelectedOffsets NegativeVotingBalancedSecondChaosDerivative
  NegativeVotingBalancedMomentComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Orthogonal decomposition of the actual surface energy bounds the
canonical offset's graph energy by the row-only quadratic form. -/
theorem canonicalOffset_graph_energy_le
    (B D : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    canonicalOffsetVariation B h D ⬝ᵥ
      (offsetJacobian B h *ᵥ canonicalOffsetVariation B h D)≤quadraticForm B h D 0 := by
  have hh := canonicalOffset_remainder B D h σ hσ hlower 0
  simp only [zero_sub,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg] at hh
  linarith [quadraticForm_nonneg B D h (canonicalOffsetVariation B h D)]

/-- No inverse coherent lift is used: the centered graph gap acts on the
one canonical offset vector and the actual weighted degree pays row energy. -/
theorem canonicalOffset_norm_sq_log_le
    (B D : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (gap : ℝ) (hgap : 0<gap)
    (hlaplacian : ∀q:ι→ℝ,(∑i,q i)=0→
      gap*(∑i,(q i)^2)≤q ⬝ᵥ (offsetJacobian B h *ᵥ q))
    (a m degree : ℝ) (hm : 1 ≤ m)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree) (v : FSC.Coord d) :
    (∑i,(canonicalOffsetVariation B h D i)^2)≤
      4*degree*quarticLogConstant a*(1+Real.log m)^4/gap*∑i,‖D i-v‖^2 := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hedge := affineWeightedEdgeScoreEnergy_log_le B D h 0 a m degree hm hinj
    hprob ha hdegree v 0
  simp only [Pi.zero_apply,sub_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero] at hedge
  rw [edgeScoreEnergy_eq_twice_quadraticForm B D h 0 hinj] at hedge
  have hg := (hlaplacian (canonicalOffsetVariation B h D)
    (canonicalOffsetVariation_centered B D h σ hσ hlower)).trans
      (canonicalOffset_graph_energy_le B D h σ hσ hlower)
  have he : (4*degree*quarticLogConstant a*(1+Real.log m)^4/gap*∑i,‖D i-v‖^2)=
      (4*degree*quarticLogConstant a*(1+Real.log m)^4*(∑i,‖D i-v‖^2))/gap := by ring
  rw [he]
  apply (le_div_iff₀ hgap).mpr
  linarith

def offsetVector (h : ι→ℝ) : EuclideanSpace ℝ ι :=
  ∑i,h i • (EuclideanSpace.basisFun ι ℝ i)

theorem offsetVector_coordinate (h : ι→ℝ) (i : ι) : offsetVector h i=h i := by
  simp [offsetVector,EuclideanSpace.basisFun_apply,PiLp.single_apply,Pi.single_apply]

theorem offsetVector_norm_sq (h : ι→ℝ) : ‖offsetVector h‖^2=∑i,(h i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [offsetVector_coordinate]

theorem offsetVector_difference_norm_sq (h k : ι→ℝ) :
    ‖offsetVector h-offsetVector k‖^2=∑i,(h i-k i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply,offsetVector_coordinate]

theorem selected_offsetVector_hasDerivAt (B D : ι→FSC.Coord d) (t : ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound (B+t•D) σ)
    (p : ι→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    HasDerivAt (fun s:ℝ=>offsetVector (selectedRowOffsets B D p s))
      (offsetVector (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)) t := by
  have hd := selectedRowOffsets_hasDerivAt B D t σ hσ hlower p hp hs
  have hi (i : ι) : HasDerivAt (fun s:ℝ=>selectedRowOffsets B D p s i)
      (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D i) t :=
    by
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i : (ι→ℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivAt t hd
  exact HasDerivAt.fun_sum (u:=Finset.univ)
    (fun i _=>(hi i).smul_const (EuclideanSpace.basisFun ι ℝ i))

/-- Integrating the actual C1 canonical response gives a finite offset
comparison in Euclidean label norm, with no coordinatewise loss. -/
theorem selected_offset_difference_sq_le (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ)
    (hlower : ∀t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (B+t•D) σ)
    (p : ι→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (gap : ℝ) (hgap : 0<gap)
    (hlaplacian : ∀t∈Ico (0:ℝ) 1,∀q:ι→ℝ,(∑i,q i)=0→
      gap*(∑i,(q i)^2)≤q ⬝ᵥ
        (offsetJacobian (B+t•D) (selectedRowOffsets B D p t) *ᵥ q))
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀t∈Ico (0:ℝ) 1,∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal (B+t•D) i j))
        (intrinsicFacet (B+t•D) (selectedRowOffsets B D p t) i j)).toReal)
    (ha : ∀t∈Ico (0:ℝ) 1,∀i j,i≠j→
      |pairOffset (B+t•D) (selectedRowOffsets B D p t) i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀t∈Ico (0:ℝ) 1,∀i,
      ∑j,facetWeight (B+t•D) (selectedRowOffsets B D p t) i j≤degree)
    (v : FSC.Coord d) :
    (∑i,((selectedOffsets (B+D) p : ι→ℝ) i-(selectedOffsets B p : ι→ℝ) i)^2)≤
      4*degree*quarticLogConstant a*(1+Real.log m)^4/gap*∑i,‖D i-v‖^2 := by
  let C := 4*degree*quarticLogConstant a*(1+Real.log m)^4/gap*∑i,‖D i-v‖^2
  have hC : 0≤C := by unfold C quarticLogConstant; positivity
  let f := fun t:ℝ=>offsetVector (selectedRowOffsets B D p t)
  let f' := fun t:ℝ=>offsetVector
    (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t :=
    (selected_offsetVector_hasDerivAt B D t σ hσ (hlower t ht) p hp hs).hasDerivWithinAt
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖f' t‖≤Real.sqrt C := by
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hh := canonicalOffset_norm_sq_log_le (B+t•D) D (selectedRowOffsets B D p t)
      σ hσ (hlower t ht') gap hgap (hlaplacian t ht) a m degree hm
      (hprob t ht) (ha t ht) (hdegree t ht) v
    have hsquare : ‖f' t‖^2≤C := by rw [offsetVector_norm_sq]; exact hh
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (f' t)]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  have hh2 := pow_le_pow_left₀ (norm_nonneg (f 1-f 0)) hh 2
  rw [Real.sq_sqrt hC] at hh2
  dsimp only [f] at hh2
  rw [offsetVector_difference_norm_sq] at hh2
  simpa only [selectedRowOffsets,one_smul,zero_smul,add_zero] using hh2

end NegativeVotingBalancedOffsetComparison
