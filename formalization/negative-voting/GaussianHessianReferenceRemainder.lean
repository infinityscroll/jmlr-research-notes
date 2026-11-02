import GaussianCorrectedTransportBound

/-! Exact regular-reference split of the actual balanced second-chaos
Hessian. The generic transport estimate is applied only to the actual moment
difference and frozen mass-adjoint scalar, never the entire reference tensor. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingHessianReferenceRemainder
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingGlobalTensorTransport NegativeVotingCoherentLiftHessian
  NegativeVotingFanQuadraticTransport NegativeVotingActualMomentOperator
  NegativeVotingBalancedFacetHessian NegativeVotingBalancedSecondChaosDerivative
  NegativeVotingCorrectedTransportBound NegativeVotingReferenceJumpComparison
  NegativeVotingMomentResponseBound NegativeVotingFanJacobian NegativeVotingCapTail
  NegativeVotingPolynomialFacetLogBound NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingTensorFacetAggregation NegativeVotingAffineLogMassBound
  NegativeVotingQuadraticBulkNorm NegativeVotingSecondChaosFacetGradient
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Algebraic tensor linearity, with the scalar correction entirely in the
remainder. This equality does not require tensor symmetry. -/
theorem correctedTensorHessian_reference_split
    (B : ι→FSC.Coord d) (h : ι→ℝ) (L : (ι→ℝ)→L[ℝ]FSC.Coord d)
    (i : ι) (U R : FSC.Coord d→L[ℝ]FSC.Coord d) (c : ℝ) (ε δ : Parameters d ι) :
    correctedTensorHessian B h L i U c ε δ=
      correctedTensorHessian B h L i R 0 ε δ+
      correctedTensorHessian B h L i (U-R) c ε δ := by
  have he (j k : Fin d) : operatorEntries (U-R) j k=operatorEntries U j k-operatorEntries R j k := rfl
  simp only [correctedTensorHessian,he,sub_mul,Finset.sum_sub_distrib,zero_mul,sub_zero]
  ring

/-- The reference transport is kept as one signed quantity. -/
def referenceTransport (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (δ : Parameters d ι) : ℝ :=
  ∑i,correctedTensorHessian B h L i (momentOperator R r i) 0 δ δ

/-- The actual balanced Hessian, with no analytic estimate yet applied. -/
theorem balancedFacetHessianValue_reference_split
    (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (c : ι→ℝ) (δ : Parameters d ι) :
    balancedFacetHessianValue B h L c δ=
      responseEnergy B h δ+referenceTransport B R h r L δ+
        ∑i,correctedTensorHessian B h L i (momentOperator B h i-momentOperator R r i) (c i) δ δ := by
  rw [←frozenCorrectedHessian_eq_surface B h σ hσ hlower L hL]
  simp only [frozenCorrectedHessian,sub_apply,sum_apply,smul_apply,smul_eq_mul]
  rw [energyHessian_corrected_eq]
  change responseEnergy B h δ+(∑i,correctedTensorHessian B h L i (momentOperator B h i) (c i) δ δ)=_
  have he : (∑i,correctedTensorHessian B h L i (momentOperator B h i) (c i) δ δ)=
      ∑i,(correctedTensorHessian B h L i (momentOperator R r i) 0 δ δ+
        correctedTensorHessian B h L i (momentOperator B h i-momentOperator R r i) (c i) δ δ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact correctedTensorHessian_reference_split B h L i _ _ _ δ δ
  rw [he,Finset.sum_add_distrib]
  dsimp only [referenceTransport]
  ring

/-- The actual balanced Hessian is bounded by the signed regular transport
and a dimension-free bound paid only by the actual moment difference. -/
theorem balancedFacetHessianValue_reference_abs_le
    (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (c : ι→ℝ) (δ : Parameters d ι)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree) (v : FSC.Coord d) (b : ℝ) :
    let V := velocityMap L δ
    |balancedFacetHessianValue B h L c δ|≤
      responseEnergy B h δ+|referenceTransport B R h r L δ|+
        520*degree*quarticLogConstant a*(1+Real.log m)^4*
          Real.sqrt ((operatorHilbertSchmidt V.1)^2+‖V.2‖^2)*
          Real.sqrt (momentDifferenceEnergy B R h r+∑i,(c i)^2)*
          Real.sqrt ((∑i,‖δ.1 i-v‖^2)+(∑i,(δ.2 i-b)^2)) := by
  dsimp only
  have hU (i : ι) : (momentOperator B h i-momentOperator R r i).toLinearMap.IsSymmetric :=
    (momentOperator_symmetric B h i).sub (momentOperator_symmetric R r i)
  have hb := correctedTensorHessian_sum_log_le B h σ hσ hlower L hL
    (fun i=>momentOperator B h i-momentOperator R r i) hU c δ δ
    a m degree hm hdegree0 hprob ha hdegree v b
  simp only [Finset.sum_add_distrib,momentDifference_HS_sum] at hb
  rw [balancedFacetHessianValue_reference_split B R h r σ hσ hlower L hL]
  have hresp : 0≤responseEnergy B h δ := by
    unfold responseEnergy
    exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
      Finset.sum_nonneg fun k _=>sq_nonneg _
  refine (abs_add_le _ _).trans (add_le_add ?_ hb)
  simpa only [abs_of_nonneg hresp] using abs_add_le (responseEnergy B h δ) (referenceTransport B R h r L δ)

/-- The derivative of the actual symmetric centered quadratic along a line. -/
theorem quadraticScore_hasDerivAt_line (U : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hU : U.toLinearMap.IsSymmetric) (x V : FSC.Coord d) :
    HasDerivAt (fun t:ℝ=>quadraticScore U (x+t • V)) (2*inner ℝ (U x) V) 0 := by
  have he : (fun t:ℝ=>quadraticScore U (x+t • V))=
      fun t:ℝ=>quadraticScore U x+t*(2*inner ℝ (U x) V)+t^2*inner ℝ V (U V) := by
    funext t
    have hs : inner ℝ (U x) V=inner ℝ x (U V) := hU x V
    have hc : inner ℝ V (U x)=inner ℝ (U x) V := real_inner_comm _ _
    simp only [quadraticScore,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,inner_smul_right,hs,hc]
    ring
  rw [he]
  convert (((hasDerivAt_const (0:ℝ) (quadraticScore U x)).add
    ((hasDerivAt_id (0:ℝ)).mul_const (2*inner ℝ (U x) V))).add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (inner ℝ V (U V)))) using 1
  · rfl
  · simp

/-- The literal moment operator generates the actual Gaussian regular-label
material derivative; no additional matrix-representation premise is needed. -/
theorem actualLabelJump_hasDerivAt_line (R : ι→FSC.Coord d) (r : ι→ℝ)
    (i j : ι) (x V : FSC.Coord d) :
    HasDerivAt (fun t:ℝ=>quadraticLabelTest R r i (x+t • V)-quadraticLabelTest R r j (x+t • V))
      (2*inner ℝ ((momentOperator R r i-momentOperator R r j) x) V) 0 := by
  have hi := quadraticScore_hasDerivAt_line (momentOperator R r i) (momentOperator_symmetric R r i) x V
  have hj := quadraticScore_hasDerivAt_line (momentOperator R r j) (momentOperator_symmetric R r j) x V
  simp only [momentOperator_quadraticScore] at hi hj
  convert hi.sub hj using 1
  simp only [ContinuousLinearMap.sub_apply,inner_sub_left]
  ring

end NegativeVotingHessianReferenceRemainder
