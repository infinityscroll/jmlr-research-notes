import GaussianHessianReferenceRemainder

/-! The actual reference/remainder Hessian split with the constructed bounded
coherent lift. Its inverse singular-value cost is retained explicitly. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingBoundedHessianRemainder
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingFanQuadraticTransport NegativeVotingBoundedCoherentLift
  NegativeVotingHessianReferenceRemainder NegativeVotingBalancedFacetHessian
  NegativeVotingReferenceJumpComparison NegativeVotingMomentResponseBound
  NegativeVotingFanJacobian NegativeVotingCapTail NegativeVotingAffineLogMassBound
  NegativeVotingPolynomialFacetLogBound NegativeVotingDisintegration NegativeVotingWeightedFacet
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Elementary cancellation of the two tangent-energy square roots, with
positive singular value. -/
theorem sqrt_velocity_product_le (C E S T σ : ℝ)
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hσ : 0<σ) (hE : E≤T/σ^2) :
    C*Real.sqrt E*Real.sqrt S*Real.sqrt T≤C/σ*Real.sqrt S*T := by
  calc
    _ ≤ C*Real.sqrt (T/σ^2)*Real.sqrt S*Real.sqrt T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hC) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = C/σ*Real.sqrt S*(Real.sqrt T)^2 := by
      rw [Real.sqrt_div hT,Real.sqrt_sq hσ.le]
      ring
    _ = _ := by rw [Real.sq_sqrt hT]

/-- The actual balanced Hessian with the inverse-lift factor reduced to 1/σ.
Only the remainder is estimated generically; the signed reference contribution
remains available for its exact regular-facet cancellation. -/
theorem balancedFacetHessianValue_boundedLift_reference_abs_le
    (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i₀ : ι)
    (c : ι→ℝ) (δ : Parameters d ι)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree) (v : FSC.Coord d) (b : ℝ) :
    let L := boundedScoreLift B σ hσ hlower i₀
    |balancedFacetHessianValue B h L c δ|≤
      responseEnergy B h δ+|referenceTransport B R h r L δ|+
        (520*degree*quarticLogConstant a*(1+Real.log m)^4/σ)*
          Real.sqrt (momentDifferenceEnergy B R h r+∑i,(c i)^2)*
          ((∑i,‖δ.1 i-v‖^2)+(∑i,(δ.2 i-b)^2)) := by
  dsimp only
  have hh := balancedFacetHessianValue_reference_abs_le B R h r σ hσ hlower
    (boundedScoreLift B σ hσ hlower i₀) (boundedScoreLift_coherent B σ hσ hlower i₀)
    c δ a m degree hm hdegree0 hprob ha hdegree v b
  refine hh.trans (add_le_add le_rfl ?_)
  apply sqrt_velocity_product_le
  · unfold quarticLogConstant
    positivity
  · apply add_nonneg
    · unfold momentDifferenceEnergy
      exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
        Finset.sum_nonneg fun k _=>sq_nonneg _
    · exact Finset.sum_nonneg fun i _=>sq_nonneg _
  · exact add_nonneg (Finset.sum_nonneg fun i _=>sq_nonneg _)
      (Finset.sum_nonneg fun i _=>sq_nonneg _)
  · exact hσ
  · exact bounded_velocity_energy_le B σ hσ hlower i₀ δ v b

end NegativeVotingBoundedHessianRemainder
