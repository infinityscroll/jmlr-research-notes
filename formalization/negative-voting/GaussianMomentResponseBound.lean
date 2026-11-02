import GaussianActualMomentOperator
import GaussianTensorFacetAggregation

/-! A dimension-free first-moment-response estimate from actual facet duality.
No inverse score lift or offset acceleration enters the bound. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingMomentResponseBound
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanQuadraticMoments
  NegativeVotingAffineLogMassBound NegativeVotingQuadraticBulkNorm
  NegativeVotingTensorHessianContraction NegativeVotingGlobalTensorTransport
  NegativeVotingActualMomentOperator NegativeVotingFanMovingCells NegativeVotingCapTail
  NegativeVotingSecondChaosFacetGradient NegativeVotingTensorFacetAggregation
  NegativeVotingWeightedFacet NegativeVotingFanHessian NegativeVotingQuadraticTensorBulkNorm
  NegativeVotingPolynomialDegree NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingPolynomialFacetLogBound NegativeVotingDisintegration NegativeVotingFanJacobian
  NegativeVotingFacetDegree
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Explicit operator of the ACTUAL first derivative of the centered moment tensor. -/
def responseOperator (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (δ : Parameters d ι) :
    FSC.Coord d→L[ℝ] FSC.Coord d :=
  ∑ j,∑ k,testedCellDerivative B h i (tensorTest j k) δ •
    (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)).smulRight
      (EuclideanSpace.basisFun (Fin d) ℝ k)

theorem responseOperator_apply (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι)
    (δ : Parameters d ι) (x : FSC.Coord d) :
    responseOperator B h i δ x=∑ j,∑ k,(testedCellDerivative B h i (tensorTest j k) δ*x j) •
      (EuclideanSpace.basisFun (Fin d) ℝ k) := by
  have he (j:Fin d) : innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) x=x j :=
    EuclideanSpace.basisFun_inner _ _ x j
  simp only [responseOperator,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,he,smul_smul]

theorem responseOperator_entries (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι)
    (δ : Parameters d ι) (j k : Fin d) :
    operatorEntries (responseOperator B h i δ) j k=testedCellDerivative B h i (tensorTest j k) δ := by
  rw [operatorEntries,responseOperator_apply]
  simp [EuclideanSpace.basisFun_apply,PiLp.single_apply,Pi.single_apply]

def responseEnergy (B : ι→FSC.Coord d) (h : ι→ℝ) (δ : Parameters d ι) : ℝ :=
  ∑ i,∑ j,∑ k,(testedCellDerivative B h i (tensorTest j k) δ)^2

theorem responseEnergy_nonneg (B : ι→FSC.Coord d) (h : ι→ℝ) (δ : Parameters d ι) :
    0 ≤ responseEnergy B h δ := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>
      Finset.sum_nonneg fun _ _=>sq_nonneg _

theorem responseOperator_HS_sum (B : ι→FSC.Coord d) (h : ι→ℝ) (δ : Parameters d ι) :
    (∑ i,(operatorHilbertSchmidt (responseOperator B h i δ))^2)=responseEnergy B h δ := by
  unfold operatorHilbertSchmidt responseEnergy
  simp only [responseOperator_entries,Real.sq_sqrt (Finset.sum_nonneg fun _ _=>
    Finset.sum_nonneg fun _ _=>sq_nonneg _)]

theorem quadratic_response_duality (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (δ : Parameters d ι) :
    (∑ i,testedCellDerivative B h i (quadraticScore (responseOperator B h i δ)) δ)=
      responseEnergy B h δ := by
  simp_rw [testedCellDerivative_quadraticScore_entries B h σ hσ hlower]
  simp only [sum_apply,smul_apply,smul_eq_mul,responseOperator_entries,responseEnergy,pow_two]

/-- Gaussian polynomial trace of arbitrary quadratic operator tests. -/
theorem affineWeightedFacetEnergy_quadraticScore_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree) (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ) ≤ 
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j) ≤ degree) :
    affineWeightedFacetEnergy B h (fun i=>quadraticScore (U i))  ≤ 
      2*degree*quarticLogConstant a*(1+Real.log m)^4*∑ i,(operatorHilbertSchmidt (U i))^2 := by
  have hpoly (i j : ι) :
      (fun x=>quadraticScore (U i) (reconstructLinear (pairNormal B i j)
        (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4 := by
    apply polynomialSpace_mono (by decide : 2 ≤ 4)
    simpa only [quadraticScore,inner_zero_left,add_zero] using
      massBulk_expression_mem (reconstructLinear (pairNormal B i j)
        (canonicalTangentCoordinates (pairNormal B i j))) (U i) 0
  have hb := affineWeightedFacetEnergy_polynomial_log_le B h (fun i=>quadraticScore (U i))
    a m degree hm hinj (fun i=>by unfold quadraticScore; fun_prop) (fun i j _=>hpoly i j)
    hprob ha hdegree
  refine hb.trans ?_
  calc
    _  ≤  degree*quarticLogConstant a*(1+Real.log m)^4*∑ i,2*(operatorHilbertSchmidt (U i))^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>quadraticScore_integral_sq_le (U i))
        (by unfold quarticLogConstant; positivity)
    _ = _ := by simp only [Finset.mul_sum]; ring

/-- Direct first-variation pairing. Its bound has no inverse lift and no
ambient-dimension or number-of-labels coefficient. -/
theorem tested_quadratic_sum_abs_le_energies (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d) (δ : Parameters d ι) :
    |∑ i,testedCellDerivative B h i (quadraticScore (U i)) δ| ≤ 
      Real.sqrt (affineWeightedFacetEnergy B h (fun i=>quadraticScore (U i)))*
      Real.sqrt (affineWeightedEdgeScoreEnergy B δ.1 h δ.2) := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hh := ordered_integral_mul_abs_le (fun _ _=>FSC.Coord d)
    (fun i j=>FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))
    (affineFacet B h) (fun i _=>quadraticScore (U i))
    (fun i j x=>inner ℝ (δ.1 i-δ.1 j) x+(δ.2 i-δ.2 j))
    (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖)
    (fun i j=>div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    (fun i j _=>by
      let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact ((quadraticScore_memLp_four μ (U i)).mono_exponent (by norm_num : (2:ENNReal) ≤ 4)).restrict _)
    (fun i j _=>by
      let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (δ.1 i-δ.1 j) |>.add
        (memLp_const (δ.2 i-δ.2 j))).restrict _)
  change |∑ i,∑ j∈Finset.univ.erase i,surfaceIntegral B h i j
    (fun x=>quadraticScore (U i) x*(inner ℝ (δ.1 i-δ.1 j) x+(δ.2 i-δ.2 j)))| ≤ 
    Real.sqrt (orderedFacetEnergy _ _ _ _ _ _)*Real.sqrt (orderedFacetEnergy _ _ _ _ _ _) at hh
  rw [orderedFacetEnergy_eq_ambient B h hinj _ (fun i _=>by unfold quadraticScore; fun_prop),
    orderedFacetEnergy_eq_ambient B h hinj _ (fun _ _=>by fun_prop)] at hh
  have he : (∑ i,testedCellDerivative B h i (quadraticScore (U i)) δ)=
      ∑ i,∑ j∈Finset.univ.erase i,surfaceIntegral B h i j
        (fun x=>quadraticScore (U i) x*(inner ℝ (δ.1 i-δ.1 j) x+(δ.2 i-δ.2 j))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [testedCellDerivative_quadraticScore_surface B h σ hσ hlower i]
    have hgap (j:ι) : (fun x=>quadraticScore (U i) x*
        (affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x))=
        (fun x=>quadraticScore (U i) x*(inner ℝ (δ.1 i-δ.1 j) x+(δ.2 i-δ.2 j))) := by
      funext x
      simp only [affineScore,inner_sub_left]
      ring
    simp_rw [hgap]
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro j _ hj
    have hji : j=i := by simpa using hj
    rw [hji,surfaceIntegral_diagonal]
  rw [he]
  exact hh



/-- The squared actual moment response is paid directly by edge-score energy.
The constant has no inverse singular value, dimension, or row-count loss. -/
theorem responseEnergy_log_le (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (δ : Parameters d ι)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ) ≤ 
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j) ≤ degree) :
    responseEnergy B h δ ≤ 2*degree*quarticLogConstant a*(1+Real.log m)^4*
      affineWeightedEdgeScoreEnergy B δ.1 h δ.2 := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  let C := 2*degree*quarticLogConstant a*(1+Real.log m)^4
  have hC : 0 ≤ C := by unfold C quarticLogConstant; positivity
  have hE := responseEnergy_nonneg B h δ
  have hS : 0 ≤ affineWeightedEdgeScoreEnergy B δ.1 h δ.2 := by
    unfold affineWeightedEdgeScoreEnergy orderedFacetEnergy
    exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
      mul_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
        (integral_nonneg fun _=>sq_nonneg _)
  have hb := affineWeightedFacetEnergy_quadraticScore_le B h (fun i=>responseOperator B h i δ)
    a m degree hm hdegree0 hinj hprob ha hdegree
  rw [responseOperator_HS_sum] at hb
  have hd := tested_quadratic_sum_abs_le_energies B h σ hσ hlower (fun i=>responseOperator B h i δ) δ
  rw [quadratic_response_duality B h σ hσ hlower,abs_of_nonneg hE] at hd
  have hh : responseEnergy B h δ ≤ Real.sqrt (C*responseEnergy B h δ)*
      Real.sqrt (affineWeightedEdgeScoreEnergy B δ.1 h δ.2) :=
    hd.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _))
  have hh2 := pow_le_pow_left₀ hE hh 2
  rw [mul_pow,Real.sq_sqrt (mul_nonneg hC hE),Real.sq_sqrt hS] at hh2
  change responseEnergy B h δ ≤ C*affineWeightedEdgeScoreEnergy B δ.1 h δ.2
  by_cases hz : responseEnergy B h δ=0
  · rw [hz]
    exact mul_nonneg hC hS
  · have hp : 0<responseEnergy B h δ := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

end NegativeVotingMomentResponseBound
