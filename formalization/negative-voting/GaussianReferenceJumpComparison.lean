import GaussianMassAdjointEnergy

/-! Quadratic jump energy split at an actual reference fan. The reference
polynomial is evaluated on the CURRENT facets, retaining its exact facet-zero
cancellation. The remainder is paid by the Euclidean tensor difference. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingReferenceJumpComparison
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian
  NegativeVotingFanHessian NegativeVotingSecondChaosFacetGradient
  NegativeVotingMassAdjointEnergy NegativeVotingSecondChaosMassAdjoint
  NegativeVotingGlobalTensorTransport NegativeVotingWeightedFacet NegativeVotingCapTail
  NegativeVotingFacetDegree NegativeVotingFanQuadraticMoments
  NegativeVotingActualMomentOperator NegativeVotingQuadraticBulkNorm
  NegativeVotingAffineLogMassBound NegativeVotingMomentResponseBound
  NegativeVotingTensorFacetAggregation NegativeVotingDisintegration NegativeVotingPolynomialFacetLogBound
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The reference tensor is tested on the current fan's actual faces. -/
def referenceJumpEnergy (B R : ι→FSC.Coord d) (h r : ι→ℝ) : ℝ :=
  (1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j
    (fun x=>(quadraticLabelTest R r i x-quadraticLabelTest R r j x)^2)

def momentDifferenceEnergy (B R : ι→FSC.Coord d) (h r : ι→ℝ) : ℝ :=
  ∑ i,∑ j,∑ k,(secondMomentTensor B h i j k-secondMomentTensor R r i j k)^2

theorem squared_integrable {μ : Measure (FSC.Coord d)} {F : FSC.Coord d→ℝ}
    (hF : MemLp F 2 μ) : Integrable (fun x=>(F x)^2) μ := by
  convert hF.integrable_mul hF using 1
  funext x
  exact pow_two (F x)

theorem surface_three_squares (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F G H : FSC.Coord d→ℝ)
    (hF : MemLp F 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hG : MemLp G 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hH : MemLp H 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    surfaceIntegral B h i j (fun x=>(F x+G x-H x)^2) ≤
      2*surfaceIntegral B h i j (fun x=>(F x)^2)+
      4*surfaceIntegral B h i j (fun x=>(G x)^2)+
      4*surfaceIntegral B h i j (fun x=>(H x)^2) := by
  have hl : Integrable (fun x=>(F x+G x-H x)^2)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := squared_integrable ((hF.add hG).sub hH)
  have hr : Integrable (fun x=>2*(F x)^2+4*(G x)^2+4*(H x)^2)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) :=
    (((squared_integrable hF).const_mul 2).add ((squared_integrable hG).const_mul 4)).add
      ((squared_integrable hH).const_mul 4)
  have hh : surfaceIntegral B h i j (fun x=>(F x+G x-H x)^2) ≤
      surfaceIntegral B h i j (fun x=>2*(F x)^2+4*(G x)^2+4*(H x)^2) := by
    unfold surfaceIntegral
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    exact integral_mono hl.restrict hr.restrict (fun x=>by
      nlinarith [sq_nonneg (F x-(G x-H x)),sq_nonneg (G x+H x)])
  have hfg : Integrable (fun x=>2*(F x)^2+4*(G x)^2)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) :=
    ((squared_integrable hF).const_mul 2).add ((squared_integrable hG).const_mul 4)
  rwa [surfaceIntegral_add B h i j _ _ hfg ((squared_integrable hH).const_mul 4),
    surfaceIntegral_add B h i j _ _ ((squared_integrable hF).const_mul 2)
      ((squared_integrable hG).const_mul 4),surfaceIntegral_const_mul,
    surfaceIntegral_const_mul,surfaceIntegral_const_mul] at hh

/-- Whole row-wise surface square energy equals the intrinsic weighted energy,
with the zero diagonal handled explicitly. -/
theorem surface_row_square_eq_weighted (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hinj : Function.Injective B) (F : ι→FSC.Coord d→ℝ) (hF : ∀ i,Continuous (F i)) :
    (∑ i,∑ j,surfaceIntegral B h i j (fun x=>(F i x)^2))=affineWeightedFacetEnergy B h F := by
  have he : (∑ i,∑ j,surfaceIntegral B h i j (fun x=>(F i x)^2))=
      ∑ i,∑ j∈Finset.univ.erase i,surfaceIntegral B h i j (fun x=>(F i x)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro j _ hj
    have hji : j=i := by simpa using hj
    rw [hji,surfaceIntegral_diagonal]
  rw [he]
  exact orderedFacetEnergy_eq_ambient B h hinj (fun i _=>F i) (fun i _=>hF i)

/-- Reference/remainder split BEFORE applying any operator-norm bound. -/
theorem quadraticJumpEnergy_le_reference (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (hinj : Function.Injective B) :
    quadraticJumpEnergy B h ≤ 2*referenceJumpEnergy B R h r+
      4*affineWeightedFacetEnergy B h (fun i x=>quadraticLabelTest B h i x-quadraticLabelTest R r i x) := by
  let F := fun i x=>quadraticLabelTest B h i x-quadraticLabelTest R r i x
  have hp (i j : ι) : surfaceIntegral B h i j
      (fun x=>(quadraticLabelTest B h i x-quadraticLabelTest B h j x)^2) ≤
      2*surfaceIntegral B h i j (fun x=>(quadraticLabelTest R r i x-quadraticLabelTest R r j x)^2)+
      4*surfaceIntegral B h i j (fun x=>(F i x)^2)+
      4*surfaceIntegral B h i j (fun x=>(F j x)^2) := by
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
    have hh := surface_three_squares B h i j
      (fun x=>quadraticLabelTest R r i x-quadraticLabelTest R r j x) (F i) (F j)
      ((quadraticLabelTest_memLp R r i μ).sub (quadraticLabelTest_memLp R r j μ))
      ((quadraticLabelTest_memLp B h i μ).sub (quadraticLabelTest_memLp R r i μ))
      ((quadraticLabelTest_memLp B h j μ).sub (quadraticLabelTest_memLp R r j μ))
    have he : (fun x=>(quadraticLabelTest R r i x-quadraticLabelTest R r j x+F i x-F j x)^2)=
        (fun x=>(quadraticLabelTest B h i x-quadraticLabelTest B h j x)^2) := by
      funext x
      dsimp only [F]
      ring
    rwa [he] at hh
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun i _=>Finset.sum_le_sum (s:=Finset.univ) fun j _=>hp i j
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hrev : (∑ i,∑ j,surfaceIntegral B h i j (fun x=>(F j x)^2))=
      ∑ i,∑ j,surfaceIntegral B h i j (fun x=>(F i x)^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact surfaceIntegral_reverse B h i j _
  rw [hrev,surface_row_square_eq_weighted B h hinj F
    (fun i=>(quadraticLabelTest_continuous B h i).sub (quadraticLabelTest_continuous R r i))] at hh
  unfold quadraticJumpEnergy referenceJumpEnergy
  dsimp only [F] at hh
  linarith

/-- The literal operator difference equals the difference of the actual tests. -/
theorem quadraticScore_momentDifference (B R : ι→FSC.Coord d) (h r : ι→ℝ) (i : ι) :
    quadraticScore (momentOperator B h i-momentOperator R r i)=
      fun x=>quadraticLabelTest B h i x-quadraticLabelTest R r i x := by
  funext x
  have he (j k : Fin d) : operatorEntries (momentOperator B h i-momentOperator R r i) j k=
      secondMomentTensor B h i j k-secondMomentTensor R r i j k := by
    change operatorEntries (momentOperator B h i) j k-operatorEntries (momentOperator R r i) j k=_
    rw [momentOperator_entries,momentOperator_entries]
  change inner ℝ x ((momentOperator B h i-momentOperator R r i) x)-
    LinearMap.trace ℝ (FSC.Coord d) (momentOperator B h i-momentOperator R r i).toLinearMap=_
  rw [quadratic_score_eq_entries]
  simp only [he,sub_mul,Finset.sum_sub_distrib,quadraticLabelTest,tensorTest]

theorem momentDifference_HS_sum (B R : ι→FSC.Coord d) (h r : ι→ℝ) :
    (∑ i,(operatorHilbertSchmidt (momentOperator B h i-momentOperator R r i))^2)=
      momentDifferenceEnergy B R h r := by
  unfold operatorHilbertSchmidt
  simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>sq_nonneg _)]
  unfold momentDifferenceEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change operatorEntries (momentOperator B h i) j k-operatorEntries (momentOperator R r i) j k=_
  rw [momentOperator_entries,momentOperator_entries]

/-- The remainder loses only the actual weighted degree and a fixed log power.
The reference jump stays on current facets for the regular cancellation. -/
theorem quadraticJumpEnergy_reference_log_le (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree) (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j) ≤ degree) :
    quadraticJumpEnergy B h ≤ 2*referenceJumpEnergy B R h r+
      8*degree*quarticLogConstant a*(1+Real.log m)^4*momentDifferenceEnergy B R h r := by
  have hh := quadraticJumpEnergy_le_reference B R h r hinj
  have hb := affineWeightedFacetEnergy_quadraticScore_le B h
    (fun i=>momentOperator B h i-momentOperator R r i) a m degree hm hdegree0 hinj hprob ha hdegree
  simp only [quadraticScore_momentDifference,momentDifference_HS_sum] at hb
  nlinarith



/-- The actual mass adjoint is controlled by the reference's current-facet
jump and the actual finite tensor difference, divided only by the actual
centered graph gap. -/
theorem massAdjoint_norm_sq_reference_log_le (B R : ι→FSC.Coord d) (h r : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (gap : ℝ) (hgap : 0<gap)
    (hlaplacian : ∀ v:ι→ℝ,(∑ i,v i)=0 →
      gap*(∑ i,(v i)^2) ≤ v ⬝ᵥ (offsetJacobian B h *ᵥ v))
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j) ≤ degree) :
    (∑ i,(massAdjoint B h i)^2) ≤
      (2*referenceJumpEnergy B R h r+
        8*degree*quarticLogConstant a*(1+Real.log m)^4*momentDifferenceEnergy B R h r)/gap := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  exact (massAdjoint_norm_sq_le B h σ hσ hlower gap hgap hlaplacian).trans
    (div_le_div_of_nonneg_right
      (quadraticJumpEnergy_reference_log_le B R h r a m degree hm hdegree0 hinj hprob ha hdegree) hgap.le)

end NegativeVotingReferenceJumpComparison
