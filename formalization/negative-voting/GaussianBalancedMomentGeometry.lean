import GaussianBalancedMomentComparison
import GaussianConditionedFacetLower

/-! Geometric inputs for the literal balanced moment comparison.  In
particular the canonical offset response is controlled by its variational
property, rather than by an inverse graph estimate. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical

namespace NegativeVotingBalancedMomentGeometry
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingFanCanonicalOffset NegativeVotingTensorFacetAggregation
  NegativeVotingWeightedFacet NegativeVotingDisintegration NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingFanJacobian NegativeVotingFanSelectedOffsets
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingBalancedMomentComparison
  NegativeVotingPolynomialFacetLogBound NegativeVotingFanQuadraticMoments

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The ordered intrinsic edge energy is exactly twice the actual expected-max
quadratic form. Both Gaussian density and edge-length normalization agree. -/
theorem edgeScoreEnergy_eq_twice_quadraticForm
    (B D : ι→FSC.Coord d) (h k : ι→ℝ) (hinj : Function.Injective B) :
    affineWeightedEdgeScoreEnergy B D h k = 2*quadraticForm B h D k := by
  have he := orderedFacetEnergy_eq_ambient B h hinj
    (fun i j x=>inner ℝ (D i-D j) x+(k i-k j)) (by intro i j; fun_prop)
  unfold affineWeightedEdgeScoreEnergy
  rw [← he]
  unfold orderedFacetEnergy quadraticForm
  have hs (i : ι) :
      (∑ j∈Finset.univ.erase i,
        gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
          ∫ x in affineFacet B h i j,(inner ℝ (D i-D j) x+(k i-k j))^2
            ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) =
      ∑ j,surfaceIntegral B h i j (fun x=>(affineScore D k i x-affineScore D k j x)^2) := by
    have hz : surfaceIntegral B h i i
        (fun x=>(affineScore D k i x-affineScore D k i x)^2)=0 :=
      surfaceIntegral_diagonal B h i _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hz,add_zero]
    apply Finset.sum_congr rfl
    intro j _
    unfold surfaceIntegral
    congr 2
    funext x
    simp only [affineScore,inner_sub_left]
    ring
  simp_rw [hs]
  ring

/-- The actual balanced edge energy never exceeds the zero-offset energy.
There is no norm assumption on the selected offset derivative. -/
theorem canonical_edgeScoreEnergy_le_zero
    (B D : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    affineWeightedEdgeScoreEnergy B D h (canonicalOffsetVariation B h D) ≤
      affineWeightedEdgeScoreEnergy B D h 0 := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  rw [edgeScoreEnergy_eq_twice_quadraticForm B D h _ hinj,
    edgeScoreEnergy_eq_twice_quadraticForm B D h _ hinj]
  exact mul_le_mul_of_nonneg_left (canonicalOffset_minimizes B D h σ hσ hlower 0)
    (by norm_num)

/-- Trace and weighted degree control the actual balanced response with no
inverse singular factor and no ambient dimension factor. -/
theorem canonical_edgeScoreEnergy_log_le
    (B D : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (a m degree : ℝ) (hm : 1 ≤ m)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) :
    affineWeightedEdgeScoreEnergy B D h (canonicalOffsetVariation B h D) ≤
      8*degree*quarticLogConstant a*(1+Real.log m)^4*∑ i,‖D i-v‖^2 := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  refine (canonical_edgeScoreEnergy_le_zero B D h σ hσ hlower).trans ?_
  simpa using
    affineWeightedEdgeScoreEnergy_log_le B D h 0 a m degree hm hinj hprob ha hdegree v 0

/-- Actual balanced cell masses give the normal-offset logarithmic estimate.
The result is independent of the norm of the selected offset vector. -/
theorem pairOffset_le_of_uniform_mass
    (B : ι→FSC.Coord d) (h : ι→ℝ) (hinj : Function.Injective B)
    (hmass : ∀ i,(Fintype.card ι : ℝ)⁻¹ ≤ mass B h i)
    (i j : ι) (hij : i≠j) :
    |pairOffset B h i j| ≤ 2*Real.sqrt (1+Real.log (Fintype.card ι : ℝ)) := by
  have hm : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hm1 : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg hm1
  have hq := NegativeVotingFanRetained.pairOffset_sq_le_log_mass B h hinj
    (Fintype.card ι : ℝ)⁻¹ (inv_pos.mpr hm) hmass i j hij
  simp only [one_div,inv_inv] at hq
  have hs := Real.sq_sqrt (show 0 ≤ 1+Real.log (Fintype.card ι : ℝ) by positivity)
  nlinarith [sq_abs (pairOffset B h i j),abs_nonneg (pairOffset B h i j),
    Real.sqrt_nonneg (1+Real.log (Fintype.card ι : ℝ))]

/-- Selected uniform masses are literal Gaussian winning-cell masses. -/
theorem selected_uniform_mass (B : ι→FSC.Coord d) (hinj : Function.Injective B) :
    mass B (selectedOffsets B (fun _=>(Fintype.card ι : ℝ)⁻¹)) =
      fun _=>(Fintype.card ι : ℝ)⁻¹ := by
  apply selectedOffsets_mass B hinj
  · intro i
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · simp [ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos : (0:ℝ)<Fintype.card ι)]

/-- A genuine finite moment bound for the selected balanced segment. All
offset and balanced edge-energy hypotheses have been discharged. The remaining
inputs are singular conditioning, actual facet probabilities and weighted degree. -/
theorem selected_uniform_moment_difference_sq_le
    (B D : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (B+t•D) σ)
    (degree : ℝ) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ t∈Ico (0:ℝ) 1,∀ i j,i≠j→(Fintype.card ι : ℝ)^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal (B+t•D) i j))
        (intrinsicFacet (B+t•D)
          (selectedRowOffsets B D (fun _=>(Fintype.card ι : ℝ)⁻¹) t) i j)).toReal)
    (hdegree : ∀ t∈Ico (0:ℝ) 1,∀ i,
      ∑ j∈Finset.univ.erase i,facetWeight (B+t•D)
        (selectedRowOffsets B D (fun _=>(Fintype.card ι : ℝ)⁻¹) t) i j ≤ degree)
    (v : FSC.Coord d) :
    (∑ i,∑ j,∑ k,
      (secondMomentTensor (B+D) (selectedOffsets (B+D) (fun _=>(Fintype.card ι : ℝ)⁻¹)) i j k-
       secondMomentTensor B (selectedOffsets B (fun _=>(Fintype.card ι : ℝ)⁻¹)) i j k)^2) ≤
      16*degree^2*(quarticLogConstant 2)^2*(1+Real.log (Fintype.card ι : ℝ))^8*
        ∑ i,‖D i-v‖^2 := by
  let m : ℝ := Fintype.card ι
  let p : ι→ℝ := fun _=>m⁻¹
  let R := 8*degree*quarticLogConstant 2*(1+Real.log m)^4*∑ i,‖D i-v‖^2
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have hm1 : 1 ≤ m := by
    dsimp only [m]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  have hp : ∀ i,0<p i := fun _=>inv_pos.mpr hm
  have hs : ∑ i,p i=1 := by simp [p,m,ne_of_gt hm]
  have hinj (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : Function.Injective (B+t•D) :=
    fun i j he=>by
      by_contra hij
      exact centered_singular_rows_ne _ σ hσ (hlower t ht) i j hij he
  have ha (t : ℝ) (ht : t∈Ico (0:ℝ) 1) (i j : ι) (hij : i≠j) :
      |pairOffset (B+t•D) (selectedRowOffsets B D p t) i j| ≤
        2*Real.sqrt (1+Real.log m) := by
    apply pairOffset_le_of_uniform_mass _ _ (hinj t ⟨ht.1,ht.2.le⟩) _ i j hij
    intro l
    have he := congrFun (selected_uniform_mass (B+t•D) (hinj t ⟨ht.1,ht.2.le⟩)) l
    exact he.ge
  have hedge (t : ℝ) (ht : t∈Ico (0:ℝ) 1) :
      affineWeightedEdgeScoreEnergy (B+t•D) D (selectedRowOffsets B D p t)
        (canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D) ≤ R := by
    apply canonical_edgeScoreEnergy_log_le _ D _ σ hσ (hlower t ⟨ht.1,ht.2.le⟩)
      2 m degree hm1 (hprob t ht) (ha t ht) _ v
    intro i
    have hz := facetWeight_self (B+t•D) (selectedRowOffsets B D p t) i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hz,add_zero]
    exact hdegree t ht i
  have hb := selected_moment_difference_sq_le B D σ hσ hlower p hp hs
    2 m degree R hm1 hdegree0 (by dsimp [R]; unfold quarticLogConstant; positivity)
    hprob ha hdegree hedge
  convert hb using 1 <;> dsimp only [R,m,p] <;> ring

end NegativeVotingBalancedMomentGeometry
