import GaussianMovingCap
import GaussianFanTestedCells

/-! Actual joint row/offset differentiation of tested Gaussian fan cells.
All normalization lengths are fixed at the base point, so the parameter map
is linear and the represented cell is exact for every varying parameter. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators

namespace NegativeVotingFanMovingCells
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFacetDegree
open NegativeVotingCapTail NegativeVotingMovingCap NegativeVotingDisintegration NegativeVotingWeightedFacet
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Fixed-base normalization of all comparison inequalities for cell i. -/
def fanParameterMap (B : ι → FSC.Coord d) (i : ι) :
    Parameters d ι →L[ℝ] Parameters d {j : ι // j ≠ i} :=
  (ContinuousLinearMap.pi (fun j : {j : ι // j ≠ i} =>
    ‖B j.1 - B i‖⁻¹ •
      (((ContinuousLinearMap.proj j.1 : (ι → FSC.Coord d) →L[ℝ] FSC.Coord d) -
        ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ))))).prod
  (ContinuousLinearMap.pi (fun j : {j : ι // j ≠ i} =>
    ‖B j.1 - B i‖⁻¹ •
      (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) -
        ContinuousLinearMap.proj j.1).comp
        (ContinuousLinearMap.snd ℝ (ι → FSC.Coord d) (ι → ℝ)))))

@[simp] theorem fanParameterMap_normal (B : ι → FSC.Coord d) (i : ι)
    (p : Parameters d ι) (j : {j : ι // j ≠ i}) :
    (fanParameterMap B i p).1 j = ‖B j.1 - B i‖⁻¹ • (p.1 j.1 - p.1 i) := rfl

@[simp] theorem fanParameterMap_support (B : ι → FSC.Coord d) (i : ι)
    (p : Parameters d ι) (j : {j : ι // j ≠ i}) :
    (fanParameterMap B i p).2 j = (p.2 i - p.2 j.1) / ‖B j.1 - B i‖ := by
  change ‖B j.1 - B i‖⁻¹ * (p.2 i - p.2 j.1) = _
  rw [div_eq_mul_inv, mul_comm]

@[simp] theorem fanParameterMap_base (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    fanParameterMap B i (B,h) = (cellNormals B i, cellSupports B h i) := by
  apply Prod.ext
  · ext j
    rfl
  · ext j
    exact fanParameterMap_support B i (B,h) j

/-- The represented halfspace equals the literal score comparison for every
varying row/offset parameter, not just in a neighborhood of the base. -/
theorem normalized_halfspace_iff_score (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (i : ι) (p : Parameters d ι) (j : {j : ι // j ≠ i}) (x : FSC.Coord d) :
    inner ℝ ((fanParameterMap B i p).1 j) x ≤ (fanParameterMap B i p).2 j ↔
      scores p.1 p.2 x j.1 ≤ scores p.1 p.2 x i := by
  have hn : 0 < ‖B j.1 - B i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hB.ne j.property))
  rw [fanParameterMap_normal, fanParameterMap_support, real_inner_smul_left]
  rw [show ‖B j.1-B i‖⁻¹ * inner ℝ (p.1 j.1-p.1 i) x =
      inner ℝ (p.1 j.1-p.1 i) x / ‖B j.1-B i‖ by rw [div_eq_mul_inv, mul_comm]]
  rw [div_le_div_iff_of_pos_right hn]
  simp only [inner_sub_left, scores]
  constructor <;> intro hh <;> linarith

/-- Exact cap/cell identity for the fixed-base parameter map. -/
theorem normalized_cap_eq_winningCell (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (i : ι) (p : Parameters d ι) :
    FSC.cap (fanParameterMap B i p).1 (fanParameterMap B i p).2 = winningCell p.1 p.2 i := by
  ext x
  constructor
  · intro hx j
    by_cases hji : j = i
    · subst j
      exact le_rfl
    · exact (normalized_halfspace_iff_score B hB i p ⟨j,hji⟩ x).mp (hx ⟨j,hji⟩)
  · intro hx j
    exact (normalized_halfspace_iff_score B hB i p j x).mpr (hx j.1)

/-- The concrete cap derivative composed with the fixed-base fan map. -/
def testedCellDerivative (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (F : FSC.Coord d → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  (capJointDerivative (cellNormals B i) (cellSupports B h i) F).comp (fanParameterMap B i)

/-- Actual Frechet derivative of a literal tested Gaussian winning cell.
Unit normals and noncoincidence are derived from the positive centered
singular bound; no boundary derivative identity is an assumption. -/
theorem hasFDerivAt_testedCell (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖)) :
    HasFDerivAt (fun p : Parameters d ι =>
      ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i F) (B,h) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hd := hasFDerivAt_capTest (cellNormals B i)
    (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
    (cellNormals_noCoincident B h σ hσ hlower i) F hFc C hC hF
  rw [← fanParameterMap_base B h i] at hd
  have hh := hd.comp (B,h) (fanParameterMap B i).hasFDerivAt
  have he : (fun p : Parameters d ι => capTest (fanParameterMap B i p) F) =
      (fun p : Parameters d ι =>
        ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d)) := by
    funext p
    unfold capTest
    rw [normalized_cap_eq_winningCell B hB]
  change HasFDerivAt (fun p => capTest (fanParameterMap B i p) F)
    (testedCellDerivative B h i F) (B,h) at hh
  rw [he] at hh
  exact hh

/-- Actual point on the outward pair plane, in the tangent Gaussian chart. -/
def outwardFacetPoint (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (j : {j : ι // j ≠ i}) (y : tangentSpace (cellNormals B i j)) : FSC.Coord d :=
  (y : FSC.Coord d) + cellSupports B h i j • cellNormals B i j

/-- Evaluated derivative: actual Gaussian face integral and actual normal
velocity, with the edge-length denominator explicit. -/
theorem testedCellDerivative_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, WeakSimplex.normalPDF (cellSupports B h i j) / ‖B j.1-B i‖ *
        ∫ y in tangentFace (cellNormals B i) (cellSupports B h i) j,
          F (outwardFacetPoint B h i j y) *
            (inner ℝ (δ.1 i-δ.1 j.1) (outwardFacetPoint B h i j y) + δ.2 i-δ.2 j.1)
          ∂stdGaussian (tangentSpace (cellNormals B i j)) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i) F (fanParameterMap B i δ) = _
  rw [capJointDerivative_apply _ (cellNormals_unit B σ hσ hlower i) _ F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  have he (x : FSC.Coord d) :
      F x * ((fanParameterMap B i δ).2 j - inner ℝ ((fanParameterMap B i δ).1 j) x) =
        (F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)) / ‖B j.1-B i‖ := by
    rw [fanParameterMap_support, fanParameterMap_normal, real_inner_smul_left]
    simp only [inner_sub_left, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [integral_div]
  unfold outwardFacetPoint
  ring

/-- The fixed outward chart pushes the tangent Gaussian to the actual
ambient conditional Gaussian on the pair plane. -/
theorem outward_sliceLaw_eq_map (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hB : Function.Injective B) (i : ι) (j : {j : ι // j ≠ i}) :
    FSC.sliceLaw (cellNormals B i j) (cellSupports B h i j) =
      (stdGaussian (tangentSpace (cellNormals B i j))).map (outwardFacetPoint B h i j) := by
  have hn : ‖cellNormals B i j‖ = 1 := pairNormal_norm B j.1 i (hB.ne j.property)
  unfold FSC.sliceLaw
  rw [gaussian_affine_slice_map _ hn]
  congr 1
  funext y
  exact add_comm _ _

/-- The remaining cap inequalities on the pair plane are exactly the
literal winning facet, with its outward orientation. -/
theorem outwardFacetPoint_preimage_facet (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hB : Function.Injective B) (i : ι) (j : {j : ι // j ≠ i}) :
    (outwardFacetPoint B h i j) ⁻¹' affineFacet B h j.1 i =
      tangentFace (cellNormals B i) (cellSupports B h i) j := by
  ext y
  let x := outwardFacetPoint B h i j y
  have hp : affineScore B h j.1 x = affineScore B h i x :=
    facetChart_on_pair_plane B h j.1 i (hB.ne j.property) y
  change (affineScore B h j.1 x = affineScore B h i x ∧
      ∀ k, affineScore B h k x ≤ affineScore B h j.1 x) ↔
    ∀ k : {k : ι // k ≠ i}, k ≠ j →
      inner ℝ (cellNormals B i k) x ≤ cellSupports B h i k
  constructor
  · intro hx k hk
    exact (cell_halfspace_iff_score B h i k (hB.ne k.property) x).mpr
      ((hx.2 k.1).trans_eq hp)
  · intro hx
    refine ⟨hp, fun k => ?_⟩
    by_cases hki : k = i
    · subst k
      exact hp.ge
    · by_cases hkj : k = j.1
      · subst k
        exact le_rfl
      · have hk : (⟨k,hki⟩ : {k : ι // k ≠ i}) ≠ j :=
          fun he => hkj (congrArg Subtype.val he)
        exact ((cell_halfspace_iff_score B h i ⟨k,hki⟩ (hB.ne hki) x).mp
          (hx ⟨k,hki⟩ hk)).trans_eq hp.symm

/-- Exact integral transport to the ambient Gaussian pair-plane law.
The facet indicator and the slice measure are both identified explicitly. -/
theorem tangentFace_integral_eq_surface (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hB : Function.Injective B) (i : ι) (j : {j : ι // j ≠ i})
    (G : FSC.Coord d → ℝ) (hG : Continuous G) :
    (∫ y in tangentFace (cellNormals B i) (cellSupports B h i) j,
      G (outwardFacetPoint B h i j y) ∂stdGaussian (tangentSpace (cellNormals B i j))) =
    ∫ x in affineFacet B h j.1 i, G x
      ∂FSC.sliceLaw (pairNormal B j.1 i) (pairOffset B h j.1 i) := by
  change _ = ∫ x in affineFacet B h j.1 i, G x
    ∂FSC.sliceLaw (cellNormals B i j) (cellSupports B h i j)
  rw [outward_sliceLaw_eq_map B h hB i j,
    setIntegral_map (isClosed_affineFacet B h j.1 i).measurableSet
      hG.measurable.aestronglyMeasurable (by unfold outwardFacetPoint; fun_prop),
    outwardFacetPoint_preimage_facet B h hB i j]

/-- Ambient evaluated derivative: one Gaussian density and one edge-length
denominator, times the actual facet integral of the test and score-difference
velocity. This form can be paired with the opposite cell orientation. -/
theorem testedCellDerivative_apply_ambient (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, gaussianPDFReal 0 1 (pairOffset B h j.1 i) / ‖B j.1-B i‖ *
        ∫ x in affineFacet B h j.1 i,
          F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)
          ∂FSC.sliceLaw (pairNormal B j.1 i) (pairOffset B h j.1 i) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  rw [testedCellDerivative_apply B h σ hσ hlower i F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tangentFace_integral_eq_surface B h hB i j
    (fun x => F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1))
    (by fun_prop)]
  rfl

/-- The required growth bound for an arbitrary affine test is discharged. -/
theorem affine_test_growth (E : FSC.Coord d) (e : ℝ) (x : FSC.Coord d) :
    |inner ℝ E x + e| ≤ (‖E‖+|e|) * (1+‖x‖) := by
  calc
    _ ≤ |inner ℝ E x| + |e| := abs_add_le _ _
    _ ≤ ‖E‖ * ‖x‖ + |e| := add_le_add (abs_real_inner_le_norm E x) le_rfl
    _ ≤ _ := by nlinarith [norm_nonneg E, norm_nonneg x, abs_nonneg e]

/-- Actual affine-tested-cell Frechet derivative, ready for the expected
maximum Hessian assembly. -/
theorem hasFDerivAt_affine_testedCell (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (E : FSC.Coord d) (e : ℝ) :
    HasFDerivAt (fun p : Parameters d ι =>
      ∫ x in winningCell p.1 p.2 i, (inner ℝ E x + e) ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i (fun x => inner ℝ E x + e)) (B,h) :=
  hasFDerivAt_testedCell B h σ hσ hlower i _ (by fun_prop) (‖E‖+|e|)
    (by positivity) (affine_test_growth E e)

end NegativeVotingFanMovingCells
