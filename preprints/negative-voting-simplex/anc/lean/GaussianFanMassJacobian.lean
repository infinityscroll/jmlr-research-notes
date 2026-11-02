import GaussianFanMassExistence
import GaussianFacetDegree

/-! The actual offset derivative of Gaussian winning-cell masses.
The coefficients are intrinsic Gaussian facet weights, not an assumed Hessian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped RealInnerProductSpace BigOperators Classical

namespace NegativeVotingFanJacobian
open NegativeVotingFan NegativeVotingFacetDegree NegativeVotingWeightedFacet
  NegativeVotingCapTail NegativeVotingDisintegration
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def facetWeight (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι) : ℝ :=
  gaussianPDFReal 0 1 (pairOffset B h i j) / ‖B i - B j‖ *
    (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem facetWeight_nonneg (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι) :
    0 ≤ facetWeight B h i j := by
  unfold facetWeight
  exact mul_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)) ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] theorem facetWeight_self (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    facetWeight B h i i = 0 := by simp [facetWeight]

def supportMap (B : ι → FSC.Coord d) (i : ι) :
    (ι → ℝ) →L[ℝ] ({j : ι // j ≠ i} → ℝ) :=
  ContinuousLinearMap.pi (fun j => ‖B j.1 - B i‖⁻¹ •
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j.1))

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] theorem supportMap_apply (B : ι → FSC.Coord d) (i : ι) (h : ι → ℝ) :
    supportMap B i h = cellSupports B h i := by
  ext j
  simp [supportMap, cellSupports, pairOffset, div_eq_mul_inv, mul_comm]

def massDerivative (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    (ι → ℝ) →L[ℝ] ℝ :=
  (FSC.supportGradient (cellNormals B i) (cellSupports B h i)).comp (supportMap B i)

theorem mass_eq_capMass (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι) :
    mass B h i = FSC.capMass (cellNormals B i) (cellSupports B h i) := by
  have hinj : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  rw [mass_eq_winningCell B hinj h i]
  unfold FSC.capMass
  rw [affine_cap_eq_cell B h σ hσ hlower i]
  rfl

/-- Actual Frechet derivative from the Gaussian cap derivative and the linear
map from offsets to thresholds. Noncoincidence is derived from singularity. -/
theorem hasFDerivAt_mass (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι) :
    HasFDerivAt (fun h' => mass B h' i) (massDerivative B h i) h := by
  have hc := FSC.hasFDerivAt_capMass (cellNormals B i)
    (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
    (cellNormals_noCoincident B h σ hσ hlower i)
  rw [← supportMap_apply B i h] at hc
  have hd := hc.comp h (supportMap B i).hasFDerivAt
  simpa only [supportMap_apply, Function.comp_def, ← mass_eq_capMass B σ hσ hlower,
    massDerivative] using hd

/-- The derivative coefficients have exactly the intrinsic normalization
already used by the weighted facet energy and degree estimates. -/
theorem massDerivative_apply (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h v : ι → ℝ) (i : ι) :
    massDerivative B h i v = ∑ j, facetWeight B h i j * (v i - v j) := by
  have he : massDerivative B h i v =
      ∑ j : {j : ι // j ≠ i},
        (capSurfaceWeight (cellNormals B i) (cellSupports B h i) j / cellEdges B i j) *
          (v i - v j.1) := by
    simp [massDerivative, FSC.supportGradient, supportMap, capSurfaceWeight, cellEdges,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [he]
  simp_rw [cell_degree_summand_eq_intrinsic B h σ hσ hlower i]
  change (∑ j : {j : ι // j ≠ i}, facetWeight B h i j.1 * (v i - v j.1)) = _
  rw [← Finset.sum_subtype (p := fun j : ι => j ≠ i) (Finset.univ.erase i)
    (fun j => by simp) (fun j => facetWeight B h i j * (v i - v j))]
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro j _ hj
  have hji : j = i := by simpa using hj
  simp [hji]

/-- The whole actual mass vector has this derivative. -/
theorem hasFDerivAt_mass_vector (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) :
    HasFDerivAt (mass B) (ContinuousLinearMap.pi (massDerivative B h)) h := by
  exact hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mass B σ hσ hlower h i)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The conditional slice law and intrinsic facet probability are identical. -/
theorem facetWeight_eq_ambient (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι)
    (hij : B i ≠ B j) :
    facetWeight B h i j = gaussianPDFReal 0 1 (pairOffset B h i j) / ‖B i - B j‖ *
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal := by
  have hlaw : FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) =
      (stdGaussian (tangentSpace (pairNormal B i j))).map (facetChart B h i j) := by
    unfold FSC.sliceLaw
    rw [gaussian_affine_slice_map _ (pairNormal_norm B i j hij)]
    congr 1
    funext y
    exact add_comm _ _
  rw [hlaw, Measure.map_apply (by unfold facetChart; fun_prop)
    (isClosed_affineFacet B h i j).measurableSet]
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem affineFacet_reverse (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι) :
    affineFacet B h j i = affineFacet B h i j := by
  ext x
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨he.symm, fun k => (hc k).trans_eq he⟩
  · rintro ⟨he, hc⟩
    exact ⟨he.symm, fun k => (hc k).trans_eq he⟩

/-- Both orientations use the same Gaussian surface measure and edge length. -/
theorem facetWeight_symm (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι) :
    facetWeight B h i j = facetWeight B h j i := by
  by_cases hij : B i = B j
  · simp [facetWeight, hij]
  rw [facetWeight_eq_ambient B h i j hij, facetWeight_eq_ambient B h j i (Ne.symm hij),
    pairNormal_reverse B i j, pairOffset_reverse B h i j, norm_sub_rev (B j) (B i),
    affineFacet_reverse]
  have hp : gaussianPDFReal 0 1 (-pairOffset B h i j) = gaussianPDFReal 0 1 (pairOffset B h i j) :=
    NegativeVotingMassCentroid.normalPDF_even _
  rw [hp]
  simp only [FSC.sliceLaw, neg_smul, smul_neg, neg_neg, inner_neg_left]

/-- The literal matrix of the offset-mass derivative. -/
def offsetJacobian (B : ι → FSC.Coord d) (h : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => ∑ j, facetWeight B h i j) - Matrix.of (fun i j => facetWeight B h i j)

omit [Nonempty ι] in
theorem offsetJacobian_mulVec (B : ι → FSC.Coord d) (h v : ι → ℝ) (i : ι) :
    (offsetJacobian B h *ᵥ v) i = ∑ j, facetWeight B h i j * (v i - v j) := by
  unfold offsetJacobian
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  change (∑ j, facetWeight B h i j) * v i - (∑ j, facetWeight B h i j * v j) = _
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem massDerivative_eq_offsetJacobian (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h v : ι → ℝ) (i : ι) :
    massDerivative B h i v = (offsetJacobian B h *ᵥ v) i := by
  rw [massDerivative_apply B σ hσ hlower, offsetJacobian_mulVec]

theorem offsetJacobian_isHermitian (B : ι → FSC.Coord d) (h : ι → ℝ) :
    (offsetJacobian B h).IsHermitian := by
  unfold offsetJacobian
  apply Matrix.IsHermitian.sub
  · exact Matrix.isHermitian_diagonal_iff.mpr (fun _ => IsSelfAdjoint.all _)
  · ext i j
    simpa using facetWeight_symm B h j i

omit [DecidableEq ι] [Nonempty ι] in
/-- Exact energy identity with the ordered-pair factor 1/2. -/
theorem symmetric_laplacian_energy (a : ι → ι → ℝ) (ha : ∀ i j, a i j = a j i)
    (v : ι → ℝ) :
    (∑ i, v i * (∑ j, a i j * (v i - v j))) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, a i j * (v i - v j) ^ 2 := by
  have hs : (∑ i, ∑ j, a i j * v j * (v i - v j)) =
      -(∑ i, ∑ j, a i j * v i * (v i - v j)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
    ring
  have he : (∑ i, ∑ j, a i j * (v i - v j) ^ 2) =
      (∑ i, ∑ j, a i j * v i * (v i - v j)) -
        (∑ i, ∑ j, a i j * v j * (v i - v j)) := by
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs] at he
  have hq : (∑ i, v i * (∑ j, a i j * (v i - v j))) =
      ∑ i, ∑ j, a i j * v i * (v i - v j) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq]
  linarith

theorem offsetJacobian_energy (B : ι → FSC.Coord d) (h v : ι → ℝ) :
    v ⬝ᵥ (offsetJacobian B h *ᵥ v) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, facetWeight B h i j * (v i - v j) ^ 2 := by
  simp only [dotProduct, offsetJacobian_mulVec]
  exact symmetric_laplacian_energy (facetWeight B h) (facetWeight_symm B h) v

/-- Positivity is a consequence of actual nonnegative facet probabilities. -/
theorem offsetJacobian_posSemidef (B : ι → FSC.Coord d) (h : ι → ℝ) :
    (offsetJacobian B h).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (offsetJacobian_isHermitian B h)
  intro v
  change 0 ≤ v ⬝ᵥ (offsetJacobian B h *ᵥ v)
  rw [offsetJacobian_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (facetWeight_nonneg B h i j) (sq_nonneg _))

/-- Offset translation is exactly the constant-vector kernel direction. -/
theorem offsetJacobian_constant (B : ι → FSC.Coord d) (h : ι → ℝ) (c : ℝ) :
    offsetJacobian B h *ᵥ (fun _ => c) = 0 := by
  ext i
  simp [offsetJacobian_mulVec]

omit [DecidableEq ι] [Nonempty ι] in
/-- The quantitative singular bound implies genuine affine independence. -/
theorem affineIndependent_of_centered_lower (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) : AffineIndependent ℝ B := by
  rw [affineIndependent_iff_of_fintype]
  intro c hc hz i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hc] at hz
  have hh := hlower c hc
  rw [hz, norm_zero, zero_pow (by decide)] at hh
  have hs : (∑ j, c j ^ 2) ≤ 0 := by
    by_contra hnot
    exact (not_lt_of_ge hh) (mul_pos (sq_pos_of_pos hσ) (lt_of_not_ge hnot))
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => sq_nonneg (c j))
    (Finset.mem_univ i)
  nlinarith [sq_nonneg (c i)]

/-- Finite independent sites can be assigned arbitrary linear score values.
The functional is extended algebraically and then represented by an actual vector. -/
theorem exists_inner_values {κ : Type*} (w : κ → FSC.Coord d)
    (hw : LinearIndependent ℝ w) (t : κ → ℝ) :
    ∃ x : FSC.Coord d, ∀ j, inner ℝ (w j) x = t j := by
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination ℝ w).exists_leftInverse_of_injective
    (linearIndependent_iff_ker.mp hw)
  let ell : FSC.Coord d →ₗ[ℝ] ℝ := (Finsupp.linearCombination ℝ t).comp g
  refine ⟨(InnerProductSpace.toDual ℝ (FSC.Coord d)).symm ell.toContinuousLinearMap, ?_⟩
  intro j
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hj := LinearMap.congr_fun hg (Finsupp.single j (1 : ℝ))
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.id_apply] at hj
  change (Finsupp.linearCombination ℝ t) (g (w j)) = t j
  rw [hj, Finsupp.linearCombination_single, one_smul]

omit [Fintype ι] [Nonempty ι] in
/-- Every edge of an affinely independent family has an actual strictly winning
pair point, for arbitrary offsets. No positive-face premise is supplied. -/
theorem exists_strict_pair_point (B : ι → FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    ∃ x : FSC.Coord d, affineScore B h i x = affineScore B h j x ∧
      ∀ k, k ≠ i → k ≠ j → affineScore B h k x < affineScore B h i x := by
  have hind : LinearIndependent ℝ (fun k : {k : ι // k ≠ i} => B k.1 - B i) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ B i).mp hB
  obtain ⟨x, hx⟩ := exists_inner_values _ hind
    (fun k => (if k.1 = j then (0 : ℝ) else -1) - h k.1 + h i)
  refine ⟨x, ?_, ?_⟩
  · have he := hx ⟨j, hij.symm⟩
    simp [inner_sub_left] at he
    unfold affineScore
    linarith
  · intro k hki hkj
    have he := hx ⟨k, hki⟩
    simp [hkj, inner_sub_left] at he
    unfold affineScore
    linarith

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Pair-score equality is exactly the normalized affine comparison plane. -/
theorem pair_plane_iff (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι)
    (hij : B i ≠ B j) (x : FSC.Coord d) :
    inner ℝ (pairNormal B i j) x = pairOffset B h i j ↔
      affineScore B h i x = affineScore B h j x := by
  have hn : ‖B i - B j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  simp only [pairNormal, real_inner_smul_left, inner_sub_left, pairOffset, affineScore]
  rw [← div_eq_inv_mul, div_left_inj' hn]
  constructor <;> intro he <;> linarith

/-- A genuine strict pair point gives positive actual Gaussian face measure. -/
theorem facetWeight_pos_of_strict_point (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι)
    (hij : B i ≠ B j) (x₀ : FSC.Coord d)
    (hplane : affineScore B h i x₀ = affineScore B h j x₀)
    (hstrict : ∀ k, k ≠ i → k ≠ j → affineScore B h k x₀ < affineScore B h i x₀) :
    0 < facetWeight B h i j := by
  let n := pairNormal B i j
  let a := pairOffset B h i j
  let P : FSC.Coord d → FSC.Coord d := fun x => a • n + (x - inner ℝ n x • n)
  have hn : ‖n‖ = 1 := pairNormal_norm B i j hij
  have hlin : Continuous (fun x : FSC.Coord d => inner ℝ n x) := by fun_prop
  have hPC : Continuous P := continuous_const.add
    (continuous_id.sub (hlin.smul continuous_const))
  have hPplane (x : FSC.Coord d) : inner ℝ n (P x) = a := by
    simp only [P, inner_add_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have hPscore (x : FSC.Coord d) : affineScore B h i (P x) = affineScore B h j (P x) :=
    (pair_plane_iff B h i j hij (P x)).mp (hPplane x)
  have hPfix : P x₀ = x₀ := by
    have hh := (pair_plane_iff B h i j hij x₀).mpr hplane
    change a • n + (x₀ - inner ℝ n x₀ • n) = x₀
    rw [hh]
    abel
  let U : Set (FSC.Coord d) := {x | ∀ k : {k : ι // k ≠ i ∧ k ≠ j},
    affineScore B h k.1 (P x) < affineScore B h i (P x)}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_lt
    · exact (continuous_const.inner hPC).add continuous_const
    · exact (continuous_const.inner hPC).add continuous_const
  have hmem : x₀ ∈ U := by
    intro k
    rw [hPfix]
    exact hstrict k.1 k.property.1 k.property.2
  have hsub : U ⊆ P ⁻¹' affineFacet B h i j := by
    intro x hx
    refine ⟨hPscore x, ?_⟩
    intro k
    by_cases hki : k = i
    · subst k
      exact le_rfl
    · by_cases hkj : k = j
      · subst k
        exact (hPscore x).ge
      · exact (hx ⟨k, hki, hkj⟩).le
  have hpos : 0 < FSC.sliceLaw n a (affineFacet B h i j) := by
    change 0 < ((stdGaussian (FSC.Coord d)).map P) (affineFacet B h i j)
    rw [Measure.map_apply hPC.measurable (isClosed_affineFacet B h i j).measurableSet]
    exact (FSC.stdGaussian_pos_of_isOpen hU ⟨x₀, hmem⟩).trans_le (measure_mono hsub)
  have hfinite : FSC.sliceLaw n a (affineFacet B h i j) ≠ ⊤ := by
    have : IsFiniteMeasure (FSC.sliceLaw n a) := by
      unfold FSC.sliceLaw
      infer_instance
    exact measure_ne_top _ _
  rw [facetWeight_eq_ambient B h i j hij]
  exact mul_pos (div_pos (gaussianPDFReal_pos _ _ _ (by norm_num))
    (norm_pos_iff.mpr (sub_ne_zero.mpr hij))) (ENNReal.toReal_pos hpos.ne' hfinite)

/-- Affine independence proves positive weights for every distinct pair and
for every offset vector. This is stronger than a connectivity assumption. -/
theorem facetWeight_pos_of_affineIndependent (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    0 < facetWeight B h i j := by
  obtain ⟨x, hx, hs⟩ := exists_strict_pair_point B hB h i j hij
  exact facetWeight_pos_of_strict_point B h i j (fun he => hij (hB.injective he)) x hx hs

/-- Positive actual pair facets make the nullspace exactly the constants. -/
theorem offsetJacobian_energy_zero_iff (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h v : ι → ℝ) :
    v ⬝ᵥ (offsetJacobian B h *ᵥ v) = 0 ↔ ∃ c : ℝ, ∀ i, v i = c := by
  constructor
  · intro hz
    rw [offsetJacobian_energy] at hz
    have hs : (∑ i, ∑ j, facetWeight B h i j * (v i - v j) ^ 2) = 0 := by linarith
    have hn (i j : ι) : 0 ≤ facetWeight B h i j * (v i - v j) ^ 2 :=
      mul_nonneg (facetWeight_nonneg B h i j) (sq_nonneg _)
    have hrows (i : ι) : (∑ j, facetWeight B h i j * (v i - v j) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => hn k j))).mp
        hs i (Finset.mem_univ i)
    let i₀ : ι := Classical.choice inferInstance
    refine ⟨v i₀, fun i => ?_⟩
    by_cases hi : i = i₀
    · rw [hi]
    · have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp
        (hrows i) i₀ (Finset.mem_univ i₀)
      have hd : (v i - v i₀) ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_left
        (facetWeight_pos_of_affineIndependent B hB h i i₀ hi).ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hd)
  · rintro ⟨c, hc⟩
    have hv : v = fun _ => c := funext hc
    rw [hv, offsetJacobian_constant]
    simp

theorem offsetJacobian_kernel_iff (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h v : ι → ℝ) :
    offsetJacobian B h *ᵥ v = 0 ↔ ∃ c : ℝ, ∀ i, v i = c := by
  have he : v ⬝ᵥ (offsetJacobian B h *ᵥ v) = 0 ↔ offsetJacobian B h *ᵥ v = 0 := by
    simpa using (offsetJacobian_posSemidef B h).dotProduct_mulVec_zero_iff (x := v)
  exact he.symm.trans (offsetJacobian_energy_zero_iff B hB h v)

/-- The actual offset-mass Jacobian is strictly positive on the centered gauge.
No connectivity or positive-face hypothesis remains. -/
theorem offsetJacobian_pos_centered (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h v : ι → ℝ) (hv : ∑ i, v i = 0) (hv0 : v ≠ 0) :
    0 < v ⬝ᵥ (offsetJacobian B h *ᵥ v) := by
  have hn : 0 ≤ v ⬝ᵥ (offsetJacobian B h *ᵥ v) := by
    simpa using (offsetJacobian_posSemidef B h).dotProduct_mulVec_nonneg v
  apply lt_of_le_of_ne hn
  intro hz
  obtain ⟨c, hc⟩ := (offsetJacobian_energy_zero_iff B hB h v).mp hz.symm
  have hsum : (Fintype.card ι : ℝ) * c = 0 := by
    simpa only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hv
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc0 : c = 0 := (mul_eq_zero.mp hsum).resolve_left hcard
  apply hv0
  ext i
  exact (hc i).trans hc0

/-- The same strict positivity uses the manuscript's quantitative singular hypothesis. -/
theorem offsetJacobian_pos_centered_of_lower (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h v : ι → ℝ)
    (hv : ∑ i, v i = 0) (hv0 : v ≠ 0) :
    0 < v ⬝ᵥ (offsetJacobian B h *ᵥ v) :=
  offsetJacobian_pos_centered B (affineIndependent_of_centered_lower B σ hσ hlower) h v hv hv0

/-- The actual mass map is C1 in all offsets for these fixed sites. -/
theorem contDiff_mass_vector (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) : ContDiff ℝ 1 (mass B) := by
  rw [contDiff_iff_contDiffAt]
  intro h
  apply contDiffAt_pi.mpr
  intro i
  have hc := FSC.contDiffAt_one_capMass (cellNormals B i)
    (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
    (cellNormals_noCoincident B h σ hσ hlower i)
  rw [← supportMap_apply B i h] at hc
  have he := hc.comp h (supportMap B i).contDiff.contDiffAt
  simpa only [supportMap_apply, Function.comp_def, ← mass_eq_capMass B σ hσ hlower] using he

end NegativeVotingFanJacobian
