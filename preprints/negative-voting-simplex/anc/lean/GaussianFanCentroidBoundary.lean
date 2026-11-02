import GaussianFanTestedCells
import GaussianCapFirstMoment

/-! Actual cell centroids as Gaussian weighted boundary Laplacians. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators

namespace NegativeVotingFanCentroid
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanTestedCells
  NegativeVotingFacetDegree NegativeVotingFanJacobian NegativeVotingCapTail
  NegativeVotingWeightedFacet NegativeVotingPolyhedral

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The actual unnormalized cell centroid is the weighted graph Laplacian
of its score rows, with the literal already-checked Gaussian facet weights. -/
theorem centroid_eq_boundary_laplacian (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    centroid B h i = ∑ j, facetWeight B h i j • (B i-B j) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  rw [centroid_eq_cell_integral B hB h i]
  change (∫ x in affineCell B h i, x ∂stdGaussian (FSC.Coord d)) = _
  rw [← affine_cap_eq_cell B h σ hσ hlower i,
    gaussian_cap_vector_first_moment (cellNormals B i) (cellNormals_unit B σ hσ hlower i)
      (cellSupports B h i) (cellNormals_noCoincident B h σ hσ hlower i),
    ← Finset.sum_neg_distrib]
  have he (j : {j : ι // j ≠ i}) :
      -((WeakSimplex.normalPDF (cellSupports B h i j)*
        FSC.sliceMass (cellNormals B i) (cellSupports B h i) j) • cellNormals B i j) =
        facetWeight B h i j.1 • (B i-B j.1) := by
    have hc : capSurfaceWeight (cellNormals B i) (cellSupports B h i) j / cellEdges B i j =
        facetWeight B h i j.1 := cell_degree_summand_eq_intrinsic B h σ hσ hlower i j
    rw [← hc]
    simp only [cellNormals,pairNormal,cellEdges,capSurfaceWeight,smul_smul,div_eq_mul_inv]
    module
  simp_rw [he]
  rw [← Finset.sum_subtype (p := fun j : ι => j≠i) (Finset.univ.erase i)
    (fun j => by simp) (fun j => facetWeight B h i j • (B i-B j))]
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro j _ hj
  have hji : j=i := by simpa using hj
  simp [hji]

/-- Finite weighted summation by parts, without positivity or an operator
assumption on either vector family. -/
theorem weighted_edge_pairing (a : ι → ι → ℝ) (ha : ∀ i j, a i j=a j i)
    (U V : ι → FSC.Coord d) :
    (∑ i, inner ℝ (∑ j, a i j • (U i-U j)) (V i)) =
      (1/2:ℝ) * ∑ i, ∑ j, a i j * inner ℝ (U i-U j) (V i-V j) := by
  simp only [sum_inner,real_inner_smul_left]
  have hs : (∑ i, ∑ j, a i j * inner ℝ (U i-U j) (V j)) =
      -(∑ i, ∑ j, a i j * inner ℝ (U i-U j) (V i)) := by
    rw [Finset.sum_comm,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
    simp only [inner_sub_left]
    ring
  simp only [inner_sub_right,mul_sub,Finset.sum_sub_distrib]
  rw [hs]
  ring

/-- The actual centroid pairing has a literal Gaussian edge representation
for every test-vector family, a stronger form than a single quadratic test. -/
theorem centroid_pairing (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (V : ι → FSC.Coord d) :
    (∑ i, inner ℝ (centroid B h i) (V i)) =
      (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * inner ℝ (B i-B j) (V i-V j) := by
  simp_rw [centroid_eq_boundary_laplacian B h σ hσ hlower]
  exact weighted_edge_pairing (facetWeight B h) (facetWeight_symm B h) B V

/-- Operator test form of the actual centroid-boundary identity. -/
theorem centroid_linear_pairing (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (Q : FSC.Coord d →ₗ[ℝ] FSC.Coord d) :
    (∑ i, inner ℝ (centroid B h i) (Q (B i))) =
      (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * inner ℝ (B i-B j) (Q (B i-B j)) := by
  simpa only [map_sub] using centroid_pairing B h σ hσ hlower (fun i => Q (B i))

/-- The exact interior quadratic contribution for a genuine symmetric
operator H: it is the Gaussian weighted squared edge strain. -/
theorem centroid_symmetric_square_pairing (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →ₗ[ℝ] FSC.Coord d) (hH : H.IsSymmetric) :
    (∑ i, inner ℝ (centroid B h i) (H (H (B i)))) =
      (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * ‖H (B i-B j)‖^2 := by
  have he := centroid_linear_pairing B h σ hσ hlower (H.comp H)
  simp only [LinearMap.comp_apply] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hH (B i-B j) (H (B i-B j)),real_inner_self_eq_norm_sq]

/-- Polarized symmetric-operator version, retaining both independent strains. -/
theorem centroid_symmetric_mixed_pairing (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (H K : FSC.Coord d →ₗ[ℝ] FSC.Coord d) (hH : H.IsSymmetric) :
    (∑ i, inner ℝ (centroid B h i) (H (K (B i)))) =
      (1/2:ℝ) * ∑ i, ∑ j, facetWeight B h i j * inner ℝ (H (B i-B j)) (K (B i-B j)) := by
  have he := centroid_linear_pairing B h σ hσ hlower (H.comp K)
  simp only [LinearMap.comp_apply] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hH (B i-B j) (K (B i-B j))]

end NegativeVotingFanCentroid
