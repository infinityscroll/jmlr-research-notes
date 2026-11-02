import Mathlib

/-! Actual barycentric reciprocal normals for a finite Euclidean simplex.
No Gaussian stratum or covariance-Hessian hypothesis is introduced here. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Minus the Riesz representative of an actual affine-coordinate derivative. -/
def barycentricOutwardVector (b : AffineBasis V ℝ E) (i : V) : E :=
  -(InnerProductSpace.toDual ℝ E).symm (b.coord i).linear.toContinuousLinearMap

theorem barycentricOutwardVector_inner (b : AffineBasis V ℝ E) (i : V) (x : E) :
    ⟪barycentricOutwardVector b i, x⟫ = -(b.coord i).linear x := by
  simp [barycentricOutwardVector]

theorem barycentricOutwardVector_edge (b : AffineBasis V ℝ E) (i j k : V) :
    ⟪barycentricOutwardVector b i, b j - b k⟫ =
      (if i = k then 1 else 0) - (if i = j then 1 else 0) := by
  rw [barycentricOutwardVector_inner]
  have h := (b.coord i).linearMap_vsub (b j) (b k)
  change (b.coord i).linear (b j - b k) = _ at h
  rw [h, b.coord_apply, b.coord_apply]
  simp only [vsub_eq_sub]
  ring

theorem barycentricOutwardVector_sum (b : AffineBasis V ℝ E) :
    ∑ i, barycentricOutwardVector b i = 0 := by
  apply ext_inner_right ℝ
  intro x
  rw [sum_inner, inner_zero_left]
  simp_rw [barycentricOutwardVector_inner]
  rw [Finset.sum_neg_distrib]
  have hc (i : V) : (b.coord i).linear x = b.coord i x - b.coord i 0 := by
    simpa using (b.coord i).linearMap_vsub x (0 : E)
  simp_rw [hc]
  rw [Finset.sum_sub_distrib, b.sum_coord_apply_eq_one, b.sum_coord_apply_eq_one]
  ring

theorem barycentricOutwardVector_ne_zero (b : AffineBasis V ℝ E) (i j : V)
    (hij : i ≠ j) : barycentricOutwardVector b i ≠ 0 := by
  intro h
  have he := barycentricOutwardVector_edge b i i j
  rw [h, inner_zero_left] at he
  simp [hij] at he

/-- This really is perpendicular to every edge of the opposite face. -/
theorem barycentricOutwardVector_orthogonal_face_edge (b : AffineBasis V ℝ E)
    (i j k : V) (hij : i ≠ j) (hik : i ≠ k) :
    ⟪barycentricOutwardVector b i, b j - b k⟫ = 0 := by
  simp [barycentricOutwardVector_edge, hij, hik]

/-- The actual Euclidean simplex underlying an affine basis. -/
def simplexOfAffineBasis {n : ℕ} (b : AffineBasis (Fin (n+1)) ℝ E) :
    Affine.Simplex ℝ E n := ⟨b, b.ind⟩

/-- A vector is determined by its inner products with all edges from one basis point. -/
theorem eq_of_inner_basis_edges (b : AffineBasis V ℝ E) (i : V) (u v : E)
    (h : ∀ j, j ≠ i → ⟪u, b j - b i⟫ = ⟪v, b j - b i⟫) : u = v := by
  apply ext_inner_right ℝ
  intro x
  have hfun : (InnerProductSpace.toDual ℝ E u).toLinearMap =
      (InnerProductSpace.toDual ℝ E v).toLinearMap := by
    apply (b.basisOf i).ext
    intro j
    simpa using h j j.property
  exact DFunLike.congr_fun hfun x

/-- Reciprocal normal equals the actual altitude vector divided by minus height squared. -/
theorem barycentricOutwardVector_eq_altitude {n : ℕ} [NeZero n]
    (b : AffineBasis (Fin (n+1)) ℝ E) (i : Fin (n+1)) :
    barycentricOutwardVector b i =
      -((simplexOfAffineBasis b).height i ^ 2)⁻¹ •
        (b i - (simplexOfAffineBasis b).altitudeFoot i) := by
  let s := simplexOfAffineBasis b
  have hh : s.height i ≠ 0 := ne_of_gt (s.height_pos i)
  apply eq_of_inner_basis_edges b i
  intro j hji
  rw [barycentricOutwardVector_edge]
  simp only [ite_true, if_neg hji.symm, sub_zero, inner_smul_left, conj_trivial]
  have he := s.inner_vsub_vsub_altitudeFoot_eq_height_sq hji.symm
  change ⟪b i - b j, b i - s.altitudeFoot i⟫ = s.height i ^ 2 at he
  have he' : ⟪b i - s.altitudeFoot i, b j - b i⟫ = -(s.height i ^ 2) := by
    rw [real_inner_comm, ← neg_sub (b i) (b j), inner_neg_left, he]
  change 1 = -(s.height i ^ 2)⁻¹ * ⟪b i - s.altitudeFoot i, b j - b i⟫
  rw [he']
  field_simp

theorem barycentricOutwardVector_norm_eq_reciprocal_height {n : ℕ} [NeZero n]
    (b : AffineBasis (Fin (n+1)) ℝ E) (i : Fin (n+1)) :
    ‖barycentricOutwardVector b i‖ = ((simplexOfAffineBasis b).height i)⁻¹ := by
  let s := simplexOfAffineBasis b
  have hh : 0 < s.height i := s.height_pos i
  have hn : ‖b i - s.altitudeFoot i‖ = s.height i := by
    simp [Affine.Simplex.height, dist_eq_norm, s, simplexOfAffineBasis]
  rw [barycentricOutwardVector_eq_altitude, norm_smul, Real.norm_eq_abs]
  change |-(s.height i ^ 2)⁻¹| * ‖b i - s.altitudeFoot i‖ = (s.height i)⁻¹
  rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), hn]
  field_simp

/-- The actual direction space of an arbitrary face of the target simplex. -/
def faceDirection (b : AffineBasis V ℝ E) (S : Set V) : Submodule ℝ E :=
  vectorSpan ℝ (b '' S)

theorem barycentricOutwardVector_mem_face_orthogonal (b : AffineBasis V ℝ E)
    (S : Set V) (k : V) (hk : k ∉ S) :
    barycentricOutwardVector b k ∈ (faceDirection b S)ᗮ := by
  have hle : faceDirection b S ≤
      LinearMap.ker (InnerProductSpace.toDual ℝ E (barycentricOutwardVector b k)).toLinearMap := by
    rw [faceDirection, vectorSpan_def, Submodule.span_le]
    rintro x ⟨a, ⟨i, hi, rfl⟩, c, ⟨j, hj, rfl⟩, rfl⟩
    have hki : k ≠ i := fun h => hk (h.symm ▸ hi)
    have hkj : k ≠ j := fun h => hk (h.symm ▸ hj)
    change ⟪barycentricOutwardVector b k, b i - b j⟫ = 0
    exact barycentricOutwardVector_orthogonal_face_edge b k i j hki hkj
  rw [Submodule.mem_orthogonal]
  intro x hx
  rw [real_inner_comm]
  exact hle hx

/-- Projected target gap used by the genuine boundary normal of a Gaussian winner stratum. -/
def projectedFaceGap (b : AffineBasis V ℝ E) (S : Set V) (i k : V) : E :=
  (faceDirection b S)ᗮ.starProjection (b i - b k)

def faceGapHeight (b : AffineBasis V ℝ E) (S : Set V) (i k : V) : ℝ :=
  ‖projectedFaceGap b S i k‖

def faceBoundaryNormal (b : AffineBasis V ℝ E) (S : Set V) (i k : V) : E :=
  (faceGapHeight b S i k)⁻¹ • projectedFaceGap b S i k

theorem barycentricOutwardVector_projectedFaceGap (b : AffineBasis V ℝ E)
    (S : Set V) (i k l : V) (hi : i ∈ S) (hk : k ∉ S) :
    ⟪barycentricOutwardVector b k, projectedFaceGap b S i l⟫ =
      if k = l then 1 else 0 := by
  have hki : k ≠ i := fun h => hk (h.symm ▸ hi)
  rw [projectedFaceGap, ← Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr
    (barycentricOutwardVector_mem_face_orthogonal b S k hk)]
  simp [barycentricOutwardVector_edge, hki]

theorem faceGapHeight_pos (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) : 0 < faceGapHeight b S i k := by
  apply norm_pos_iff.mpr
  intro hz
  have he := barycentricOutwardVector_projectedFaceGap b S i k k hi hk
  rw [hz, inner_zero_right] at he
  norm_num at he

/-- Exact reciprocal-height/annihilation identity for every actual face boundary normal. -/
theorem barycentricOutwardVector_faceBoundaryNormal (b : AffineBasis V ℝ E)
    (S : Set V) (i k l : V) (hi : i ∈ S) (hk : k ∉ S) :
    ⟪barycentricOutwardVector b k, faceBoundaryNormal b S i l⟫ =
      (if k = l then 1 else 0) / faceGapHeight b S i l := by
  rw [faceBoundaryNormal, real_inner_smul_right,
    barycentricOutwardVector_projectedFaceGap b S i k l hi hk]
  ring

theorem faceBoundaryNormal_norm (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) : ‖faceBoundaryNormal b S i k‖ = 1 := by
  have hh := faceGapHeight_pos b S i k hi hk
  rw [faceBoundaryNormal, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hh))]
  change (faceGapHeight b S i k)⁻¹ * faceGapHeight b S i k = 1
  exact inv_mul_cancel₀ (ne_of_gt hh)

/-- Orthogonal projection onto the actual affine hull of a nonempty face. -/
def faceProjection (b : AffineBasis V ℝ E) (S : Set V) (i k : V) (hi : i ∈ S) : E :=
  let F := affineSpan ℝ (b '' S)
  letI : Nonempty F := ⟨⟨b i, subset_affineSpan ℝ _ (Set.mem_image_of_mem b hi)⟩⟩
  EuclideanGeometry.orthogonalProjection F (b k)

theorem projectedFaceGap_eq_projection_sub (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) :
    projectedFaceGap b S i k = faceProjection b S i k hi - b k := by
  let F := affineSpan ℝ (b '' S)
  have hiF : b i ∈ F := subset_affineSpan ℝ _ (Set.mem_image_of_mem b hi)
  letI : Nonempty F := ⟨⟨b i, hiF⟩⟩
  have hdir : F.direction = faceDirection b S := direction_affineSpan ℝ _
  let q : E := EuclideanGeometry.orthogonalProjection F (b k)
  have hq : q - b k ∈ (faceDirection b S)ᗮ := by
    simpa [q, hdir] using
      EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal F (b k)
  have hiq : b i - q ∈ faceDirection b S := by
    have he := EuclideanGeometry.vsub_orthogonalProjection_mem_direction (b k) hiF
    change b i - q ∈ F.direction at he
    rwa [hdir] at he
  change (faceDirection b S)ᗮ.starProjection (b i - b k) = q - b k
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq
  intro x hx
  have he : b i - b k - (q - b k) = b i - q := by abel
  rw [he]
  exact Submodule.inner_right_of_mem_orthogonal hiq hx

theorem faceGapHeight_eq_dist_projection (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) :
    faceGapHeight b S i k = dist (b k) (faceProjection b S i k hi) := by
  rw [faceGapHeight, projectedFaceGap_eq_projection_sub b S i k hi, dist_eq_norm]
  exact norm_sub_rev _ _

/-- Projection and hence height do not depend on the chosen point of the face. -/
theorem projectedFaceGap_independent_anchor (b : AffineBasis V ℝ E) (S : Set V)
    (i j k : V) (hi : i ∈ S) (hj : j ∈ S) :
    projectedFaceGap b S i k = projectedFaceGap b S j k := by
  rw [projectedFaceGap_eq_projection_sub b S i k hi,
    projectedFaceGap_eq_projection_sub b S j k hj]
  rfl

end NegativeVotingFanCycle
