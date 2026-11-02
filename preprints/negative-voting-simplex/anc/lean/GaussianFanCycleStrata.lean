import GaussianFanCycleGram

/-! Concrete affine origins and score strata of the full target simplex. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The genuine common apex of all affine score equalities. -/
def affineFanApex (b : AffineBasis V ℝ E) (h : V → ℝ) : E :=
  ∑ k, h k • barycentricOutwardVector b k

theorem affineFanApex_edge (b : AffineBasis V ℝ E) (h : V → ℝ) (i j : V) :
    ⟪affineFanApex b h, b i-b j⟫ = h j-h i := by
  rw [affineFanApex, sum_inner]
  simp_rw [real_inner_smul_left, barycentricOutwardVector_edge, mul_sub]
  simp

theorem affineFanApex_scores_tie (b : AffineBasis V ℝ E) (h : V → ℝ) (i j : V) :
    ⟪b i, affineFanApex b h⟫+h i = ⟪b j, affineFanApex b h⟫+h j := by
  have he := affineFanApex_edge b h i j
  rw [inner_sub_right] at he
  have hi := real_inner_comm (affineFanApex b h) (b i)
  have hj := real_inner_comm (affineFanApex b h) (b j)
  linarith

def faceAnchor (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) : E :=
  (faceDirection b S).starProjection (affineFanApex b h)

theorem apex_sub_faceAnchor_mem (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) :
    affineFanApex b h-faceAnchor b h S ∈ (faceDirection b S)ᗮ :=
  (faceDirection b S).sub_starProjection_mem_orthogonal _

theorem target_face_edge_mem (b : AffineBasis V ℝ E) (S : Set V)
    (i j : V) (hi : i ∈ S) (hj : j ∈ S) : b i-b j ∈ faceDirection b S := by
  exact vsub_mem_vectorSpan ℝ (Set.mem_image_of_mem b hi) (Set.mem_image_of_mem b hj)

theorem faceAnchor_scores_tie (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
    ⟪b i,faceAnchor b h S⟫+h i = ⟪b j,faceAnchor b h S⟫+h j := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (target_face_edge_mem b S i j hi hj) (apex_sub_faceAnchor_mem b h S)
  have he := affineFanApex_scores_tie b h i j
  simp only [inner_sub_left, inner_sub_right] at ho
  linarith

/-- Exactly the tied maximum-score stratum, including all of its boundary faces. -/
def winnerStratum (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) : Set E :=
  {x | ∀ i ∈ S, ∀ j, ⟪b j,x⟫+h j ≤ ⟪b i,x⟫+h i}

theorem mem_winnerStratum_iff_apex (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (x : E) :
    x ∈ winnerStratum b h S ↔ ∀ i ∈ S, ∀ j, 0 ≤ ⟪b i-b j,x-affineFanApex b h⟫ := by
  unfold winnerStratum
  simp only [Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  have he := affineFanApex_scores_tie b h i j
  simp only [inner_sub_left, inner_sub_right]
  constructor <;> intro hx <;> linarith

theorem mem_winnerStratum_tangent (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (x : E) (hx : x ∈ winnerStratum b h S) :
    x-affineFanApex b h ∈ (faceDirection b S)ᗮ := by
  have hle : faceDirection b S ≤
      LinearMap.ker (InnerProductSpace.toDual ℝ E (x-affineFanApex b h)).toLinearMap := by
    rw [faceDirection, vectorSpan_def, Submodule.span_le]
    rintro y ⟨a,⟨i,hi,rfl⟩,c,⟨j,hj,rfl⟩,rfl⟩
    change ⟪x-affineFanApex b h,b i-b j⟫ = 0
    have h1 := (mem_winnerStratum_iff_apex b h S x).mp hx i hi j
    have h2 := (mem_winnerStratum_iff_apex b h S x).mp hx j hj i
    rw [real_inner_comm]
    simp only [inner_sub_left] at h1 h2 ⊢
    linarith
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [real_inner_comm]
  exact hle hy

theorem mem_winnerStratum_iff_tangent_gaps (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (x : E) :
    x ∈ winnerStratum b h S ↔ x-affineFanApex b h ∈ (faceDirection b S)ᗮ ∧
      ∀ k ∉ S, 0 ≤ ⟪b i-b k,x-affineFanApex b h⟫ := by
  constructor
  · intro hx
    exact ⟨mem_winnerStratum_tangent b h S x hx,
      fun k _ => (mem_winnerStratum_iff_apex b h S x).mp hx i hi k⟩
  · rintro ⟨ht,hg⟩
    apply (mem_winnerStratum_iff_apex b h S x).mpr
    intro j hj k
    by_cases hk : k ∈ S
    · have he := Submodule.inner_right_of_mem_orthogonal
        (target_face_edge_mem b S j k hj hk) ht
      rw [he]
    · have he := Submodule.inner_right_of_mem_orthogonal
        (target_face_edge_mem b S j i hj hi) ht
      have hc := hg k hk
      simp only [inner_sub_left] at he hc ⊢
      linarith

theorem faceBoundaryNormal_mem_tangent (b : AffineBasis V ℝ E) (S : Set V) (i k : V) :
    faceBoundaryNormal b S i k ∈ (faceDirection b S)ᗮ := by
  apply Submodule.smul_mem
  exact ((faceDirection b S)ᗮ.orthogonalProjectionOnto (b i-b k)).property

theorem faceBoundaryNormal_inner_tangent (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (z : E) (hz : z ∈ (faceDirection b S)ᗮ) :
    ⟪faceBoundaryNormal b S i k,z⟫ =
      (faceGapHeight b S i k)⁻¹ * ⟪b i-b k,z⟫ := by
  rw [faceBoundaryNormal, real_inner_smul_left, projectedFaceGap,
    Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hz]

/-- Outward unit normals of the intrinsic Gaussian cap, opposite to the inward stratum normals. -/
def intrinsicCapNormal (b : AffineBasis V ℝ E) (S : Set V) (i : V)
    (k : {k : V // k ∉ S}) : (faceDirection b S)ᗮ :=
  ⟨-faceBoundaryNormal b S i k, (faceDirection b S)ᗮ.neg_mem
    (faceBoundaryNormal_mem_tangent b S i k)⟩

def intrinsicCapOffset (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (k : {k : V // k ∉ S}) : ℝ :=
  -⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫

def intrinsicWinnerCap (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) : Set (faceDirection b S)ᗮ :=
  {z | ∀ k, ⟪intrinsicCapNormal b S i k,z⟫ ≤ intrinsicCapOffset b h S i k}

def embedFace (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (z : (faceDirection b S)ᗮ) : E := faceAnchor b h S+z

theorem intrinsicCapNormal_norm (b : AffineBasis V ℝ E) (S : Set V) (i : V)
    (hi : i ∈ S) (k : {k : V // k ∉ S}) : ‖intrinsicCapNormal b S i k‖ = 1 := by
  change ‖-faceBoundaryNormal b S i k‖ = 1
  rw [norm_neg]
  exact faceBoundaryNormal_norm b S i k hi k.property

theorem embedFace_sub_apex_mem (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (z : (faceDirection b S)ᗮ) : embedFace b h S z-affineFanApex b h ∈ (faceDirection b S)ᗮ := by
  have he : embedFace b h S z-affineFanApex b h =
      (z : E)-(affineFanApex b h-faceAnchor b h S) := by unfold embedFace; abel
  rw [he]
  exact (faceDirection b S)ᗮ.sub_mem z.property (apex_sub_faceAnchor_mem b h S)

theorem intrinsicCap_inequality_iff_gap (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S})
    (z : (faceDirection b S)ᗮ) :
    ⟪intrinsicCapNormal b S i k,z⟫ ≤ intrinsicCapOffset b h S i k ↔
      0 ≤ ⟪b i-b k,embedFace b h S z-affineFanApex b h⟫ := by
  have hh := inv_pos.mpr (faceGapHeight_pos b S i k hi k.property)
  have ht := faceBoundaryNormal_inner_tangent b S i k
    (embedFace b h S z-affineFanApex b h) (embedFace_sub_apex_mem b h S z)
  have hs : ⟪faceBoundaryNormal b S i k,embedFace b h S z-affineFanApex b h⟫ =
      ⟪faceBoundaryNormal b S i k,(z : E)⟫-
        ⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫ := by
    simp only [embedFace, inner_add_right, inner_sub_right]
    ring
  change ⟪-faceBoundaryNormal b S i k,(z : E)⟫ ≤
    -⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫ ↔ _
  rw [inner_neg_left]
  constructor
  · intro hc
    apply (mul_nonneg_iff_of_pos_left hh).mp
    linarith
  · intro hg
    have hm := mul_nonneg (le_of_lt hh) hg
    linarith

/-- Literal score strata equal the intrinsic unit-normal cap in the constructed coordinates. -/
theorem embedFace_mem_winnerStratum_iff (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (z : (faceDirection b S)ᗮ) :
    embedFace b h S z ∈ winnerStratum b h S ↔ z ∈ intrinsicWinnerCap b h S i := by
  rw [mem_winnerStratum_iff_tangent_gaps b h S i hi]
  constructor
  · rintro ⟨_,hg⟩ k
    exact (intrinsicCap_inequality_iff_gap b h S i hi k z).mpr (hg k k.property)
  · intro hc
    exact ⟨embedFace_sub_apex_mem b h S z, fun k hk =>
      (intrinsicCap_inequality_iff_gap b h S i hi ⟨k,hk⟩ z).mp (hc ⟨k,hk⟩)⟩

theorem winnerStratum_eq_image_intrinsicWinnerCap (b : AffineBasis V ℝ E)
    (h : V → ℝ) (S : Set V) (i : V) (hi : i ∈ S) :
    winnerStratum b h S = embedFace b h S '' intrinsicWinnerCap b h S i := by
  ext x
  constructor
  · intro hx
    have htan : x-faceAnchor b h S ∈ (faceDirection b S)ᗮ := by
      have he : x-faceAnchor b h S =
          (x-affineFanApex b h)+(affineFanApex b h-faceAnchor b h S) := by abel
      rw [he]
      exact (faceDirection b S)ᗮ.add_mem
        (mem_winnerStratum_tangent b h S x hx) (apex_sub_faceAnchor_mem b h S)
    let z : (faceDirection b S)ᗮ := ⟨x-faceAnchor b h S,htan⟩
    have he : embedFace b h S z = x := by dsimp [embedFace,z]; abel
    refine ⟨z,?_,he⟩
    apply (embedFace_mem_winnerStratum_iff b h S i hi z).mp
    rwa [he]
  · rintro ⟨z,hz,rfl⟩
    exact (embedFace_mem_winnerStratum_iff b h S i hi z).mpr hz

theorem embedFace_isometry (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) :
    Isometry (embedFace b h S) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist (faceAnchor b h S+(z:E)) (faceAnchor b h S+(w:E)) = dist z w
  rw [dist_add_left]
  rfl

theorem intrinsicWinnerCap_isClosed (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) : IsClosed (intrinsicWinnerCap b h S i) := by
  unfold intrinsicWinnerCap
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Reciprocal target vectors placed in the actual tangent space. -/
def intrinsicReciprocal (b : AffineBasis V ℝ E) (S : Set V)
    (k : {k : V // k ∉ S}) : (faceDirection b S)ᗮ :=
  ⟨barycentricOutwardVector b k,barycentricOutwardVector_mem_face_orthogonal b S k k.property⟩

theorem intrinsicReciprocal_capNormal (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (hi : i ∈ S) (k l : {k : V // k ∉ S}) :
    ⟪intrinsicReciprocal b S k,intrinsicCapNormal b S i l⟫ =
      -(if k = l then 1 else 0) / faceGapHeight b S i l := by
  change ⟪barycentricOutwardVector b k,-faceBoundaryNormal b S i l⟫ = _
  rw [inner_neg_right, barycentricOutwardVector_faceBoundaryNormal b S i k l hi k.property]
  simp only [Subtype.coe_inj, neg_div]

/-- Distinct actual cap normals are never scalar multiples; no separation premise is assumed. -/
theorem intrinsicCapNormal_ne_smul (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (hi : i ∈ S) (k l : {k : V // k ∉ S}) (hkl : k ≠ l) (c : ℝ) :
    intrinsicCapNormal b S i k ≠ c • intrinsicCapNormal b S i l := by
  intro he
  have hp := congrArg (fun z => ⟪intrinsicReciprocal b S k,z⟫) he
  rw [real_inner_smul_right, intrinsicReciprocal_capNormal b S i hi,
    intrinsicReciprocal_capNormal b S i hi] at hp
  simp only [ite_true, if_neg hkl, neg_zero, zero_div, mul_zero, neg_div, one_div] at hp
  have hh := inv_pos.mpr (faceGapHeight_pos b S i k hi k.property)
  linarith

/-- A concrete strictly feasible cap point, even when the complement index set is empty. -/
def intrinsicStrictPoint (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) :
    (faceDirection b S)ᗮ := by
  classical
  exact ⟨affineFanApex b h-faceAnchor b h S,apex_sub_faceAnchor_mem b h S⟩ +
    ∑ k : {k : V // k ∉ S}, intrinsicReciprocal b S k

theorem intrinsicStrictPoint_strict (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    ⟪intrinsicCapNormal b S i k,intrinsicStrictPoint b h S⟫ <
      intrinsicCapOffset b h S i k := by
  classical
  have hp : ⟪intrinsicCapNormal b S i k,
      ∑ l : {k : V // k ∉ S}, intrinsicReciprocal b S l⟫ =
      -(faceGapHeight b S i k)⁻¹ := by
    rw [inner_sum]
    have he (l : {k : V // k ∉ S}) :
        ⟪intrinsicCapNormal b S i k,intrinsicReciprocal b S l⟫ =
          -(if l = k then 1 else 0) / faceGapHeight b S i k := by
      rw [real_inner_comm]
      exact intrinsicReciprocal_capNormal b S i hi l k
    simp_rw [he]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hh := inv_pos.mpr (faceGapHeight_pos b S i k hi k.property)
  rw [intrinsicStrictPoint, inner_add_right, hp]
  change ⟪-faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫-
    (faceGapHeight b S i k)⁻¹ <
    -⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫
  rw [inner_neg_left]
  linarith

theorem intrinsicWinnerCap_nonempty (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) : (intrinsicWinnerCap b h S i).Nonempty := by
  refine ⟨intrinsicStrictPoint b h S,fun k => ?_⟩
  exact le_of_lt (intrinsicStrictPoint_strict b h S i hi k)

theorem intrinsicStrictPoint_mem_interior (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) :
    intrinsicStrictPoint b h S ∈ interior (intrinsicWinnerCap b h S i) := by
  classical
  let U : Set (faceDirection b S)ᗮ :=
    {z | ∀ k, ⟪intrinsicCapNormal b S i k,z⟫ < intrinsicCapOffset b h S i k}
  have hopen : IsOpen U := by
    dsimp [U]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt (by fun_prop) continuous_const
  have hmem : intrinsicStrictPoint b h S ∈ U := fun k =>
    intrinsicStrictPoint_strict b h S i hi k
  have hsub : U ⊆ intrinsicWinnerCap b h S i := fun z hz k => le_of_lt (hz k)
  exact mem_interior.mpr ⟨U,hsub,hopen,hmem⟩

end NegativeVotingFanCycle
