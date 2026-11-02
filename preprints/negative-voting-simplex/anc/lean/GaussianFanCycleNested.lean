import GaussianFanCycleCoordinates

/-! Exact nested-face geometry and Gaussian density ratios. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem faceDirection_mono (b : AffineBasis V ℝ E) {S T : Set V} (hST : S ⊆ T) :
    faceDirection b S ≤ faceDirection b T :=
  vectorSpan_mono ℝ (Set.image_mono hST)

theorem mem_face_tangent_iff_anchor_edges (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (hi : i ∈ S) (z : E) :
    z ∈ (faceDirection b S)ᗮ ↔ ∀ j ∈ S, ⟪b j-b i,z⟫ = 0 := by
  constructor
  · intro hz j hj
    exact Submodule.inner_right_of_mem_orthogonal (target_face_edge_mem b S j i hj hi) hz
  · intro hz
    have hle : faceDirection b S ≤ LinearMap.ker (InnerProductSpace.toDual ℝ E z).toLinearMap := by
      rw [faceDirection, vectorSpan_def, Submodule.span_le]
      rintro u ⟨a,⟨j,hj,rfl⟩,c,⟨k,hk,rfl⟩,rfl⟩
      change ⟪z,b j-b k⟫ = 0
      rw [real_inner_comm]
      have hj0 := hz j hj
      have hk0 := hz k hk
      simp only [inner_sub_left] at hj0 hk0 ⊢
      linarith
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [real_inner_comm]
    exact hle hx

theorem mem_child_tangent_iff (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) (z : E) :
    z ∈ (faceDirection b (Set.insert k S))ᗮ ↔
      z ∈ (faceDirection b S)ᗮ ∧ ⟪faceBoundaryNormal b S i k,z⟫ = 0 := by
  have hik : i ∈ Set.insert k S := Set.mem_insert_of_mem k hi
  constructor
  · intro hz
    have he := (mem_face_tangent_iff_anchor_edges b (Set.insert k S) i hik z).mp hz
    have ht : z ∈ (faceDirection b S)ᗮ :=
      (mem_face_tangent_iff_anchor_edges b S i hi z).mpr fun j hj => he j (Set.mem_insert_of_mem k hj)
    refine ⟨ht,?_⟩
    rw [faceBoundaryNormal_inner_tangent b S i k z ht]
    have hk0 := he k (Set.mem_insert k S)
    have hg : ⟪b i-b k,z⟫ = 0 := by
      simp only [inner_sub_left] at hk0 ⊢
      linarith
    rw [hg,mul_zero]
  · rintro ⟨ht,hn⟩
    rw [faceBoundaryNormal_inner_tangent b S i k z ht] at hn
    have hheight : (faceGapHeight b S i k)⁻¹ ≠ 0 :=
      ne_of_gt (inv_pos.mpr (faceGapHeight_pos b S i k hi hk))
    have hg := (mul_eq_zero.mp hn).resolve_left hheight
    apply (mem_face_tangent_iff_anchor_edges b (Set.insert k S) i hik z).mpr
    intro j hj
    rcases Set.mem_insert_iff.mp hj with rfl | hj
    · simp only [inner_sub_left] at hg ⊢
      linarith
    · exact (mem_face_tangent_iff_anchor_edges b S i hi z).mp ht j hj

theorem faceDirection_insert (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    faceDirection b (Set.insert k S) =
      faceDirection b S ⊔ Submodule.span ℝ {faceBoundaryNormal b S i k} := by
  have he : (faceDirection b (Set.insert k S))ᗮ =
      (faceDirection b S ⊔ Submodule.span ℝ {faceBoundaryNormal b S i k})ᗮ := by
    rw [← Submodule.inf_orthogonal]
    ext z
    rw [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact mem_child_tangent_iff b S i k hi hk z
  have hh := congrArg (fun T : Submodule ℝ E => Tᗮ) he
  simpa only [Submodule.orthogonal_orthogonal] using hh

theorem faceBoundaryNormal_mem_child_direction (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    faceBoundaryNormal b S i k ∈ faceDirection b (Set.insert k S) := by
  rw [faceDirection_insert b S i k hi hk]
  exact Submodule.mem_sup_right (Submodule.subset_span (by simp))

/-- Exact nested affine origin, with the INWARD normal sign made explicit. -/
theorem faceAnchor_insert (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    faceAnchor b h (Set.insert k S) = faceAnchor b h S +
      ⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫ •
        faceBoundaryNormal b S i k := by
  let n := faceBoundaryNormal b S i k
  let c := ⟪n,affineFanApex b h-faceAnchor b h S⟫
  have hq : faceAnchor b h S ∈ faceDirection b (Set.insert k S) :=
    faceDirection_mono b (Set.subset_insert k S)
      ((faceDirection b S).orthogonalProjectionOnto (affineFanApex b h)).property
  have hn := faceBoundaryNormal_mem_child_direction b S i k hi hk
  have hmem : faceAnchor b h S+c•n ∈ faceDirection b (Set.insert k S) :=
    (faceDirection b (Set.insert k S)).add_mem hq
      ((faceDirection b (Set.insert k S)).smul_mem c hn)
  have hperp : affineFanApex b h-(faceAnchor b h S+c•n) ∈
      (faceDirection b (Set.insert k S))ᗮ := by
    apply (mem_child_tangent_iff b S i k hi hk _).mpr
    constructor
    · have he : affineFanApex b h-(faceAnchor b h S+c•n) =
          (affineFanApex b h-faceAnchor b h S)-c•n := by abel
      rw [he]
      exact (faceDirection b S)ᗮ.sub_mem (apex_sub_faceAnchor_mem b h S)
        ((faceDirection b S)ᗮ.smul_mem c (faceBoundaryNormal_mem_tangent b S i k))
    · change ⟪n,affineFanApex b h-(faceAnchor b h S+c•n)⟫ = 0
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      have hnorm : ‖n‖ = 1 := faceBoundaryNormal_norm b S i k hi hk
      rw [hnorm]
      dsimp [c]
      rw [inner_sub_right]
      ring
  exact Submodule.eq_starProjection_of_mem_orthogonal hmem hperp

theorem faceDirection_rank_insert (b : AffineBasis V ℝ E) (S : Set V)
    (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    Module.finrank ℝ (faceDirection b (Set.insert k S)) =
      Module.finrank ℝ (faceDirection b S)+1 := by
  let n := faceBoundaryNormal b S i k
  have hn : n ≠ 0 := by
    intro hz
    have hh := faceBoundaryNormal_norm b S i k hi hk
    change ‖n‖ = 1 at hh
    rw [hz,norm_zero] at hh
    norm_num at hh
  have hle : Submodule.span ℝ {n} ≤ (faceDirection b S)ᗮ := by
    rw [Submodule.span_le]
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact faceBoundaryNormal_mem_tangent b S i k
  have hd : Disjoint (faceDirection b S) (Submodule.span ℝ {n}) :=
    (faceDirection b S).orthogonal_disjoint.mono_right hle
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (faceDirection b S) (Submodule.span ℝ {n})
  rw [hd.eq_bot,finrank_bot,add_zero,finrank_span_singleton hn] at hr
  rw [faceDirection_insert b S i k hi hk]
  exact hr

/-- Same affine-origin identity expressed in the OUTWARD cap convention. -/
theorem faceAnchor_insert_outward (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    faceAnchor b h (Set.insert k.1 S) = faceAnchor b h S+
      intrinsicCapOffset b h S i k • (intrinsicCapNormal b S i k : E) := by
  rw [faceAnchor_insert b h S i k hi k.property]
  change faceAnchor b h S+_ = faceAnchor b h S+
    (-⟪faceBoundaryNormal b S i k,affineFanApex b h-faceAnchor b h S⟫) •
      (-faceBoundaryNormal b S i k)
  simp

theorem faceAnchor_norm_sq_insert (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    ‖faceAnchor b h (Set.insert k.1 S)‖^2 =
      ‖faceAnchor b h S‖^2+(intrinsicCapOffset b h S i k)^2 := by
  have hq : faceAnchor b h S ∈ faceDirection b S :=
    ((faceDirection b S).orthogonalProjectionOnto (affineFanApex b h)).property
  have hn : (intrinsicCapNormal b S i k : E) ∈ (faceDirection b S)ᗮ :=
    (intrinsicCapNormal b S i k).property
  have ho := Submodule.inner_right_of_mem_orthogonal hq hn
  rw [faceAnchor_insert_outward b h S i hi k, norm_add_sq_real,
    real_inner_smul_right,ho,mul_zero,mul_zero,add_zero,norm_smul,Real.norm_eq_abs]
  have hu : ‖(intrinsicCapNormal b S i k : E)‖ = 1 := intrinsicCapNormal_norm b S i hi k
  rw [hu,mul_one,sq_abs]

/-- Exact normal-density ratio between a stratum and each actual child stratum. -/
theorem stratumDensityFactor_insert (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (hi : i ∈ S) (k : {k : V // k ∉ S}) :
    stratumDensityFactor b h (Set.insert k.1 S) = stratumDensityFactor b h S *
      WeakSimplex.normalPDF (intrinsicCapOffset b h S i k) := by
  unfold stratumDensityFactor
  rw [faceDirection_rank_insert b S i k hi k.property,
    faceAnchor_norm_sq_insert b h S i hi k,pow_succ]
  have he : -(‖faceAnchor b h S‖^2+(intrinsicCapOffset b h S i k)^2)/2 =
      -‖faceAnchor b h S‖^2/2 + -(intrinsicCapOffset b h S i k)^2/2 := by ring
  rw [he,Real.exp_add]
  simp only [WeakSimplex.normalPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  ring

end NegativeVotingFanCycle
