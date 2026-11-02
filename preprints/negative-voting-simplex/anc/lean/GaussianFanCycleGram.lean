import GaussianFanCycleGeometry

/-! Exact Gram contents and orthogonal-height factorizations for target faces. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Module
namespace NegativeVotingFanCycle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Squared parallelogram content, as an actual Gram determinant. -/
def pairGram (u v : E) : ℝ := (Matrix.gram ℝ ![u,v]).det

/-- Squared parallelepiped content, as an actual Gram determinant. -/
def tripleGram (u v w : E) : ℝ := (Matrix.gram ℝ ![u,v,w]).det

theorem pairGram_formula (u v : E) :
    pairGram u v = ⟪u,u⟫ * ⟪v,v⟫ - ⟪u,v⟫ ^ 2 := by
  simp only [pairGram, Matrix.det_fin_two, Matrix.gram_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [real_inner_comm v u]
  ring

theorem tripleGram_formula (u v w : E) :
    tripleGram u v w = ⟪u,u⟫ * ⟪v,v⟫ * ⟪w,w⟫ +
      2 * ⟪u,v⟫ * ⟪u,w⟫ * ⟪v,w⟫ - ⟪u,u⟫ * ⟪v,w⟫ ^ 2 -
      ⟪v,v⟫ * ⟪u,w⟫ ^ 2 - ⟪w,w⟫ * ⟪u,v⟫ ^ 2 := by
  simp only [tripleGram, Matrix.det_fin_three, Matrix.gram_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Fin.reduceFinMk]
  rw [real_inner_comm v u, real_inner_comm w u, real_inner_comm w v]
  ring

theorem pairGram_nonneg (u v : E) : 0 ≤ pairGram u v :=
  (Matrix.posSemidef_gram ℝ ![u,v]).det_nonneg

theorem tripleGram_nonneg (u v w : E) : 0 ≤ tripleGram u v w :=
  (Matrix.posSemidef_gram ℝ ![u,v,w]).det_nonneg

theorem pairGram_shear (u v : E) (a : ℝ) : pairGram u (v+a•u) = pairGram u v := by
  rw [pairGram_formula, pairGram_formula]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u]
  ring

theorem tripleGram_shear (u v w : E) (a b : ℝ) :
    tripleGram u v (w+a•u+b•v) = tripleGram u v w := by
  rw [tripleGram_formula, tripleGram_formula]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u, real_inner_comm w u, real_inner_comm w v]
  ring

theorem pairGram_projection_factor (u v : E) :
    pairGram u v = ‖u‖ ^ 2 * ‖(Submodule.span ℝ {u})ᗮ.starProjection v‖ ^ 2 := by
  let S := Submodule.span ℝ ({u} : Set E)
  let r := Sᗮ.starProjection v
  have hp : S.starProjection v ∈ S := (S.orthogonalProjectionOnto v).property
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hp
  have hv : v = r + a • u := by
    rw [ha]
    dsimp [r]
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hr : r ∈ Sᗮ := (Sᗮ.orthogonalProjectionOnto v).property
  have hu : u ∈ S := Submodule.subset_span (by simp)
  have hur : ⟪u,r⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hr
  change pairGram u v = ‖u‖ ^ 2 * ‖r‖ ^ 2
  calc
    pairGram u v = pairGram u (r+a•u) := congrArg (pairGram u) hv
    _ = pairGram u r := pairGram_shear u r a
    _ = _ := by rw [pairGram_formula, hur, real_inner_self_eq_norm_sq,
                   real_inner_self_eq_norm_sq]; ring

theorem tripleGram_projection_factor (u v w : E) :
    tripleGram u v w = pairGram u v *
      ‖(Submodule.span ℝ ({u,v} : Set E))ᗮ.starProjection w‖ ^ 2 := by
  let S := Submodule.span ℝ ({u,v} : Set E)
  let r := Sᗮ.starProjection w
  have hp : S.starProjection w ∈ S := (S.orthogonalProjectionOnto w).property
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hp
  have hw : w = r + a • u + b • v := by
    have hs : a • u + b • v = S.starProjection w := hab
    rw [add_assoc, hs]
    dsimp [r]
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hr : r ∈ Sᗮ := (Sᗮ.orthogonalProjectionOnto w).property
  have hu : u ∈ S := Submodule.subset_span (by simp)
  have hv : v ∈ S := Submodule.subset_span (by simp)
  have hur : ⟪u,r⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hr
  have hvr : ⟪v,r⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hv hr
  change tripleGram u v w = pairGram u v * ‖r‖ ^ 2
  calc
    tripleGram u v w = tripleGram u v (r+a•u+b•v) := congrArg (tripleGram u v) hw
    _ = tripleGram u v r := tripleGram_shear u v r a b
    _ = _ := by
      rw [tripleGram_formula, pairGram_formula, hur, hvr]
      simp only [real_inner_self_eq_norm_sq]
      ring

/-- Twice the triangle area, defined by the Gram content. -/
def triangleContent (a b c : E) : ℝ := Real.sqrt (pairGram (b-a) (c-a))

/-- Six times the tetrahedron volume, defined by the Gram content. -/
def tetrahedronContent (a b c d : E) : ℝ := Real.sqrt (tripleGram (b-a) (c-a) (d-a))

theorem triangleContent_projection_factor (a b c : E) :
    triangleContent a b c = ‖b-a‖ *
      ‖(Submodule.span ℝ ({b-a} : Set E))ᗮ.starProjection (c-a)‖ := by
  rw [triangleContent, pairGram_projection_factor, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]

theorem tetrahedronContent_projection_factor (a b c d : E) :
    tetrahedronContent a b c d = triangleContent a b c *
      ‖(Submodule.span ℝ ({b-a,c-a} : Set E))ᗮ.starProjection (d-a)‖ := by
  rw [tetrahedronContent, tripleGram_projection_factor,
    Real.sqrt_mul (pairGram_nonneg _ _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  rfl

theorem triangleContent_swap_first (a b c : E) :
    triangleContent b a c = triangleContent a b c := by
  unfold triangleContent
  congr 1
  simp only [pairGram_formula, inner_sub_left, inner_sub_right]
  simp only [real_inner_comm b a, real_inner_comm c a, real_inner_comm c b]
  ring

theorem triangleContent_swap_last (a b c : E) :
    triangleContent a c b = triangleContent a b c := by
  unfold triangleContent
  congr 1
  rw [pairGram_formula, pairGram_formula, real_inner_comm (c-a) (b-a)]
  ring

theorem tetrahedronContent_swap_first (a b c d : E) :
    tetrahedronContent b a c d = tetrahedronContent a b c d := by
  unfold tetrahedronContent
  congr 1
  simp only [tripleGram_formula, inner_sub_left, inner_sub_right]
  simp only [real_inner_comm b a, real_inner_comm c a, real_inner_comm c b,
    real_inner_comm d a, real_inner_comm d b, real_inner_comm d c]
  ring

theorem tetrahedronContent_swap_middle (a b c d : E) :
    tetrahedronContent a c b d = tetrahedronContent a b c d := by
  unfold tetrahedronContent
  congr 1
  rw [tripleGram_formula, tripleGram_formula, real_inner_comm (c-a) (b-a)]
  ring

theorem tetrahedronContent_swap_last (a b c d : E) :
    tetrahedronContent a b d c = tetrahedronContent a b c d := by
  unfold tetrahedronContent
  congr 1
  rw [tripleGram_formula, tripleGram_formula, real_inner_comm (d-a) (c-a)]
  ring

/-- Full vertex permutation invariance, not merely selected reorderings. -/
theorem triangleContent_perm (x : Fin 3 → E) (σ : Equiv.Perm (Fin 3)) :
    triangleContent (x (σ 0)) (x (σ 1)) (x (σ 2)) = triangleContent (x 0) (x 1) (x 2) := by
  classical
  have hs (y : Fin 3 → E) (i j : Fin 3) :
      triangleContent (y (Equiv.swap i j 0)) (y (Equiv.swap i j 1)) (y (Equiv.swap i j 2)) =
        triangleContent (y 0) (y 1) (y 2) := by
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, triangleContent_swap_first, triangleContent_swap_last] <;>
      exact triangleContent_swap_first _ _ _
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap f i j hij ih =>
    exact (hs (fun k => x (f k)) i j).trans ih

theorem tetrahedronContent_perm (x : Fin 4 → E) (σ : Equiv.Perm (Fin 4)) :
    tetrahedronContent (x (σ 0)) (x (σ 1)) (x (σ 2)) (x (σ 3)) =
      tetrahedronContent (x 0) (x 1) (x 2) (x 3) := by
  classical
  have hs (y : Fin 4 → E) (i j : Fin 4) :
      tetrahedronContent (y (Equiv.swap i j 0)) (y (Equiv.swap i j 1))
        (y (Equiv.swap i j 2)) (y (Equiv.swap i j 3)) =
        tetrahedronContent (y 0) (y 1) (y 2) (y 3) := by
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, tetrahedronContent_swap_first,
        tetrahedronContent_swap_middle, tetrahedronContent_swap_last] <;>
      exact tetrahedronContent_swap_first _ _ _ _
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap f i j hij ih =>
    exact (hs (fun k => x (f k)) i j).trans ih

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem faceDirection_pair (b : AffineBasis V ℝ E) (i j : V) :
    faceDirection b {i,j} = Submodule.span ℝ ({b j-b i} : Set E) := by
  rw [faceDirection, vectorSpan_eq_span_vsub_set_right ℝ (by simp : b i ∈ b '' {i,j})]
  simp [Set.image_insert_eq, Set.image_singleton, Submodule.span_insert_zero]

theorem faceDirection_triple (b : AffineBasis V ℝ E) (i j k : V) :
    faceDirection b {i,j,k} = Submodule.span ℝ ({b j-b i,b k-b i} : Set E) := by
  rw [faceDirection, vectorSpan_eq_span_vsub_set_right ℝ (by simp : b i ∈ b '' {i,j,k})]
  simp [Set.image_insert_eq, Set.image_singleton, Submodule.span_insert_zero]

theorem triangleContent_eq_edge_mul_height (b : AffineBasis V ℝ E) (i j k : V) :
    triangleContent (b i) (b j) (b k) = ‖b j-b i‖ * faceGapHeight b {i,j} i k := by
  rw [triangleContent_projection_factor, faceGapHeight, projectedFaceGap]
  simp only [faceDirection_pair]
  rw [← neg_sub (b k) (b i), map_neg, norm_neg]

theorem tetrahedronContent_eq_face_mul_height (b : AffineBasis V ℝ E) (i j k l : V) :
    tetrahedronContent (b i) (b j) (b k) (b l) =
      triangleContent (b i) (b j) (b k) * faceGapHeight b {i,j,k} i l := by
  rw [tetrahedronContent_projection_factor, faceGapHeight, projectedFaceGap]
  simp only [faceDirection_triple]
  rw [← neg_sub (b l) (b i), map_neg, norm_neg]

theorem triangleContent_pos (b : AffineBasis V ℝ E) (i j k : V)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    0 < triangleContent (b i) (b j) (b k) := by
  rw [triangleContent_eq_edge_mul_height]
  apply mul_pos
  · exact norm_pos_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij.symm))
  · exact faceGapHeight_pos b {i,j} i k (by simp) (by simp [hki,hkj])

theorem tetrahedronContent_pos (b : AffineBasis V ℝ E) (i j k l : V)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    0 < tetrahedronContent (b i) (b j) (b k) (b l) := by
  rw [tetrahedronContent_eq_face_mul_height]
  exact mul_pos (triangleContent_pos b i j k hij hki hkj)
    (faceGapHeight_pos b {i,j,k} i l (by simp) (by simp [hli,hlj,hlk]))

/-- The triangle reciprocal height is its edge length divided by twice-area content. -/
theorem reciprocal_pair_height (b : AffineBasis V ℝ E) (i j k : V)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (faceGapHeight b {i,j} i k)⁻¹ =
      ‖b j-b i‖ / triangleContent (b i) (b j) (b k) := by
  have he : ‖b j-b i‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij.symm))
  rw [triangleContent_eq_edge_mul_height]
  field_simp

/-- The tetrahedron reciprocal height is its face content divided by six-volume content. -/
theorem reciprocal_triple_height (b : AffineBasis V ℝ E) (i j k l : V)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (faceGapHeight b {i,j,k} i l)⁻¹ =
      triangleContent (b i) (b j) (b k) / tetrahedronContent (b i) (b j) (b k) (b l) := by
  have hg := ne_of_gt (triangleContent_pos b i j k hij hki hkj)
  rw [tetrahedronContent_eq_face_mul_height]
  field_simp

/-- Exact coefficient used when the stratum first-moment formula selects one tetrahedron. -/
theorem barycentricOutwardVector_tetrahedron_normal (b : AffineBasis V ℝ E)
    (i j k l : V) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    ⟪barycentricOutwardVector b l, faceBoundaryNormal b {i,j,k} i l⟫ =
      triangleContent (b i) (b j) (b k) / tetrahedronContent (b i) (b j) (b k) (b l) := by
  rw [barycentricOutwardVector_faceBoundaryNormal b {i,j,k} i l l (by simp)
    (by simp [hli,hlj,hlk])]
  simp only [ite_true, one_div]
  exact reciprocal_triple_height b i j k l hij hki hkj

end NegativeVotingFanCycle
