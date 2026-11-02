import NegativeVoting.RegularSimplex

/-!
# Regular simplex references in the exact theorem dimensions

Center the coordinate vectors in the orthogonal complement of the all-ones
vector, choose orthonormal coordinates on that codimension-one space, and
pad with zero coordinates when the target ambient dimension is larger.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NegativeVoting
open scoped BigOperators RealInnerProductSpace
open Module

/-- An exact regular simplex in its minimal ambient dimension. -/
theorem exists_regularSimplexGram_minimal {m : ℕ} (hm : 1 ≤ m) :
    ∃ rows : Fin m → Fin (m - 1) → ℝ, RegularSimplexGram rows := by
  classical
  let u : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => 1)
  let c : ℝ := 1 / (m : ℝ)
  let v (i : Fin m) : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1 - c • u
  have hmpos : 0 < m := by omega
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hu_ne : u ≠ 0 := by
    intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x ⟨0, hmpos⟩) h
    norm_num [u] at hh
  have huu : inner ℝ u u = (m : ℝ) := by
    rw [PiLp.inner_apply]
    simp [u]
  have heu (i : Fin m) : inner ℝ (EuclideanSpace.single i 1) u = 1 := by
    simp [EuclideanSpace.inner_single_left, u]
  have hue (i : Fin m) : inner ℝ u (EuclideanSpace.single i 1) = 1 := by
    rw [real_inner_comm]
    exact heu i
  have hee (i j : Fin m) :
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
        if i = j then 1 else 0 := by
    simp [EuclideanSpace.inner_single_left, PiLp.single_apply]
  have hv_mem (i : Fin m) : v i ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [v, inner_sub_left, real_inner_smul_left, heu, huu]
    dsimp [c]
    field_simp
    ring
  have hv_inner (i j : Fin m) :
      inner ℝ (v i) (v j) = (if i = j then 1 else 0) - 1 / (m : ℝ) := by
    simp only [v, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hee, heu, hue, huu]
    dsimp [c]
    field_simp
    ring
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin m)) = (m - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let H := (ℝ ∙ u)ᗮ
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (m - 1) hu_ne
  let rows (i : Fin m) (k : Fin (m - 1)) : ℝ :=
    b.repr (⟨v i, hv_mem i⟩ : H) k
  refine ⟨rows, ?_⟩
  intro i j
  calc
    (∑ k, rows i k * rows j k) =
        inner ℝ (b.repr (⟨v i, hv_mem i⟩ : H)) (b.repr (⟨v j, hv_mem j⟩ : H)) := by
      rw [PiLp.inner_apply]
      simp only [rows, Real.inner_apply]
    _ = inner ℝ (v i) (v j) := b.repr.inner_map_map _ _
    _ = _ := hv_inner i j

/-- Zero padding preserves the exact regular Gram matrix. -/
theorem exists_regularSimplexGram_of_le {m d N : ℕ} (hdN : d ≤ N)
    (rows : Fin m → Fin d → ℝ) (hrows : RegularSimplexGram rows) :
    ∃ larger : Fin m → Fin N → ℝ, RegularSimplexGram larger := by
  classical
  let larger (i : Fin m) (k : Fin N) : ℝ :=
    if hk : k.val < d then rows i ⟨k.val, hk⟩ else 0
  refine ⟨larger, ?_⟩
  intro i j
  have hsum := Fintype.sum_of_injective (Fin.castLE hdN)
    (Fin.castLE_injective hdN) (fun k => rows i k * rows j k)
    (fun k => larger i k * larger j k) ?_ ?_
  · rw [← hsum]
    exact hrows i j
  · intro k hk
    by_cases hkd : k.val < d
    · exfalso
      apply hk
      exact ⟨⟨k.val, hkd⟩, by ext; rfl⟩
    · simp [larger, hkd]
  · intro k
    simp [larger, k.isLt]

/-- The existential reference in the main target is inhabited in every
ambient dimension allowed by its stated dimension inequality. -/
theorem exists_regularSimplexGram_main_dimensions {m n : ℕ}
    (hm : 3 ≤ m) (hdim : m - 1 ≤ n + 1) :
    ∃ rows : Fin m → Fin (n + 1) → ℝ, RegularSimplexGram rows := by
  obtain ⟨rows, hrows⟩ := exists_regularSimplexGram_minimal (m := m) (by omega)
  exact exists_regularSimplexGram_of_le hdim rows hrows

end NegativeVoting
