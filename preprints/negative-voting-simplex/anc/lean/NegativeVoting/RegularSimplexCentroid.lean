import NegativeVoting.RegularSimplexMoments

/-!
# Full Gaussian centroid direction of a regular simplex

Reflections control both the span of the score rows and its ambient orthogonal
complement. Membership of the centroid in the row span is proved from the actual
Gaussian integral, not assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NegativeVoting
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

variable {κ : Type*} [Fintype κ] {m : ℕ} [Nonempty (Fin m)]

def simplexRow (rows : Fin m → κ → ℝ) (i : Fin m) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (rows i)

def simplexCentroid (rows : Fin m → κ → ℝ) (i : Fin m) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i)

def simplexRowSpan (rows : Fin m → κ → ℝ) : Submodule ℝ (EuclideanSpace ℝ κ) :=
  Submodule.span ℝ (Set.range (simplexRow rows))

omit [Nonempty (Fin m)] in
theorem simplexRow_inner (rows : Fin m → κ → ℝ) (i : Fin m) (x : EuclideanSpace ℝ κ) :
    inner ℝ (simplexRow rows i) x = ∑ k, rows i k * x k := by
  rw [PiLp.inner_apply]
  simp only [simplexRow, Real.inner_apply]

omit [Nonempty (Fin m)] in
theorem simplexRow_gram (rows : Fin m → κ → ℝ) (hrows : RegularSimplexGram rows)
    (i j : Fin m) : inner ℝ (simplexRow rows i) (simplexRow rows j) =
      (if i = j then 1 else 0) - 1 / (m : ℝ) := by
  rw [simplexRow_inner]
  exact hrows i j

/-- The Euclidean centroid pairing is the actual Gaussian first-moment integral. -/
theorem simplexCentroid_inner_integral (rows : Fin m → κ → ℝ) (i : Fin m)
    (v : EuclideanSpace ℝ κ) :
    inner ℝ (simplexCentroid rows i) v =
      ∫ x : EuclideanSpace ℝ κ, regularAssignment rows x.ofLp i * inner ℝ v x
        ∂stdGaussian (EuclideanSpace ℝ κ) := by
  classical
  have hint (k : κ) : Integrable (fun x => regularAssignment rows x i * x k)
      (standardGaussian κ) :=
    integrable_weighted_score (standardGaussian κ) (regularAssignment rows)
      (fun x _ => x k) i (Filter.Eventually.of_forall (regularAssignment_simplex rows))
      (regularAssignment_measurable rows i).aemeasurable
      (gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) k)
  calc
    _ = ∑ k, v k * gaussianCentroid (fun _ => 0) (fun _ => 1)
        (regularAssignment rows) i k := by
      rw [PiLp.inner_apply]
      simp only [simplexCentroid, Real.inner_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = ∫ x, regularAssignment rows x i * (∑ k, v k * x k)
        ∂standardGaussian κ := by
      rw [show (fun x => regularAssignment rows x i * (∑ k, v k * x k)) =
        (fun x => ∑ k, v k * (regularAssignment rows x i * x k)) by
          funext x
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring]
      rw [integral_finsetSum Finset.univ (fun k _ => (hint k).const_mul (v k))]
      simp only [integral_const_mul, gaussianCentroid, standardGaussian]
    _ = _ := by
      rw [integral_standardGaussian_eq_euclidean]
      congr 1
      funext x
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply]

theorem regularAssignment_isometry_permutation (rows : Fin m → κ → ℝ)
    (R : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (hsymm : R.symm = R) (e : Equiv.Perm (Fin m))
    (hR : ∀ k, R (simplexRow rows k) = simplexRow rows (e k))
    (x : EuclideanSpace ℝ κ) (i : Fin m) :
    regularAssignment rows (R x).ofLp i = regularAssignment rows x.ofLp (e i) := by
  have hscore (k : Fin m) : (∑ l, rows k l * (R x) l) = ∑ l, rows (e k) l * x l := by
    rw [← simplexRow_inner, ← simplexRow_inner]
    calc
      inner ℝ (simplexRow rows k) (R x) = inner ℝ (R (simplexRow rows k)) x := by
        simpa only [hsymm] using (R.inner_map_eq_flip (simplexRow rows k) x).symm
      _ = _ := by rw [hR]
  unfold regularAssignment
  simp_rw [hscore]
  exact maxWeights_perm (fun k => ∑ l, rows k l * x l) e i

/-- If a Gaussian-preserving reflection fixes the assignment and reverses v,
the actual centroid has zero component along v. -/
theorem simplexCentroid_orthogonal_of_reflection (rows : Fin m → κ → ℝ) (i : Fin m)
    (R : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (hsymm : R.symm = R) (v : EuclideanSpace ℝ κ) (hv : R v = -v)
    (hp : ∀ x, regularAssignment rows (R x).ofLp i = regularAssignment rows x.ofLp i) :
    inner ℝ (simplexCentroid rows i) v = 0 := by
  have hR : MeasurePreserving R (stdGaussian (EuclideanSpace ℝ κ))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨R.continuous.measurable, stdGaussian_map R⟩
  have hinner (x : EuclideanSpace ℝ κ) : inner ℝ v (R x) = -inner ℝ v x := by
    calc
      inner ℝ v (R x) = inner ℝ (R v) x := by
        simpa only [hsymm] using (R.inner_map_eq_flip v x).symm
      _ = _ := by rw [hv, inner_neg_left]
  have hsame := hR.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => regularAssignment rows x.ofLp i * inner ℝ v x)
  simp only [hp, hinner, mul_neg, integral_neg] at hsame
  rw [simplexCentroid_inner_integral]
  linarith

omit [Nonempty (Fin m)] in
theorem simplexRowSpan_orthogonal_iff (rows : Fin m → κ → ℝ) (v : EuclideanSpace ℝ κ) :
    v ∈ (simplexRowSpan rows)ᗮ ↔ ∀ j, inner ℝ v (simplexRow rows j) = 0 := by
  constructor
  · intro hv j
    exact (Submodule.mem_orthogonal' _ _).mp hv _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro h
    have hle : simplexRowSpan rows ≤ (ℝ ∙ v)ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (h j)
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hw)

/-- The ambient orthogonal-complement component vanishes by an actual Gaussian
reflection; the centroid's row-span membership is not a premise. -/
theorem simplexCentroid_mem_rowSpan (rows : Fin m → κ → ℝ) (i : Fin m) :
    simplexCentroid rows i ∈ simplexRowSpan rows := by
  have hperp : simplexCentroid rows i ∈ (simplexRowSpan rows)ᗮᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro v hv
    let R := (ℝ ∙ v)ᗮ.reflection
    have hrows (j : Fin m) : R (simplexRow rows j) = simplexRow rows j := by
      apply Submodule.reflection_mem_subspace_eq_self
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        ((simplexRowSpan_orthogonal_iff rows v).mp hv j)
    apply simplexCentroid_orthogonal_of_reflection rows i R (by rfl) v
      (Submodule.reflection_orthogonalComplement_singleton_eq_neg v)
    intro x
    exact regularAssignment_isometry_permutation rows R (by rfl) (Equiv.refl _) hrows x i
  simpa only [Submodule.orthogonal_orthogonal] using hperp

def simplexSwap (rows : Fin m → κ → ℝ) (j k : Fin m) :
    EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
  (ℝ ∙ (simplexRow rows j - simplexRow rows k))ᗮ.reflection

omit [Nonempty (Fin m)] in
theorem simplexSwap_row (rows : Fin m → κ → ℝ) (hrows : RegularSimplexGram rows)
    (j k l : Fin m) : simplexSwap rows j k (simplexRow rows l) =
      simplexRow rows (Equiv.swap j k l) := by
  classical
  have hn : ‖simplexRow rows j‖ = ‖simplexRow rows k‖ := by
    have hj := simplexRow_gram rows hrows j j
    have hk := simplexRow_gram rows hrows k k
    rw [real_inner_self_eq_norm_sq] at hj hk
    simp only [ite_true] at hj hk
    nlinarith [norm_nonneg (simplexRow rows j), norm_nonneg (simplexRow rows k)]
  have hRj : simplexSwap rows j k (simplexRow rows j) = simplexRow rows k :=
    Submodule.reflection_sub hn
  have hRk : simplexSwap rows j k (simplexRow rows k) = simplexRow rows j := by
    rw [← hRj]
    exact Submodule.reflection_reflection _ _
  by_cases hlj : l = j
  · subst l
    simpa using hRj
  · by_cases hlk : l = k
    · subst l
      simpa using hRk
    · have hl : simplexRow rows l ∈ (ℝ ∙ (simplexRow rows j - simplexRow rows k))ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right,
          simplexRow_gram rows hrows, simplexRow_gram rows hrows]
        simp [hlj, hlk]
      simpa [simplexSwap, Equiv.swap_apply_of_ne_of_ne hlj hlk] using
        Submodule.reflection_mem_subspace_eq_self hl

/-- Permutations of the other labels force orthogonality to their row differences. -/
theorem simplexCentroid_other_difference (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (i j k : Fin m) (hji : j ≠ i) (hki : k ≠ i) :
    inner ℝ (simplexCentroid rows i) (simplexRow rows j - simplexRow rows k) = 0 := by
  apply simplexCentroid_orthogonal_of_reflection rows i (simplexSwap rows j k) (by rfl)
    (simplexRow rows j - simplexRow rows k)
    (Submodule.reflection_orthogonalComplement_singleton_eq_neg _)
  intro x
  simpa only [Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki)] using
    regularAssignment_isometry_permutation rows (simplexSwap rows j k) (by rfl)
      (Equiv.swap j k) (simplexSwap_row rows hrows j k) x i

theorem simplexRows_sum_zero (rows : Fin m → κ → ℝ) (hrows : RegularSimplexGram rows) :
    (∑ j, simplexRow rows j) = 0 := by
  classical
  have hmpos : 0 < m := Fin.pos_iff_nonempty.mpr inferInstance
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hinner (k : Fin m) : inner ℝ (∑ j, simplexRow rows j) (simplexRow rows k) = 0 := by
    rw [sum_inner]
    simp_rw [simplexRow_gram rows hrows]
    simp [Finset.sum_sub_distrib, hmne]
  have hzero : inner ℝ (∑ j, simplexRow rows j) (∑ j, simplexRow rows j) = 0 := by
    rw [inner_sum]
    simp only [hinner, Finset.sum_const_zero]
  exact inner_self_eq_zero.mp hzero

/-- Full vector proportionality, with the ambient orthogonal complement
eliminated by Gaussian reflection and the scalar fixed by the actual maximum. -/
theorem simplexCentroid_eq_smul_row (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (hm : 3 ≤ m) (i : Fin m) :
    simplexCentroid rows i =
      ((∫ x, maxScore (fun j => ∑ k, rows j k * x k) ∂standardGaussian κ) /
        ((m : ℝ) - 1)) • simplexRow rows i := by
  classical
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hm1pos : 0 < (m : ℝ) - 1 := by exact_mod_cast (show 0 < (m : ℤ) - 1 by omega)
  have hm1ne : (m : ℝ) - 1 ≠ 0 := ne_of_gt hm1pos
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hji⟩ := exists_ne i
  let C := simplexCentroid rows i
  let d := inner ℝ C (simplexRow rows i)
  let b := inner ℝ C (simplexRow rows j)
  have hother (k : Fin m) (hki : k ≠ i) : inner ℝ C (simplexRow rows k) = b := by
    have hh := simplexCentroid_other_difference rows hrows i k j hki hji
    rw [inner_sub_right] at hh
    exact sub_eq_zero.mp hh
  have hcoeff (k : Fin m) :
      inner ℝ C (simplexRow rows k) = b + if k = i then d - b else 0 := by
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
      dsimp [d]
      ring
    · simpa only [hki, ite_false, add_zero] using hother k hki
  have hsum : (m : ℝ) * b + (d - b) = 0 := by
    have hh : (∑ k, inner ℝ C (simplexRow rows k)) = 0 := by
      rw [← inner_sum, simplexRows_sum_zero rows hrows, inner_zero_right]
    simp_rw [hcoeff] at hh
    simpa [Finset.sum_add_distrib] using hh
  have hzrow (k : Fin m) :
      inner ℝ (C - (d - b) • simplexRow rows i) (simplexRow rows k) = 0 := by
    rw [inner_sub_left, real_inner_smul_left, simplexRow_gram rows hrows]
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
      change d - (d - b) * (1 - 1 / (m : ℝ)) = 0
      field_simp
      nlinarith [hsum]
    · rw [hother k hki]
      simp only [Ne.symm hki, ite_false]
      field_simp
      nlinarith [hsum]
  have hzspan : C - (d - b) • simplexRow rows i ∈ simplexRowSpan rows :=
    (simplexRowSpan rows).sub_mem (simplexCentroid_mem_rowSpan rows i)
      ((simplexRowSpan rows).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  have hzorth := (simplexRowSpan_orthogonal_iff rows _).mpr hzrow
  have hzinner : inner ℝ (C - (d - b) • simplexRow rows i)
      (C - (d - b) • simplexRow rows i) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hzspan hzorth
  have hC : C = (d - b) • simplexRow rows i := sub_eq_zero.mp (inner_self_eq_zero.mp hzinner)
  let W := ∫ x, maxScore (fun j => ∑ k, rows j k * x k) ∂standardGaussian κ
  have hd : d = W / (m : ℝ) := by
    calc
      d = ∑ k, rows i k * gaussianCentroid (fun _ => 0) (fun _ => 1)
          (regularAssignment rows) i k := by
        dsimp [d, C]
        rw [PiLp.inner_apply]
        simp only [simplexCentroid, simplexRow, Real.inner_apply]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      _ = _ := regularAssignment_centroid_projection rows hrows i
  have hscalar : d - b = W / ((m : ℝ) - 1) := by
    apply (eq_div_iff hm1ne).mpr
    have hd' := (eq_div_iff hmne).mp hd
    nlinarith [hsum, hd']
  rw [hscalar] at hC
  exact hC

theorem regularAssignment_centroid_direction (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (hm : 3 ≤ m) (i : Fin m) (k : κ) :
    gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i k =
      ((∫ x, maxScore (fun j => ∑ l, rows j l * x l) ∂standardGaussian κ) /
        ((m : ℝ) - 1)) * rows i k := by
  have h := congrArg (fun x : EuclideanSpace ℝ κ => x k)
    (simplexCentroid_eq_smul_row rows hrows hm i)
  simpa only [simplexCentroid, simplexRow, PiLp.smul_apply, smul_eq_mul] using h

/-- Coordinate form of the full centroid identity for the actual Gaussian
integral, with no row-span or symmetry-of-moments premise. -/
theorem regularAssignment_first_moment (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (hm : 3 ≤ m) (i : Fin m) (k : κ) :
    (∫ x, x k * regularAssignment rows x i ∂standardGaussian κ) =
      ((∫ x, maxScore (fun j => ∑ l, rows j l * x l) ∂standardGaussian κ) /
        ((m : ℝ) - 1)) * rows i k := by
  calc
    _ = gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i k := by
      unfold gaussianCentroid
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _
    _ = _ := regularAssignment_centroid_direction rows hrows hm i k

theorem regularSimplexGram_energy (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) :
    (∑ i, ∑ k, (rows i k) ^ 2) = (m : ℝ) - 1 := by
  have hmpos : 0 < m := Fin.pos_iff_nonempty.mpr inferInstance
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hdiag (i : Fin m) : (∑ k, (rows i k) ^ 2) = 1 - 1 / (m : ℝ) := by
    simpa only [pow_two, ite_true] using hrows i i
  simp_rw [hdiag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The exact squared Frobenius centroid norm, hence the reference's first
Gaussian chaos energy under the concrete spectral identification. -/
theorem regularAssignment_centroid_energy (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (hm : 3 ≤ m) :
    (∑ i, ∑ k,
      (gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i k) ^ 2) =
      (∫ x, maxScore (fun j => ∑ l, rows j l * x l) ∂standardGaussian κ) ^ 2 /
        ((m : ℝ) - 1) := by
  have hm1pos : 0 < (m : ℝ) - 1 := by exact_mod_cast (show 0 < (m : ℤ) - 1 by omega)
  have hm1ne : (m : ℝ) - 1 ≠ 0 := ne_of_gt hm1pos
  simp_rw [regularAssignment_centroid_direction rows hrows hm, mul_pow]
  let W := ∫ x, maxScore (fun j => ∑ l, rows j l * x l) ∂standardGaussian κ
  change (∑ i, ∑ k, (W / ((m : ℝ) - 1)) ^ 2 * (rows i k) ^ 2) =
    W ^ 2 / ((m : ℝ) - 1)
  calc
    _ = (W / ((m : ℝ) - 1)) ^ 2 * (∑ i, ∑ k, (rows i k) ^ 2) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [regularSimplexGram_energy rows hrows]
      field_simp

end NegativeVoting
