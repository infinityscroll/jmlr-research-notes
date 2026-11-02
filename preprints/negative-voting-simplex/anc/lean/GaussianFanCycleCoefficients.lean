import GaussianFanCycleForms
import GaussianFanCycleMoments

/-! Genuine positive Gaussian weights and the reciprocal-height coefficients
used in the finite-fan cycle factorization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem cycleEdgeWeight_pos (b : AffineBasis V ℝ E) (h : V → ℝ) (a j : V) :
    0 < cycleEdgeWeight b h a j := by
  unfold cycleEdgeWeight
  split_ifs with hij
  · norm_num
  · exact div_pos (stratumMassAt_pos b h _ a (by simp))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij)))

theorem cycleTriangleWeight_pos (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) :
    0 < cycleTriangleWeight b h a j k := by
  unfold cycleTriangleWeight
  split_ifs with hd
  · exact div_pos (triangleContent_pos b a j k hd.1 hd.2.1.symm hd.2.2.symm)
      (stratumMassAt_pos b h _ a (by simp))
  · norm_num

theorem cycleTetrahedronWeight_nonneg (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) : 0 ≤ cycleTetrahedronWeight b h a j k l := by
  exact div_nonneg (le_of_lt (stratumMassAt_pos b h _ a (by simp))) (Real.sqrt_nonneg _)

theorem cycleTriangleWeight_swap_first (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) :
    cycleTriangleWeight b h a j k = cycleTriangleWeight b h j a k := by
  by_cases hd : a ≠ j ∧ a ≠ k ∧ j ≠ k
  · have hd' : j ≠ a ∧ j ≠ k ∧ a ≠ k := by tauto
    simp only [cycleTriangleWeight,if_pos hd,if_pos hd']
    have hs : ({a,j,k}:Set V) = {j,a,k} := by ext x; simp [or_left_comm]
    rw [triangleContent_swap_first,hs,
      stratumMassAt_independent_anchor b h {j,a,k} a j (by simp) (by simp)]
  · have hd' : ¬ (j ≠ a ∧ j ≠ k ∧ a ≠ k) := by tauto
    simp [cycleTriangleWeight,hd,hd']

theorem cycleTriangleWeight_swap_last (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) :
    cycleTriangleWeight b h a j k = cycleTriangleWeight b h a k j := by
  by_cases hd : a ≠ j ∧ a ≠ k ∧ j ≠ k
  · have hd' : a ≠ k ∧ a ≠ j ∧ k ≠ j := by tauto
    simp only [cycleTriangleWeight,if_pos hd,if_pos hd']
    have hs : ({a,j,k}:Set V) = {a,k,j} := by ext x; simp [or_comm,or_left_comm]
    rw [triangleContent_swap_last,hs]
  · have hd' : ¬ (a ≠ k ∧ a ≠ j ∧ k ≠ j) := by tauto
    simp [cycleTriangleWeight,hd,hd']

theorem cycleTriangleWeight_cyclic (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) :
    cycleTriangleWeight b h a j k = cycleTriangleWeight b h j k a := by
  rw [cycleTriangleWeight_swap_first b h a j k,cycleTriangleWeight_swap_last b h j a k]

theorem cycleTetrahedronWeight_swap_first (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) : cycleTetrahedronWeight b h a j k l = cycleTetrahedronWeight b h j a k l := by
  have hs : ({a,j,k,l}:Set V) = {j,a,k,l} := by ext x; simp [or_left_comm]
  unfold cycleTetrahedronWeight
  rw [tetrahedronContent_swap_first,hs,
    stratumMassAt_independent_anchor b h {j,a,k,l} a j (by simp) (by simp)]

theorem cycleTetrahedronWeight_swap_middle (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) : cycleTetrahedronWeight b h a j k l = cycleTetrahedronWeight b h a k j l := by
  have hs : ({a,j,k,l}:Set V) = {a,k,j,l} := by ext x; simp [or_left_comm]
  unfold cycleTetrahedronWeight
  rw [tetrahedronContent_swap_middle,hs]

theorem cycleTetrahedronWeight_swap_last (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) : cycleTetrahedronWeight b h a j k l = cycleTetrahedronWeight b h a j l k := by
  have hs : ({a,j,k,l}:Set V) = {a,j,l,k} := by ext x; simp [or_comm,or_left_comm]
  unfold cycleTetrahedronWeight
  rw [tetrahedronContent_swap_last,hs]

/-- The actual Gaussian off-diagonal coefficient, with all geometric inputs discharged. -/
theorem cycleMean_barycentric_outside (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) (haj : a ≠ j) (hka : k ≠ a) (hkj : k ≠ j)
    (hla : l ≠ a) (hlj : l ≠ j) (hlk : l ≠ k) :
    cycleMean b h a j k (barycentricOutwardVector b l) =
      cycleTriangleWeight b h a j k * cycleTetrahedronWeight b h a j k l := by
  rw [cycleMean,stratum_mean_barycentric b h {a,j,k} a l (by simp) (by simp [hla,hlj,hlk])]
  simp only [div_eq_mul_inv]
  rw [reciprocal_triple_height b a j k l haj hka hkj]
  have hs : Set.insert l ({a,j,k}:Set V) = {a,j,k,l} := by
    ext x
    change (x=l ∨ x=a ∨ x=j ∨ x=k) ↔ (x=a ∨ x=j ∨ x=k ∨ x=l)
    tauto
  rw [hs,cycleTriangleWeight,if_pos ⟨haj,hka.symm,hkj.symm⟩,cycleTetrahedronWeight]
  ring

/-- The exact facet normalization used to identify the local covariance-deficit matrix. -/
theorem cycleTriangleWeight_facet_mean (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k : V) (haj : a ≠ j) (hka : k ≠ a) (hkj : k ≠ j) :
    cycleTriangleWeight b h a j k *
      stratumMeanPairing b h {a,j} a (barycentricOutwardVector b k) =
        1/cycleEdgeWeight b h a j := by
  rw [stratum_mean_barycentric b h {a,j} a k (by simp) (by simp [hka,hkj])]
  have hs : Set.insert k ({a,j}:Set V) = {a,j,k} := by
    ext x
    change (x=k ∨ x=a ∨ x=j) ↔ (x=a ∨ x=j ∨ x=k)
    tauto
  rw [hs,cycleTriangleWeight,if_pos ⟨haj,hka.symm,hkj.symm⟩,cycleEdgeWeight,if_neg haj]
  simp only [div_eq_mul_inv]
  rw [reciprocal_pair_height b a j k haj hka hkj,norm_sub_rev (b j) (b a)]
  have hm := ne_of_gt (stratumMassAt_pos b h {a,j,k} a (by simp))
  have ht := ne_of_gt (triangleContent_pos b a j k haj hka hkj)
  field_simp

theorem cycleMean_swap_first (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k : V) (v : E) : cycleMean b h a j k v = cycleMean b h j a k v := by
  have hs : ({a,j,k}:Set V) = {j,a,k} := by ext x; simp [or_left_comm]
  unfold cycleMean
  rw [hs,stratumMeanPairing_independent_anchor b h {j,a,k} a j (by simp) (by simp)]

theorem cycleMean_cyclic (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k : V) (v : E) : cycleMean b h a j k v = cycleMean b h j k a v := by
  have hs : ({a,j,k}:Set V) = {j,k,a} := by ext x; simp [or_comm,or_left_comm]
  unfold cycleMean
  rw [hs,stratumMeanPairing_independent_anchor b h {j,k,a} a j (by simp) (by simp)]

theorem cycle_weighted_triangle_alternating (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) :
    AlternatingTriangle (fun a j k => cycleTriangleWeight b h a j k * lam a j k) := by
  constructor
  · intro a j k
    change cycleTriangleWeight b h a j k * lam a j k = -(cycleTriangleWeight b h j a k * lam j a k)
    rw [cycleTriangleWeight_swap_first b h a j k,hlam.1 a j k]
    ring
  · intro a j k
    change cycleTriangleWeight b h a j k * lam a j k = cycleTriangleWeight b h j k a * lam j k a
    rw [cycleTriangleWeight_cyclic b h a j k,hlam.2 a j k]

theorem cycle_weighted_tetrahedron_alternating (b : AffineBasis V ℝ E) (h : V → ℝ)
    (tau : V → V → V → V → ℝ) (htau : AlternatingTetrahedron tau) :
    AlternatingTetrahedron (fun a j k l => cycleTetrahedronWeight b h a j k l * tau a j k l) := by
  refine ⟨?_,?_,?_⟩
  · intro a j k l
    change cycleTetrahedronWeight b h a j k l * tau a j k l = -(cycleTetrahedronWeight b h j a k l * tau j a k l)
    rw [cycleTetrahedronWeight_swap_first b h a j k l,htau.1 a j k l]
    ring
  · intro a j k l
    change cycleTetrahedronWeight b h a j k l * tau a j k l = -(cycleTetrahedronWeight b h a k j l * tau a k j l)
    rw [cycleTetrahedronWeight_swap_middle b h a j k l,htau.2.1 a j k l]
    ring
  · intro a j k l
    change cycleTetrahedronWeight b h a j k l * tau a j k l = -(cycleTetrahedronWeight b h a j l k * tau a j l k)
    rw [cycleTetrahedronWeight_swap_last b h a j k l,htau.2.2 a j k l]
    ring

end NegativeVotingFanCycle
