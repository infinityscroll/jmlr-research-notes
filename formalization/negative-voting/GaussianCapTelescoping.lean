import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Exact finite replacement identity for moving cap indicators. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace NegativeVotingCapTelescoping

private def hybrid {n : ℕ} (a b : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∏ i, if i.val < k then a i else b i

private theorem hybrid_step {n : ℕ} (a b : Fin n → ℝ) (j : Fin n) :
    hybrid a b (j.val + 1) - hybrid a b j.val =
      (a j - b j) * ∏ i ∈ Finset.univ.erase j,
        if i.val < j.val then a i else b i := by
  classical
  have hprod : (∏ i ∈ Finset.univ.erase j,
      if i.val < j.val + 1 then a i else b i) =
      ∏ i ∈ Finset.univ.erase j, if i.val < j.val then a i else b i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    have he : (i.val < j.val + 1) = (i.val < j.val) := propext (by omega)
    simp only [he]
  unfold hybrid
  rw [← Finset.mul_prod_erase _ (fun i : Fin n => if i.val < j.val + 1 then a i else b i)
    (Finset.mem_univ j)]
  rw [← Finset.mul_prod_erase _ (fun i : Fin n => if i.val < j.val then a i else b i)
    (Finset.mem_univ j)]
  simp only [Nat.lt_succ_self, ↓reduceIte, lt_self_iff_false]
  rw [hprod]
  ring

/-- Simultaneous finite replacements decompose into one changing factor at a time. -/
theorem prod_difference {n : ℕ} (a b : Fin n → ℝ) :
    (∏ i, a i) - (∏ i, b i) =
      ∑ j, (a j - b j) * ∏ i ∈ Finset.univ.erase j,
        if i.val < j.val then a i else b i := by
  classical
  have htel := Finset.sum_range_sub (hybrid a b) n
  rw [← Fin.sum_univ_eq_sum_range] at htel
  simp only [hybrid_step] at htel
  simpa [hybrid] using htel.symm

/-- The intersection indicator is the product of the literal constraint indicators. -/
theorem indicator_iInter_eq_prod {X : Type*} {n : ℕ}
    (C : Fin n → Set X) (x : X) :
    (⋂ i, C i).indicator (fun _ => (1 : ℝ)) x =
      ∏ i, (C i).indicator (fun _ => (1 : ℝ)) x := by
  classical
  have hone : ((fun _ : X => (1 : ℝ)) ^ n) = (fun _ => 1) := by
    funext y
    simp [Pi.pow_apply]
  simpa [hone] using (prod_indicator_apply Finset.univ C (fun _ _ => (1 : ℝ)) x).symm

/-- Pointwise moving-cap decomposition. The other factors are genuinely mixed
old/new constraints, not assumed fixed while all constraints move. -/
theorem indicator_intersection_difference {X : Type*} {n : ℕ}
    (C D : Fin n → Set X) (x : X) :
    (⋂ i, C i).indicator (fun _ => (1 : ℝ)) x -
      (⋂ i, D i).indicator (fun _ => (1 : ℝ)) x =
    ∑ j, ((C j).indicator (fun _ => (1 : ℝ)) x -
      (D j).indicator (fun _ => (1 : ℝ)) x) *
      ∏ i ∈ Finset.univ.erase j,
        if i.val < j.val then (C i).indicator (fun _ => (1 : ℝ)) x
        else (D i).indicator (fun _ => (1 : ℝ)) x := by
  rw [indicator_iInter_eq_prod, indicator_iInter_eq_prod]
  exact prod_difference _ _


/-- The mixed remaining product is the literal conjunction of the other caps. -/
theorem remaining_product_eq_mask {X : Type*} {n : ℕ}
    (C D : Fin n → Set X) (j : Fin n) (x : X) :
    (∏ i ∈ Finset.univ.erase j,
      if i.val < j.val then (C i).indicator (fun _ => (1 : ℝ)) x
      else (D i).indicator (fun _ => (1 : ℝ)) x) =
    if ∀ i, i ≠ j → x ∈ (if i.val < j.val then C i else D i)
    then 1 else 0 := by
  classical
  let K : Fin n → Set X := fun i => if i.val < j.val then C i else D i
  have hp : (∏ i ∈ Finset.univ.erase j,
      if i.val < j.val then (C i).indicator (fun _ => (1 : ℝ)) x
      else (D i).indicator (fun _ => (1 : ℝ)) x) =
      ∏ i ∈ Finset.univ.erase j, (K i).indicator (fun _ => (1 : ℝ)) x := by
    apply Finset.prod_congr rfl
    intro i _
    dsimp [K]
    split_ifs <;> rfl
  rw [hp, prod_indicator_apply]
  simp [Set.indicator, K]

/-- The form used by moving-slab differentiation: one changing indicator
multiplied by the conjunction of genuinely mixed remaining constraints. -/
theorem cap_difference_as_moving_slabs {X : Type*} {n : ℕ}
    (C D : Fin n → Set X) (x : X) :
    (⋂ i, C i).indicator (fun _ => (1 : ℝ)) x -
      (⋂ i, D i).indicator (fun _ => (1 : ℝ)) x =
    ∑ j, ((C j).indicator (fun _ => (1 : ℝ)) x -
      (D j).indicator (fun _ => (1 : ℝ)) x) *
      (if ∀ i, i ≠ j → x ∈ (if i.val < j.val then C i else D i)
       then 1 else 0) := by
  rw [indicator_intersection_difference]
  apply Finset.sum_congr rfl
  intro j _
  rw [remaining_product_eq_mask]


private theorem iInter_reindex {X ι : Type*} {n : ℕ}
    (e : ι ≃ Fin n) (C : ι → Set X) :
    (⋂ k, C (e.symm k)) = (⋂ i, C i) := by
  ext x
  simp only [Set.mem_iInter]
  exact e.symm.forall_congr_right (q := fun i => x ∈ C i)

/-- Reindexed statement preserves arbitrary finite constraint indices,
including subtypes of fan labels and the empty constraint family. -/
theorem cap_difference_as_moving_slabs_equiv {X ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (C D : ι → Set X) (x : X) :
    (⋂ i, C i).indicator (fun _ => (1 : ℝ)) x -
      (⋂ i, D i).indicator (fun _ => (1 : ℝ)) x =
    ∑ j, ((C j).indicator (fun _ => (1 : ℝ)) x -
      (D j).indicator (fun _ => (1 : ℝ)) x) *
      (if ∀ i, i ≠ j → x ∈ (if (e i).val < (e j).val then C i else D i)
       then 1 else 0) := by
  classical
  have h := cap_difference_as_moving_slabs
    (fun k => C (e.symm k)) (fun k => D (e.symm k)) x
  rw [iInter_reindex, iInter_reindex, ← e.sum_comp] at h
  simp only [Equiv.symm_apply_apply] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  have hall :
      (∀ k : Fin n, k ≠ e j → x ∈
        (if k.val < (e j).val then C (e.symm k) else D (e.symm k))) ↔
      (∀ i : ι, i ≠ j → x ∈
        (if (e i).val < (e j).val then C i else D i)) := by
    constructor
    · intro hh i hi
      simpa using hh (e i) (fun he => hi (e.injective he))
    · intro hh k hk
      have hi : e.symm k ≠ j := by
        intro he
        apply hk
        simpa using congrArg e he
      simpa using hh (e.symm k) hi
  simp only [hall]

end NegativeVotingCapTelescoping
