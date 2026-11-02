import Mathlib
import NegativeVoting.GaussianMoments

/-!
# Concrete regular-simplex classifiers

Tie weights are divided equally among maximizers. This supplies an everywhere
measurable simplex assignment without making an arbitrary choice on tie sets.
For a regular Gram matrix these ties have Gaussian measure zero.
-/
namespace NegativeVoting
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def maxScore {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty s

noncomputable def maxIndicator {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if s i = maxScore s then 1 else 0

noncomputable def maxMultiplicity {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) : ℝ := ∑ i, maxIndicator s i

noncomputable def maxWeights {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (i : ι) : ℝ := maxIndicator s i / maxMultiplicity s

theorem maxIndicator_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (i : ι) : 0 ≤ maxIndicator s i := by
  classical
  unfold maxIndicator
  split_ifs <;> norm_num

theorem maxMultiplicity_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) : 0 < maxMultiplicity s := by
  classical
  have hw : s (chosenWinner s) = maxScore s :=
    (finite_max_eq_chosenWinner s).symm
  have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    maxIndicator_nonneg s i) (Finset.mem_univ (chosenWinner s))
  have hwin : maxIndicator s (chosenWinner s) = 1 := by simp [maxIndicator, hw]
  rw [hwin] at hle
  exact lt_of_lt_of_le zero_lt_one hle

theorem maxWeights_simplex {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) : SimplexWeights (maxWeights s) := by
  classical
  constructor
  · intro i
    exact div_nonneg (maxIndicator_nonneg s i) (le_of_lt (maxMultiplicity_pos s))
  · simp only [maxWeights, ← Finset.sum_div]
    exact div_self (ne_of_gt (maxMultiplicity_pos s))

theorem measurable_finite_max {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (s : Ω → ι → ℝ)
    (t : Finset ι) (hne : t.Nonempty) (hs : ∀ i ∈ t, Measurable (fun x => s x i)) :
    Measurable (fun x => t.sup' hne (s x)) := by
  induction t using Finset.induction_on with
  | empty => simp at hne
  | @insert a t ha ih =>
    by_cases ht : t.Nonempty
    · have hi := ih ht (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      have hai := hs a (Finset.mem_insert_self a t)
      simpa only [Finset.sup'_insert ht, Pi.sup_def] using hai.sup hi
    · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      simpa using hs a (Finset.mem_singleton_self a)

theorem measurable_maxWeights {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (s : Ω → ι → ℝ)
    (hs : ∀ i, Measurable (fun x => s x i)) (i : ι) :
    Measurable (fun x => maxWeights (s x) i) := by
  classical
  have hm : Measurable (fun x => maxScore (s x)) :=
    measurable_finite_max s Finset.univ Finset.univ_nonempty (fun i _ => hs i)
  have hi (j : ι) : Measurable (fun x => maxIndicator (s x) j) := by
    exact Measurable.ite (measurableSet_eq_fun (hs j) hm) measurable_const measurable_const
  exact (hi i).div (Finset.measurable_sum Finset.univ (fun j _ => hi j))

theorem maxWeights_eq_indicator_of_strict_max {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (s : ι → ℝ) (t : ι) (ht : ∀ i, i ≠ t → s i < s t) :
    ∀ i, maxWeights s i = if i = t then 1 else 0 := by
  classical
  have hmax : maxScore s = s t := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => by
        by_cases h : i = t
        · simp [h]
        · exact le_of_lt (ht i h))
    · exact Finset.le_sup' s (Finset.mem_univ t)
  have hi (i : ι) : maxIndicator s i = if i = t then 1 else 0 := by
    by_cases h : i = t
    · simp [maxIndicator, h, hmax]
    · simp [maxIndicator, hmax, h, ne_of_lt (ht i h)]
  have hd : maxMultiplicity s = 1 := by simp [maxMultiplicity, hi]
  intro i
  simp [maxWeights, hi, hd]

/-- The unit projection Gram matrix has diagonal 1-1/m and off-diagonal -1/m.
Its positive scalar multiples give the same winning partition. -/
def RegularSimplexGram {κ : Type*} [Fintype κ] {m : ℕ}
    (rows : Fin m → κ → ℝ) : Prop :=
  ∀ i j, (∑ k, rows i k * rows j k) = (if i = j then 1 else 0) - 1 / (m : ℝ)

theorem regularSimplexGram_injective {κ : Type*} [Fintype κ] {m : ℕ}
    (rows : Fin m → κ → ℝ) (h : RegularSimplexGram rows) :
    Function.Injective rows := by
  intro i j hij
  by_contra hne
  have hd := h i i
  have ho := h i j
  rw [← hij] at ho
  simp only [ite_true] at hd
  simp only [if_neg hne] at ho
  linarith

noncomputable def regularAssignment {κ : Type*} [Fintype κ] {m : ℕ}
    [Nonempty (Fin m)] (rows : Fin m → κ → ℝ) (x : κ → ℝ) : Fin m → ℝ :=
  maxWeights (fun i => ∑ j, rows i j * x j)

theorem regularAssignment_simplex {κ : Type*} [Fintype κ] {m : ℕ}
    [Nonempty (Fin m)] (rows : Fin m → κ → ℝ) (x : κ → ℝ) :
    SimplexWeights (regularAssignment rows x) := maxWeights_simplex _

theorem regularAssignment_measurable {κ : Type*} [Fintype κ] {m : ℕ}
    [Nonempty (Fin m)] (rows : Fin m → κ → ℝ) (i : Fin m) :
    Measurable (fun x => regularAssignment rows x i) := by
  apply measurable_maxWeights
  intro k
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).const_mul _)

theorem ae_regularAssignment_indicator {n m : ℕ} [Nonempty (Fin m)]
    (rows : Fin m → Fin (n + 1) → ℝ) (h : RegularSimplexGram rows) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1),
      ∃ t, (∀ i, regularAssignment rows x i = if i = t then 1 else 0) ∧
        (∀ i, i ≠ t → linearScore (rows i) x < linearScore (rows t) x) := by
  filter_upwards [ae_gaussian_unique_max (fun _ => 0) (fun _ => 1)
    (fun _ => one_ne_zero) rows (regularSimplexGram_injective rows h)] with x hx
  obtain ⟨t, ht⟩ := hx
  exact ⟨t, maxWeights_eq_indicator_of_strict_max _ t ht, ht⟩

end NegativeVoting
