import NegativeVoting.Routing
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Integrability of finite scores and fractional routing

These lemmas discharge the integrability premise of routing rigidity whenever the
individual scores are integrable and the assignment is measurable and simplex-valued.
They hold for arbitrary measures and require no smoothness of the assignment.
-/

namespace NegativeVoting

open MeasureTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Each coordinate of a simplex vector belongs to `[0,1]`. -/
theorem simplex_weight_le_one (p : ι → ℝ) (hp : SimplexWeights p) (i : ι) : p i ≤ 1 := by
  calc
    p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
    _ = 1 := hp.2

/-- A measurable fractional assignment times an integrable score is integrable;
the simplex constraint supplies the essential bound on each weight. -/
theorem integrable_weighted_score (μ : Measure Ω) (p s : Ω → ι → ℝ) (i : ι)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (p x))
    (hpmeas : AEMeasurable (fun x => p x i) μ)
    (hs : Integrable (fun x => s x i) μ) :
    Integrable (fun x => p x i * s x i) μ := by
  apply hs.bdd_mul' hpmeas.aestronglyMeasurable
  filter_upwards [hp] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
  exact simplex_weight_le_one (p x) hx i

/-- The finite fractional score mixture is integrable. -/
theorem integrable_score_mixture (μ : Measure Ω) (p s : Ω → ι → ℝ)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i) μ)
    (hs : ∀ i, Integrable (fun x => s x i) μ) :
    Integrable (fun x => ∑ i, p x i * s x i) μ := by
  exact integrable_finset_sum Finset.univ (fun i _ =>
    integrable_weighted_score μ p s i hp (hpmeas i) (hs i))

/-- The maximum of any nonempty finite collection of integrable scores is
integrable. The statement uses an actual finite maximum, not a bound hypothesis. -/
theorem integrable_finite_max (μ : Measure Ω) (s : Ω → ι → ℝ)
    (t : Finset ι) (hne : t.Nonempty)
    (hs : ∀ i ∈ t, Integrable (fun x => s x i) μ) :
    Integrable (fun x => t.sup' hne (s x)) μ := by
  induction t using Finset.induction_on with
  | empty => simp at hne
  | @insert a t ha ih =>
    by_cases ht : t.Nonempty
    · have hi := ih ht (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      have hai := hs a (Finset.mem_insert_self a t)
      simpa only [Finset.sup'_insert ht, Pi.sup_apply] using hai.sup hi
    · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      simpa using hs a (Finset.mem_singleton_self a)

/-- If a measurable selected score is pointwise a maximum, routing loss is
integrable. This removes the separate integrability premise used by the basic
zero-integral rigidity lemma. -/
theorem integrable_routing_loss [Nonempty ι]
    (μ : Measure Ω) (p s : Ω → ι → ℝ) (winner : Ω → ι)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i) μ)
    (hs : ∀ i, Integrable (fun x => s x i) μ)
    (hmax : ∀ᵐ x ∂μ, ∀ i, s x i ≤ s x (winner x)) :
    Integrable (fun x => routingLoss (p x) (s x) (winner x)) μ := by
  have hmaxint := integrable_finite_max μ s Finset.univ Finset.univ_nonempty
    (fun i _ => hs i)
  have hwinner : Integrable (fun x => s x (winner x)) μ := by
    apply hmaxint.congr
    filter_upwards [hmax] with x hx
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => hx i)
    · exact Finset.le_sup' (s x) (Finset.mem_univ (winner x))
  exact hwinner.sub (integrable_score_mixture μ p s hp hpmeas hs)

/-- Full generic routing rigidity with its integrability established from the
score functions and the measurable simplex assignment. -/
theorem ae_pure_of_integrable_scores [Nonempty ι]
    (μ : Measure Ω) (p s : Ω → ι → ℝ) (winner : Ω → ι)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i) μ)
    (hs : ∀ i, Integrable (fun x => s x i) μ)
    (hunique : ∀ᵐ x ∂μ, ∀ i, i ≠ winner x → s x i < s x (winner x))
    (hzero : ∫ x, routingLoss (p x) (s x) (winner x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∀ i, p x i = if i = winner x then 1 else 0 := by
  have hmax : ∀ᵐ x ∂μ, ∀ i, s x i ≤ s x (winner x) := by
    filter_upwards [hunique] with x hx
    intro i
    by_cases hi : i = winner x
    · simp [hi]
    · exact le_of_lt (hx i hi)
  exact ae_pure_of_zero_integrated_routing_loss μ p s winner hp hunique
    (integrable_routing_loss μ p s winner hp hpmeas hs hmax) hzero

end NegativeVoting
