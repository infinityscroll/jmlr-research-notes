import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exact finite-simplex routing loss

This file proves elementary rigidity for a simplex-valued assignment at a unique
maximizing score. Its statements are independent of the unformalized Gaussian
comparison estimates in the manuscript.
-/

namespace NegativeVoting

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegative weights with total mass one. -/
def SimplexWeights (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Loss relative to a chosen score maximizer. -/
def routingLoss (p s : ι → ℝ) (t : ι) : ℝ :=
  s t - ∑ i, p i * s i

/-- Routing loss is the sum of the nonnegative weighted score gaps. -/
theorem routingLoss_eq_sum (p s : ι → ℝ) (t : ι)
    (hp : SimplexWeights p) :
    routingLoss p s t = ∑ i, p i * (s t - s i) := by
  unfold routingLoss
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

/-- A convex mixture cannot exceed its largest score. -/
theorem routingLoss_nonneg (p s : ι → ℝ) (t : ι)
    (hp : SimplexWeights p) (hmax : ∀ i, s i ≤ s t) :
    0 ≤ routingLoss p s t := by
  rw [routingLoss_eq_sum p s t hp]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (sub_nonneg.mpr (hmax i)))

/-- Quantitative routing bound: a uniform winning-score margin charges every
unit of mass sent to a different label. No probabilistic estimate is assumed. -/
theorem routingLoss_margin_bound (p s : ι → ℝ) (t : ι) (η : ℝ)
    (hp : SimplexWeights p)
    (hmargin : ∀ i, i ≠ t → η ≤ s t - s i) :
    η * (1 - p t) ≤ routingLoss p s t := by
  have hpoint : ∀ i, p i * η ≤ p i * (s t - s i) +
      (if i = t then p t * η else 0) := by
    intro i
    by_cases hi : i = t
    · subst i; simp
    · simpa [hi] using mul_le_mul_of_nonneg_left (hmargin i hi) (hp.1 i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  rw [← Finset.sum_mul, hp.2, one_mul, Finset.sum_add_distrib,
    ← routingLoss_eq_sum p s t hp] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  nlinarith

/-- Zero routing loss puts no positive weight on a strictly inferior score. -/
theorem weight_eq_zero_of_zero_routingLoss
    (p s : ι → ℝ) (t j : ι)
    (hp : SimplexWeights p) (hmax : ∀ i, s i ≤ s t)
    (hloss : routingLoss p s t = 0) (hj : s j < s t) : p j = 0 := by
  have hsum : ∑ i, p i * (s t - s i) = 0 := by
    rw [← routingLoss_eq_sum p s t hp]
    exact hloss
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ p i * (s t - s i) :=
    fun i _ => mul_nonneg (hp.1 i) (sub_nonneg.mpr (hmax i))
  have hterm : p j * (s t - s j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (sub_pos.mpr hj))

/-- At a unique winner, zero routing loss forces the entire simplex-valued
assignment to be the winner's indicator vector. -/
theorem simplex_routing_rigidity (p s : ι → ℝ) (t : ι)
    (hp : SimplexWeights p)
    (hunique : ∀ i, i ≠ t → s i < s t)
    (hloss : routingLoss p s t = 0) :
    ∀ i, p i = if i = t then 1 else 0 := by
  have hmax : ∀ i, s i ≤ s t := by
    intro i
    by_cases h : i = t
    · subst i; exact le_rfl
    · exact le_of_lt (hunique i h)
  have hzero : ∀ i, i ≠ t → p i = 0 := by
    intro i hi
    exact weight_eq_zero_of_zero_routingLoss p s t i hp hmax hloss (hunique i hi)
  have ht : p t = 1 := by
    have hsum : ∑ i, p i = p t := by
      apply Finset.sum_eq_single t
      · intro b _ hbt
        exact hzero b hbt
      · intro h
        exact False.elim (h (Finset.mem_univ t))
    exact hsum.symm.trans hp.2
  intro i
  by_cases hi : i = t
  · subst i; simp [ht]
  · simp [hi, hzero i hi]

end NegativeVoting

namespace NegativeVoting

open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Measure-theoretic rigidity: an integrable, nonnegative routing loss with
zero integral forces almost every assignment to choose its unique winning score.
No Gaussian structure is assumed or needed in this general lemma. -/
theorem ae_pure_of_zero_integrated_routing_loss
    (μ : Measure Ω) (p s : Ω → ι → ℝ) (winner : Ω → ι)
    (hp : ∀ᵐ x ∂μ, SimplexWeights (p x))
    (hunique : ∀ᵐ x ∂μ, ∀ i, i ≠ winner x → s x i < s x (winner x))
    (hintegrable : Integrable (fun x => routingLoss (p x) (s x) (winner x)) μ)
    (hzero : ∫ x, routingLoss (p x) (s x) (winner x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∀ i, p x i = if i = winner x then 1 else 0 := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => routingLoss (p x) (s x) (winner x) := by
    filter_upwards [hp, hunique] with x hpx hux
    apply routingLoss_nonneg (p x) (s x) (winner x) hpx
    intro i
    by_cases hi : i = winner x
    · simp [hi]
    · exact le_of_lt (hux i hi)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).mp hzero
  filter_upwards [hp, hunique, hae] with x hpx hux hzx
  exact simplex_routing_rigidity (p x) (s x) (winner x) hpx hux hzx

end NegativeVoting
