import Mathlib

/-!
# Infinite signed spectral tails

These results prove convergence and tail comparison for genuine infinite
series, including orthonormal coefficient families whose finite energy is
derived from Bessel's inequality. They do not identify a Gaussian Hermite
basis or prove the Mehler representation of noise stability.
-/

noncomputable section

open scoped BigOperators

namespace NegativeVoting

/-- Finite nonnegative energy implies absolute convergence of the full
signed chaos series, including negative correlation. -/
theorem chaos_series_absolutely_summable (A : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (henergy : Summable A)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    Summable (fun k => ‖ρ ^ k * A k‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ henergy
  intro k
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hA k)]
  exact mul_le_of_le_one_left (hA k) (pow_le_one₀ (abs_nonneg ρ) hρ)

/-- The infinite series separates its first three degrees exactly. -/
theorem chaos_series_split_three (A : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (henergy : Summable A)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    (∑' k, ρ ^ k * A k) = A 0 + ρ * A 1 + ρ ^ 2 * A 2 +
      ∑' k, ρ ^ (k + 3) * A (k + 3) := by
  have hs := (chaos_series_absolutely_summable A hA henergy ρ hρ).of_norm
  have h := hs.sum_add_tsum_nat_add 3
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_assoc] using h.symm

/-- Absolute tail control from the actual summable energy sequence. -/
theorem chaos_tail_abs_le (A : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (henergy : Summable A)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (K : ℕ) :
    |∑' k, ρ ^ (k + K) * A (k + K)| ≤
      |ρ| ^ K * ∑' k, A (k + K) := by
  have hshift : Summable (fun k => A (k + K)) :=
    henergy.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hmajor := hshift.mul_left (|ρ| ^ K)
  have hb : ∀ k, ‖ρ ^ (k + K) * A (k + K)‖ ≤
      |ρ| ^ K * A (k + K) := by
    intro k
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (hA _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (abs_nonneg ρ) hρ (Nat.le_add_left K k)) (hA _)
  simpa only [Real.norm_eq_abs, tsum_mul_left] using
    tsum_of_norm_bounded hmajor.hasSum hb

/-- Negative correlation retains the complete odd contribution with its
negative sign; the even and odd subseries both converge absolutely. -/
theorem negative_chaos_series_even_odd (A : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (henergy : Summable A)
    (r : ℝ) (hr : |r| ≤ 1) :
    (∑' k, (-r) ^ k * A k) =
      (∑' k, r ^ (2 * k) * A (2 * k)) -
        ∑' k, r ^ (2 * k + 1) * A (2 * k + 1) := by
  have hs := (chaos_series_absolutely_summable A hA henergy (-r)
    (by simpa only [abs_neg] using hr)).of_norm
  have he := hs.comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k) from
      fun _ _ h => Nat.eq_of_mul_eq_mul_left (by decide) h)
  have ho := hs.comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k + 1) from
      fun _ _ h => Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel h))
  have heq : ∀ k : ℕ, (-r) ^ (2 * k) = r ^ (2 * k) :=
    fun k => (even_two_mul k).neg_pow r
  have hoq : ∀ k : ℕ, (-r) ^ (2 * k + 1) = -(r ^ (2 * k + 1)) :=
    fun k => (odd_two_mul_add_one k).neg_pow r
  calc
    (∑' k, (-r) ^ k * A k) =
        (∑' k, (-r) ^ (2 * k) * A (2 * k)) +
          ∑' k, (-r) ^ (2 * k + 1) * A (2 * k + 1) :=
      (tsum_even_add_odd (f := fun k => (-r) ^ k * A k) he ho).symm
    _ = _ := by simp only [heq, hoq, neg_mul, tsum_neg, sub_eq_add_neg]

/-- The first three degrees of a difference at negative correlation,
with the first-degree sign and the complete remaining tail explicit. -/
theorem negative_chaos_series_difference_split (A B : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (henergyA : Summable A) (henergyB : Summable B)
    (r : ℝ) (hr : |r| ≤ 1) :
    (∑' k, (-r) ^ k * A k) - (∑' k, (-r) ^ k * B k) =
      (A 0 - B 0) - r * (A 1 - B 1) + r ^ 2 * (A 2 - B 2) +
        ((∑' k, (-r) ^ (k + 3) * A (k + 3)) -
          ∑' k, (-r) ^ (k + 3) * B (k + 3)) := by
  have hneg : |-r| ≤ 1 := by simpa only [abs_neg] using hr
  rw [chaos_series_split_three A hA henergyA (-r) hneg,
    chaos_series_split_three B hB henergyB (-r) hneg]
  ring

section OrthonormalTails

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- Infinite Cauchy--Schwarz for coefficients, with summability and the
energy bound derived from orthonormality, rather than assumed. -/
theorem orthonormal_abs_product_summable_bound (e : ι → E)
    (he : Orthonormal ℝ e) (x y : E) :
    Summable (fun i => ‖⟪e i, x⟫‖ * ‖⟪e i, y⟫‖) ∧
      (∑' i, ‖⟪e i, x⟫‖ * ‖⟪e i, y⟫‖) ≤ ‖x‖ * ‖y‖ := by
  have hx := he.inner_products_summable x
  have hy := he.inner_products_summable y
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg ⟪e i, x⟫) (fun i => norm_nonneg ⟪e i, y⟫)
    (by simpa only [Real.rpow_two] using hx)
    (by simpa only [Real.rpow_two] using hy)
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact mul_le_mul
    (Real.sqrt_le_iff.mpr ⟨norm_nonneg x, he.tsum_inner_products_le x⟩)
    (Real.sqrt_le_iff.mpr ⟨norm_nonneg y, he.tsum_inner_products_le y⟩)
    (Real.sqrt_nonneg _) (norm_nonneg _)

/-- A degree-filtered signed spectral tail. The indexing type can contain
many coefficients in the same degree. -/
def spectralTail (e : ι → E) (degree : ι → ℕ) (K : ℕ)
    (ρ : ℝ) (x : E) : ℝ :=
  ∑' i, if K ≤ degree i then ρ ^ degree i * ⟪e i, x⟫ ^ 2 else 0

/-- All tail series here converge absolutely by Bessel's inequality. -/
theorem spectral_tail_absolutely_summable (e : ι → E)
    (he : Orthonormal ℝ e) (degree : ι → ℕ) (K : ℕ)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (x : E) :
    Summable (fun i => ‖if K ≤ degree i then
      ρ ^ degree i * ⟪e i, x⟫ ^ 2 else 0‖) := by
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => ?_) (he.inner_products_summable x)
  split_ifs with hi
  · simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg ρ) hρ)
  · simpa only [norm_zero, Real.norm_eq_abs, sq_abs] using sq_nonneg ⟪e i, x⟫

/-- The complete signed tail, not a finite truncation, obeys the residual
multiplier estimate. This is the Hilbert-space Cauchy step used after
smoothing in the exterior argument. -/
theorem spectral_tail_difference_bound (e : ι → E)
    (he : Orthonormal ℝ e) (degree : ι → ℕ) (K : ℕ)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (x y : E) :
    |spectralTail e degree K ρ x - spectralTail e degree K ρ y| ≤
      |ρ| ^ K * (‖x - y‖ * ‖x + y‖) := by
  have hx := (spectral_tail_absolutely_summable e he degree K ρ hρ x).of_norm
  have hy := (spectral_tail_absolutely_summable e he degree K ρ hρ y).of_norm
  have hc := orthonormal_abs_product_summable_bound e he (x - y) (x + y)
  have hm := hc.1.mul_left (|ρ| ^ K)
  have hb : ∀ i, ‖(if K ≤ degree i then ρ ^ degree i * ⟪e i, x⟫ ^ 2 else 0) -
      (if K ≤ degree i then ρ ^ degree i * ⟪e i, y⟫ ^ 2 else 0)‖ ≤
      |ρ| ^ K * (‖⟪e i, x - y⟫‖ * ‖⟪e i, x + y⟫‖) := by
    intro i
    by_cases hi : K ≤ degree i
    · simp only [if_pos hi, inner_sub_right, inner_add_right]
      have hid : ρ ^ degree i * ⟪e i, x⟫ ^ 2 - ρ ^ degree i * ⟪e i, y⟫ ^ 2 =
          ρ ^ degree i * ((⟪e i, x⟫ - ⟪e i, y⟫) *
            (⟪e i, x⟫ + ⟪e i, y⟫)) := by ring
      rw [hid, norm_mul, norm_mul, Real.norm_eq_abs, abs_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (abs_nonneg ρ) hρ hi) (by positivity)
    · simp only [if_neg hi, sub_self, norm_zero]
      positivity
  have ht := tsum_of_norm_bounded hm.hasSum hb
  have ht' : |spectralTail e degree K ρ x - spectralTail e degree K ρ y| ≤
      |ρ| ^ K * (∑' i, ‖⟪e i, x - y⟫‖ * ‖⟪e i, x + y⟫‖) := by
    simpa only [Real.norm_eq_abs, spectralTail, hx.tsum_sub hy, tsum_mul_left] using ht
  exact ht'.trans (mul_le_mul_of_nonneg_left hc.2 (pow_nonneg (abs_nonneg ρ) K))

/-- Factoring through smoothing is an equality of the entire series.
The coefficient identity states exactly what a degree-diagonal smoothing
operator must provide; no Gaussian operator is postulated here. -/
theorem spectral_tail_smoothing_identity (e : ι → E)
    (degree : ι → ℕ) (K : ℕ) (r τ : ℝ) (hτ : 0 < τ) (x X : E)
    (hcoeff : ∀ i, ⟪e i, X⟫ = τ ^ degree i * ⟪e i, x⟫) :
    spectralTail e degree K (-r) x =
      spectralTail e degree K (-(r / τ ^ 2)) X := by
  unfold spectralTail
  apply tsum_congr
  intro i
  split_ifs
  · rw [hcoeff]
    simp only [← neg_div, div_pow, mul_pow, ← pow_mul]
    rw [Nat.mul_comm (degree i) 2]
    field_simp [ne_of_gt hτ]
  · rfl

/-- Infinite signed-tail estimate after smoothing. All convergence comes
from Bessel's inequality. The two smoothing coefficient identities are
explicit, and must be proved for an actual Gaussian semigroup before this
can be applied to Gaussian noise stability. -/
theorem smoothed_negative_spectral_tail_difference_bound (e : ι → E)
    (he : Orthonormal ℝ e) (degree : ι → ℕ) (K : ℕ)
    (r τ : ℝ) (hr : 0 ≤ r) (hτ : 0 < τ) (hrτ : r ≤ τ ^ 2)
    (x y X Y : E)
    (hx : ∀ i, ⟪e i, X⟫ = τ ^ degree i * ⟪e i, x⟫)
    (hy : ∀ i, ⟪e i, Y⟫ = τ ^ degree i * ⟪e i, y⟫) :
    |spectralTail e degree K (-r) x - spectralTail e degree K (-r) y| ≤
      (r / τ ^ 2) ^ K * (‖X - Y‖ * (‖X‖ + ‖Y‖)) := by
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hq : 0 ≤ r / τ ^ 2 := div_nonneg hr hτsq.le
  have hqone : r / τ ^ 2 ≤ 1 := (div_le_one hτsq).mpr hrτ
  rw [spectral_tail_smoothing_identity e degree K r τ hτ x X hx,
    spectral_tail_smoothing_identity e degree K r τ hτ y Y hy]
  have hbound := spectral_tail_difference_bound e he degree K (-(r / τ ^ 2))
    (by simpa only [abs_neg, abs_of_nonneg hq] using hqone) X Y
  simp only [abs_neg, abs_of_nonneg hq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (norm_add_le X Y) (norm_nonneg _)) (pow_nonneg hq K))

end OrthonormalTails

end NegativeVoting
