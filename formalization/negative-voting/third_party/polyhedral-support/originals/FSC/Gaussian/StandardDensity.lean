import FSC.Definitions
import WeakSimplexConjectureLean.Vendor.StatLean.PiGaussian
import WeakSimplexConjectureLean.Vendor.StatLean.WithDensityMap
import Mathlib.MeasureTheory.Integral.Pi

/-!
Narrow adaptation of the private standard-density declarations in
WeakSimplexConjectureLean/Gaussian/DensityRatio.lean, lines 16–45 and 64–74,
at WSC commit a204c53cae45652d12524132dbb9a2e0ffe8cf78.
Changes: public FSC names, Fin n indexing, and the shared Coord alias.
The mathematical hypotheses and product-density normalization are unchanged.
The imported StatLean adapters retain their upstream Apache-2.0 notices.
-/

/-
MIT License

Copyright (c) 2026 Abhijeet Mulgund

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace FSC

def standardDensity {n : ℕ} (x : Coord n) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

theorem measurable_standardDensity (n : ℕ) :
    Measurable (standardDensity (n := n)) := by
  unfold standardDensity
  fun_prop

theorem standardDensity_ne_zero {n : ℕ} (x : Coord n) : standardDensity x ≠ 0 := by
  unfold standardDensity
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact (gaussianPDF_pos 0 one_ne_zero (x i)).ne'

theorem standardDensity_ne_top {n : ℕ} (x : Coord n) : standardDensity x ≠ ∞ := by
  exact ENNReal.prod_ne_top fun _ _ ↦ gaussianPDF_ne_top

theorem toReal_standardDensity {n : ℕ} (x : Coord n) :
    (standardDensity x).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-‖x‖ ^ 2 / 2) := by
  rw [standardDensity, ENNReal.toReal_prod]
  simp_rw [toReal_gaussianPDF, gaussianPDFReal]
  rw [Finset.prod_mul_distrib]
  simp_rw [← Real.exp_sum]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [NNReal.coe_one, mul_one, Nat.ofNat_nonneg, Real.sqrt_mul, mul_inv_rev,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_zero, mul_eq_mul_left_iff,
    Real.exp_eq_exp, pow_eq_zero_iff', mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero,
    OfNat.ofNat_ne_zero, or_false, ne_eq, hsqrt, false_and]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem stdGaussian_eq_volume_withDensity (n : ℕ) :
    stdGaussian (Coord n) = (volume : Measure (Coord n)).withDensity standardDensity := by
  rw [← map_pi_eq_stdGaussian,
    WeakSimplex.Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity]
  have hmap := WeakSimplex.Vendor.StatLean.AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (volume : Measure (Fin n → ℝ)) (WithLp.toLp 2) (by fun_prop)
    (standardDensity (n := n)) (measurable_standardDensity n)
  rw [(PiLp.volume_preserving_toLp (Fin n)).map_eq] at hmap
  exact hmap.symm.trans (by rfl)

end FSC
