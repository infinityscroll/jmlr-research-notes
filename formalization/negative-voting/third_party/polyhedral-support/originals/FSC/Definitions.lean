import WeakSimplexConjectureLean.Core.Correlation
import WeakSimplexConjectureLean.Core.Euclidean
import WeakSimplexConjectureLean.Coding.Gram
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Transparent public objects. No comparison theorem or analytic assumption is encoded here. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSC

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Coord (n : ℕ) := WeakSimplex.Coord n
abbrev simplex (n : ℕ) : Mat n := WeakSimplex.regularSimplexGram n

def CorrSet (n : ℕ) : Set (Mat n) := {G | WeakSimplex.IsCorrelation G}

def DistinctScores {n : ℕ} (G : Mat n) : Prop :=
  ∀ i j : Fin n, i ≠ j → G i j < 1

def thresholdEvent {n : ℕ} (b : Coord n) : Set (Coord n) :=
  {x | ∀ i, x i ≤ b i}

def thresholdCDF {n : ℕ} (G : Mat n) (b : Coord n) : ℝ :=
  (multivariateGaussian (0 : Coord n) G (thresholdEvent b)).toReal

def cdf {n : ℕ} (G : Mat n) (t : ℝ) : ℝ :=
  (multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t)).toReal

theorem measurableSet_thresholdEvent {n : ℕ} (b : Coord n) :
    MeasurableSet (thresholdEvent b) := by
  rw [thresholdEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun i ↦ measurableSet_le ?_ measurable_const
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

theorem cdf_nonneg {n : ℕ} (G : Mat n) (t : ℝ) : 0 ≤ cdf G t :=
  ENNReal.toReal_nonneg

theorem thresholdCDF_nonneg {n : ℕ} (G : Mat n) (b : Coord n) :
    0 ≤ thresholdCDF G b := ENNReal.toReal_nonneg

theorem thresholdCDF_le_one {n : ℕ} (G : Mat n) (b : Coord n) :
    thresholdCDF G b ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using
    (prob_le_one (μ := multivariateGaussian (0 : Coord n) G) (s := thresholdEvent b)))

theorem measurable_thresholdCDF {n : ℕ} (G : Mat n) :
    Measurable (thresholdCDF G) := by
  have hS : MeasurableSet {p : Coord n × Coord n | ∀ i, p.2 i ≤ p.1 i} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (by fun_prop) (by fun_prop)
  exact (measurable_measure_prodMk_left
    (ν := multivariateGaussian (0 : Coord n) G) hS).ennreal_toReal

theorem cdf_le_one {n : ℕ} (G : Mat n) (t : ℝ) : cdf G t ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using
    (prob_le_one (μ := multivariateGaussian (0 : Coord n) G)
      (s := WeakSimplex.lowerOrthant t)))

theorem cdf_eq_measure {n : ℕ} (G : Mat n) (t : ℝ) :
    ENNReal.ofReal (cdf G t) =
      multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t) := by
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem thresholdCDF_const {n : ℕ} (G : Mat n) (t : ℝ) :
    thresholdCDF G (WeakSimplex.Coord.ofFun fun _ ↦ t) = cdf G t := rfl

/-- Real subtraction in the denominator; no natural-subtraction convention is implicit. -/
theorem simplex_apply {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    simplex n i j = if i = j then 1 else -1 / ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  simp only [simplex, WeakSimplex.regularSimplexGram, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, WeakSimplex.allOnesMatrix_apply, smul_eq_mul]
  split_ifs <;> field_simp
  ring

theorem simplex_eq_scaled_matrix {n : ℕ} (hn : 2 ≤ n) :
    simplex n = (1 / ((n : ℝ) - 1)) •
      ((n : ℝ) • (1 : Mat n) - WeakSimplex.allOnesMatrix n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  ext i j
  rw [simplex_apply hn]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    WeakSimplex.allOnesMatrix_apply, smul_eq_mul]
  split_ifs <;> field_simp
  ring

def normalizedAdd {n : ℕ} (G L : Mat n) (s : ℝ) : Mat n :=
  fun i j ↦ (G i j + s * L i j) /
    (Real.sqrt (1 + s * L i i) * Real.sqrt (1 + s * L j j))

end FSC
