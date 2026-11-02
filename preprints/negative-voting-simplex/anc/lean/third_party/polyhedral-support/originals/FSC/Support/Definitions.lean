import FSC.Definitions
import WeakSimplexConjectureLean.Normal.PDFCDF

/-! Finite Gaussian caps in the given ambient dimension, retaining unused energy directions. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FSC

def cap {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) : Set (Coord d) :=
  {y | ∀ j, inner ℝ (w j) y ≤ b j}

def capMass {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) : ℝ :=
  (stdGaussian (Coord d) (cap w b)).toReal

def capEnergy {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) : ℝ :=
  ∫ y in cap w b, ‖y‖ ^ 2 ∂stdGaussian (Coord d)

def NoCoincident {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) : Prop :=
  ∀ j k, j ≠ k →
    (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)

/-- Explicit affine image used for a unit-normal pin; rank deficiency is allowed. -/
def sliceLaw {d : ℕ} (w : Coord d) (z : ℝ) : Measure (Coord d) :=
  (stdGaussian (Coord d)).map (fun y ↦ z • w + (y - inner ℝ w y • w))

def sliceMass {d : ℕ} {ι : Type*} (w : ι → Coord d) (b : ι → ℝ) (j : ι) : ℝ :=
  (sliceLaw (w j) (b j) {y | ∀ k, k ≠ j → inner ℝ (w k) y ≤ b k}).toReal

def supportGradient {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) (b : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight
    (WeakSimplex.normalPDF (b j) * sliceMass w b j)

theorem measurableSet_cap {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) (b : ι → ℝ) : MeasurableSet (cap w b) := by
  rw [cap, Set.setOf_forall]
  exact MeasurableSet.iInter fun j ↦
    measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const

end FSC
