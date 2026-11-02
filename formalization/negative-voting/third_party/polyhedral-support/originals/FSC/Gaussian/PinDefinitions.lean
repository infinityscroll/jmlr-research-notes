import FSC.Definitions
import WeakSimplexConjectureLean.Normal.PDFCDF

/-! Canonical full-index residual laws and one shared pair-weight convention. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FSC

def singleMean {n : ℕ} (G : Mat n) (i : Fin n) (t : ℝ) : Coord n :=
  WeakSimplex.Coord.ofFun fun k ↦ t * G k i

def singleCov {n : ℕ} (G : Mat n) (i : Fin n) : Mat n :=
  fun k l ↦ G k l - G k i * G l i

def singleLaw {n : ℕ} (G : Mat n) (i : Fin n) (t : ℝ) : Measure (Coord n) :=
  multivariateGaussian (singleMean G i t) (singleCov G i)

def singleEvent {n : ℕ} (i : Fin n) (t : ℝ) : Set (Coord n) :=
  {x | ∀ k, k ≠ i → x k ≤ t}

def singlePinMass {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ :=
  (singleLaw G i t (singleEvent i t)).toReal

def pairAlpha {n : ℕ} (G : Mat n) (i j : Fin n) (k : Fin n) : ℝ :=
  (G k i - G i j * G k j) / (1 - (G i j) ^ 2)

def pairBeta {n : ℕ} (G : Mat n) (i j : Fin n) (k : Fin n) : ℝ :=
  (G k j - G i j * G k i) / (1 - (G i j) ^ 2)

def pairResidual {n : ℕ} (G : Mat n) (i j : Fin n) : Mat n :=
  fun k l ↦ (if k = l then 1 else 0) -
    pairAlpha G i j k * (if i = l then 1 else 0) -
    pairBeta G i j k * (if j = l then 1 else 0)

def pairCov {n : ℕ} (G : Mat n) (i j : Fin n) : Mat n :=
  pairResidual G i j * G * (pairResidual G i j).transpose

def pairMean {n : ℕ} (G : Mat n) (i j : Fin n) (r s : ℝ) : Coord n :=
  WeakSimplex.Coord.ofFun fun k ↦ pairAlpha G i j k * r + pairBeta G i j k * s

def pairLaw {n : ℕ} (G : Mat n) (i j : Fin n) (r s : ℝ) : Measure (Coord n) :=
  multivariateGaussian (pairMean G i j r s) (pairCov G i j)

/-- Excludes both deterministic pinned coordinates, including in frontier arguments. -/
def pairEvent {n : ℕ} (i j : Fin n) (t : ℝ) : Set (Coord n) :=
  {x | ∀ k, k ≠ i → k ≠ j → x k ≤ t}

def pairSuccess {n : ℕ} (G : Mat n) (i j : Fin n) (t : ℝ) : ℝ :=
  (pairLaw G i j t t (pairEvent i j t)).toReal

def pairSigma {n : ℕ} (G : Mat n) (i j : Fin n) : ℝ :=
  Real.sqrt (1 - (G i j) ^ 2)

def pairSupport {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) : ℝ :=
  t * (1 - G i j) / pairSigma G i j

def q {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) : ℝ :=
  if i ≠ j ∧ -1 < G i j ∧ G i j < 1 then
    WeakSimplex.normalPDF t * WeakSimplex.normalPDF (pairSupport G t i j) /
      pairSigma G i j * pairSuccess G i j t
  else 0

def stress {n : ℕ} (G : Mat n) (t : ℝ) : Mat n :=
  fun i j ↦ if i = j then -∑ k ∈ Finset.univ.erase i, G i k * q G t i k
    else q G t i j

def rowK {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (1 - G i j) * q G t i j

def rowC {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, pairSigma G i j * q G t i j

def kappa {n : ℕ} (G : Mat n) (t : ℝ) : ℝ := ∑ i, rowK G t i

def boundarySlope {n : ℕ} (G : Mat n) (t : ℝ) : ℝ :=
  WeakSimplex.normalPDF t * ∑ i, singlePinMass G t i

theorem measurableSet_singleEvent {n : ℕ} (i : Fin n) (t : ℝ) :
    MeasurableSet (singleEvent i t) := by
  classical
  rw [singleEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun k ↦ ?_
  by_cases h : k = i
  · simp [h]
  · simpa [h] using
      (measurableSet_le (EuclideanSpace.proj (𝕜 := ℝ) k).measurable measurable_const
        : MeasurableSet {x : Coord n | x k ≤ t})

theorem measurableSet_pairEvent {n : ℕ} (i j : Fin n) (t : ℝ) :
    MeasurableSet (pairEvent i j t) := by
  classical
  rw [pairEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun k ↦ ?_
  by_cases hi : k = i
  · simp [hi]
  by_cases hj : k = j
  · simp [hj]
  · simpa [hi, hj] using
      (measurableSet_le (EuclideanSpace.proj (𝕜 := ℝ) k).measurable measurable_const
        : MeasurableSet {x : Coord n | x k ≤ t})

@[simp] theorem q_self {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) :
    q G t i i = 0 := by simp [q]

end FSC
