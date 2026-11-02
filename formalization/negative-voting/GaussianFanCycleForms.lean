import GaussianFanCycleSlice
import GaussianFanCycleGram
import GaussianFanCycleGauge

/-! Actual Gaussian finite-fan cycle forms. These use ordered alternating arrays,
so the edge pairing has factor 1/2 and the tetrahedron pairing factor 1/24.
The A-B identity itself is a subsequent theorem, not an assumption here. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def cycleEdgeWeight (b : AffineBasis V ℝ E) (h : V → ℝ) (a j : V) : ℝ :=
  if a = j then 1 else stratumMassAt b h {a,j} a / ‖b a-b j‖

def cycleTriangleWeight (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) : ℝ :=
  if a ≠ j ∧ a ≠ k ∧ j ≠ k then
    triangleContent (b a) (b j) (b k) / stratumMassAt b h {a,j,k} a
  else 1

def cycleTetrahedronWeight (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k l : V) : ℝ :=
  stratumMassAt b h {a,j,k,l} a / tetrahedronContent (b a) (b j) (b k) (b l)

def cycleMean (b : AffineBasis V ℝ E) (h : V → ℝ) (a j k : V) (v : E) : ℝ :=
  stratumMeanPairing b h {a,j,k} a v

def cycleA (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) : ℝ :=
  (1/2:ℝ) * ∑ a, ∑ j,
    triangleBoundary lam a j * triangleBoundary eta a j / cycleEdgeWeight b h a j

def cycleB (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) : ℝ :=
  (1/2:ℝ) * ∑ a, ∑ j, ∑ k, ∑ l,
    lam k a j * eta l a j *
      (1/cycleEdgeWeight b h a j-
        cycleTriangleWeight b h k a j * cycleMean b h l a j (barycentricOutwardVector b k))

def cycleWeightedCoboundary (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) : V → V → V → V → ℝ :=
  triangleCoboundary (fun a j k => cycleTriangleWeight b h a j k * lam a j k)

def cycleFactorizationRHS (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) : ℝ :=
  -(1/24:ℝ) * ∑ a, ∑ j, ∑ k, ∑ l,
    cycleTetrahedronWeight b h a j k l *
      cycleWeightedCoboundary b h lam a j k l * cycleWeightedCoboundary b h eta a j k l

/-- The exact entrywise difference, before using any Gaussian mean identity. -/
theorem cycleA_sub_cycleB (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) :
    cycleA b h lam eta-cycleB b h lam eta =
      (1/2:ℝ) * ∑ a, ∑ j, ∑ k, ∑ l,
        lam k a j * eta l a j * cycleTriangleWeight b h k a j *
          cycleMean b h l a j (barycentricOutwardVector b k) := by
  have ha : cycleA b h lam eta = (1/2:ℝ) * ∑ a, ∑ j, ∑ k, ∑ l,
      lam k a j * eta l a j / cycleEdgeWeight b h a j := by
    unfold cycleA
    simp_rw [triangleBoundary,Finset.sum_mul,Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
  rw [ha,cycleB,← mul_sub]
  congr 1
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end NegativeVotingFanCycle
