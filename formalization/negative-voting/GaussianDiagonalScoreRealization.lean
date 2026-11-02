import GaussianDiagonalFacetIntegral
import GaussianFanSelectedOffsets

/-! Intrinsic transport of the actual diagonal Gaussian mass and facet laws.
Only literal row-Gram equalities are assumed; probability and facet-integral
identities are derived from the Gaussian score law and mass derivative. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingDiagonalScoreRealization
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingFan NegativeVotingCapTail
  NegativeVotingFanJacobian NegativeVotingFanOffsetCovarianceLaw NegativeVotingFanCovarianceLaw
  NegativeVotingFanSelectedOffsets
variable {n m d e : ℕ}

theorem singular_lower_of_gram {V : Type*} [Fintype V]
    (B : V→FSC.Coord d) (C : V→FSC.Coord e) (b : ℝ)
    (hlower : CenteredSingularLowerBound B b)
    (hGram : ∀i j,inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) :
    CenteredSingularLowerBound C b := by
  intro q hq
  rw [←linearCombination_norm_sq_eq_of_gram B C hGram q]
  exact hlower q hq

theorem centered_diagonal_injective (σ : Fin m→ℝ) (hσ : ∀i,0<σ i) (v : FSC.Coord m) :
    Function.Injective (fun i=>diagonalRows σ i-v) := by
  intro i j he
  apply diagonalRows_injective σ hσ
  simpa only [sub_add_cancel] using congrArg (fun x=>x+v) he

/-- Exact mass law for every realization of the centered diagonal covariance,
including a minimal-dimensional projected realization. -/
theorem mass_diagonal_gram_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (v : FSC.Coord (n+1)) (C : Fin (n+1)→FSC.Coord d)
    (hGram : ∀i j,inner ℝ (diagonalRows σ i-v) (diagonalRows σ j-v)=inner ℝ (C i) (C j))
    (i : Fin (n+1)) :
    mass C h i=∫x,gaussianDensity (σ i) (h i) x*
      (∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) x) := by
  rw [←congrFun (mass_eq_of_gram (fun i=>diagonalRows σ i-v) C
    (centered_diagonal_injective σ hσ v) hGram h) i]
  exact mass_centered_diagonal_integral σ h hσ v i

/-- Exact physical facet law for a Gram-equivalent projected realization.
The Jacobian normalization is inherited, rather than supplied as a premise. -/
theorem facetWeight_diagonal_gram_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (v : FSC.Coord (n+1)) (C : Fin (n+1)→FSC.Coord d)
    (hGram : ∀i j,inner ℝ (diagonalRows σ i-v) (diagonalRows σ j-v)=inner ℝ (C i) (C j))
    (i j : Fin (n+1)) (hij : i≠j) :
    facetWeight C h i j=∫x,hazardPairDensity σ h x i j := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  have hCen:=singular_lower_common_row_sub (diagonalRows σ) b hB v
  have hC:=singular_lower_of_gram (fun i=>diagonalRows σ i-v) C b hCen hGram
  have he:=facetWeight_eq_of_mass_eq (fun i=>diagonalRows σ i-v) C b b hb hb hCen hC
    (fun h'=>mass_eq_of_gram _ C (centered_diagonal_injective σ hσ v) hGram h') h i j hij
  rw [←he]
  exact facetWeight_centered_diagonal_integral σ h hσ v i j hij

theorem selectedOffsets_common_row_sub {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : V→FSC.Coord d) (b : ℝ) (hb : 0<b) (hB : CenteredSingularLowerBound B b)
    (v : FSC.Coord d) (p : V→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    selectedOffsets (fun i=>B i-v) p=selectedOffsets B p := by
  have hinj : Function.Injective B:=fun i j he=>by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B b hb hB i j hij he
  apply selectedOffsets_eq (fun i=>B i-v) p b hb (singular_lower_common_row_sub B b hB v)
  exact (funext (fun i=>mass_common_row_sub B hinj _ v i)).trans (selectedOffsets_mass B hinj p hp hs)

/-- The canonical balancing offsets themselves are independent of the
ambient realization, including common centering of the independent scores. -/
theorem selectedOffsets_diagonal_gram (σ : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (v : FSC.Coord (n+1)) (C : Fin (n+1)→FSC.Coord d)
    (hGram : ∀i j,inner ℝ (diagonalRows σ i-v) (diagonalRows σ j-v)=inner ℝ (C i) (C j))
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    selectedOffsets C p=selectedOffsets (diagonalRows σ) p := by
  obtain ⟨b,hb,hB⟩:=exists_diagonal_singular_lower σ hσ
  rw [←selectedOffsets_eq_of_gram (fun i=>diagonalRows σ i-v) C b hb
    (singular_lower_common_row_sub (diagonalRows σ) b hB v) hGram p hp hs,
    selectedOffsets_common_row_sub (diagonalRows σ) b hb hB v p hp hs]

/-- The literal balancing equation in one dimension, with no supplied
mass-integral identity or selection-regularity assumption. -/
theorem selectedOffsets_diagonal_integral (σ : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) (i : Fin (n+1)) :
    (∫x,gaussianDensity (σ i) ((selectedOffsets (diagonalRows σ) p : Fin (n+1)→ℝ) i) x*
      (∏j∈Finset.univ.erase i,gaussianCDF (σ j) ((selectedOffsets (diagonalRows σ) p : Fin (n+1)→ℝ) j) x))=p i := by
  rw [←mass_diagonal_integral σ _ hσ i]
  exact congrFun (selectedOffsets_mass (diagonalRows σ) (diagonalRows_injective σ hσ) p hp hs) i

end NegativeVotingDiagonalScoreRealization
