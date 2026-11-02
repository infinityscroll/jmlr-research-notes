import GaussianDiagonalHazardQuadraticForm
import GaussianDiagonalScoreRealization
import GaussianHazardIntegrability

/-! The exact all-label hazard identity integrated against arbitrary
Euclidean rows. Analytic diagonal terms are retained. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingDiagonalIntegratedLaplacian
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalHazardQuadraticForm
  NegativeVotingDiagonalScoreRealization NegativeVotingHazardIntegrability NegativeVotingFanJacobian
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def integratedRowSum (σ h : V→ℝ) (i : V) : ℝ := ∑j,∫x,hazardPairDensity σ h x i j

lemma integrable_pair (σ h : V→ℝ) (hσ : ∀i,0<σ i) (i j : V) :
    Integrable (fun x=>hazardPairDensity σ h x i j) volume := by
  simpa only [pow_zero,mul_one] using integrable_hazardPairDensity_polynomial σ h hσ i j 0

lemma integral_pair_sum (σ h : V→ℝ) (hσ : ∀i,0<σ i) (c : V→V→ℝ) :
    (∫x,∑i,∑j,hazardPairDensity σ h x i j*c i j)=
      ∑i,∑j,(∫x,hazardPairDensity σ h x i j)*c i j := by
  have hi (i:V):Integrable (fun x=>∑j,hazardPairDensity σ h x i j*c i j) volume:=
    integrable_finsetSum _ fun j _=>(integrable_pair σ h hσ i j).mul_const _
  rw [integral_finset_sum _ (fun i _=>hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>(integrable_pair σ h hσ i j).mul_const _)]
  simp only [integral_mul_const]

/-- The integrated rank-one subtraction is nonnegative for any rectangular
row system. In particular no competitor rank hypothesis is used. -/
theorem integrated_hazard_laplacian_le_diagonal (σ h : V→ℝ) (hσ : ∀i,0<σ i) (B : V→E) :
    (1/2:ℝ)*(∑i,∑j,(∫x,hazardPairDensity σ h x i j)*‖B i-B j‖^2) ≤
      ∑i,integratedRowSum σ h i*‖B i‖^2 := by
  have hL:Integrable (fun x=>(1/2:ℝ)*(∑i,∑j,hazardPairDensity σ h x i j*‖B i-B j‖^2)) volume:=
    (integrable_finsetSum _ fun i _=>integrable_finsetSum _ fun j _=>
      (integrable_pair σ h hσ i j).mul_const _).const_mul _
  have hR:Integrable (fun x=>∑i,∑j,hazardPairDensity σ h x i j*‖B i‖^2) volume:=
    integrable_finsetSum _ fun i _=>integrable_finsetSum _ fun j _=>
      (integrable_pair σ h hσ i j).mul_const _
  have hh:=(integral_mono hL hR (fun x=>by
    simpa only [hazardRowSum,Finset.sum_mul] using hazard_laplacian_le_diagonal σ h x B))
  rw [integral_const_mul,integral_pair_sum σ h hσ,integral_pair_sum σ h hσ] at hh
  simpa only [integratedRowSum,Finset.sum_mul] using hh

/-- Actual geometric facets are replaced by their proved Gaussian integrals.
The analytic diagonal contributes zero to the edge sum and is nevertheless
retained in the dominating row coefficient. -/
theorem physical_laplacian_le_hazard_diagonal {n d : ℕ}
    (σ h : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i) (v : FSC.Coord (n+1))
    (C : Fin (n+1)→FSC.Coord d)
    (hGram : ∀i j,inner ℝ (NegativeVotingDiagonalWinnerIntegral.diagonalRows σ i-v)
      (NegativeVotingDiagonalWinnerIntegral.diagonalRows σ j-v)=inner ℝ (C i) (C j))
    (B : Fin (n+1)→E) :
    (1/2:ℝ)*(∑i,∑j,facetWeight C h i j*‖B i-B j‖^2) ≤
      ∑i,integratedRowSum σ h i*‖B i‖^2 := by
  have he:(∑i,∑j,facetWeight C h i j*‖B i-B j‖^2)=
      ∑i,∑j,(∫x,hazardPairDensity σ h x i j)*‖B i-B j‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:i=j
    · subst j;simp
    · rw [facetWeight_diagonal_gram_integral σ h hσ v C hGram i j hij]
  rw [he]
  exact integrated_hazard_laplacian_le_diagonal σ h hσ B

end NegativeVotingDiagonalIntegratedLaplacian
