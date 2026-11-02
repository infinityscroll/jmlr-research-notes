import GaussianDiagonalBalancedDerivative

/-! The actual selected diagonal Gaussian offset derivative solves its
physical graph-Laplacian equation. The variance forcing retains every pair;
the analytic diagonal is never assigned a physical facet weight. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingDiagonalBalanceEquation
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingDiagonalScoreRealization
  NegativeVotingDiagonalBalancedDerivative NegativeVotingHazardIntegrability
  NegativeVotingHazardPolynomialBounds NegativeVotingFan NegativeVotingFanJacobian
  NegativeVotingFanSelectedOffsets
variable {n m : ℕ}

theorem integrable_hazardPairDensity_affine (σ h : Fin m→ℝ) (hσ : ∀i,0<σ i)
    (i j : Fin m) (a b : ℝ) : Integrable (fun x=>hazardPairDensity σ h x i j*(a*x+b)) volume := by
  have hi:=(integrable_hazardPairDensity_polynomial σ h hσ i j 1).const_mul (|a|+|b|)
  apply hi.mono' ((continuous_hazardPairDensity σ h i j).mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  have hr:=hazardPairDensity_nonneg σ h hσ x i j
  have hab : |a*x+b|≤(|a|+|b|)*(1+|x|):=by
    have hh:=abs_add_le (a*x) b
    rw [abs_mul] at hh
    nlinarith [abs_nonneg a,abs_nonneg b,mul_nonneg (abs_nonneg b) (abs_nonneg x)]
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hr,pow_one]
  calc
    _≤hazardPairDensity σ h x i j*((|a|+|b|)*(1+|x|)):=mul_le_mul_of_nonneg_left hab hr
    _=_:=by ring

def varianceSpeed (σ h ζ : Fin m→ℝ) (i : Fin m) (x : ℝ) : ℝ := ζ i/σ i*(x-h i)
def varianceForcing (σ h ζ : Fin m→ℝ) (i : Fin m) : ℝ :=
  ∑j∈Finset.univ.erase i,∫x,hazardPairDensity σ h x i j*(varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x)
def offsetLaplacian (σ h k : Fin m→ℝ) (i : Fin m) : ℝ :=
  ∑j,facetWeight (diagonalRows σ) h i j*(k i-k j)

theorem integrable_variancePair (σ h ζ : Fin m→ℝ) (hσ : ∀i,0<σ i) (i j : Fin m) :
    Integrable (fun x=>hazardPairDensity σ h x i j*(varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x)) volume := by
  convert integrable_hazardPairDensity_affine σ h hσ i j (ζ i/σ i-ζ j/σ j)
    (-ζ i/σ i*h i+ζ j/σ j*h j) using 1
  funext x
  unfold varianceSpeed
  ring

theorem massFlux_eq_laplacian_add_forcing (σ h ζ k : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (i : Fin (n+1)) :
    massFlux σ h ζ k i=offsetLaplacian σ h k i+varianceForcing σ h ζ i := by
  have hconst (j:Fin (n+1)) : Integrable (fun x=>hazardPairDensity σ h x i j*(k i-k j)) volume:=by
    simpa using integrable_hazardPairDensity_affine σ h hσ i j 0 (k i-k j)
  unfold massFlux varianceForcing offsetLaplacian
  have he : (∑j,facetWeight (diagonalRows σ) h i j*(k i-k j))=
      ∑j∈Finset.univ.erase i,facetWeight (diagonalRows σ) h i j*(k i-k j):=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij:i≠j:=Ne.symm (Finset.mem_erase.mp hj).1
  have hf : (fun x=>hazardPairDensity σ h x i j*
      (transportSpeed (σ i) (h i) (ζ i) (k i) x-transportSpeed (σ j) (h j) (ζ j) (k j) x))=
      fun x=>hazardPairDensity σ h x i j*(k i-k j)+
        hazardPairDensity σ h x i j*(varianceSpeed σ h ζ i x-varianceSpeed σ h ζ j x):=by
    funext x
    unfold transportSpeed varianceSpeed
    ring
  rw [hf,integral_add (hconst j) (integrable_variancePair σ h ζ hσ i j),integral_mul_const,
    ←facetWeight_diagonal_integral σ h hσ i j hij]

/-- The actual balancing derivative solves Lk=-b, where L is the physical
Gaussian facet Laplacian and b is the exact variance forcing integral. -/
theorem exists_selected_diagonal_laplacian_equation (σ ζ : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    ∃k : NegativeVotingFanInverse.centeredGauge (Fin (n+1)),
      HasDerivAt (fun t=>selectedOffsets (diagonalRows (parameterLine σ ζ t)) p) k 0 ∧
      ∀i,offsetLaplacian σ (selectedOffsets (diagonalRows σ) p) k i=
        -varianceForcing σ (selectedOffsets (diagonalRows σ) p) ζ i := by
  obtain ⟨k,hk,hflux⟩:=exists_selected_diagonal_derivative_flux σ ζ hσ p hp hs
  refine ⟨k,hk,fun i=>?_⟩
  have hh:=hflux i
  rw [massFlux_eq_laplacian_add_forcing σ _ ζ k hσ i] at hh
  linarith

end NegativeVotingDiagonalBalanceEquation
