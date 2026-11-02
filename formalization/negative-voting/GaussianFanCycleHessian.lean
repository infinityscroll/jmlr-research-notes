import GaussianFanCycleQuadratic
import GaussianFanCycleFlux
import GaussianFanCycleEhrhard
import GaussianFanCovarianceEnvelope

/-! The actual optimized covariance Hessian, including the residual Ehrhard term. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Matrix
namespace NegativeVotingFanCycleHessian
open NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingFanCycleQuadratic
  NegativeVotingFanCycleFlux NegativeVotingFanHessian NegativeVotingFanScore
  NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanCovarianceEnvelope
  NegativeVotingFanCanonicalOffset NegativeVotingFanEnvelope NegativeVotingCapTail
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Complete ordered-edge energy with the genuine geometric Gaussian weights. -/
def fullEdgeEnergy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) : ℝ :=
  (1/2:ℝ) * ∑ i, ∑ j, cycleEdgeWeight b h i j * ‖z i-z j‖^2

/-- Normal score strain; the orthogonal projection is onto the actual edge span. -/
def normalEdgeEnergy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) : ℝ :=
  (1/2:ℝ) * ∑ i, ∑ j, cycleEdgeWeight b h i j *
    ‖(faceDirection b {i,j}).starProjection (z i-z j)‖^2

/-- The energy left after subtracting the entire mean-cycle contribution. -/
def residualEnergyGap (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) (beta : V → ℝ) : ℝ :=
  (1/2:ℝ) * (∑ i, ∑ j, cycleDeficit b h i j (z i-z j) (z i-z j))-
    cycleMeanEnergy b h (cycleFlux b h z beta)

theorem surface_gap_square (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) (beta : V → ℝ) (i j : V) :
    surfaceIntegral b h i j (fun x => (affineScore z beta i x-affineScore z beta j x)^2) =
      cycleEdgeWeight b h i j * (stratumDirectionalVariance b h {i,j} i (z i-z j)+
        (cycleMeanEdge b h z i j+beta i-beta j)^2) := by
  by_cases hij : i=j
  · subst j
    simp [surfaceIntegral_diagonal,cycleMeanEdge,stratumDirectionalVariance,stratumMeanPairing]
  · have he : (fun x => (affineScore z beta i x-affineScore z beta j x)^2) =
        (fun x => (inner ℝ (z i-z j) x+(beta i-beta j))^2) := by
      funext x
      simp only [affineScore,inner_sub_left]
      ring
    rw [he,surfaceIntegral_affine_square b h i j hij]
    unfold cycleMeanEdge
    ring

/-- All ordered-pair factors agree with the literal moving-cell Hessian. -/
theorem quadraticForm_cycle_decomposition (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) (beta : V → ℝ) :
    quadraticForm b h z beta = fullEdgeEnergy b h z-normalEdgeEnergy b h z-
      residualEnergyGap b h z beta := by
  have hp (i j : V) :
      surfaceIntegral b h i j (fun x => (affineScore z beta i x-affineScore z beta j x)^2) =
        cycleEdgeWeight b h i j * ‖z i-z j‖^2-
        cycleEdgeWeight b h i j * ‖(faceDirection b {i,j}).starProjection (z i-z j)‖^2-
        (cycleDeficit b h i j (z i-z j) (z i-z j)-
          (cycleFlux b h z beta i j)^2/cycleEdgeWeight b h i j) := by
    rw [surface_gap_square,cycleDeficit,stratumDeficit_self b h {i,j} i (by simp),
      Submodule.norm_sq_eq_add_norm_sq_starProjection (z i-z j) (faceDirection b {i,j})]
    unfold cycleFlux cycleMeanEdge
    field_simp [ne_of_gt (cycleEdgeWeight_pos b h i j)]
    <;> ring
  unfold quadraticForm
  simp_rw [hp,Finset.sum_sub_distrib]
  unfold fullEdgeEnergy normalEdgeEnergy residualEnergyGap cycleMeanEnergy
  ring

theorem normalEdgeEnergy_nonneg (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) : 0 ≤ normalEdgeEnergy b h z := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (cycleEdgeWeight_pos b h i j).le (sq_nonneg _)

theorem residualEnergyGap_nonneg (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) (beta : V → ℝ) (r : V)
    (hc : ∀ i, edgeBoundary (cycleFlux b h z beta) i = 0) :
    0 ≤ residualEnergyGap b h z beta := by
  obtain ⟨lam,_,_,_,he⟩ := exists_actual_cycle_residual b h z beta r hc
  change 0 ≤ (1/2:ℝ) * (∑ i, ∑ j, cycleDeficit b h i j (z i-z j) (z i-z j))-
    cycleMeanEnergy b h (cycleFlux b h z beta)
  rw [he]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => cycleDeficit_nonneg b h i j _

/-- The spectral row energy agrees with the literal analytic facet normalization. -/
theorem fullEdgeEnergy_rowsOfOperator (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    fullEdgeEnergy b h (rowsOfOperator b H) =
      (1/2:ℝ) * ∑ i, ∑ j, facetWeight b h i j * ‖H (b i-b j)‖^2 := by
  unfold fullEdgeEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [rowsOfOperator]
  · rw [cycleEdgeWeight_eq_facetWeight b h i j hij]
    simp [rowsOfOperator,map_sub]

/-- Exact optimized Hessian decomposition. The offset is constructed from the
actual mass Jacobian and no stationarity, cycle, or Hessian identity is assumed. -/
theorem covarianceHessianValue_eq_cycle_energy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    covarianceHessianValue b h H =
      -(1/4:ℝ) * (normalEdgeEnergy b h (rowsOfOperator b H)+
        residualEnergyGap b h (rowsOfOperator b H)
          (canonicalOffsetVariation b h (rowsOfOperator b H))) := by
  unfold covarianceHessianValue
  rw [← canonicalOffset_elimination_formula b (rowsOfOperator b H) h σ hσ hlower,
    quadraticForm_cycle_decomposition,← fullEdgeEnergy_rowsOfOperator b h H]
  ring

/-- Concavity with the actual nonnegative normal-strain remainder. -/
theorem covarianceHessianValue_le_normal_energy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    covarianceHessianValue b h H ≤ -(1/4:ℝ)*normalEdgeEnergy b h (rowsOfOperator b H) := by
  rw [covarianceHessianValue_eq_cycle_energy b h σ hσ hlower H]
  have hg := residualEnergyGap_nonneg b h (rowsOfOperator b H)
    (canonicalOffsetVariation b h (rowsOfOperator b H)) (Classical.choice inferInstance)
    (canonicalOffset_cycle b h σ hσ hlower (rowsOfOperator b H))
  linarith

/-- The optimized covariance Hessian is nonpositive for every actual full simplex. -/
theorem covarianceHessianValue_nonpos (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : covarianceHessianValue b h H ≤ 0 := by
  have he := covarianceHessianValue_le_normal_energy b h σ hσ hlower H
  have hn := normalEdgeEnergy_nonneg b h (rowsOfOperator b H)
  linarith

/-- Full refined curvature, including the corrected offset and normal-anchor
term and the explicit logarithmic coefficient of the actual facet probability. -/
theorem covarianceHessianValue_log_ehrhard_bound (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (hcard : 3 ≤ Fintype.card V) (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    covarianceHessianValue b h H ≤
      -(1/4:ℝ)*normalEdgeEnergy b h (rowsOfOperator b H)-
      (1/8:ℝ)*(∑ i, ∑ j, cycleEdgeWeight b h i j *
        (Real.exp (-4)/(2*(1+2*Real.log (1/cycleIntrinsicProbability b h i j)))) *
        ((canonicalOffsetVariation b h (rowsOfOperator b H) i-
          canonicalOffsetVariation b h (rowsOfOperator b H) j)+
          inner ℝ (H (b i-b j)) (faceAnchor b h {i,j}))^2) := by
  rw [covarianceHessianValue_eq_cycle_energy b h σ hσ hlower H]
  have he := actual_cycle_log_ehrhard_bound b h hcard (rowsOfOperator b H)
    (canonicalOffsetVariation b h (rowsOfOperator b H)) (Classical.choice inferInstance)
    (canonicalOffset_cycle b h σ hσ hlower (rowsOfOperator b H))
  change _ ≤ residualEnergyGap b h (rowsOfOperator b H)
    (canonicalOffsetVariation b h (rowsOfOperator b H)) at he
  have hr (i j : V) : rowsOfOperator b H i-rowsOfOperator b H j=H (b i-b j) := by
    change H (b i)-H (b j)=H (b i-b j)
    rw [map_sub]
  simp_rw [hr] at he
  linarith

end NegativeVotingFanCycleHessian
