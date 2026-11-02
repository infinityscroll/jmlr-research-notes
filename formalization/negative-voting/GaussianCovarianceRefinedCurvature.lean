import GaussianAffineBasisLower
import GaussianFanCycleHessian
import GaussianFanCovarianceValue
import GaussianFanValueDerivative

/-! Actual first and second covariance derivatives with the proved cycle-refined
curvature estimate. Every geometric and optimization input is constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix
namespace NegativeVotingCovarianceRefinement
open NegativeVotingFan NegativeVotingFanScore NegativeVotingCapTail NegativeVotingFanInverse
  NegativeVotingFanEnvelope NegativeVotingFanCovarianceEnvelope NegativeVotingFanValueDerivative
  NegativeVotingFanCovarianceValue NegativeVotingFanCycleHessian NegativeVotingAffineBasisLower
  NegativeVotingCovariancePath NegativeVotingFanCycle NegativeVotingFanCanonicalOffset
  NegativeVotingFanJacobian
variable {m d : ℕ} [NeZero m]

/-- First Price derivative of the actual optimized covariance value. -/
theorem hasDerivAt_intrinsic_covariance_value (B : Fin m → FSC.Coord d) (p : Fin m → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) (h₀ : centeredGauge (Fin m))
    (hm : mass B h₀=p) (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hH : H.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ => covarianceValue (Matrix.gram ℝ B+t•gramVelocity B H) p)
      ((1/4:ℝ)*∑ i, ∑ j, facetWeight B h₀ i j*inner ℝ (B i-B j) (H (B i-B j))) 0 := by
  obtain ⟨S,hS0,hSsym,_,hSsquare,hS1,_,_,_⟩ := exists_smooth_local_covariance_factor H hH
  have hv := (optimizedValue_C1_and_derivative B p σ hσ hlower hp hs h₀ hm).2
  have hR : HasDerivAt (fun t : ℝ => rowsOfOperator B (S t))
      (rowsOfOperator B ((1/2:ℝ)•H)) 0 :=
    (rowsOfOperator B).hasFDerivAt.comp_hasDerivAt 0 hS1
  have hv' : HasFDerivAt (fun C : Rows d (Fin m) => NegativeVotingFanValue.optimizedValue C p)
      (rowDerivative B h₀) (rowsOfOperator B (S 0)) := by simpa [hS0] using hv
  have hd := hv'.comp_hasDerivAt 0 hR
  have heq : (fun t : ℝ => covarianceValue (Matrix.gram ℝ B+t•gramVelocity B H) p) =ᶠ[𝓝 0]
      (fun t : ℝ => NegativeVotingFanValue.optimizedValue (rowsOfOperator B (S t)) p) := by
    filter_upwards [hSsquare] with t ht
    rw [← covariance_factor_gram B H (S t) t (hSsym t) ht]
    exact covarianceValue_gram _ p
  have hd' : HasDerivAt (fun t : ℝ => covarianceValue (Matrix.gram ℝ B+t•gramVelocity B H) p)
      (rowDerivative B h₀ (rowsOfOperator B ((1/2:ℝ)•H))) 0 := by
    exact hd.congr_of_eventuallyEq heq
  rwa [covariance_first_derivative_value B h₀ σ hσ hlower H] at hd'

/-- Actual first and second derivatives for every finite full simplex and every
strictly positive mass vector. No singular-value, inverse, or stationarity hypothesis remains. -/
theorem exists_actual_covariance_derivatives (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    ∃ h₀ : centeredGauge (Fin m), mass b h₀=p ∧
      HasDerivAt (fun t : ℝ => covarianceValue (Matrix.gram ℝ b+t•gramVelocity b H) p)
        ((1/4:ℝ)*∑ i, ∑ j, facetWeight b h₀ i j*inner ℝ (b i-b j) (H (b i-b j))) 0 ∧
      HasDerivAt (deriv (fun t : ℝ => covarianceValue (Matrix.gram ℝ b+t•gramVelocity b H) p))
        (covarianceHessianValue b h₀ H) 0 ∧
      covarianceHessianValue b h₀ H ≤ -(1/4:ℝ)*normalEdgeEnergy b h₀ (rowsOfOperator b H) := by
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound b
  obtain ⟨h₀,hm,hd⟩ := exists_intrinsic_covariance_hessian b p σ hσ hlower hp hs H hH
  exact ⟨h₀,hm,hasDerivAt_intrinsic_covariance_value b p σ hσ hlower hp hs h₀ hm H hH,
    hd,covarianceHessianValue_le_normal_energy b h₀ σ hσ hlower H⟩

/-- The same actual second derivative has the explicit refined bound needed
for simultaneous covariance and prescribed-mass perturbations. -/
theorem exists_actual_refined_covariance_derivatives (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) (hcard : 3 ≤ m)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    ∃ h₀ : centeredGauge (Fin m), mass b h₀=p ∧
      HasDerivAt (fun t : ℝ => covarianceValue (Matrix.gram ℝ b+t•gramVelocity b H) p)
        ((1/4:ℝ)*∑ i, ∑ j, facetWeight b h₀ i j*inner ℝ (b i-b j) (H (b i-b j))) 0 ∧
      HasDerivAt (deriv (fun t : ℝ => covarianceValue (Matrix.gram ℝ b+t•gramVelocity b H) p))
        (covarianceHessianValue b h₀ H) 0 ∧
      covarianceHessianValue b h₀ H ≤
        -(1/4:ℝ)*normalEdgeEnergy b h₀ (rowsOfOperator b H)-
        (1/8:ℝ)*(∑ i, ∑ j, cycleEdgeWeight b h₀ i j *
          (Real.exp (-4)/(2*(1+2*Real.log (1/cycleIntrinsicProbability b h₀ i j)))) *
          ((canonicalOffsetVariation b h₀ (rowsOfOperator b H) i-
            canonicalOffsetVariation b h₀ (rowsOfOperator b H) j)+
            inner ℝ (H (b i-b j)) (faceAnchor b h₀ {i,j}))^2) := by
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound b
  obtain ⟨h₀,hm,hd⟩ := exists_intrinsic_covariance_hessian b p σ hσ hlower hp hs H hH
  exact ⟨h₀,hm,hasDerivAt_intrinsic_covariance_value b p σ hσ hlower hp hs h₀ hm H hH,
    hd,covarianceHessianValue_log_ehrhard_bound b h₀ σ hσ hlower (by simpa using hcard) H⟩

end NegativeVotingCovarianceRefinement
