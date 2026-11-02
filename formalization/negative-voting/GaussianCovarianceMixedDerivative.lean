import GaussianCovarianceOffsetResponse

/-! The quantitative intrinsic mixed-derivative bound in the original
covariance coordinates. No inverse-covariance loss enters the constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovarianceMixedDerivative
open NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingFanCovarianceValue NegativeVotingCovarianceOffsets
  NegativeVotingCovarianceOffsetResponse NegativeVotingFanSelectedOffsets
  NegativeVotingFanRetained
variable {m d : ℕ} [NeZero m]

theorem operator_line_gram (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C) (t : ℝ) :
    gramVelocity b (C+t • A)=Matrix.gram ℝ (mappedBasis b R)+t •
      gramVelocity (mappedBasis b R)
        (R.symm.toContinuousLinearMap.comp (A.comp R.symm.toContinuousLinearMap)) := by
  rw [gramVelocity_add_smul]
  have hg : Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C := factor_gram b C R hR hRC
  have hv : gramVelocity (mappedBasis b R)
      (R.symm.toContinuousLinearMap.comp (A.comp R.symm.toContinuousLinearMap))=gramVelocity b A :=
    conjugate_gramVelocity b A R hR
  rw [hg,hv]

/-- The actual derivative of the mass offset along every symmetric covariance
line is controlled by the actual second derivative of Γ along that same line. -/
theorem operator_offsets_derivative_control
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (hcard : 3 ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : A.toLinearMap.IsSymmetric)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (p0 ellMin ellMax τ degreeCap : ℝ)
    (hp0 : 0<p0) (hmin : 0<ellMin) (hmax : 0<ellMax) (hτ : 0<τ) (hDpos : 0<degreeCap)
    (hmass : ∀ i,p0 ≤ p i)
    (hedgeMin : ∀ i j,i≠j→ellMin≤‖mappedBasis b R i-mappedBasis b R j‖)
    (hedgeMax : ∀ i j,i≠j→‖mappedBasis b R i-mappedBasis b R j‖≤ellMax)
    (hD : ∀ i,(∑ j,NegativeVotingFanJacobian.facetWeight (mappedBasis b R)
      (selectedOffsets (mappedBasis b R) p) i j)≤degreeCap)
    (ht : τ*(m:ℝ)≤(p0/(2*Real.pi*ellMax))/2) :
    retainedGapCoefficient p0 ellMax degreeCap *
      (∑ i,(deriv (fun t : ℝ => (operatorOffsets b p (C+t • A) : Fin m → ℝ)) 0 i)^2) ≤
      retainedCoefficientCeiling p0 τ ellMin *
        (-deriv (deriv (fun t : ℝ => operatorValue b p (C+t • A))) 0) := by
  let H := R.symm.toContinuousLinearMap.comp (A.comp R.symm.toContinuousLinearMap)
  have hH : H.toLinearMap.IsSymmetric := symmetric_conjugate _ _ hRi hA
  have hb := intrinsic_offset_derivative_control (mappedBasis b R) hcard p hp hs H hH
    p0 ellMin ellMax τ degreeCap hp0 hmin hmax hτ hDpos hmass hedgeMin hedgeMax hD ht
  simpa only [operatorOffsets,operatorValue,operator_line_gram b C A R hR hRC] using hb

end NegativeVotingCovarianceMixedDerivative
