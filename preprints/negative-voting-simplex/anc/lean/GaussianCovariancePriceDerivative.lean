import GaussianCovarianceOffsets
import GaussianCovarianceOptimizer

/-! The actual covariance Price derivative in unwhitened coordinates,
including the precise trace-penalty derivative used by optimizer KKT. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovariancePrice
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanSelectedOffsets
  NegativeVotingFanCovarianceValue NegativeVotingFanCovarianceEnvelope
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingCovarianceStrict NegativeVotingCovarianceRefinement
  NegativeVotingAffineBasisLower NegativeVotingFanJacobian
variable {m d : ℕ} [NeZero m]

theorem conjugate_pairing (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hRi : R.symm.toLinearMap.IsSymmetric)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (x : FSC.Coord d) :
    inner ℝ (R x) ((R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap)) (R x))=
      inner ℝ x (D x) := by
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  have hh := hRi (R x) (D x)
  change inner ℝ (R.symm (R x)) (D x)=inner ℝ (R x) (R.symm (D x)) at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh.symm

/-- The whitening factors cancel in the Price pairing. All Gaussian weights
are still evaluated at the actual transformed rows and selected offsets. -/
theorem hasDerivAt_operatorValue_factor (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hD : D.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ => operatorValue b p (C+t • D))
      ((1/4:ℝ)*∑ i,∑ j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j *
        inner ℝ (b i-b j) (D (b i-b j))) 0 := by
  let bR := mappedBasis b R
  let H := R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap)
  have hH : H.toLinearMap.IsSymmetric := symmetric_conjugate _ _ hRi hD
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound bR
  have hm := selectedOffsets_mass bR bR.ind.injective p hp hs
  have hd := hasDerivAt_intrinsic_covariance_value bR p σ hσ hlower hp hs
    (selectedOffsets bR p) hm H hH
  have hfun : (fun t : ℝ => operatorValue b p (C+t • D))=
      (fun t : ℝ => covarianceValue (Matrix.gram ℝ bR+t • gramVelocity bR H) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    have hg : Matrix.gram ℝ bR=gramVelocity b C := factor_gram b C R hR hRC
    have hv : gramVelocity bR H=gramVelocity b D := conjugate_gramVelocity b D R hR
    rw [hg,hv]
  rw [hfun]
  have hcoef : (∑ i,∑ j,facetWeight bR (selectedOffsets bR p) i j *
      inner ℝ (bR i-bR j) (H (bR i-bR j)))=
      ∑ i,∑ j,facetWeight bR (selectedOffsets bR p) i j *
        inner ℝ (b i-b j) (D (b i-b j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change inner ℝ (R (b i)-R (b j)) (H (R (b i)-R (b j)))=_
    rw [←map_sub]
    exact conjugate_pairing R hRi D (b i-b j)
  rwa [hcoef] at hd

/-- Actual derivative of 2Γ−trace, with the ordered-edge factor one half. -/
theorem hasDerivAt_penalizedValue_factor (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hD : D.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ => penalizedValue b p (C+t • D))
      ((1/2:ℝ)*∑ i,∑ j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j *
        inner ℝ (b i-b j) (D (b i-b j)) - LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap) 0 := by
  have hd := (hasDerivAt_operatorValue_factor b p hp hs C D R hR hRi hRC hD).const_mul 2
  have htr (t : ℝ) : LinearMap.trace ℝ (FSC.Coord d) (C+t • D).toLinearMap=
      LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap+t*LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap := by
    change LinearMap.trace ℝ (FSC.Coord d) (C.toLinearMap+t • D.toLinearMap)=_
    simp only [map_add,map_smul,smul_eq_mul]
  have ht : HasDerivAt (fun t : ℝ => LinearMap.trace ℝ (FSC.Coord d) (C+t • D).toLinearMap)
      (LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap) 0 := by
    simp_rw [htr]
    convert (hasDerivAt_const (0:ℝ) (LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap)).add
      ((hasDerivAt_id (0:ℝ)).mul_const (LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap)) using 1 <;> simp [Pi.add_def]
  convert hd.sub ht using 1
  · rfl
  · ring

end NegativeVotingCovariancePrice
