import GaussianCovarianceOffsets
import GaussianFanRetainedCoefficient

/-! The actual intrinsic covariance-offset derivative is the canonical
response, and the actual mixed derivative obeys the retained-graph bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovarianceOffsetResponse
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanSelectedOffsets
  NegativeVotingFanJointInverse NegativeVotingFanJointOffsets NegativeVotingFanJointMass
  NegativeVotingFanCovarianceValue NegativeVotingFanCovarianceEnvelope
  NegativeVotingCovarianceOffsets NegativeVotingCovariancePath NegativeVotingFanCanonicalOffset
  NegativeVotingFanRetained NegativeVotingCapTail NegativeVotingFacetDegree
  NegativeVotingAffineBasisLower
variable {m d : ℕ} [NeZero m]

/-- All factor and mass-preserving curves are constructed in the proof.
The derivative refers to the literal globally selected intrinsic offsets. -/
theorem hasDerivAt_covarianceOffsets_line (B : Fin m → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ =>
      (covarianceOffsets (Matrix.gram ℝ B+t • gramVelocity B H) p : Fin m → ℝ))
      ((1/2:ℝ) • canonicalOffsetVariation B (selectedOffsets B p) (rowsOfOperator B H)) 0 := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  let h₀ := selectedOffsets B p
  have hm₀ : mass B h₀=p := selectedOffsets_mass B hB p hp hs
  obtain ⟨S,hS0,hSsym,_,hSsquare,hS1,_,hSsmooth,_⟩ :=
    exists_smooth_local_covariance_factor H hH
  let R : ℝ → Fin m → FSC.Coord d := fun t => rowsOfOperator B (S t)
  have hR0 : R 0=B := by simp [R,hS0]
  have hR : ContDiffAt ℝ 1 R 0 :=
    (rowsOfOperator B).contDiff.contDiffAt.comp 0 (hSsmooth.of_le le_top)
  have hlower0 : CenteredSingularLowerBound (R 0) σ := by rwa [hR0]
  obtain ⟨a,ha0,haC,hacenter,ham⟩ := exists_C1_offsets_along_rows R h₀ σ hσ hlower0 hR
  have hm : ∀ᶠ t : ℝ in 𝓝 0, mass (R t) (a t)=p := by
    simpa only [hR0,hm₀] using ham
  have haD := haC.differentiableAt_one.hasDerivAt
  have hresponse := covariance_offset_response B h₀ p σ hσ hlower H S a (deriv a 0)
    hS0 ha0 hS1 haD hacenter hm
  rw [hresponse] at haD
  have hparam : ContinuousAt (fun t : ℝ => (R t,a t)) 0 :=
    hR.continuousAt.prodMk haC.continuousAt
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, CenteredSingularLowerBound (R t) (σ/2) :=
    hparam.tendsto.eventually (by
      simpa only [hR0,ha0] using eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  have heq : (fun t : ℝ =>
      (covarianceOffsets (Matrix.gram ℝ B+t • gramVelocity B H) p : Fin m → ℝ)) =ᶠ[𝓝 0] a := by
    filter_upwards [hSsquare,hnear,hm] with t ht hl hmt
    rw [←covariance_factor_gram B H (S t) t (hSsym t) ht]
    have hsel := selectedOffsets_eq (R t) p (σ/2) (by positivity) hl ⟨a t,hacenter t⟩ hmt
    have hc := covarianceOffsets_gram (R t) (σ/2) (by positivity) hl p hp hs
    exact congrArg (fun h : centeredGauge (Fin m) => (h : Fin m → ℝ)) (hc.trans hsel)
  exact haD.congr_of_eventuallyEq heq

/-- The second derivative of the actual covariance value uses the same
intrinsic offset as the mixed-derivative estimate. -/
theorem hasDerivAt_deriv_covarianceValue_selected (B : Fin m → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    HasDerivAt (deriv (fun t : ℝ => covarianceValue (Matrix.gram ℝ B+t • gramVelocity B H) p))
      (covarianceHessianValue B (selectedOffsets B p) H) 0 := by
  obtain ⟨h,hm,hd⟩ := exists_intrinsic_covariance_hessian B p σ hσ hlower hp hs H hH
  simpa only [selectedOffsets_eq B p σ hσ hlower h hm] using hd

/-- A quantitative bound on the literal intrinsic mixed derivative. The
remaining hypotheses concern actual masses, edges and Jacobian degrees. -/
theorem intrinsic_offset_derivative_control
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (hcard : 3 ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (p0 ellMin ellMax τ D : ℝ)
    (hp0 : 0<p0) (hmin : 0<ellMin) (hmax : 0<ellMax) (hτ : 0<τ) (hDpos : 0<D)
    (hmass : ∀ i,p0≤p i)
    (hedgeMin : ∀ i j,i≠j→ellMin≤‖b i-b j‖)
    (hedgeMax : ∀ i j,i≠j→‖b i-b j‖≤ellMax)
    (hD : ∀ i,(∑ j,NegativeVotingFanJacobian.facetWeight b (selectedOffsets b p) i j)≤D)
    (ht : τ*(m:ℝ)≤(p0/(2*Real.pi*ellMax))/2) :
    retainedGapCoefficient p0 ellMax D *
      (∑ i,(deriv (fun t : ℝ =>
        (covarianceOffsets (Matrix.gram ℝ b+t • gramVelocity b H) p : Fin m → ℝ)) 0 i)^2) ≤
      retainedCoefficientCeiling p0 τ ellMin *
        (-deriv (deriv (fun t : ℝ => covarianceValue (Matrix.gram ℝ b+t • gramVelocity b H) p)) 0) := by
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound b
  rw [(hasDerivAt_covarianceOffsets_line b σ hσ hlower p hp hs H hH).deriv,
    (hasDerivAt_deriv_covarianceValue_selected b σ hσ hlower p hp hs H hH).deriv]
  have hm : ∀ i,p0 ≤ mass b (selectedOffsets b p) i := by
    rw [selectedOffsets_mass b b.ind.injective p hp hs]
    exact hmass
  have hb := canonicalOffset_control_from_mass_edge_geometry b (selectedOffsets b p)
    (by simpa using hcard) H p0 ellMin ellMax τ D hp0 hmin hmax hτ hDpos hm hedgeMin hedgeMax hD
    (by simpa using ht)
  simpa only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,one_mul,mul_comm] using hb

end NegativeVotingCovarianceOffsetResponse
