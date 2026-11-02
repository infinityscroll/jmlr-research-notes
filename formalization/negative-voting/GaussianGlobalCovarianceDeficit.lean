import GaussianExteriorOrbitBounds
import GaussianUniformLocalCurvature

/-! Unconditional global Gaussian covariance and regular-orbit deficit bounds.
Actual facet continuation discharges the local curvature interface, and an
actual canonical Parseval basis discharges all reference-frame premises. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
universe u
namespace NegativeVotingGlobalCovarianceDeficit
open NegativeVoting NegativeVotingProcrustes NegativeVotingRayDeficit
  NegativeVotingBalancedReference NegativeVotingGaussianMaximumMean
  NegativeVotingRegularCovarianceDeficit NegativeVotingCentroidOptimization
  NegativeVotingAffineLogMassBound NegativeVotingCenteredParseval
  NegativeVotingUniformLocalCurvature NegativeVotingRegularFacetNeighborhood
  NegativeVotingExteriorOrbit NegativeVotingAssignmentCoordinateBridge
  NegativeVotingRegularSecondGap NegativeVotingGaussianMaximum

def globalRadius:ℝ:=facetRadius 64

theorem globalRadius_bounds:0< globalRadius ∧ globalRadius≤1:=
  ⟨(facetRadius_bounds 64 (by norm_num)).1,(facetRadius_bounds 64 (by norm_num)).2.1⟩

def referenceBasis (n:ℕ):AffineBasis (Fin (n+2)) ℝ (FSC.Coord (n+2-1)):=
  centeredParsevalBasis (n+2) (by omega)

theorem referenceBasis_spec (n:ℕ):
    (∑i,referenceBasis n i)=0 ∧
    (∀i j,inner ℝ (referenceBasis n i) (referenceBasis n j)=
      (if i=j then 1 else 0)-1/((n:ℝ)+2)) ∧
    ∀x,(∑i,inner ℝ (referenceBasis n i) x • referenceBasis n i)=x:=by
  simpa only [referenceBasis,Nat.cast_add,Nat.cast_ofNat] using
    centeredParsevalBasis_spec (n+2) (by omega)

theorem eventually_canonical_local_curvature:
    ∀ᶠ n:ℕ in atTop,LocalGaussianCurvature (referenceBasis n) (uniformMass n)
      (globalRadius/(1+Real.log ((n:ℝ)+2))) (referenceScale n/(12*((n:ℝ)+2))):=by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one] with n hn hsq
  have hmean:1≤ maximumMean n:=
    (sq_le_sq₀ (by norm_num:0≤(1:ℝ)) (maximumMean_pos n).le).mp (by simpa using hsq)
  have hb:=referenceBasis_spec n
  exact uniform_local_curvature hn hmean (referenceBasis n) hb.1 hb.2.2 hb.2.1

/-- All PSD covariances, including singular ones, with one threshold before
ambient dimension and rectangular row realization. No curvature premise. -/
theorem eventually_uniform_global_covariance_ray_bound:
    ∀ᶠ n:ℕ in atTop,∀(e:ℕ) (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0),
      let defect:=operatorHilbertSchmidt (normalizedRowCovariance n (referenceBasis n) B-
        ContinuousLinearMap.id ℝ (FSC.Coord (n+2-1)))
      (referenceScale n)^2*defect^2/(48*((n:ℝ)+2))*
        min 1 ((globalRadius/(1+Real.log ((n:ℝ)+2)))/defect)≤ regularCovarianceDeficit n B:=by
  filter_upwards [eventually_canonical_local_curvature,eventually_gt_atTop (0:ℕ)] with n hcurv hn
  intro e B hB
  have hb:=referenceBasis_spec n
  have hL:0<1+Real.log ((n:ℝ)+2):=by
    have hh:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  exact regularCovarianceDeficit_ray_bound_normalized hn (referenceBasis n) hb.2.1 hb.2.2
    _ (div_pos globalRadius_bounds.1 hL) hcurv B hB

/-- The literal rectangular regular-orbit distance, with no spectral,
positive-rank or curvature premise. -/
theorem eventually_uniform_global_orbit_bound:
    ∀ᶠ n:ℕ in atTop,∀(e:ℕ) (he:n+1≤ e)
      (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0),
      let q:=regularOrbitDistance n B/referenceScale n
      (referenceScale n)^2*q^2/(48*((n:ℝ)+2))*
        min 1 ((globalRadius/(1+Real.log ((n:ℝ)+2)))/q)≤ regularCovarianceDeficit n B:=by
  filter_upwards [eventually_canonical_local_curvature,eventually_gt_atTop (0:ℕ)] with n hcurv hn
  intro e he B hB
  have hb:=referenceBasis_spec n
  have hL:0<1+Real.log ((n:ℝ)+2):=by
    have hh:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  exact regularCovarianceDeficit_orbit_bound hn (referenceBasis n) hb.2.1 hb.2.2
    _ (div_pos globalRadius_bounds.1 hL) hcurv (by omega) B hB

/-- Explicit exterior-scale bounds for every actual centered row system
with the displayed energy cap; singular and repeated rows are allowed. -/
theorem eventually_uniform_global_exterior_bounds:
    ∀ᶠ n:ℕ in atTop,∀(e:ℕ) (he:n+1≤ e)
      (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0)
      (hW:rowEnergy B≤2*referenceFirstWeight n)
      (hd:1/((n:ℝ)+2)< regularOrbitDistance n B),
      globalRadius/(240*((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))≤ regularCovarianceDeficit n B ∧
      (regularOrbitDistance n B)^2≤(144/globalRadius)*
        (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B:=by
  filter_upwards [eventually_canonical_local_curvature,
    eventually_uniform_exterior_bounds globalRadius globalRadius_bounds.1 globalRadius_bounds.2]
    with n hcurv hext
  intro e he B hB hW hd
  have hb:=referenceBasis_spec n
  exact hext (n+2-1) e (referenceBasis n) hb.2.1 hb.2.2 hcurv (by omega) B hB hW hd

/-- Actual competitive fractional assignments discharge the energy cap and
centering as well. One threshold precedes every ambient coordinate type,
reference, rule, correlation and Euclidean coordinate realization. -/
theorem eventually_uniform_actual_competitive_exterior_bounds:
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0< r) (hr:r≤1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (e:ℕ) (he:n+1≤ e) (coord:FSC.Coord e≃ₗᵢ[ℝ]EuclideanSpace ℝ κ),
      let B:=centroidRows (coordinateRule coord f)
      1/((n:ℝ)+2)< regularOrbitDistance n B →
      globalRadius/(240*((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2)))≤ regularCovarianceDeficit n B ∧
      (regularOrbitDistance n B)^2≤(144/globalRadius)*
        (((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*regularCovarianceDeficit n B:=by
  filter_upwards [eventually_canonical_local_curvature,
    eventually_uniform_competitive_exterior_bounds globalRadius globalRadius_bounds.1 globalRadius_bounds.2]
    with n hcurv hext
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp e he coord
  have hb:=referenceBasis_spec n
  exact hext κ Ref hRef f hf hp r hr0 hr hcomp (n+2-1) e coord
    (referenceBasis n) hb.2.1 hb.2.2 (by omega) hcurv

end NegativeVotingGlobalCovarianceDeficit
