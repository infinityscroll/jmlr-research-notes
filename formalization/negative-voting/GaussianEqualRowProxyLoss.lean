import GaussianEqualRowRegularCoefficient
import GaussianCompetitiveEqualRowProxy

/-! Exact first-moment loss of an actual equal-radius proxy. This bridge
retains the complete covariance and radial errors before any absorption. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingEqualRowProxyLoss
open NegativeVoting NegativeVotingSecondChaosLower NegativeVotingMassCentroid
  NegativeVotingCentroidOptimization NegativeVotingAssignmentCoordinateBridge
  NegativeVotingFractionalMass NegativeVotingEqualRowRoutingComparison
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingOneRowRadialCloseness NegativeVotingBalancedReference
  NegativeVotingCovarianceRadialNormalization NegativeVotingCompetitiveDeficit
variable {n d : ℕ}

lemma coordinate_centroid_eq_firstMoment (f : (Fin d→ℝ)→ℝ)
    (hf : AEMeasurable f (standardGaussian (Fin d)))
    (h01 : ∀ᵐx ∂standardGaussian (Fin d),0 ≤ f x ∧ f x ≤ 1) :
    gaussianCentroid (fun x:FSC.Coord d=>f x.ofLp)=firstMomentVector f := by
  let e:FSC.Coord d≃ₗᵢ[ℝ]EuclideanSpace ℝ (Fin d):=LinearIsometryEquiv.refl ℝ _
  let F:FSC.Coord d→ℝ:=fun x=>f x.ofLp
  have hm:=coordinate_map_measurePreserving e
  have hF:AEMeasurable F (stdGaussian (FSC.Coord d)):=
    (hf.aestronglyMeasurable.comp_measurePreserving hm).aemeasurable
  have hF01:∀ᵐx ∂stdGaussian (FSC.Coord d),0 ≤ F x ∧ F x ≤ 1:=hm.quasiMeasurePreserving.ae h01
  have hV:=fractional_vector_integrable F hF hF01
  ext j
  let L:FSC.Coord d→L[ℝ]ℝ:=EuclideanSpace.proj (𝕜:=ℝ) j
  change (gaussianCentroid F) j=∫x,x j*f x ∂standardGaussian (Fin d)
  calc
    _ = ∫x:FSC.Coord d,L (F x • x) ∂stdGaussian (FSC.Coord d):=(L.integral_comp_comm hV).symm
    _ = ∫x:FSC.Coord d,F x*x j ∂stdGaussian (FSC.Coord d):=by
      apply integral_congr_ae;filter_upwards with x;rw [map_smul];rfl
    _ = _:=by
      have hh:=coordinate_integral e (fun x=>f x*x j)
        (hf.aestronglyMeasurable.mul (measurable_pi_apply j).aestronglyMeasurable)
      change (∫x:FSC.Coord d,f x.ofLp*x j ∂stdGaussian (FSC.Coord d))=
        ∫x,f x*x j ∂standardGaussian (Fin d) at hh
      simpa only [F,mul_comm] using hh

lemma proxy_row_energy (Z : Fin (n+2)→FSC.Coord d)
    (hZ : ∀i,‖Z i‖=referenceRowRadius n) : rowEnergy Z=referenceFirstWeight n := by
  unfold rowEnergy
  simp only [hZ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  exact referenceRadius_energy n

/-- Exact square completion, with the actual fractional assignment. -/
theorem proxyLoss_square_completion (Z : Fin (n+2)→FSC.Coord d)
    (hZ : ∀i,‖Z i‖=referenceRowRadius n)
    (f : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) :
    proxyLoss Z f (referenceScale n)=
      (referenceFirstWeight n-assignmentFirstEnergy f)/2+
      (∑i,‖Z i-centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i‖^2)/2 := by
  have h0:∀ᵐx ∂standardGaussian (Fin d),∀i,0 ≤ f x i:=hp.mono fun x hx=>hx.1
  have hs:∀ᵐx ∂standardGaussian (Fin d),∑i,f x i=1:=hp.mono fun x hx=>hx.2
  have hcent (i:Fin (n+2)):centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i=
      firstMomentVector (fun x=>f x i):=coordinate_centroid_eq_firstMoment _ (hf i)
        (fractional_coordinate_bounds f hp i)
  have hw:referenceScale n*maximumMean n=referenceFirstWeight n:=by
    unfold referenceScale referenceFirstWeight;ring
  rw [proxyLoss_eq_centroid Z f (referenceScale n) hf h0 hs]
  change referenceScale n*maximumMean n-_=_
  rw [hw]
  simp_rw [←hcent]
  have he:=coordinateRule_centroidEnergy (LinearIsometryEquiv.refl ℝ (FSC.Coord d)) f hf hp
  have hsq:(∑i,‖Z i-centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i‖^2)=
      rowEnergy Z+assignmentFirstEnergy f-
      2*(∑i,inner ℝ (Z i) (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i)):=by
    simp only [norm_sub_sq_real,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    change rowEnergy Z-2*(∑i,inner ℝ (Z i) (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i))+
      centroidEnergy (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)=_
    rw [he]
    ring
  rw [proxy_row_energy Z hZ] at hsq
  linarith

/-- Only the literal proxy distance is left here; no row-payment theorem is
presupposed. The mass term is nonnegative for every actual assignment. -/
theorem proxyLoss_le_competitiveDeficit_and_distance (Z : Fin (n+2)→FSC.Coord d)
    (hZ : ∀i,‖Z i‖=referenceRowRadius n)
    (f : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
    (r : ℝ) (hr : 0<r) :
    proxyLoss Z f (referenceScale n) ≤ competitiveDeficit n r f/(2*r)+
      (∑i,‖Z i-centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i‖^2)/2 := by
  rw [proxyLoss_square_completion Z hZ f hf hp]
  have hδ:0 ≤ massDeficit n f:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hh:(referenceFirstWeight n-assignmentFirstEnergy f)/2 ≤ competitiveDeficit n r f/(2*r):=by
    apply (le_div_iff₀ (by positivity : 0<2*r)).mpr
    unfold competitiveDeficit
    nlinarith
  linarith

end NegativeVotingEqualRowProxyLoss
