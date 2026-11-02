import GaussianEqualRowProxyLoss

/-! Actual competitive second-chaos comparison through the equal-row proxy.
The only unpaid geometric input is explicitly the original radial error. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingCompetitiveSecondChaosComparison
open NegativeVoting NegativeVotingModern NegativeVotingEqualRowProxyLoss
  NegativeVotingEqualRowRegularCoefficient NegativeVotingCompetitiveEqualRowProxy
  NegativeVotingCompetitiveCovarianceTransfer NegativeVotingCentroidOptimization
  NegativeVotingAssignmentCoordinateBridge NegativeVotingRegularCovarianceDeficit
  NegativeVotingGeometricMedianProxy NegativeVotingOneRowRadialCloseness
  NegativeVotingBalancedReference NegativeVotingCompetitiveDeficit
  NegativeVotingEqualRowRoutingComparison NegativeVotingRegularScoreLaw
  NegativeVotingGaussianMaximumLocalization OAI.MinUncut.GaussianHermite

/-- This specializes all Gaussian and feasible-proxy hypotheses. The remaining
row-payment hypothesis is displayed, not mistaken for an established estimate. -/
theorem eventually_second_chaos_of_radial_payment :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (Ref : Fin (n+2)→Fin d→ℝ), RegularSimplexGram Ref →
      ∀ (f : (Fin d→ℝ)→Fin (n+2)→ℝ),
        (∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d))) →
        (∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) →
      ∀ r : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) →
        gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref) →
      ∀ K : ℝ, 0 ≤ K →
        radialError (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)) (referenceRowRadius n) ≤
          K*regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)) →
        referenceSecondWeight n-chaosEnergy f 2 ≤
          240*(1+Real.log ((n:ℝ)+2))*(1+16386*K)*(competitiveDeficit n r f/r)+
          2160*(1+Real.log ((n:ℝ)+2))*Real.exp (-16*(1+Real.log ((n:ℝ)+2))) := by
  filter_upwards [eventually_competitive_equalRowProxy,
    eventually_uniform_actual_covariance_deficit_transfer,
    eventually_equal_row_actual_second_chaos_lower] with n hproxy htransfer hE2
  intro d Ref hRef f hf hp r hr0 hr hcomp K hK hpay
  let coord:FSC.Coord d≃ₗᵢ[ℝ]EuclideanSpace ℝ (Fin d):=LinearIsometryEquiv.refl ℝ _
  let B:=centroidRows (coordinateRule coord f)
  let J:=competitiveDeficit n r f/r
  let L:ℝ:=1+Real.log ((n:ℝ)+2)
  have hL:0 ≤ L:=by
    have hh:=Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    dsimp [L];linarith
  obtain ⟨Z,hZcenter,hZnorm,hZspan,hZdist⟩:=hproxy (Fin d) Ref hRef f hf hp r hr0 hr hcomp d coord
  have hR:regularCovarianceDeficit n B ≤ J:=(htransfer (Fin d) Ref hRef f hf hp r hr0 hr hcomp d coord).1
  have hd:(∑i,‖Z i-B i‖^2) ≤ 16386*K*J:=by
    apply hZdist.trans
    change radialError B (referenceRowRadius n) ≤ K*regularCovarianceDeficit n B at hpay
    have hh:=hpay.trans (mul_le_mul_of_nonneg_left hR hK)
    have hh2:=mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 16386)
    simpa only [mul_assoc] using hh2
  have hloss:proxyLoss Z f (referenceScale n) ≤ (1+16386*K)*J/2:=by
    have hh:=proxyLoss_le_competitiveDeficit_and_distance Z hZnorm f hf hp r hr0
    change proxyLoss Z f (referenceScale n) ≤ competitiveDeficit n r f/(2*r)+(∑i,‖Z i-B i‖^2)/2 at hh
    have hj:competitiveDeficit n r f/(2*r)=J/2:=by dsimp [J];ring
    rw [hj] at hh
    nlinarith
  have hz (i:Fin (n+2)):‖Z i‖^2=(referenceScale n)^2*(1-1/((n:ℝ)+2)):=by
    rw [hZnorm i,referenceRowRadius_sq]
    field_simp
    ring
  have hactual:=hE2 d Z hz hZcenter f hf (hp.mono fun x hx=>hx.1) (hp.mono fun x hx=>hx.2)
  have hh:=mul_le_mul_of_nonneg_left hloss (show 0 ≤ 480*L by positivity)
  change referenceSecondWeight n-480*L*proxyLoss Z f (referenceScale n)-
    2160*L*Real.exp (-16*L) ≤ chaosEnergy f 2 at hactual
  change referenceSecondWeight n-chaosEnergy f 2 ≤ 240*L*(1+16386*K)*J+2160*L*Real.exp (-16*L)
  nlinarith only [hh,hactual]

end NegativeVotingCompetitiveSecondChaosComparison
