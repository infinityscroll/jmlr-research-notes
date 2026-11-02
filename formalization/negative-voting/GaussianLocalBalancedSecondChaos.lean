import GaussianBalancedCovarianceSecondChaos
import GaussianNormalizedLocalGeometry
import GaussianLocalOwnCentroidRigidity

/-! The balanced local second-chaos estimate for the literal regular-orbit
ball, with radial scale, rank, core covariance and all analytic inputs derived. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingLocalBalancedSecondChaos
open NegativeVotingBalancedCovarianceSecondChaos NegativeVotingNormalizedLocalGeometry
  NegativeVotingLocalOwnCentroidRigidity NegativeVotingLocalOrbitDeficitPayment
  NegativeVotingCovarianceRadialNormalization NegativeVotingGlobalCovarianceDeficit
  NegativeVotingCentroidOptimization NegativeVotingRegularCovarianceDeficit
  NegativeVotingBalancedReference NegativeVotingProcrustes
  NegativeVotingFanQuadraticMoments NegativeVotingFanSelectedOffsets

def localBalancedConstant : ℝ := 2*rectangleLogConstant

theorem localBalancedConstant_nonneg : 0 ≤ localBalancedConstant :=
  mul_nonneg (by norm_num) rectangleLogConstant_nonneg

/-- No balanced-energy, CDF, curvature or covariance-factor premise remains. -/
theorem actual_eventual_local_balanced_second_loss :
    EventualLocalBalancedSecondLoss localBalancedConstant 18 := by
  filter_upwards [eventually_normalized_balanced_secondEnergy,
    eventually_normalized_local_data,eventually_exists_local_paid_reference] with n hbal hnorm hpaid
  intro e he B hB hR hlocal
  obtain ⟨U,hU,hclose,_⟩ := hpaid e he B hB hR hlocal
  obtain ⟨hW,_,hdef,hsmall,hE⟩ := hnorm e B U hB hU hclose
  have hb := referenceBasis_spec n
  have h := hbal (n+2-1) e (referenceBasis n) hb.1 hb.2.2 hb.2.1
    (normalizedRows n B) (normalizedRows_centered B hB) (normalizedRows_energy B hW) hsmall
  rw [hE] at h
  have hL : 0 ≤ 1+Real.log ((n:ℝ)+2) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hcoef : 0 ≤ rectangleLogConstant*(1+Real.log ((n:ℝ)+2))^18*Real.sqrt ((n:ℝ)+2) := by
    positivity [rectangleLogConstant_nonneg]
  have hh := mul_le_mul_of_nonneg_left hdef hcoef
  dsimp only [localBalancedConstant]
  nlinarith only [h,hh]

end NegativeVotingLocalBalancedSecondChaos
