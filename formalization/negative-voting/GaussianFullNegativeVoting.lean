import GaussianLocalBalancedSecondChaos
import GaussianExteriorNoiseAssembly
import GaussianMainGoalAssembly

/-! Final assembly of the original negative-voting statement. All local and
exterior analytic inputs are instantiated by the actual Gaussian theorems. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace NegativeVotingFullAssembly
open NegativeVotingMainGoalAssembly NegativeVotingLocalBalancedSecondChaos
  NegativeVotingLocalOwnCentroidRigidity NegativeVotingExteriorNoiseAssembly

theorem eventual_competitive_rigidity : EventualCompetitiveRigidity := by
  have hlocal := eventually_local_rigidity_of_balanced_loss localBalancedConstant 18
    localBalancedConstant_nonneg actual_eventual_local_balanced_second_loss
  filter_upwards [eventually_competitive_orbit_distance_le,hlocal] with n hext hloc
  intro d hd Ref hRef f hf hp r hr hrange hcomp
  have hnear := hext d hd Ref hRef f hf hp r hr hrange hcomp
  exact hloc d hd Ref hRef f hf hp r hr hrange hcomp hnear

end NegativeVotingFullAssembly

namespace NegativeVoting

/-- The exact original large-alphabet Gaussian negative-voting theorem,
including the full negative voting interval and the AE-regular equality class. -/
theorem full_negative_voting : FullNegativeVotingStatement :=
  NegativeVotingMainGoalAssembly.fullStatement_of_eventual_competitive_rigidity
    NegativeVotingFullAssembly.eventual_competitive_rigidity

end NegativeVoting
