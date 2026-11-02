import GaussianExteriorSignedTailRelative
import GaussianCompetitiveTightMassWindow
import GaussianCompetitiveCovarianceTransfer

/-! The actual exterior signed high-tail estimate for every competitive rule.
There is one alphabet threshold before dimension, correlation and competitor;
all geometric and mass premises of the analytic estimate are discharged. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
universe u
namespace NegativeVotingCompetitiveExteriorHighTail
open NegativeVoting NegativeVotingExteriorSignedTailRelative NegativeVotingCompetitiveTightMassWindow
  NegativeVotingGlobalCovarianceDeficit NegativeVotingCompetitiveCovarianceTransfer
  NegativeVotingCompetitiveDeficit NegativeVotingUniformMassBound NegativeVotingExteriorReference
  NegativeVotingCentroidOptimization NegativeVotingProcrustes NegativeVotingAssignmentCoordinateBridge
  NegativeVotingFractionalMass NegativeVotingBalancedReference NegativeVotingGaussianMaximumMean

def globalHighTailConstant : ℝ :=
  exteriorHighTailConstant (144/globalRadius) (globalRadius/240)

/-- No final tail inequality, mass box, covariance floor, source norm,
rank condition on the competitor, or dimension-dependent threshold is assumed. -/
theorem eventually_uniform_competitive_exterior_high_tail :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐx ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0 < r) (hr:r ≤ 1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (e:ℕ) (he:n+1 ≤ e) (coord:FSC.Coord e≃ₗᵢ[ℝ]EuclideanSpace ℝ κ),
      let F:=coordinateRule coord f
      1/((n:ℝ)+2) < regularOrbitDistance n (centroidRows F) →
      ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
        |signedTailDifference r F (NegativeVotingFan.weights R 0)| ≤
          globalHighTailConstant*r^3*((n:ℝ)+2)^(15/8:ℝ)*
            (1+Real.log ((n:ℝ)+2))^4*(competitiveDeficit n r f/r) := by
  filter_upwards [eventually_uniform_competitive_half_mass_window,
    eventually_uniform_cubic_tail_scale,eventually_reference_scale_bounds,
    eventually_uniform_actual_covariance_deficit_transfer,
    eventually_uniform_actual_competitive_exterior_bounds,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds,
    eventually_gt_atTop (0:ℕ)] with n hmass htail hscale htransfer hext hdef hn
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp e he coord
  dsimp only
  intro hd
  let F:=coordinateRule coord f
  let J:=competitiveDeficit n r f/r
  have hF:=coordinateRule_feasible coord f hf hp
  have hm := hmass κ Ref hRef f hf hp r hr0.le hr hcomp
  have hD := hdef κ Ref hRef f hf hp r hr0.le hr hcomp
  have hJ:0 ≤ J := div_nonneg hD.1 hr0.le
  have htr := (htransfer κ Ref hRef f hf hp r hr0 hr hcomp e coord).1
  have hx := hext κ Ref hRef f hf hp r hr0 hr hcomp e he coord hd
  have hL : 0 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh:=Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  have hα:Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n := by
    apply (sq_le_sq₀ (by positivity) (referenceScale_pos n).le).mp
    rw [div_pow,Real.sq_sqrt hL]
    exact hscale.1
  have hfirst:referenceFirstWeight n-centroidEnergy F ≤ J := by
    rw [coordinateRule_centroidEnergy coord f hf hp]
    apply (le_div_iff₀ hr0).mpr
    have hδ:0 ≤ massDeficit n f := Finset.sum_nonneg fun i _=>sq_nonneg _
    dsimp [J,competitiveDeficit]
    nlinarith
  have hRad := globalRadius_bounds.1
  have hdist:(regularOrbitDistance n (centroidRows F))^2 ≤
      (144/globalRadius)*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*
        (1+Real.log ((n:ℝ)+2))*J := by
    exact hx.2.trans (mul_le_mul_of_nonneg_left htr (by positivity))
  have hfloor:(globalRadius/240)/(((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2))) ≤ J := by
    have hh:=hx.1.trans htr
    simpa only [div_div, mul_assoc] using hh
  have hb:=referenceBasis_spec n
  exact exists_regular_relative_signed_tail hn (referenceBasis n) hb.2.1 hb.2.2 (by omega)
    hα (assignmentMass f) F hF (fun i=>(hm i).2) r hr0 (htail r hr0.le hr)
    J (144/globalRadius) (globalRadius/240) hJ (by positivity)
    (by positivity) hfirst
    (lt_trans (by positivity : (0:ℝ) < 1/((n:ℝ)+2)) hd) hdist hfloor

end NegativeVotingCompetitiveExteriorHighTail
