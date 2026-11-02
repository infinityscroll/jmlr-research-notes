import GaussianPrimalDualDeficit
import GaussianUniformMassBound

/-! The actual competitive transfer R <= D/r. All bounded-row, dual-offset,
rank and Gaussian realization interfaces are discharged, including singular
and duplicate centroid rows. One alphabet threshold precedes every dimension,
reference, fractional competitor and negative noise parameter. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
universe u
namespace NegativeVotingCompetitiveCovarianceTransfer
open NegativeVoting NegativeVotingPrimalDualDeficit NegativeVotingBoundedOffsetCertificate
open NegativeVotingRegularCovarianceDeficit NegativeVotingOptimizerConstants
open NegativeVotingFractionalMass NegativeVotingAssignmentCoordinateBridge
open NegativeVotingCentroidOptimization NegativeVotingCompetitiveDeficit
open NegativeVotingCompetitiveSharpMass NegativeVotingCompetitiveMassWindow
open NegativeVotingGaussianMaximumLocalization NegativeVotingGaussianMaximumMean
open NegativeVotingBalancedReference NegativeVotingRegularScoreLaw

/-- The coefficient is uniformly absorbable on the complete negative voting
range; no lower cutoff on the magnitude of the correlation is introduced. -/
theorem eventually_uniform_offset_absorption:
    ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ 1/((n:ℝ)+1) →
      (4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2)*r≤1:=by
  have hsmall:∀ᶠn:ℕ in atTop,sharpMassMajorant (4*certificateQuadraticConstant) n<1:=
    (sharpMassMajorant_tendsto_zero (4*certificateQuadraticConstant)).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  intro r hr0 hr
  have hm:0<(n:ℝ)+2:=by positivity
  have hr2:r≤2/((n:ℝ)+2):=hr.trans (by
    apply (div_le_div_iff₀ (by positivity) hm).mpr
    have hh:0≤(n:ℝ):=Nat.cast_nonneg n
    linarith)
  have hC:0≤ certificateQuadraticConstant:=le_trans (by norm_num) certificateQuadraticConstant_ge_thirtytwo
  have hmajor:(2/((n:ℝ)+2))*(4*certificateQuadraticConstant)*(1+Real.log ((n:ℝ)+2))^2≤1:=by
    unfold sharpMassMajorant at hn
    have hA:=referenceSecondWeight_nonneg n
    have hi:0≤2/((n:ℝ)+2):=by positivity
    linarith
  have hh:=mul_le_mul_of_nonneg_left hr2
    (show 0≤4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2 by positivity)
  exact hh.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hmajor)

/-- Every actual completed-measurable fractional competitor has the stated
covariance deficit bound, including arbitrarily small negative correlations. -/
theorem eventually_uniform_actual_covariance_deficit_transfer:
    ∀ᶠn:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐx∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0< r) (hr:r≤1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (d:ℕ) (coord:FSC.Coord d≃ₗᵢ[ℝ]EuclideanSpace ℝ κ),
      regularCovarianceDeficit n (centroidRows (coordinateRule coord f))≤ competitiveDeficit n r f/r∧
      regularCovarianceDeficit n (centroidRows (coordinateRule coord f))≤128*r/((n:ℝ)+2):=by
  filter_upwards [eventually_ge_atTop numericThreshold,
    eventually_uniform_regular_competitive_mass_window,eventually_uniform_offset_absorption,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds]
    with n hn hwindow habs hdef
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp d coord
  have hm:∀i,assignmentMass f i≤2/((n:ℝ)+2):=fun i=>
    ((hwindow κ Ref hRef f hf hp r hr0.le hr hcomp).2 i).2
  have hfeas:=coordinateRule_feasible coord f hf hp
  have hR:=feasible_covariance_deficit_bound (by omega) (assignmentMass f)
    (fun i=>(assignmentMass_mem_Icc f hf hp i).1) (assignmentMass_sum f hf hp)
    (coordinateRule coord f) hfeas hm
  rw [coordinateRule_centroidEnergy coord f hf hp] at hR
  change regularCovarianceDeficit n (centroidRows (coordinateRule coord f))≤
    referenceFirstWeight n-assignmentFirstEnergy f+
      4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f at hR
  have hδ:0≤ massDeficit n f:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hsmall:=mul_le_mul_of_nonneg_right (habs r hr0.le hr) hδ
  have hscaled:=mul_le_mul_of_nonneg_right hR hr0.le
  have htransfer:regularCovarianceDeficit n (centroidRows (coordinateRule coord f))≤ competitiveDeficit n r f/r:=by
    apply (le_div_iff₀ hr0).mpr
    unfold competitiveDeficit
    nlinarith
  refine ⟨htransfer,htransfer.trans ?_⟩
  have hD:competitiveDeficit n r f≤128*r^2/((n:ℝ)+2):=
    (hdef κ Ref hRef f hf hp r hr0.le hr hcomp).2.2.2
  apply (div_le_iff₀ hr0).mpr
  convert hD using 1 <;> ring

end NegativeVotingCompetitiveCovarianceTransfer
