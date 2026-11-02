import GaussianMassSemiconcavity
import GaussianAssignmentCoordinateBridge
import GaussianCenteredParsevalBasis
import GaussianCompetitiveDeficit

/-! Uniform actual Gaussian mass-value and competitive-localization bounds.
All covariance, offset, optimizer, and mass-value premises are discharged. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical RealInnerProductSpace
universe u
namespace NegativeVotingUniformMassBound
open NegativeVoting NegativeVotingFractionalMass NegativeVotingMassSemiconcavity
  NegativeVotingAssignmentCoordinateBridge NegativeVotingCenteredParseval
  NegativeVotingOptimizerConstants NegativeVotingBalancedReference
  NegativeVotingGaussianMaximumMean NegativeVotingRegularScoreLaw
  NegativeVotingCompetitiveDeficit
variable {κ : Type u} [Fintype κ]

/-- An actual canonical centered Parseval affine basis removes every geometric
input from the uniform prescribed-mass first-chaos estimate. -/
theorem assignmentFirstEnergy_bound_in_mass_window (n:ℕ)
    (hm : numericThreshold ≤ n+2)
    (f:(κ→ℝ)→Fin (n+2)→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
    (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
    (hwindow:∀i,assignmentMass f i∈Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2))) :
    assignmentFirstEnergy f≤ referenceFirstWeight n+
      mixedConstant*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f := by
  obtain ⟨b,hcenter,hG,hP⟩:=exists_centered_parseval_affineBasis (n+2) (by omega)
  have hG':∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hdim : 2 ≤ n+2-1:=by
    have hh:3 ≤ n+2:=(numericThreshold_spec (n+2) hm).1
    omega
  obtain ⟨δ,hδ,hbound⟩:=uniform_positive_floor_mass_bound b hG' hP hdim hm
  have hbox:∀i,assignmentMass f i∈Icc (actualMassLower ((n+2:ℕ):ℝ)) (2/((n+2:ℕ):ℝ)):=by
    simpa only [actualMassLower,Nat.cast_add,Nat.cast_ofNat,div_div] using hwindow
  have hlo:0<actualMassLower ((n+2:ℕ):ℝ):=by unfold actualMassLower;positivity
  have hmass:∀i,0<assignmentMass f i:=fun i=>hlo.trans_le (hbox i).1
  have hb:assignmentFirstEnergy f≤ massValueUpperBound n (assignmentMass f):=by
    apply assignmentFirstEnergy_bound_of_small_floors b hG hP f hf hp hmass
      (massValueUpperBound n (assignmentMass f)) δ hδ
    intro ε hε hεδ C hC _
    exact hbound ε hε hεδ (assignmentMass f) (assignmentMass_sum f hf hp) hbox C hC
  exact hb

/-- The alphabet threshold precedes every ambient dimension and fractional
Gaussian rule. Completed measurability and AE simplex constraints suffice. -/
theorem eventually_uniform_mass_value_bound :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x)),
      (∀i,assignmentMass f i∈Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2))) →
      assignmentFirstEnergy f≤ referenceFirstWeight n+
        mixedConstant*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f := by
  filter_upwards [eventually_ge_atTop numericThreshold] with n hn
  intro κ _ f hf hp hw
  exact assignmentFirstEnergy_bound_in_mass_window n (by omega) f hf hp hw

/-- Cubic mass localization for actual negative-noise competitors, with the
previously explicit mass-value premise now proved and discharged. -/
theorem eventually_uniform_sharp_competitive_mass_bound :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (B:Fin (n+2)→κ→ℝ) (hB:RegularSimplexGram B)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0≤ r) (hr:r≤1/((n:ℝ)+1)),
      gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment B) →
      massDeficit n f≤512/((n:ℝ)+2)^3 := by
  filter_upwards [eventually_uniform_mass_value_bound,
    eventually_uniform_regular_competitive_mass_window,
    NegativeVotingCompetitiveSharpMass.eventually_uniform_sharp_mass_bound mixedConstant mixedConstant_pos.le]
    with n hvalue hwindow hsharp
  intro κ _ B hB f hf hp r hr0 hr hcomp
  exact hsharp κ B hB f hf hp r hr0 hr hcomp
    (hvalue κ f hf hp (hwindow κ B hB f hf hp r hr0 hr hcomp).2)

/-- The actual r-squared deficit estimate is uniform down to r=0 and across
all finite Gaussian ambient spaces and all regular reference orientations. -/
theorem eventually_uniform_competitive_deficit_bounds :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (B:Fin (n+2)→κ→ℝ) (hB:RegularSimplexGram B)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0≤ r) (hr:r≤1/((n:ℝ)+1)),
      gaussianNoiseStability (-r) f≤ gaussianNoiseStability (-r) (regularAssignment B) →
      0≤ competitiveDeficit n r f ∧ massDeficit n f≤2*competitiveDeficit n r f ∧
      r*|assignmentFirstEnergy f-referenceFirstWeight n|≤ competitiveDeficit n r f ∧
      competitiveDeficit n r f≤128*r^2/((n:ℝ)+2) := by
  filter_upwards [eventually_uniform_mass_value_bound,
    eventually_uniform_regular_competitive_mass_window,
    NegativeVotingCompetitiveDeficit.eventually_uniform_competitive_deficit_bounds mixedConstant mixedConstant_pos.le]
    with n hvalue hwindow hdeficit
  intro κ _ B hB f hf hp r hr0 hr hcomp
  exact hdeficit κ B hB f hf hp r hr0 hr hcomp
    (hvalue κ f hf hp (hwindow κ B hB f hf hp r hr0 hr hcomp).2)

end NegativeVotingUniformMassBound
