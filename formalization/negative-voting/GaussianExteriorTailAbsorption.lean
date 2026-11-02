import GaussianCompetitiveExteriorHighTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform absorption of the actual exterior signed high tail. The fractional
alphabet exponent 15/8 is retained before the full voting-range estimate. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
universe u
namespace NegativeVotingExteriorTailAbsorption
open NegativeVoting NegativeVotingCompetitiveExteriorHighTail NegativeVotingExteriorSignedTailRelative
  NegativeVotingGlobalCovarianceDeficit NegativeVotingCompetitiveDeficit NegativeVotingUniformMassBound
  NegativeVotingProcrustes NegativeVotingCentroidOptimization NegativeVotingAssignmentCoordinateBridge
  NegativeVotingExteriorRoutingMargin NegativeVotingGaussianMaximumSecondMoment

 theorem voting_coefficient_bound (C m r:ℝ) (hC:0 ≤ C) (hm:1 ≤ Real.log m)
    (hm0:0 < m) (hr:0 ≤ r) (hrm:r ≤ 2/m) :
    C*r^2*m^(15/8:ℝ)*(1+Real.log m)^4 ≤ 64*C*(Real.log m)^4/m^(1/8:ℝ) := by
  have hlog : 0 ≤ Real.log m := by linarith
  have hL : 0 ≤ 1+Real.log m := by linarith
  have hrsq := pow_le_pow_left₀ hr hrm 2
  have hL4 := pow_le_pow_left₀ hL (show 1+Real.log m ≤ 2*Real.log m by linarith) 4
  have hstep : C*r^2*m^(15/8:ℝ)*(1+Real.log m)^4 ≤
      C*(2/m)^2*m^(15/8:ℝ)*(2*Real.log m)^4 := by gcongr
  have he : m^(15/8:ℝ)/m^2=1/m^(1/8:ℝ) := by
    rw [←Real.rpow_natCast m 2,←Real.rpow_sub hm0]
    norm_num
    rw [Real.rpow_neg hm0.le]
  refine hstep.trans_eq ?_
  calc
    _ = 64*C*(Real.log m)^4*(m^(15/8:ℝ)/m^2) := by ring
    _ = _ := by rw [he];ring

 theorem eventually_uniform_coefficient_small (C ε:ℝ) (hC:0 ≤ C) (hε:0 < ε) :
    ∀ᶠ n:ℕ in atTop,∀r:ℝ,0 ≤ r → r ≤ 1/((n:ℝ)+1) →
      C*r^2*((n:ℝ)+2)^(15/8:ℝ)*(1+Real.log ((n:ℝ)+2))^4 < ε := by
  have ht : Tendsto (fun n:ℕ=>(Real.log ((n:ℝ)+2))^4/((n:ℝ)+2)^(1/8:ℝ)) atTop (𝓝 0) := by
    convert ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ) < 1/8)).tendsto_div_nhds_zero).comp
      size_tendsto using 1
    funext n
    simp only [Function.comp_def]
    norm_num
  have htC : Tendsto (fun n:ℕ=>64*C*((Real.log ((n:ℝ)+2))^4/((n:ℝ)+2)^(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (64*C)
  have hsmall := htC.eventually (Iio_mem_nhds hε)
  have hlarge := (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1
  filter_upwards [hsmall,hlarge] with n hs hl
  simp only [Function.comp_def,mul_zero] at hs hl
  intro r hr hrange
  have hm0:(0:ℝ) < (n:ℝ)+2 := by positivity
  have hr2:r ≤ 2/((n:ℝ)+2) := hrange.trans ((div_le_div_iff₀ (by positivity) hm0).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  exact (voting_coefficient_bound C ((n:ℝ)+2) r hC hl hm0 hr hr2).trans_lt
    (by simpa only [mul_div_assoc] using hs)

 theorem globalHighTailConstant_nonneg : 0 ≤ globalHighTailConstant := by
  have hRad := globalRadius_bounds.1
  have hK := regularMarginConstant_ge_one
  unfold globalHighTailConstant exteriorHighTailConstant exteriorMismatchConstant
  positivity

/-- For any prescribed positive fraction of D, one alphabet threshold works
for all competitive exterior rules and all admissible negative correlations. -/
theorem eventually_uniform_exterior_tail_absorption (ε:ℝ) (hε:0 < ε) :
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
          ε*competitiveDeficit n r f := by
  filter_upwards [eventually_uniform_competitive_exterior_high_tail,
    eventually_uniform_coefficient_small globalHighTailConstant ε globalHighTailConstant_nonneg hε,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds] with n htail hcoef hdef
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp e he coord
  dsimp only
  intro hd
  obtain ⟨R,hR,hH⟩ := htail κ Ref hRef f hf hp r hr0 hr hcomp e he coord hd
  have hD := (hdef κ Ref hRef f hf hp r hr0.le hr hcomp).1
  have hc := mul_le_mul_of_nonneg_right (hcoef r hr0.le hr).le hD
  refine ⟨R,hR,hH.trans ?_⟩
  convert hc using 1 <;> field_simp

end NegativeVotingExteriorTailAbsorption
