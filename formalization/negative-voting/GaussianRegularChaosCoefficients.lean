import GaussianRegularQuadraticSymmetry
import RegularSimplexSecondMomentAlgebra

/-! Concrete regular-simplex second-chaos coefficient, with all moment hypotheses derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingRegularMaximum
open NegativeVoting NegativeVotingModern NegativeVotingRegularQuadratic
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingGaussianMaximumLocalization
  NegativeVotingRegularSecondAlgebra OAI.MinUncut.GaussianHermite

/-- The actual moment tensor has the predicted Frobenius norm. -/
theorem canonical_second_tensor_energy (n : ℕ) (hn : 0 < n) (i : Fin (n+2)) :
    (∑ a, ∑ c, (moment n i a c)^2)=
      (maximumSecondMoment n-1)^2/(((n:ℝ)+1)*(n:ℝ)) := by
  have h := frobenius_sq_of_stabilizer (m := n+2) (by omega) i (moment n i)
    (moment_symm n i) (moment_row_sum_zero n i) (moment_trace_zero n i)
    (fun a b ha hb j k => moment_swap_invariant n i a b ha hb j k)
  rw [h,moment_distinguished]
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  norm_num only [Nat.cast_add,Nat.cast_ofNat]
  rw [show ((n:ℝ)+2)-1=(n:ℝ)+1 by ring,show ((n:ℝ)+2)-2=(n:ℝ) by ring]
  field_simp [hnR.ne',show (n:ℝ)+1 ≠ 0 by positivity,show (n:ℝ)+2 ≠ 0 by positivity] <;> ring

/-- The second coefficient is the literal degree-two Hermite energy of the
canonical regular-max assignment. No covariance/symmetry/trace premise remains. -/
theorem canonical_chaosEnergy_two (n : ℕ) (hn : 0 < n) :
    chaosEnergy (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) 2=referenceSecondWeight n := by
  rw [chaosEnergy_two]
  change (1/2:ℝ)*(∑ i, ∑ a, ∑ c, (moment n i a c)^2)=referenceSecondWeight n
  simp_rw [canonical_second_tensor_energy n hn]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  unfold referenceSecondWeight
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  field_simp [hnR.ne',show (n:ℝ)+1 ≠ 0 by positivity] <;> ring

/-- The moment calculation therefore gives a vanishing actual reference second energy. -/
theorem canonical_second_energy_tendsto_zero :
    Tendsto (fun n => chaosEnergy (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) 2) atTop (𝓝 0) := by
  apply referenceSecondWeight_tendsto_zero.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (canonical_chaosEnergy_two n hn).symm

end NegativeVotingRegularMaximum
