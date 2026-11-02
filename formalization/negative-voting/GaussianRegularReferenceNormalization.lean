import GaussianNearRegularBalancedGeometry
import GaussianRegularMassSymmetry
import GaussianBalancedReference

/-! Exact normalization of the scaled regular reference: its selected
balanced offsets are zero and its actual Gaussian moments do not depend on
positive score scaling. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularReferenceNormalization
open NegativeVoting NegativeVotingFan NegativeVotingFanSelectedOffsets
  NegativeVotingNearRegularBalancedGeometry NegativeVotingRegularMassSymmetry
  NegativeVotingBalancedReference NegativeVotingFanQuadraticMoments NegativeVotingFanInverse
variable {d m : ℕ} [NeZero m]

theorem scaled_weights_zero_general (R : Fin m→FSC.Coord d) (α : ℝ) (hα : 0 < α)
    (x : FSC.Coord d) (i : Fin m) : weights (α•R) 0 x i=weights R 0 x i := by
  change maxWeights (fun j=>inner ℝ (α • R j) x+0) i=
    maxWeights (fun j=>inner ℝ (R j) x+0) i
  simp only [add_zero,real_inner_smul_left]
  exact maxWeights_mul_pos _ α hα i

theorem regular_mass_zero (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    mass R 0=(fun _=>(m:ℝ)⁻¹) := by
  funext i
  have he j : mass R 0 j=mass R 0 i :=
    regular_mass_eq_of_offset_eq R (1/(m:ℝ)) hG 0 j i rfl
  have hs := mass_sum R 0
  simp_rw [he] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hm : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [← one_div]
  apply (eq_div_iff hm).mpr
  simpa only [mul_comm] using hs

theorem regular_scaled_mass_zero (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) : mass (α•R) 0=(fun _=>(m:ℝ)⁻¹) := by
  rw [←regular_mass_zero R hG]
  funext i
  unfold mass
  simp_rw [scaled_weights_zero_general R α hα]

theorem selected_regular_scaled_zero (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) :
    (selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹) : Fin m→ℝ)=0 := by
  have hh := selectedOffsets_eq (α•R) (fun _=>(m:ℝ)⁻¹) α hα
    (regular_scaled_singular R hG α) (0:centeredGauge (Fin m)) (regular_scaled_mass_zero R hG α hα)
  exact congrArg (fun a : centeredGauge (Fin m)=>(a:Fin m→ℝ)) hh

theorem winningCell_scaled_zero (R : Fin m→FSC.Coord d) (α : ℝ) (hα : 0 < α) (i : Fin m) :
    winningCell (α•R) 0 i=winningCell R 0 i := by
  ext x
  simp only [winningCell,scores,Pi.zero_apply,add_zero,Pi.smul_apply,real_inner_smul_left,
    mul_le_mul_iff_right₀ hα]

theorem secondMomentTensor_scaled_zero (R : Fin m→FSC.Coord d)
    (α : ℝ) (hα : 0 < α) (i : Fin m) (j k : Fin d) :
    secondMomentTensor (α•R) 0 i j k=secondMomentTensor R 0 i j k := by
  unfold secondMomentTensor
  rw [winningCell_scaled_zero R α hα]

end NegativeVotingRegularReferenceNormalization
