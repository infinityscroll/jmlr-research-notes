import GaussianDiagonalSecondBalanceEquation
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Exact time reversal for the literal variance and selected balancing
paths. Both first and second derivative identities are unconditional identities
of Lean's total derivative; genuine differentiability is supplied separately. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Classical Topology
namespace NegativeVotingVariancePathSymmetry
open NegativeVotingDiagonalOffsetContinuation NegativeVotingFanInverse
variable {n : ℕ}

lemma varianceSigma_neg_direction (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceSigma (-ξ) t=varianceSigma ξ (-t) := by
  funext i
  simp only [varianceSigma,Pi.neg_apply,mul_neg,neg_mul]

lemma varianceSigma_neg_neg (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceSigma (-ξ) (-t)=varianceSigma ξ t := by
  rw [varianceSigma_neg_direction,neg_neg]

lemma varianceOffsets_neg_direction (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceOffsets n (-ξ) t=varianceOffsets n ξ (-t) := by
  unfold varianceOffsets
  rw [varianceSigma_neg_direction]

lemma varianceOffsets_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceOffsets n (-ξ) (-t)=varianceOffsets n ξ t := by
  rw [varianceOffsets_neg_direction,neg_neg]

lemma varianceOffsetVector_neg_direction (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceOffsetVector n (-ξ) t=varianceOffsetVector n ξ (-t) := by
  unfold varianceOffsetVector
  rw [varianceOffsets_neg_direction]

lemma varianceOffsetVector_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceOffsetVector n (-ξ) (-t)=varianceOffsetVector n ξ t := by
  rw [varianceOffsetVector_neg_direction,neg_neg]

lemma varianceOffsets_deriv_neg_direction (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    deriv (varianceOffsets n (-ξ)) t = -deriv (varianceOffsets n ξ) (-t) := by
  have he:varianceOffsets n (-ξ)=(fun s=>varianceOffsets n ξ (-s)):=
    funext (varianceOffsets_neg_direction n ξ)
  rw [he,deriv_comp_neg]

lemma varianceOffsets_deriv_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    deriv (varianceOffsets n (-ξ)) (-t) = -deriv (varianceOffsets n ξ) t := by
  rw [varianceOffsets_deriv_neg_direction,neg_neg]

lemma varianceOffsets_secondDeriv_neg_direction (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    deriv (deriv (varianceOffsets n (-ξ))) t = deriv (deriv (varianceOffsets n ξ)) (-t) := by
  have he:deriv (varianceOffsets n (-ξ))=(fun s=>-deriv (varianceOffsets n ξ) (-s)):=
    funext (varianceOffsets_deriv_neg_direction n ξ)
  rw [he,deriv.fun_neg,deriv_comp_neg,neg_neg]

lemma varianceOffsets_secondDeriv_neg_neg (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    deriv (deriv (varianceOffsets n (-ξ))) (-t) = deriv (deriv (varianceOffsets n ξ)) t := by
  rw [varianceOffsets_secondDeriv_neg_direction,neg_neg]

end NegativeVotingVariancePathSymmetry
