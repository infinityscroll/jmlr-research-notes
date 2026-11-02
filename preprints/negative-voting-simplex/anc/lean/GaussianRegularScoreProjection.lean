import GaussianCenteredParsevalBasis

/-! The actual regular score-frame operator is an orthogonal projection in
any finite ambient dimension. No full affine-span premise is imposed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingRegularScoreProjection
open NegativeVoting NegativeVotingCenteredParseval
variable {d m : ℕ} [NeZero m]

theorem regular_rows_sum_zero (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    (∑i,B i)=0 := by
  have hrows : RegularSimplexGram (fun i => (B i).ofLp) := by
    intro i j
    simpa only [PiLp.inner_apply,Real.inner_apply] using hG i j
  exact simplexRows_sum_zero (fun i => (B i).ofLp) hrows

theorem regular_score_sum_zero (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) : (∑i,inner ℝ (B i) x)=0 := by
  rw [←sum_inner,regular_rows_sum_zero B hG,inner_zero_left]

/-- Projection preserves every actual score, including in spectator dimensions. -/
theorem frame_preserves_scores (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) (i : Fin m) :
    inner ℝ (B i) (frameOperator B x)=inner ℝ (B i) x := by
  rw [real_inner_comm,frameOperator_apply,weighted_inner B hG,
    regular_score_sum_zero B hG]
  simp

theorem frame_norm_sq (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) :
    ‖frameOperator B x‖^2=∑i,(inner ℝ (B i) x)^2 := by
  rw [frameOperator_apply,weighted_norm_sq B hG,regular_score_sum_zero B hG]
  simp

theorem frame_inner_self (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) : inner ℝ (frameOperator B x) x=‖frameOperator B x‖^2 := by
  rw [frame_norm_sq B hG,frameOperator_apply,sum_inner]
  simp only [real_inner_smul_left,pow_two]

theorem frame_norm_le (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) : ‖frameOperator B x‖ ≤ ‖x‖ := by
  by_cases hz : ‖frameOperator B x‖=0
  · rw [hz]
    exact norm_nonneg x
  have hp : 0<‖frameOperator B x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hh := real_inner_le_norm (frameOperator B x) x
  rw [frame_inner_self B hG,pow_two] at hh
  exact (mul_le_mul_iff_right₀ hp).mp hh

theorem frame_idempotent (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) : frameOperator B (frameOperator B x)=frameOperator B x := by
  conv_lhs => rw [frameOperator_apply]
  simp_rw [frame_preserves_scores B hG]
  exact (frameOperator_apply B x).symm

end NegativeVotingRegularScoreProjection
