import GaussianAffineBasisLower

/-! Quantitative realization of actual centered scores, using the barycentric
dual of an actual affine basis. No inverse or score-surjectivity premise. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingScoreRealization
open NegativeVotingFanCycle NegativeVotingAffineBasisLower NegativeVotingCapTail
variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def scoreLift (b : AffineBasis V ℝ E) (q : V → ℝ) : E :=
  -(∑ i, q i • barycentricOutwardVector b i)

theorem scoreLift_edge (b : AffineBasis V ℝ E) (q : V → ℝ) (i j : V) :
    inner ℝ (scoreLift b q) (b i-b j) = q i-q j := by
  simp only [scoreLift,inner_neg_left,sum_inner,real_inner_smul_left,
    barycentricOutwardVector_edge,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite]

theorem scoreLift_scores (b : AffineBasis V ℝ E) (hb : ∑ i, b i = 0)
    (q : V → ℝ) (hq : ∑ i, q i = 0) (i : V) :
    inner ℝ (b i) (scoreLift b q) = q i := by
  have hs : (∑ j, inner ℝ (scoreLift b q) (b i-b j)) = (∑ j, (q i-q j)) :=
    Finset.sum_congr rfl (fun j _ => scoreLift_edge b q i j)
  simp only [inner_sub_right,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← inner_sum,hb,inner_zero_right,hq,sub_zero] at hs
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he := mul_left_cancel₀ hc hs
  simpa only [real_inner_comm] using he

theorem centered_linear_coefficients (b : AffineBasis V ℝ E) (x : E) :
    (∑ i, (b.coord i x-b.coord i 0)) = 0 ∧
      (∑ i, (b.coord i x-b.coord i 0) • b i) = x := by
  constructor
  · rw [Finset.sum_sub_distrib,b.sum_coord_apply_eq_one,b.sum_coord_apply_eq_one,sub_self]
  · simp only [sub_smul,Finset.sum_sub_distrib,b.linear_combination_coord_eq_self,sub_zero]

/-- The squared norm bound has the exact inverse singular-value constant. -/
theorem scoreLift_norm_sq (b : AffineBasis V ℝ E) (hb : ∑ i, b i = 0)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (q : V → ℝ) (hq : ∑ i, q i = 0) :
    ‖scoreLift b q‖^2 ≤ (∑ i, (q i)^2)/σ^2 := by
  let x := scoreLift b q
  let c := fun i => b.coord i x-b.coord i 0
  have hc := centered_linear_coefficients b x
  have hlo := hlower c hc.1
  change σ^2*(∑ i, (c i)^2) ≤ ‖∑ i, c i • b i‖^2 at hlo
  rw [hc.2] at hlo
  have hi : ‖x‖^2 = ∑ i, c i*q i := by
    calc
      _ = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
      _ = inner ℝ (∑ i, c i • b i) x := by rw [hc.2]
      _ = _ := by simp only [x,sum_inner,real_inner_smul_left,scoreLift_scores b hb q hq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c q
  rw [← hi] at hcs
  have hq2 : 0 ≤ ∑ i, (q i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm1 := mul_le_mul_of_nonneg_left hcs (sq_nonneg σ)
  have hm2 := mul_le_mul_of_nonneg_right hlo hq2
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  by_cases hx : ‖x‖ = 0
  · simpa only [x] using (show ‖x‖^2*σ^2 ≤ ∑ i, (q i)^2 by simpa [hx] using hq2)
  · have hx2 : 0 < ‖x‖^2 := sq_pos_of_ne_zero hx
    have hf : ‖x‖^2*(‖x‖^2*σ^2) ≤ ‖x‖^2*(∑ i, (q i)^2) := by nlinarith
    exact (mul_le_mul_iff_right₀ hx2).mp hf

theorem exists_centered_score_vector (b : AffineBasis V ℝ E) (hb : ∑ i, b i = 0)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound b σ)
    (q : V → ℝ) (hq : ∑ i, q i = 0) :
    ∃ x : E, (∀ i, inner ℝ (b i) x = q i) ∧ ‖x‖^2 ≤ (∑ i, (q i)^2)/σ^2 :=
  ⟨scoreLift b q,scoreLift_scores b hb q hq,scoreLift_norm_sq b hb σ hσ hlower q hq⟩

end NegativeVotingScoreRealization
