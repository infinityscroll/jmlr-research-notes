import GaussianFanCycleGeometry
import GaussianCapTailAndStrip

/-! A genuine affine basis supplies its own strictly positive centered singular
lower bound; no numerical nondegeneracy certificate is assumed. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingAffineBasisLower
open NegativeVotingFanCycle NegativeVotingCapTail
variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The barycentric dual recovers each zero-sum coefficient from its actual vector. -/
theorem centered_coefficient_pairing (b : AffineBasis V ℝ E) (c : V → ℝ)
    (hc : ∑ i, c i = 0) (i : V) :
    inner ℝ (barycentricOutwardVector b i) (∑ k, c k • b k) = -c i := by
  let j : V := Classical.choice inferInstance
  have he : (∑ k, c k • (b k-b j)) = ∑ k, c k • b k := by
    simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hc,zero_smul,sub_zero]
  rw [← he]
  simp only [inner_sum,real_inner_smul_right,barycentricOutwardVector_edge,mul_sub,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul,hc,zero_mul]
  simp [mul_ite]

/-- A concrete coefficient recovery estimate for the literal affine basis. -/
theorem centered_coefficients_bound (b : AffineBasis V ℝ E) (c : V → ℝ)
    (hc : ∑ i, c i = 0) :
    (∑ i, c i ^ 2) ≤ (∑ i, ‖barycentricOutwardVector b i‖^2)*‖∑ k, c k • b k‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have ha := abs_real_inner_le_norm (barycentricOutwardVector b i) (∑ k, c k • b k)
  rw [centered_coefficient_pairing b c hc i,abs_neg] at ha
  have hb := sq_le_sq₀ (abs_nonneg (c i))
    (mul_nonneg (norm_nonneg (barycentricOutwardVector b i)) (norm_nonneg (∑ k, c k • b k)))
  have he := hb.mpr ha
  simpa only [sq_abs,mul_pow] using he

/-- Every finite affine basis satisfies the quantitative assumption used by the
moving-cell and inverse-mass theorems, with an explicitly constructed positive constant. -/
theorem exists_centeredSingularLowerBound (b : AffineBasis V ℝ E) :
    ∃ σ : ℝ, 0 < σ ∧ CenteredSingularLowerBound b σ := by
  let A : ℝ := ∑ i, ‖barycentricOutwardVector b i‖^2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hden : 0 < 1+A := by positivity
  let σ : ℝ := 1/(1+A)
  have hσ : 0 < σ := div_pos (by norm_num) hden
  refine ⟨σ,hσ,?_⟩
  intro c hc
  have hbound := centered_coefficients_bound b c hc
  change (∑ i, c i^2) ≤ A*‖∑ k, c k • b k‖^2 at hbound
  have hcoeff : σ^2*A ≤ 1 := by
    change (1/(1+A))^2*A ≤ 1
    rw [div_pow,one_pow,div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [sq_nonneg A]
  have hmul := mul_le_mul_of_nonneg_left hbound (sq_nonneg σ)
  have hlast := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖∑ k, c k • b k‖)
  nlinarith

end NegativeVotingAffineBasisLower
