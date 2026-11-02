import GaussianPolynomialFacetTrace

/-! Dimension-independent logarithmic specialization of the actual quartic
Gaussian face trace. All smoothing and probability parameters are explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open NegativeVotingProjection NegativeVotingFiniteHermite NegativeVotingPolynomialDegree
open NegativeVotingPolynomialFacetTrace NegativeVotingSmoothingComposition
open NegativeVotingNormalTrace GaussianFin
open scoped BigOperators ENNReal Classical

namespace NegativeVotingPolynomialFacetLogBound

def quarticLogConstant (A : ℝ) : ℝ :=
  2 * Real.exp (1 + A^2) * (8192 : ℝ)^4

theorem log_smoothing_parameters {L : ℝ} (hL : 1 ≤ L) :
    let τ := 1 / Real.sqrt (8192 * L)
    0 < τ ∧ τ < 1 ∧ τ^2 * L = 1/8192 ∧ τ^2 ≤ 1/2 := by
  dsimp only
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : 0 < Real.sqrt (8192 * L) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 8192 * L by positivity)
  have hs1 : 1 < Real.sqrt (8192 * L) := by nlinarith
  have ht : 0 < 1 / Real.sqrt (8192 * L) := by positivity
  have ht1 : 1 / Real.sqrt (8192 * L) < 1 := (div_lt_one hs).mpr hs1
  have hrel : (1 / Real.sqrt (8192 * L))^2 * L = 1/8192 := by
    rw [div_pow, one_pow, hs2]
    field_simp
  refine ⟨ht, ht1, hrel, ?_⟩
  nlinarith [sq_nonneg (1 / Real.sqrt (8192 * L))]

theorem probability_rpow_log_gain {p L τ : ℝ} (hp : 0 < p)
    (hlog : -Real.log p ≤ 4096 * L) (hτ : 0 < τ)
    (hrel : τ^2 * L = 1/8192) :
    p ^ (1-2/(1+(τ^2)⁻¹)) ≤ Real.exp 1 * p := by
  have ht : 0 < τ^2 := sq_pos_of_pos hτ
  have hmul : -(2 * Real.log p * τ^2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hlog ht.le
    nlinarith
  have he : 1-2/(1+(τ^2)⁻¹) = (1-τ^2)/(1+τ^2) := by
    field_simp
    ring
  have hx : Real.log p * (1-2/(1+(τ^2)⁻¹)) ≤ Real.log p + 1 := by
    rw [he, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 1+τ^2 by positivity)).mpr
    nlinarith
  calc
    _ = Real.exp (Real.log p * (1-2/(1+(τ^2)⁻¹))) :=
      Real.rpow_def_of_pos hp _
    _ ≤ Real.exp (Real.log p + 1) := Real.exp_le_exp.mpr hx
    _ = Real.exp 1 * p := by rw [Real.exp_add, Real.exp_log hp]; ring

theorem normalRowSquare_le_log_bound {τ a A L : ℝ}
    (hL : 1 ≤ L) (hτ : 0 < τ) (hτ2 : τ^2 ≤ 1/2)
    (hrel : τ^2 * L = 1/8192) (ha : a^2 ≤ A^2 * L) :
    normalRowSquare τ a ≤ 2 * Real.exp (A^2) := by
  have hsminus : (1/2 : ℝ) ≤ Real.sqrt (1-τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsplus : (1 : ℝ) ≤ Real.sqrt (1+τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg τ]
  have hm : (Real.sqrt (1-τ^2))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1/2) hsminus
  have hp : (Real.sqrt (1+τ^2))⁻¹ ≤ 1 := by
    simpa using inv_anti₀ zero_lt_one hsplus
  have he : τ^2 * a^2 / (1+τ^2) ≤ A^2 := by
    apply (div_le_iff₀ (show 0 < 1+τ^2 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left ha (sq_nonneg τ)
    have hA : 0 ≤ A^2 := sq_nonneg A
    have heq : τ^2 * (A^2 * L) = A^2 / 8192 := by
      calc
        _ = A^2 * (τ^2 * L) := by ring
        _ = _ := by rw [hrel]; ring
    rw [heq] at hh
    nlinarith [mul_nonneg hA (sq_nonneg τ)]
  unfold normalRowSquare
  have hprod : (Real.sqrt (1-τ^2))⁻¹ * (Real.sqrt (1+τ^2))⁻¹ ≤ 2 := by
    simpa using mul_le_mul hm hp (by positivity) (by norm_num)
  exact mul_le_mul hprod (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by norm_num)

/-- The scalar coefficient estimate keeps the actual face probability as a
linear factor; the only remaining loss is the fourth power of the log scale. -/
theorem quartic_trace_coefficient_log_bound {p L τ a A : ℝ}
    (hp : 0 < p) (hL : 1 ≤ L) (hlog : -Real.log p ≤ 4096 * L)
    (hτ : 0 < τ) (hτ2 : τ^2 ≤ 1/2) (hrel : τ^2 * L = 1/8192)
    (ha : a^2 ≤ A^2 * L) :
    p ^ (1-2/(1+(τ^2)⁻¹)) *
        (Real.sqrt (normalRowSquare τ a) * (τ^4)⁻¹)^2 ≤
      p * quarticLogConstant A * L^4 := by
  have hprob := probability_rpow_log_gain hp hlog hτ hrel
  have hrow := normalRowSquare_le_log_bound hL hτ hτ2 hrel ha
  have hi : (τ^2)⁻¹ = 8192 * L := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hrel]
  have hpow : ((τ^4)⁻¹)^2 = (8192 * L)^4 := by
    calc
      _ = ((τ^2)⁻¹)^4 := by simp only [← inv_pow, ← pow_mul]
      _ = _ := by rw [hi]
  rw [mul_pow, Real.sq_sqrt (normalRowSquare_nonneg τ a), hpow]
  calc
    _ ≤ (Real.exp 1 * p) * ((2 * Real.exp (A^2)) * (8192 * L)^4) := by
      apply mul_le_mul hprob
        (mul_le_mul_of_nonneg_right hrow (by positivity))
        (mul_nonneg (normalRowSquare_nonneg τ a) (by positivity)) (by positivity)
    _ = p * quarticLogConstant A * L^4 := by
      simp only [quarticLogConstant, Real.exp_add, mul_pow]
      ring

/-- A genuine polynomial-plane trace with an explicit logarithmic coefficient. -/
theorem polynomial_face_integral_sq_log {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : f ∈ polynomialSpace 4)
    (a A L : ℝ) (F : Set (Fin n → ℝ))
    (hp : 0 < ((γFin n) F).toReal) (hL : 1 ≤ L)
    (hlog : -Real.log (((γFin n) F).toReal) ≤ 4096 * L)
    (ha : a^2 ≤ A^2 * L) :
    (∫ x in F, normalLift f (x,a)^2 ∂γFin n) ≤
      ((γFin n) F).toReal * quarticLogConstant A * L^4 *
        ∫ x, f x^2 ∂γFin (n+1) := by
  let τ := 1 / Real.sqrt (8192 * L)
  obtain ⟨hτ, hτ1, hrel, hτ2⟩ := log_smoothing_parameters hL
  have ht := polynomial_face_integral_sq hf τ hτ hτ1 a F
  exact ht.trans (mul_le_mul_of_nonneg_right
    (quartic_trace_coefficient_log_bound hp hL hlog hτ hτ2 hrel ha)
    (integral_nonneg (fun _ => sq_nonneg _)))

/-- The requested m-dependent specialization. The facet probability lower
bound and offset bound are geometric hypotheses; the polynomial trace is
derived from the actual function and its algebraic degree. -/
theorem polynomial_face_integral_sq_log_m {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : f ∈ polynomialSpace 4)
    (a A m : ℝ) (F : Set (Fin n → ℝ)) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤ ((γFin n) F).toReal)
    (ha : |a| ≤ A * Real.sqrt (1 + Real.log m)) :
    (∫ x in F, normalLift f (x,a)^2 ∂γFin n) ≤
      ((γFin n) F).toReal * quarticLogConstant A * (1 + Real.log m)^4 *
        ∫ x, f x^2 ∂γFin (n+1) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hp : 0 < ((γFin n) F).toReal :=
    (Real.rpow_pos_of_pos hm0 _).trans_le hprob
  have hL : 1 ≤ 1 + Real.log m := by linarith [Real.log_nonneg hm]
  have hlog : -Real.log (((γFin n) F).toReal) ≤ 4096 * (1 + Real.log m) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hprob
    rw [Real.log_rpow hm0] at hh
    linarith
  have ha2 : a^2 ≤ A^2 * (1 + Real.log m) := by
    have hh := pow_le_pow_left₀ (abs_nonneg a) ha 2
    simpa only [sq_abs, mul_pow,
      Real.sq_sqrt (show 0 ≤ 1 + Real.log m by linarith)] using hh
  exact polynomial_face_integral_sq_log hf a A (1 + Real.log m) F hp hL hlog ha2

/-- The degree cutoff is discharged for finite sums of actual affine products. -/
theorem quartic_affine_product_face_integral_sq_log_m {n : ℕ} {ι ν : Type*}
    (S : Finset ι) (T : ι → Finset ν) (w : ι → ℝ)
    (l : ι → ν → Fin (n+1) → ℝ) (c : ι → ν → ℝ)
    (hdegree : ∀ i ∈ S, (T i).card ≤ 4)
    (a A m : ℝ) (F : Set (Fin n → ℝ)) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤ ((γFin n) F).toReal)
    (ha : |a| ≤ A * Real.sqrt (1 + Real.log m)) :
    (∫ x in F, normalLift (affineProductSum S T w l c) (x,a)^2 ∂γFin n) ≤
      ((γFin n) F).toReal * quarticLogConstant A * (1 + Real.log m)^4 *
        ∫ x, (affineProductSum S T w l c x)^2 ∂γFin (n+1) :=
  polynomial_face_integral_sq_log_m
    (affineProductSum_mem S T w l c 4 hdegree) a A m F hm hprob ha

end NegativeVotingPolynomialFacetLogBound
