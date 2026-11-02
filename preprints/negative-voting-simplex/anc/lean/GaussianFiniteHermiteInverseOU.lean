import GaussianLowModeProjection

/-! Pointwise finite Hermite inversion of the actual Gaussian OU integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open NegativeVotingModern NegativeVotingChaosDecay NegativeVotingProjection
open NegativeVotingSmoothingComposition NegativeVotingNormalTrace NegativeVotingHypercontractivity GaussianFin
open scoped BigOperators ENNReal

namespace NegativeVotingFiniteHermite
variable {κ : Type*} [Fintype κ]

def hermiteSum (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ a ∈ S, c a * psi a x

def inverseOUSum (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ) (τ : ℝ) :=
  hermiteSum S (fun a => c a / τ ^ degree a)

theorem hermiteSum_memLp (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ) :
    MemLp (hermiteSum S c) 2 (γpi κ) :=
  memLp_finsetSum S (fun a _ => (memLp_psi a).const_mul (c a))

theorem hermiteSum_continuous (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ) :
    Continuous (hermiteSum S c) :=
  continuous_finsetSum S (fun a _ => (continuous_psi a).const_mul (c a))

theorem coeff_hermiteSum (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ)
    (a : κ → ℕ) : coeff (hermiteSum S c) a = if a ∈ S then c a else 0 := by
  classical
  have heq : (fun x => psi a x * hermiteSum S c x) =
      fun x => ∑ b ∈ S, c b * (psi a x * psi b x) := by
    funext x
    simp only [hermiteSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  change (∫ x, psi a x * hermiteSum S c x ∂γpi κ) = _
  rw [heq, integral_finsetSum S (f := fun b x => c b * (psi a x * psi b x)) (fun b _ => by
    simpa only [Pi.mul_apply] using ((memLp_psi a).integrable_mul (memLp_psi b)).const_mul (c b))]
  simp_rw [integral_const_mul, psi_product]
  simp [mul_ite]

theorem hermiteSum_integral_sq (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ) :
    (∫ x, hermiteSum S c x ^ 2 ∂γpi κ) = ∑ a ∈ S, (c a)^2 := by
  classical
  rw [← (coefficient_energy_hasSum_of_memLp (hermiteSum_memLp S c)).tsum_eq]
  rw [tsum_eq_sum (s := S) (fun a ha => by simp [coeff_hermiteSum, ha])]
  exact Finset.sum_congr rfl (fun a ha => by simp [coeff_hermiteSum, ha])

theorem integrable_psi_affine (a : κ → ℕ) (τ s : ℝ) (x : κ → ℝ) :
    Integrable (fun y => psi a (fun i => τ * x i + s * y i)) (γpi κ) := by
  exact Integrable.fintype_prod (fun i =>
    (integrable_he_affine (a i) (τ * x i) s).div_const (Real.sqrt ((a i).factorial : ℝ)))

theorem inverseOUSum_noise_pointwise (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ)
    (τ s : ℝ) (hτ : τ ≠ 0) (hs : τ^2+s^2=1) (x : κ → ℝ) :
    noise τ s (inverseOUSum S c τ) x = hermiteSum S c x := by
  unfold noise inverseOUSum hermiteSum
  change (∫ y, ∑ a ∈ S, (c a / τ ^ degree a) *
    psi a (fun i => τ * x i + s * y i) ∂γpi κ) = _
  rw [integral_finsetSum S (fun a _ =>
    (integrable_psi_affine a τ s x).const_mul (c a / τ ^ degree a))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul, psi_noise τ s hs]
  change (c a / τ ^ degree a) * (τ ^ degree a * psi a x) = _
  field_simp

/-- The inverse amplification depends on the largest degree, not on dimension or support size. -/
theorem inverseOUSum_integral_sq_le (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ)
    (k : ℕ) (hdegree : ∀ a ∈ S, degree a ≤ k) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (∫ x, inverseOUSum S c τ x ^ 2 ∂γpi κ) ≤
      (τ^k)⁻¹ ^ 2 * ∫ x, hermiteSum S c x ^ 2 ∂γpi κ := by
  rw [inverseOUSum, hermiteSum_integral_sq, hermiteSum_integral_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hp : τ ^ k ≤ τ ^ degree a := pow_le_pow_of_le_one hτ.le hτ1 (hdegree a ha)
  have hi : (τ ^ degree a)⁻¹ ≤ (τ ^ k)⁻¹ := inv_anti₀ (pow_pos hτ k) hp
  have hi2 : (τ ^ degree a)⁻¹ ^ 2 ≤ (τ ^ k)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (pow_nonneg hτ.le _)) hi 2
  simpa only [div_eq_mul_inv, mul_pow, mul_comm] using
    mul_le_mul_of_nonneg_right hi2 (sq_nonneg (c a))


theorem inverseOUSum_eLpNorm_le (S : Finset (κ → ℕ)) (c : (κ → ℕ) → ℝ)
    (k : ℕ) (hdegree : ∀ a ∈ S, degree a ≤ k) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    eLpNorm (inverseOUSum S c τ) 2 (γpi κ) ≤
      ENNReal.ofReal ((τ^k)⁻¹) * eLpNorm (hermiteSum S c) 2 (γpi κ) := by
  have hi : MemLp (inverseOUSum S c τ) 2 (γpi κ) := hermiteSum_memLp S _
  rw [eLpNorm_two_eq_sqrt_integral_sq hi,
    eLpNorm_two_eq_sqrt_integral_sq (hermiteSum_memLp S c),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hτ.le k))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt ((τ^k)⁻¹ ^ 2 * ∫ x, hermiteSum S c x ^ 2 ∂γpi κ) :=
      Real.sqrt_le_sqrt (inverseOUSum_integral_sq_le S c k hdegree τ hτ hτ1)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem inverseOUSum_gaussianAverage {n : ℕ} (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℝ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (x : Fin n → ℝ) :
    gaussianAverage τ (inverseOUSum S c τ) x = hermiteSum S c x := by
  apply inverseOUSum_noise_pointwise S c τ (Real.sqrt (1-τ^2)) hτ.ne'
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg τ])]
  ring

/-- A finite polynomial has a genuine fixed-plane trace bound: equality is pointwise,
not inferred by restricting an ambient almost-everywhere identity. -/
theorem hermiteSum_normal_trace_lq {n : ℕ} (S : Finset (Fin (n+1) → ℕ))
    (c : (Fin (n+1) → ℕ) → ℝ) (k : ℕ) (hdegree : ∀ a ∈ S, degree a ≤ k)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (a : ℝ) :
    eLpNorm (fun x => normalLift (hermiteSum S c) (x,a))
        (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a) * (τ^k)⁻¹) *
        eLpNorm (hermiteSum S c) 2 (γFin (n+1)) := by
  have hi : MemLp (inverseOUSum S c τ) 2 (γFin (n+1)) := hermiteSum_memLp S _
  have ht := actual_product_normalTrace_lq_bound_sharp hτ hτ1 a
    (normalLift (inverseOUSum S c τ)) (normalLift_memLp _ hi)
  change eLpNorm (fun x => productGaussianAverage τ (normalLift (inverseOUSum S c τ)) (x,a))
    _ _ ≤ _ at ht
  have he (x : Fin n → ℝ) :
      productGaussianAverage τ (normalLift (inverseOUSum S c τ)) (x,a) =
        normalLift (hermiteSum S c) (x,a) := by
    rw [← gaussianAverage_normalCoordinates, inverseOUSum_gaussianAverage S c τ hτ hτ1]
    rfl
  simp_rw [he] at ht
  rw [normalLift_eLpNorm _ hi.aestronglyMeasurable] at ht
  calc
    _ ≤ _ := ht
    _ ≤ ENNReal.ofReal (Real.sqrt (normalRowSquare τ a)) *
        (ENNReal.ofReal ((τ^k)⁻¹) * eLpNorm (hermiteSum S c) 2 (γFin (n+1))) :=
      mul_le_mul' le_rfl (inverseOUSum_eLpNorm_le S c k hdegree τ hτ hτ1.le)
    _ = _ := by rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; ac_rfl

end NegativeVotingFiniteHermite
