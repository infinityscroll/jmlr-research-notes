import GaussianSpectralBridge
import GaussianHypercontractivityBridge
import GaussianNormalTrace

/-! Actual Gaussian smoothing decay after removing low Hermite levels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open SlowEquilibration.GaussianMaximalCorrelation NegativeVotingModern
open NegativeVotingHypercontractivity GaussianFin NegativeVotingNormalTrace
open scoped BigOperators RealInnerProductSpace ENNReal

namespace NegativeVotingChaosDecay
variable {κ : Type*} [Fintype κ]

/-- Parseval for a completed-measure L² function; no Borel representative is assumed. -/
theorem coefficient_energy_hasSum_of_memLp {f : (κ → ℝ) → ℝ}
    (hf : MemLp f 2 (γpi κ)) :
    HasSum (fun a : κ → ℕ => (coeff f a)^2) (∫ x, f x ^ 2 ∂γpi κ) := by
  have hp := productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have heq : (fun a : κ → ℕ => inner ℝ (hf.toLp f) (productHermiteBasis a) *
      inner ℝ (productHermiteBasis a) (hf.toLp f)) = fun a => (coeff f a)^2 := by
    funext a
    rw [real_inner_comm, hermite_basis_coefficient hf]
    ring
  rw [heq, integral_inner_toLp] at hp
  simpa only [pow_two] using hp

/-- Removing all levels below k gives the actual squared-L² noise contraction. -/
theorem noise_integral_sq_decay (ρ s : ℝ) (hρs : ρ^2+s^2=1)
    {f : (κ → ℝ) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 (γpi κ))
    (k : ℕ) (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    (∫ x, noise ρ s f x ^ 2 ∂γpi κ) ≤
      (ρ^2)^k * ∫ x, f x ^ 2 ∂γpi κ := by
  have hn := memLp_noise_L2 ρ s hρs hf hf2
  have hs1 := coefficient_energy_hasSum_of_memLp hn
  have hs2 := (coefficient_energy_hasSum_of_memLp hf2).mul_left ((ρ^2)^k)
  refine hasSum_le ?_ hs1 hs2
  intro a
  rw [noise_coefficient_L2 ρ s hρs hf hf2, mul_pow,
    show (ρ ^ degree a)^2 = (ρ^2)^degree a by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  by_cases ha : degree a < k
  · simp [hvanish a ha]
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (sq_nonneg ρ) (by nlinarith [sq_nonneg s])
        (Nat.le_of_not_gt ha)) (sq_nonneg _)

/-- The decay bound holds for the actual OU integral and every Gaussian L² input. -/
theorem gaussianAverage_integral_sq_decay {n : ℕ} (τ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (γFin n)) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    (∫ x, gaussianAverage τ f x ^ 2 ∂γFin n) ≤
      (τ^2)^k * ∫ x, f x ^ 2 ∂γFin n := by
  let g := hf.toLp f
  have hfg : (g : (Fin n → ℝ) → ℝ) =ᵐ[γFin n] f := hf.coeFn_toLp
  have hc (a : Fin n → ℕ) : coeff (g : (Fin n → ℝ) → ℝ) a = coeff f a := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    simp only [hx]
  have hsq : 0 ≤ 1-τ^2 := by nlinarith
  have hmix : τ^2 + (Real.sqrt (1-τ^2))^2=1 := by rw [Real.sq_sqrt hsq]; ring
  have hh := noise_integral_sq_decay τ (Real.sqrt (1-τ^2)) hmix
    (Lp.stronglyMeasurable g).measurable (Lp.memLp g) k (fun a ha => by rw [hc]; exact hvanish a ha)
  change (∫ x, gaussianAverage τ g x ^ 2 ∂γFin n) ≤
    (τ^2)^k * ∫ x, g x ^ 2 ∂γFin n at hh
  have hN := gaussianAverage_congr_ae τ hτ hτ1 hfg
  have hiN : (∫ x, gaussianAverage τ g x ^ 2 ∂γFin n) =
      ∫ x, gaussianAverage τ f x ^ 2 ∂γFin n :=
    integral_congr_ae (hN.fun_comp fun x => x^2)
  have hi : (∫ x, g x ^ 2 ∂γFin n) = ∫ x, f x ^ 2 ∂γFin n :=
    integral_congr_ae (hfg.fun_comp fun x => x^2)
  rwa [hiN, hi] at hh

/-- The actual squared-L² decay is also a norm estimate. -/
theorem gaussianAverage_eLpNorm_decay {n : ℕ} (τ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (γFin n)) (k : ℕ)
    (hvanish : ∀ a, degree a < k → coeff f a = 0) :
    eLpNorm (gaussianAverage τ f) 2 (γFin n) ≤
      ENNReal.ofReal (τ^k) * eLpNorm f 2 (γFin n) := by
  have hsq : 0 ≤ 1-τ^2 := by nlinarith
  have hmix : τ^2+(Real.sqrt (1-τ^2))^2=1 := by rw [Real.sq_sqrt hsq]; ring
  have hg := memLp_noise_L2 τ (Real.sqrt (1-τ^2)) hmix
    (Lp.stronglyMeasurable (hf.toLp f)).measurable (Lp.memLp (hf.toLp f))
  have hN : MemLp (gaussianAverage τ f) 2 (γFin n) :=
    MemLp.ae_eq (gaussianAverage_congr_ae τ hτ hτ1 hf.coeFn_toLp) hg
  rw [eLpNorm_two_eq_sqrt_integral_sq hN, eLpNorm_two_eq_sqrt_integral_sq hf,
    ← ENNReal.ofReal_mul (pow_nonneg hτ.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt ((τ^2)^k * ∫ x, f x ^ 2 ∂γFin n) :=
      Real.sqrt_le_sqrt (gaussianAverage_integral_sq_decay τ hτ hτ1 f hf k hvanish)
    _ = _ := by
      rw [Real.sqrt_mul (pow_nonneg (sq_nonneg τ) _),
        show (τ^2)^k=(τ^k)^2 by rw [←pow_mul, ←pow_mul, Nat.mul_comm],
        Real.sqrt_sq (pow_nonneg hτ.le _)]

end NegativeVotingChaosDecay
