import GaussianChaosDecay
import GaussianAffineComparison
import GaussianSmoothingComposition

/-! Concrete finite Hermite projections and their actual Gaussian L² residual. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open NegativeVotingModern NegativeVotingAffine NegativeVotingChaosDecay
open scoped BigOperators RealInnerProductSpace ENNReal
namespace NegativeVotingProjection
variable {κ : Type*} [Fintype κ]

def projectModes (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ a ∈ S, coeff f a * psi a x

def removeModes (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ) (x : κ → ℝ) : ℝ :=
  f x - projectModes S f x

theorem projectModes_memLp (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ) :
    MemLp (projectModes S f) 2 (γpi κ) := by
  exact memLp_finsetSum S (fun a _ => (memLp_psi a).const_mul (coeff f a))

theorem removeModes_memLp (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) : MemLp (removeModes S f) 2 (γpi κ) :=
  hf.sub (projectModes_memLp S f)

theorem coeff_projectModes (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ)
    (a : κ → ℕ) : coeff (projectModes S f) a = if a ∈ S then coeff f a else 0 := by
  classical
  have heq : (fun x => psi a x * projectModes S f x) =
      fun x => ∑ b ∈ S, coeff f b * (psi a x * psi b x) := by
    funext x
    simp only [projectModes, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  change (∫ x, psi a x * projectModes S f x ∂γpi κ) = _
  rw [heq, integral_finsetSum S (f := fun b x => coeff f b * (psi a x * psi b x)) (fun b _ => by
    simpa only [Pi.mul_apply] using ((memLp_psi a).integrable_mul (memLp_psi b)).const_mul (coeff f b))]
  simp_rw [integral_const_mul, psi_product]
  simp [mul_ite]

theorem coeff_removeModes (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) (a : κ → ℕ) :
    coeff (removeModes S f) a = if a ∈ S then 0 else coeff f a := by
  classical
  rw [show removeModes S f = fun x => f x - projectModes S f x by rfl,
    coeff_sub hf (projectModes_memLp S f), coeff_projectModes]
  split_ifs <;> simp

theorem removeModes_integral_sq_le (S : Finset (κ → ℕ)) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) :
    (∫ x, removeModes S f x ^ 2 ∂γpi κ) ≤ ∫ x, f x ^ 2 ∂γpi κ := by
  refine hasSum_le ?_ (coefficient_energy_hasSum_of_memLp (removeModes_memLp S f hf))
    (coefficient_energy_hasSum_of_memLp hf)
  intro a
  rw [coeff_removeModes S f hf a]
  split_ifs
  · simp only [zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · exact le_rfl

/-- A genuinely finite set containing exactly the Hermite levels below k. -/
def lowerModes (k : ℕ) : Finset (κ → ℕ) := by
  classical
  exact (Finset.univ.image (fun a : κ → Fin k => fun i => (a i).val)).filter
    (fun a => degree a < k)

theorem mem_lowerModes_iff (k : ℕ) (a : κ → ℕ) :
    a ∈ lowerModes k ↔ degree a < k := by
  classical
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).2
  · intro ha
    have hi (i : κ) : a i < k := by
      have hle : a i ≤ degree a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact lt_of_le_of_lt hle ha
    apply Finset.mem_filter.mpr
    refine ⟨?_,ha⟩
    exact Finset.mem_image.mpr ⟨fun i => ⟨a i, hi i⟩, Finset.mem_univ _, rfl⟩

def highModes (k : ℕ) (f : (κ → ℝ) → ℝ) : (κ → ℝ) → ℝ :=
  removeModes (lowerModes k) f

theorem highModes_memLp (k : ℕ) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) : MemLp (highModes k f) 2 (γpi κ) :=
  removeModes_memLp (lowerModes k) f hf

theorem highModes_coeff_vanish (k : ℕ) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) (a : κ → ℕ) (ha : degree a < k) :
    coeff (highModes k f) a = 0 := by
  classical
  simp only [highModes, coeff_removeModes _ _ hf, ite_eq_left ((mem_lowerModes_iff k a).mpr ha)]

theorem highModes_integral_sq_le (k : ℕ) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) :
    (∫ x, highModes k f x ^ 2 ∂γpi κ) ≤ ∫ x, f x ^ 2 ∂γpi κ :=
  removeModes_integral_sq_le (lowerModes k) f hf

theorem highModes_eLpNorm_le (k : ℕ) (f : (κ → ℝ) → ℝ)
    (hf : MemLp f 2 (γpi κ)) :
    eLpNorm (highModes k f) 2 (γpi κ) ≤ eLpNorm f 2 (γpi κ) := by
  rw [NegativeVotingNormalTrace.eLpNorm_two_eq_sqrt_integral_sq (highModes_memLp k f hf),
    NegativeVotingNormalTrace.eLpNorm_two_eq_sqrt_integral_sq hf]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (highModes_integral_sq_le k f hf))

/-- The projection is explicitly constructed; no vanishing-coefficient premise remains. -/
theorem gaussianAverage_highModes_integral_sq_le {n : ℕ} (τ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (k : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (GaussianFin.γFin n)) :
    (∫ x, NegativeVotingHypercontractivity.gaussianAverage τ (highModes k f) x ^ 2
      ∂GaussianFin.γFin n) ≤ (τ^2)^k * ∫ x, f x ^ 2 ∂GaussianFin.γFin n := by
  exact (gaussianAverage_integral_sq_decay τ hτ hτ1 (highModes k f)
    (highModes_memLp k f hf) k (highModes_coeff_vanish k f hf)).trans
      (mul_le_mul_of_nonneg_left (highModes_integral_sq_le k f hf)
        (pow_nonneg (sq_nonneg τ) _))

/-- Literal normal-interval supremum of the smoothed, explicitly projected
residual. Low-degree coefficient vanishing and residual norm control are proved
from the construction; neither is an additional hypothesis. -/
theorem actual_gaussian_normal_sup_highModes_lq_bound {n : ℕ} {τ σ A : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A)
    (k : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : MemLp f 2 (GaussianFin.γFin (n + 1))) :
    let S := fun x => ⨆ a : Set.Icc (-A) A,
      ‖NegativeVotingHypercontractivity.gaussianAverage (τ * σ) (highModes k f)
        (NegativeVotingSmoothingComposition.normalCoordinates.symm (x, a))‖
    MemLp S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (GaussianFin.γFin n) ∧
      eLpNorm S (ENNReal.ofReal (1 + (τ ^ 2)⁻¹)) (GaussianFin.γFin n) ≤
      ENNReal.ofReal (Real.sqrt (NegativeVotingNormalTrace.normalRowSquare τ A) * σ ^ k) *
        eLpNorm f 2 (GaussianFin.γFin (n + 1)) := by
  intro S
  have h := NegativeVotingSmoothingComposition.actual_gaussian_normal_sup_highChaos_lq_bound
    hτ hτ1 hσ hσ1 hA (highModes k f) (highModes_memLp k f hf) k
      (highModes_coeff_vanish k f hf)
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_right (highModes_eLpNorm_le k f hf) _

end NegativeVotingProjection
