import Mathlib
import NegativeVoting.Threshold
import NegativeVoting.Assembly

/-!
# One scalar threshold for the entire negative voting interval

The manuscript's exterior errors are controlled uniformly in the noise
magnitude `0 < r ≤ 1 / (m - 1)`. This file proves the endpoint scaling
and the existence of a single natural threshold for those actual errors.
The analytic estimates producing the constants remain explicit hypotheses.
-/

namespace NegativeVoting

/-- The voting endpoint is at most `2 / m` once the alphabet is at least two. -/
theorem voting_noise_le_two_div (m r : ℝ) (hm : 2 ≤ m)
    (hr : r ≤ 1 / (m - 1)) : r ≤ 2 / m := by
  have hmpos : 0 < m := by linarith
  have hdenom : 0 < m - 1 := by linarith
  apply le_trans hr
  apply (div_le_div_iff₀ hdenom hmpos).mpr
  nlinarith

/-- The fractional-power endpoint identity is exact at every positive base. -/
theorem voting_endpoint_rpow_identity (m : ℝ) (hm : 0 < m) :
    (2 / m) ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) =
      4 / m ^ ((1 : ℝ) / 4) := by
  have hpowers : m ^ ((7 : ℝ) / 4) / m ^ (2 : ℕ) =
      1 / m ^ ((1 : ℝ) / 4) := by
    calc
      m ^ ((7 : ℝ) / 4) / m ^ (2 : ℕ) = m ^ (((7 : ℝ) / 4) - 2) := by
        rw [Real.rpow_sub hm, Real.rpow_two]
      _ = m ^ (-((1 : ℝ) / 4)) := by congr 1; norm_num
      _ = 1 / m ^ ((1 : ℝ) / 4) := by simp only [Real.rpow_neg hm.le, one_div]
  calc
    (2 / m) ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) =
        4 * (m ^ ((7 : ℝ) / 4) / m ^ (2 : ℕ)) := by
          rw [div_pow]
          norm_num
          ring
    _ = 4 / m ^ ((1 : ℝ) / 4) := by rw [hpowers]; ring

/-- The full quadratic voting-noise term has the claimed `m^(-1/4)` bound. -/
theorem voting_noise_quadratic_bound (m r : ℝ) (hm : 2 ≤ m)
    (hrnonneg : 0 ≤ r) (hr : r ≤ 1 / (m - 1)) :
    r ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) ≤ 4 / m ^ ((1 : ℝ) / 4) := by
  have hmpos : 0 < m := by linarith
  have hrbound := voting_noise_le_two_div m r hm hr
  have htwo : 0 ≤ 2 / m := div_nonneg (by norm_num) hmpos.le
  have hsquare : r ^ (2 : ℕ) ≤ (2 / m) ^ (2 : ℕ) := by
    simpa only [pow_two] using mul_le_mul hrbound hrbound hrnonneg htwo
  calc
    r ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) ≤
        (2 / m) ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hsquare (Real.rpow_nonneg hmpos.le _)
    _ = 4 / m ^ ((1 : ℝ) / 4) := voting_endpoint_rpow_identity m hmpos

/-- Actual voting-interval errors are bounded by two scalar endpoint rates,
with both constants and both powers explicit. -/
theorem voting_remainder_majorant (A B m r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 2 ≤ m)
    (hrnonneg : 0 ≤ r) (hr : r ≤ 1 / (m - 1)) :
    A * r * (1 + Real.log m) ^ (3 : ℕ) +
      B * r ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) *
        (1 + Real.log m) ^ ((7 : ℝ) / 2) ≤
    (2 * A) * ((1 + Real.log m) ^ (3 : ℕ) / m) +
      (4 * B) * ((1 + Real.log m) ^ ((7 : ℝ) / 2) /
        m ^ ((1 : ℝ) / 4)) := by
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hL : 0 ≤ 1 + Real.log m := by linarith
  have hfirst := mul_le_mul_of_nonneg_left
    (voting_noise_le_two_div m r hm hr)
    (mul_nonneg hA (pow_nonneg hL 3))
  have hsecond := mul_le_mul_of_nonneg_left
    (voting_noise_quadratic_bound m r hm hrnonneg hr)
    (mul_nonneg hB (Real.rpow_nonneg hL ((7 : ℝ) / 2)))
  calc
    A * r * (1 + Real.log m) ^ (3 : ℕ) +
        B * r ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4) *
          (1 + Real.log m) ^ ((7 : ℝ) / 2) =
      (A * (1 + Real.log m) ^ (3 : ℕ)) * r +
        (B * (1 + Real.log m) ^ ((7 : ℝ) / 2)) *
          (r ^ (2 : ℕ) * m ^ ((7 : ℝ) / 4)) := by ring
    _ ≤ (A * (1 + Real.log m) ^ (3 : ℕ)) * (2 / m) +
        (B * (1 + Real.log m) ^ ((7 : ℝ) / 2)) *
          (4 / m ^ ((1 : ℝ) / 4)) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- A single natural alphabet threshold controls every noise magnitude in the
entire voting interval. The constants must be fixed and nonnegative; no
dimension or noise dependence is hidden in this quantifier order. -/
theorem exists_uniform_voting_remainder_threshold (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m : ℕ, M ≤ m → ∀ r : ℝ,
      0 < r → r ≤ 1 / ((m : ℝ) - 1) →
      A * r * (1 + Real.log (m : ℝ)) ^ (3 : ℕ) +
        B * r ^ (2 : ℕ) * (m : ℝ) ^ ((7 : ℝ) / 4) *
          (1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2) ≤ 1 / 2 := by
  obtain ⟨M, hM⟩ := exists_uniform_remainder_threshold (2 * A) (4 * B)
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  intro m hm r hrpos hr
  have hm2 : 2 ≤ m := le_trans (le_max_right M 2) hm
  have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  exact (voting_remainder_majorant A B (m : ℝ) r hA hB hmreal hrpos.le hr).trans
    (hM m (le_trans (le_max_left M 2) hm))

/-- Conditional local/exterior closure with a proved existential threshold
uniform throughout the voting interval. The local and exterior analytic
bounds remain explicit assumptions; this is not a Gaussian simplex theorem. -/
theorem exists_uniform_voting_assembly_threshold (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m : ℕ, M ≤ m → ∀ r : ℝ,
      0 < r → r ≤ 1 / ((m : ℝ) - 1) → ∀ E d δ R D : ℝ,
      0 ≤ δ → 0 ≤ R →
      (E ≤ 0 → d ≤ 1 / (m : ℝ) → δ / 2 + r * R ≤ E) →
      (E ≤ 0 → 1 / (m : ℝ) < d →
        0 < D ∧ D * (1 - A * r * (1 + Real.log (m : ℝ)) ^ (3 : ℕ) -
          B * r ^ (2 : ℕ) * (m : ℝ) ^ ((7 : ℝ) / 4) *
            (1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2)) ≤ E) →
      0 ≤ E ∧ (E ≤ 0 → E = 0 ∧ δ = 0 ∧ R = 0 ∧ d ≤ 1 / (m : ℝ)) := by
  obtain ⟨M, hMtwo, hM⟩ := exists_uniform_voting_remainder_threshold A B hA hB
  refine ⟨M, hMtwo, ?_⟩
  intro m hm r hrpos hr E d δ R D hδ hR hlocal hexterior
  have hloss := hM m hm r hrpos hr
  constructor
  · exact nonnegative_of_local_exterior E d δ R D r (1 / (m : ℝ))
      (A * r * (1 + Real.log (m : ℝ)) ^ (3 : ℕ))
      (B * r ^ (2 : ℕ) * (m : ℝ) ^ ((7 : ℝ) / 4) *
        (1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2))
      hrpos hδ hR hlocal hexterior hloss
  · intro hcompetitive
    exact competitive_assembly E d δ R D r (1 / (m : ℝ))
      (A * r * (1 + Real.log (m : ℝ)) ^ (3 : ℕ))
      (B * r ^ (2 : ℕ) * (m : ℝ) ^ ((7 : ℝ) / 4) *
        (1 + Real.log (m : ℝ)) ^ ((7 : ℝ) / 2))
      hrpos hδ hR hlocal hexterior hloss hcompetitive

end NegativeVoting
