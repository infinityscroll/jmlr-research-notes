import Mathlib
import NegativeVoting.NoiseStability
import NegativeVoting.RegularSimplex
import NegativeVoting.Admissible

/-!
# The exact outstanding Gaussian theorem

`FullNegativeVotingStatement` is a proposition, not a proved theorem. No instance,
axiom, or theorem asserting it is supplied. A successful project build checks the
well-formed statement and its supporting lemmas; it does not prove this goal.

The existential reference prevents a vacuous universal assertion over nonexistent
regular matrices. The alphabet threshold precedes dimension and correlation, so
it must be uniform in both. Ambient dimension is n+1; the threshold is at least 3,
so every dimension allowed by the manuscript is represented. Normalized Gram
matrices define the same partitions as the manuscript's positive rescaling.
-/
namespace NegativeVoting
open MeasureTheory

/-- The full large-alphabet negative-voting Gaussian simplex statement, including
all measurable fractional assignments and the exact regular equality class.
The reference may depend on m and dimension, but not on rho or the competitor. -/
def FullNegativeVotingStatement : Prop :=
  ∃ M : ℕ, ∃ hM : 3 ≤ M, ∀ m : ℕ, ∀ hm : M ≤ m,
    letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp
      (lt_of_lt_of_le (by decide : 0 < 3) (le_trans hM hm))
    ∀ n : ℕ, m - 1 ≤ n + 1 →
      ∃ reference : Fin m → Fin (n + 1) → ℝ,
        RegularSimplexGram reference ∧
        ∀ ρ : ℝ, -(1 / ((m : ℝ) - 1)) ≤ ρ → ρ < 0 →
        ∀ f : (Fin (n + 1) → ℝ) → Fin m → ℝ,
          (∀ i, AEMeasurable (fun x => f x i) (standardGaussian (Fin (n + 1)))) →
          (∀ᵐ x ∂standardGaussian (Fin (n + 1)), SimplexWeights (f x)) →
          gaussianNoiseStability ρ (regularAssignment reference) ≤
            gaussianNoiseStability ρ f ∧
          (gaussianNoiseStability ρ f =
              gaussianNoiseStability ρ (regularAssignment reference) ↔
            ∃ rows : Fin m → Fin (n + 1) → ℝ,
              RegularSimplexGram rows ∧
              ∀ᵐ x ∂standardGaussian (Fin (n + 1)),
                f x = regularAssignment rows x)

end NegativeVoting
