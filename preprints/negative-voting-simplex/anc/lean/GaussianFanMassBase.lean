import NegativeVoting.RegularSimplex
import NegativeVoting.Integrability
import FSC.Support.Slicing

/-! Concrete Gaussian affine fans and the convex dual used to prescribe masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators

namespace NegativeVotingFan
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

def scores (B : ι → FSC.Coord d) (h : ι → ℝ) (x : FSC.Coord d) (i : ι) : ℝ :=
  inner ℝ (B i) x + h i

def weights (B : ι → FSC.Coord d) (h : ι → ℝ) (x : FSC.Coord d) : ι → ℝ :=
  NegativeVoting.maxWeights (scores B h x)

def mass (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) : ℝ :=
  ∫ x, weights B h x i ∂stdGaussian (FSC.Coord d)

def expectedMax (B : ι → FSC.Coord d) (h : ι → ℝ) : ℝ :=
  ∫ x, NegativeVoting.maxScore (scores B h x) ∂stdGaussian (FSC.Coord d)

def potential (B : ι → FSC.Coord d) (p h : ι → ℝ) : ℝ :=
  expectedMax B h - ∑ i, p i * h i

theorem score_integrable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Integrable (fun x => scores B h x i) (stdGaussian (FSC.Coord d)) := by
  exact (IsGaussian.integrable_dual _ (innerSL ℝ (B i))).add (integrable_const _)

theorem integral_score (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    (∫ x, scores B h x i ∂stdGaussian (FSC.Coord d)) = h i := by
  unfold scores
  have hi : Integrable (fun x : FSC.Coord d => inner ℝ (B i) x)
      (stdGaussian (FSC.Coord d)) := IsGaussian.integrable_dual _ (innerSL ℝ (B i))
  rw [integral_add hi (integrable_const _)]
  have hz := integral_strongDual_stdGaussian (innerSL ℝ (B i))
  change (∫ x, inner ℝ (B i) x ∂stdGaussian (FSC.Coord d)) = 0 at hz
  simp [hz]

theorem max_integrable (B : ι → FSC.Coord d) (h : ι → ℝ) :
    Integrable (fun x => NegativeVoting.maxScore (scores B h x))
      (stdGaussian (FSC.Coord d)) := by
  classical
  exact NegativeVoting.integrable_finite_max _ _ Finset.univ Finset.univ_nonempty
    (fun i _ => score_integrable B h i)

theorem offset_le_expectedMax (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    h i ≤ expectedMax B h := by
  rw [← integral_score B h i]
  exact integral_mono (score_integrable B h i) (max_integrable B h)
    (fun x => Finset.le_sup' (f := scores B h x) (Finset.mem_univ i))

theorem maxScore_sub_bound (s t : ι → ℝ) :
    |NegativeVoting.maxScore s - NegativeVoting.maxScore t| ≤ ‖s - t‖ := by
  classical
  have hupper (a b : ι → ℝ) :
      NegativeVoting.maxScore a ≤ NegativeVoting.maxScore b + ‖a - b‖ := by
    apply Finset.sup'_le
    intro i _
    have hb : b i ≤ NegativeVoting.maxScore b :=
      Finset.le_sup' (f := b) (Finset.mem_univ i)
    have hn : |a i - b i| ≤ ‖a - b‖ := norm_le_pi_norm (a - b) i
    have ha := le_abs_self (a i - b i)
    linarith
  have hst := hupper s t
  have hts := hupper t s
  rw [norm_sub_rev t s] at hts
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem max_score_offset_bound (B : ι → FSC.Coord d) (h k : ι → ℝ)
    (x : FSC.Coord d) :
    |NegativeVoting.maxScore (scores B h x) -
      NegativeVoting.maxScore (scores B k x)| ≤ ‖h - k‖ := by
  have he : scores B h x - scores B k x = h - k := by
    ext i
    simp only [Pi.sub_apply, scores]
    ring
  simpa only [he] using maxScore_sub_bound (scores B h x) (scores B k x)

theorem expectedMax_sub_bound (B : ι → FSC.Coord d) (h k : ι → ℝ) :
    |expectedMax B h - expectedMax B k| ≤ ‖h - k‖ := by
  have hh := max_integrable B h
  have hk := max_integrable B k
  have hb := norm_integral_le_of_norm_le_const (μ := stdGaussian (FSC.Coord d))
    (f := fun x => NegativeVoting.maxScore (scores B h x) -
      NegativeVoting.maxScore (scores B k x))
    (Filter.Eventually.of_forall (fun x => max_score_offset_bound B h k x))
  simpa [integral_sub hh hk, expectedMax] using hb

theorem expectedMax_lipschitz (B : ι → FSC.Coord d) :
    LipschitzWith 1 (expectedMax B) := by
  apply LipschitzWith.of_dist_le_mul
  intro h k
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] using
    expectedMax_sub_bound B h k

theorem potential_continuous (B : ι → FSC.Coord d) (p : ι → ℝ) :
    Continuous (potential B p) := by
  unfold potential
  exact (expectedMax_lipschitz B).continuous.sub (by fun_prop)

end NegativeVotingFan
