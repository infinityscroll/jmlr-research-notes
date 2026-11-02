import GaussianFanMassBase
import GaussianFacetDisintegration

/-! The actual Gaussian score law and expected maximum depend only on the
row Gram matrix, including across different ambient Euclidean dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Topology Classical

namespace NegativeVotingFanCovarianceLaw
open NegativeVotingFan
variable {ι : Type*} [Fintype ι]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The literal vector of centered linear Gaussian scores. -/
def scoreVector (B : ι → E) (x : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => inner ℝ (B i) x)

theorem continuous_scoreVector (B : ι → E) : Continuous (scoreVector B) := by
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).comp (continuous_pi (fun i => by fun_prop))

@[simp] theorem scoreVector_apply (B : ι → E) (x : E) (i : ι) :
    scoreVector B x i = inner ℝ (B i) x := rfl

theorem scoreVector_inner (B : ι → E) (x : E) (z : EuclideanSpace ℝ ι) :
    inner ℝ (scoreVector B x) z = inner ℝ x (∑ i, z i • B i) := by
  simp only [PiLp.inner_apply, scoreVector_apply, Real.inner_apply,
    inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (B i) x]
  ring

/-- This law is the actual pushforward of the standard Gaussian. -/
def scoreLaw (B : ι → E) : Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian E).map (scoreVector B)

instance scoreLaw_isProbabilityMeasure (B : ι → E) : IsProbabilityMeasure (scoreLaw B) := by
  unfold scoreLaw
  infer_instance

theorem charFun_scoreLaw (B : ι → E) (z : EuclideanSpace ℝ ι) :
    charFun (scoreLaw B) z = charFun (stdGaussian E) (∑ i, z i • B i) := by
  rw [scoreLaw, charFun_apply,
    integral_map (continuous_scoreVector B).aemeasurable (by fun_prop)]
  simp_rw [scoreVector_inner]
  rfl

/-- Gram equality identifies all linear-combination variances without
assuming an isometry between the two ambient spaces. -/
theorem linearCombination_norm_sq_eq_of_gram (B : ι → E) (C : ι → F)
    (hGram : ∀ i j, inner ℝ (B i) (B j) = inner ℝ (C i) (C j)) (z : ι → ℝ) :
    ‖∑ i, z i • B i‖ ^ 2 = ‖∑ i, z i • C i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [hGram]

/-- Equality of the actual joint Gaussian score laws follows from their
computed characteristic functions. No distribution-equivalence premise is used. -/
theorem scoreLaw_eq_of_gram (B : ι → E) (C : ι → F)
    (hGram : ∀ i j, inner ℝ (B i) (B j) = inner ℝ (C i) (C j)) :
    scoreLaw B = scoreLaw C := by
  apply Measure.ext_of_charFun
  funext z
  rw [charFun_scoreLaw, charFun_scoreLaw, charFun_stdGaussian, charFun_stdGaussian]
  have hs := linearCombination_norm_sq_eq_of_gram B C hGram (fun i => z i)
  have hn : ‖∑ i, z i • B i‖ = ‖∑ i, z i • C i‖ := by
    nlinarith [norm_nonneg (∑ i, z i • B i), norm_nonneg (∑ i, z i • C i)]
  rw [hn]

section Fan
variable [Nonempty ι] {d e : ℕ}

theorem expectedMax_eq_scoreLaw_integral (B : ι → FSC.Coord d) (h : ι → ℝ) :
    expectedMax B h = ∫ z : EuclideanSpace ℝ ι,
      NegativeVoting.maxScore (fun i => z i + h i) ∂scoreLaw B := by
  have hF : Measurable (fun z : EuclideanSpace ℝ ι =>
      NegativeVoting.maxScore (fun i => z i + h i)) :=
    NegativeVoting.measurable_finite_max _ Finset.univ Finset.univ_nonempty
      (fun i _ => by fun_prop)
  symm
  exact integral_map (continuous_scoreVector B).aemeasurable hF.aestronglyMeasurable

/-- Literal expected Gaussian maxima agree whenever the row Gram matrices
agree, even if the two ambient Euclidean dimensions differ. -/
theorem expectedMax_eq_of_gram (B : ι → FSC.Coord d) (C : ι → FSC.Coord e)
    (hGram : ∀ i j, inner ℝ (B i) (B j) = inner ℝ (C i) (C j)) (h : ι → ℝ) :
    expectedMax B h = expectedMax C h := by
  rw [expectedMax_eq_scoreLaw_integral, expectedMax_eq_scoreLaw_integral,
    scoreLaw_eq_of_gram B C hGram]

/-- The full mass-constrained dual potential is intrinsic to the row Gram
matrix. No rank, nondegeneracy, positivity, or optimizer premise is needed. -/
theorem potential_eq_of_gram (B : ι → FSC.Coord d) (C : ι → FSC.Coord e)
    (hGram : ∀ i j, inner ℝ (B i) (B j) = inner ℝ (C i) (C j)) (p h : ι → ℝ) :
    potential B p h = potential C p h := by
  simp only [potential, expectedMax_eq_of_gram B C hGram h]

end Fan
end NegativeVotingFanCovarianceLaw
