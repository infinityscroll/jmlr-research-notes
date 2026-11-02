import GaussianRegularMaximumMoments
import GaussianCompetitiveMassWindow

/-! Actual equal-Gram Gaussian score laws and regular-reference noise stability,
including different finite ambient dimensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical RealInnerProductSpace
namespace NegativeVotingRegularScoreLaw
open NegativeVoting NegativeVotingRegularMaximum

section GaussianVectors
variable {E F ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def scoreVector (B : ι → E) (x : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => inner ℝ (B i) x)

theorem scoreVector_measurable (B : ι → E) : Measurable (scoreVector B) := by
  unfold scoreVector
  fun_prop

theorem inner_scoreVector (B : ι → E) (x : E) (t : EuclideanSpace ℝ ι) :
    inner ℝ (scoreVector B x) t=inner ℝ x (∑ i, t i • B i) := by
  rw [PiLp.inner_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [scoreVector,WithLp.ofLp_toLp,Real.inner_apply,real_inner_smul_right]
  rw [real_inner_comm (B i) x]
  ring

theorem weightedRows_norm_sq_eq_of_gram (B : ι → E) (C : ι → F)
    (hG : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) (t : EuclideanSpace ℝ ι) :
    ‖∑ i, t i • B i‖^2=‖∑ i, t i • C i‖^2 := by
  rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,hG]

theorem scoreLaw_charFun (B : ι → E) (t : EuclideanSpace ℝ ι) :
    charFun ((stdGaussian E).map (scoreVector B)) t=
      Complex.exp (-‖∑ i, t i • B i‖^2/2) := by
  rw [charFun_apply,integral_map (scoreVector_measurable B).aemeasurable (by fun_prop)]
  simp_rw [inner_scoreVector]
  exact charFun_stdGaussian (∑ i, t i • B i)

/-- The complete finite-dimensional Gaussian score distribution depends only
on the Gram matrix, across different ambient dimensions. -/
theorem gaussian_scoreLaw_eq_of_gram (B : ι → E) (C : ι → F)
    (hG : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) :
    (stdGaussian E).map (scoreVector B)=(stdGaussian F).map (scoreVector C) := by
  apply Measure.ext_of_charFun
  funext t
  rw [scoreLaw_charFun,scoreLaw_charFun]
  have he := (sq_eq_sq₀ (norm_nonneg (∑ i, t i • B i))
    (norm_nonneg (∑ i, t i • C i))).mp (weightedRows_norm_sq_eq_of_gram B C hG t)
  rw [he]
end GaussianVectors

section Coordinates
variable {κ κ₂ ι : Type*} [Fintype κ] [Fintype κ₂] [Fintype ι]

def coordinateScores (B : ι → κ → ℝ) (x : κ → ℝ) : ι → ℝ :=
  fun i => ∑ j, B i j*x j

theorem coordinateScores_measurable (B : ι → κ → ℝ) : Measurable (coordinateScores B) := by
  unfold coordinateScores
  fun_prop

theorem coordinateScoreLaw_eq_vector (B : ι → κ → ℝ) :
    (standardGaussian κ).map (coordinateScores B)=
      ((stdGaussian (EuclideanSpace ℝ κ)).map
        (scoreVector (fun i => WithLp.toLp 2 (B i)))).map
        (fun x : EuclideanSpace ℝ ι => x.ofLp) := by
  rw [Measure.map_map (by fun_prop) (scoreVector_measurable _),←map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i
  simp [coordinateScores,scoreVector,PiLp.inner_apply,Real.inner_apply,mul_comm]

theorem coordinateScoreLaw_eq_of_gram (B : ι → κ → ℝ) (C : ι → κ₂ → ℝ)
    (hG : ∀ i j, (∑ k, B i k*B j k)=∑ k, C i k*C j k) :
    (standardGaussian κ).map (coordinateScores B)=
      (standardGaussian κ₂).map (coordinateScores C) := by
  rw [coordinateScoreLaw_eq_vector,coordinateScoreLaw_eq_vector]
  have h := gaussian_scoreLaw_eq_of_gram (fun i => WithLp.toLp 2 (B i))
    (fun i => WithLp.toLp 2 (C i)) (fun i j => by
      simpa [PiLp.inner_apply,Real.inner_apply,mul_comm] using hG i j)
  rw [h]

/-- Equal-Gram score laws transport every measurable scalar score observable. -/
theorem coordinateScore_integral_eq_of_gram (B : ι → κ → ℝ) (C : ι → κ₂ → ℝ)
    (hG : ∀ i j, (∑ k, B i k*B j k)=∑ k, C i k*C j k)
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) :
    (∫ x, g (coordinateScores B x) ∂standardGaussian κ)=
      ∫ x, g (coordinateScores C x) ∂standardGaussian κ₂ := by
  rw [←integral_map (coordinateScores_measurable B).aemeasurable hg.aestronglyMeasurable,
    ←integral_map (coordinateScores_measurable C).aemeasurable hg.aestronglyMeasurable,
    coordinateScoreLaw_eq_of_gram B C hG]

theorem coordinateScores_correlated (B : ι → κ → ℝ) (ρ : ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) :
    coordinateScores B (correlatedVector ρ z)=
      correlatedVector ρ (Prod.map (coordinateScores B) (coordinateScores B) z) := by
  ext i
  simp only [coordinateScores,correlatedVector,Prod.map_fst,Prod.map_snd,mul_add,
    Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

variable {m : ℕ} [Nonempty (Fin m)]

theorem score_pullback_noiseIntegrand (B : Fin m → κ → ℝ) (ρ : ℝ)
    (z : (κ → ℝ) × (κ → ℝ)) :
    noiseIntegrand ρ (regularAssignment B) z=
      noiseIntegrand ρ (maxWeights : (Fin m → ℝ) → Fin m → ℝ)
        (Prod.map (coordinateScores B) (coordinateScores B) z) := by
  unfold noiseIntegrand regularAssignment
  change (∑ i, maxWeights (coordinateScores B z.1) i*
    maxWeights (coordinateScores B (correlatedVector ρ z)) i)=_
  rw [coordinateScores_correlated]
  rfl

theorem gaussianNoiseStability_eq_scoreLaw_integral (B : Fin m → κ → ℝ) (ρ : ℝ) :
    gaussianNoiseStability ρ (regularAssignment B)=
      ∫ z, noiseIntegrand ρ (maxWeights : (Fin m → ℝ) → Fin m → ℝ) z
        ∂((standardGaussian κ).map (coordinateScores B)).prod
          ((standardGaussian κ).map (coordinateScores B)) := by
  rw [Measure.map_prod_map _ _ (coordinateScores_measurable B) (coordinateScores_measurable B)]
  rw [integral_map ((coordinateScores_measurable B).prodMap
    (coordinateScores_measurable B)).aemeasurable
    (measurable_noiseIntegrand ρ maxWeights
      (fun i => measurable_maxWeights id (fun k => measurable_pi_apply k) i)).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ (score_pullback_noiseIntegrand B ρ)

/-- Actual regular-rule noise stability is invariant under equal Gram data.
No joint-Gaussian law is assumed: the score law and its independent product
are proved to agree, and the correlation map commutes with the scores. -/
theorem gaussianNoiseStability_equal_gram (B : Fin m → κ → ℝ) (C : Fin m → κ₂ → ℝ)
    (hG : ∀ i j, (∑ k, B i k*B j k)=∑ k, C i k*C j k) (ρ : ℝ) :
    gaussianNoiseStability ρ (regularAssignment B)=gaussianNoiseStability ρ (regularAssignment C) := by
  rw [gaussianNoiseStability_eq_scoreLaw_integral,gaussianNoiseStability_eq_scoreLaw_integral,
    coordinateScoreLaw_eq_of_gram B C hG]

/-- Every regular-simplex realization in any finite ambient dimension has
exactly the canonical max-rule noise stability. -/
theorem regularAssignment_noise_eq_canonical (n : ℕ) (B : Fin (n+2) → κ → ℝ)
    (hB : RegularSimplexGram B) (ρ : ℝ) :
    gaussianNoiseStability ρ (regularAssignment B)=
      gaussianNoiseStability ρ (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) := by
  rw [gaussianNoiseStability_equal_gram B (canonicalRows n)
    (fun i j => (hB i j).trans ((canonicalRows_gram n) i j).symm) ρ]
  have he : regularAssignment (canonicalRows n)=
      (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) := by
    funext x i
    exact canonicalAssignment_eq n x i
  rw [he]
theorem regular_maximum_mean_eq_canonical (n : ℕ) (B : Fin (n+2) → κ → ℝ)
    (hB : RegularSimplexGram B) :
    (∫ x, maxScore (fun i => ∑ k, B i k*x k) ∂standardGaussian κ)=
      NegativeVotingGaussianMaximum.maximumMean n := by
  have h := coordinateScore_integral_eq_of_gram B (canonicalRows n)
    (fun i j => (hB i j).trans ((canonicalRows_gram n) i j).symm)
    (maxScore : (Fin (n+2) → ℝ) → ℝ)
    NegativeVotingGaussianMaximum.maximum_measurable
  exact h.trans (canonical_maximum_mean n)

theorem regular_chaosEnergy_one_eq_reference (n : ℕ) (hn : 0 < n)
    (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B) :
    NegativeVotingModern.chaosEnergy (regularAssignment B) 1=
      NegativeVotingGaussianMaximumMean.referenceFirstWeight n := by
  rw [regular_chaosEnergy_one B hB (by omega),regular_maximum_mean_eq_canonical n B hB]
  unfold NegativeVotingGaussianMaximumMean.referenceFirstWeight
  congr 1
  push_cast
  ring

end Coordinates

universe u
/-- One threshold applies to every actual regular-simplex realization and every
fractional competitor, simultaneously over the full voting correlation range. -/
theorem eventually_uniform_regular_competitive_mass_window :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (B : Fin (n+2) → κ → ℝ) (hB : RegularSimplexGram B)
      (f : (κ → ℝ) → Fin (n+2) → ℝ)
      (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
      (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
      (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/((n:ℝ)+1))
      (hcomp : gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment B)),
      ((n:ℝ)+2)^2*NegativeVotingFractionalMass.massDeficit n f ≤ 49/50 ∧
      ∀ i, NegativeVotingFractionalMass.assignmentMass f i ∈
        Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2)) := by
  filter_upwards [NegativeVotingCompetitiveMassWindow.eventually_uniform_competitive_mass_window]
    with n hn
  intro κ _ B hB f hf hp r hr0 hr hcomp
  rw [regularAssignment_noise_eq_canonical n B hB (-r)] at hcomp
  exact hn κ f hf hp r hr0 hr hcomp

end NegativeVotingRegularScoreLaw
