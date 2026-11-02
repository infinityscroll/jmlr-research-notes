import GaussianMaximumLocalization
import NegativeVoting.RegularSimplexCentroid
import GaussianSecondChaos

/-! Actual regular-max assignment and its Gaussian moment identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace NegativeVotingRegularMaximum
open NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingGaussianMaximumLocalization
  NegativeVoting NegativeVotingModern OAI.MinUncut.GaussianHermite

def canonicalRows (n : ℕ) (i k : Fin (n+2)) : ℝ :=
  (if i=k then 1 else 0)-1/((n:ℝ)+2)

def coordinateMean (n : ℕ) (x : Fin (n+2) → ℝ) : ℝ := (∑ k, x k)/((n:ℝ)+2)

theorem canonicalRows_score (n : ℕ) (i : Fin (n+2)) (x : Fin (n+2) → ℝ) :
    (∑ k, canonicalRows n i k*x k)=x i-coordinateMean n x := by
  unfold canonicalRows coordinateMean
  simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum]
  ring

theorem canonicalRows_gram (n : ℕ) : RegularSimplexGram (canonicalRows n) := by
  intro i j
  have hc : (n:ℝ)+2 ≠ 0 := by positivity
  have he (k : Fin (n+2)) : canonicalRows n i k*canonicalRows n j k =
      (if i=k then 1 else 0)*(if j=k then 1 else 0)-
      (1/((n:ℝ)+2))*(if i=k then 1 else 0)-
      (1/((n:ℝ)+2))*(if j=k then 1 else 0)+(1/((n:ℝ)+2))^2 := by
    unfold canonicalRows
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp [ite_mul,eq_comm,Nat.cast_add,Nat.cast_ofNat]
  field_simp <;> ring

theorem maxScore_sub_const {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (c : ℝ) :
    maxScore (fun i => s i-c)=maxScore s-c := by
  exact (map_finset_sup' (OrderIso.subRight c) Finset.univ_nonempty s).symm

theorem maxWeights_sub_const {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (c : ℝ) (i : ι) :
    maxWeights (fun j => s j-c) i=maxWeights s i := by
  have he (j : ι) : maxIndicator (fun k => s k-c) j=maxIndicator s j := by
    simp only [maxIndicator,maxScore_sub_const,sub_left_inj]
  unfold maxWeights maxMultiplicity
  simp only [he]

theorem canonicalAssignment_eq (n : ℕ) (x : Fin (n+2) → ℝ) (i : Fin (n+2)) :
    regularAssignment (canonicalRows n) x i=maxWeights x i := by
  unfold regularAssignment
  simp_rw [canonicalRows_score]
  exact maxWeights_sub_const x (coordinateMean n x) i

theorem coordinateMean_integrable (n : ℕ) : Integrable (coordinateMean n) (standardGaussian (Fin (n+2))) := by
  exact (integrable_finsetSum Finset.univ (fun k _ =>
    gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) k)).div_const _

theorem standardGaussian_coordinate_integral {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) :
    (∫ x, x k ∂standardGaussian κ)=0 := by
  calc
    _ = ∫ y : ℝ, y ∂((standardGaussian κ).map (fun x : κ → ℝ => x k)) :=
      (integral_map (μ := standardGaussian κ) (φ := fun x : κ → ℝ => x k)
        (f := fun y : ℝ => y) (measurable_pi_apply k).aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = 0 := by
      rw [gaussian_product_coordinate_law]
      exact integral_id_gaussianReal

theorem coordinateMean_integral (n : ℕ) : (∫ x, coordinateMean n x ∂standardGaussian (Fin (n+2)))=0 := by
  unfold coordinateMean
  rw [integral_div,integral_finsetSum Finset.univ (fun k _ =>
    gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) k)]
  simp [standardGaussian_coordinate_integral]

/-- The actual centered regular scores have exactly the iid maximum mean. -/
theorem canonical_maximum_mean (n : ℕ) :
    (∫ x, maxScore (fun i => ∑ k, canonicalRows n i k*x k) ∂standardGaussian (Fin (n+2)))=maximumMean n := by
  simp_rw [canonicalRows_score,maxScore_sub_const]
  change (∫ x, maximum x-coordinateMean n x ∂standardGaussian (Fin (n+2)))=maximumMean n
  rw [integral_sub maximum_integrable (coordinateMean_integrable n),coordinateMean_integral,sub_zero]
  rfl

theorem canonical_mass (n : ℕ) (i : Fin (n+2)) :
    (∫ x, maxWeights x i ∂standardGaussian (Fin (n+2)))=1/((n:ℝ)+2) := by
  have h := regularAssignment_mass (canonicalRows n) (canonicalRows_gram n) i
  simpa only [canonicalAssignment_eq,Nat.cast_add,Nat.cast_ofNat] using h

/-- Actual first chaos for every regular Gram realization, in its own ambient dimension. -/
theorem regular_chaosEnergy_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    {m : ℕ} [Nonempty (Fin m)] (rows : Fin m → κ → ℝ)
    (hrows : RegularSimplexGram rows) (hm : 3 ≤ m) :
    chaosEnergy (regularAssignment rows) 1=
      (∫ x, maxScore (fun j => ∑ k, rows j k*x k) ∂standardGaussian κ)^2/((m:ℝ)-1) := by
  rw [chaosEnergy_one]
  have he (i : Fin m) (k : κ) : (∫ x, x k*regularAssignment rows x i ∂γpi κ)=
      gaussianCentroid (fun _ => 0) (fun _ => 1) (regularAssignment rows) i k := by
    change (∫ x, x k*regularAssignment rows x i ∂standardGaussian κ)=
      ∫ x, regularAssignment rows x i*x k ∂standardGaussian κ
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  simp_rw [he]
  exact regularAssignment_centroid_energy rows hrows hm

/-- Concrete transfer: the first-weight expression is the literal Hermite energy
of the canonical regular-max assignment, not an assumed coefficient formula. -/
theorem canonical_chaosEnergy_one (n : ℕ) (hn : 0 < n) :
    chaosEnergy (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) 1=referenceFirstWeight n := by
  have he : regularAssignment (canonicalRows n)=(maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ) := by
    funext x i
    exact canonicalAssignment_eq n x i
  rw [← he,regular_chaosEnergy_one _ (canonicalRows_gram n) (by omega),canonical_maximum_mean]
  unfold referenceFirstWeight
  congr 1
  push_cast
  ring

end NegativeVotingRegularMaximum
