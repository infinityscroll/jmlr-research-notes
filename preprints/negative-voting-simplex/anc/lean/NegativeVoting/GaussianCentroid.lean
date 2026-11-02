import Mathlib
import NegativeVoting.GaussianMoments

/-!
# Exact Gaussian centroid pairing

The actual finite product-Gaussian integrals are used here. Measurable fractional
assignments have integrable coordinate moments; pairing them with linear scores
is exactly pairing their centroid matrix with the score matrix. The self-centroid
case yields the squared Frobenius norm in the manuscript's routing calculation.
-/

namespace NegativeVoting

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- Coordinate moments of a fractional assignment under a finite product Gaussian. -/
noncomputable def gaussianCentroid (means : κ → ℝ) (variances : κ → ℝ≥0)
    (p : (κ → ℝ) → ι → ℝ) (i : ι) (j : κ) : ℝ :=
  ∫ x, p x i * x j ∂Measure.pi (fun k => gaussianReal (means k) (variances k))

/-- Expected linear-assignment score equals the exact score/centroid pairing. -/
theorem gaussian_centroid_pairing
    (means : κ → ℝ) (variances : κ → ℝ≥0)
    (p : (κ → ℝ) → ι → ℝ) (a : ι → κ → ℝ)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i)
      (Measure.pi (fun j => gaussianReal (means j) (variances j)))) :
    (∫ x, ∑ i, p x i * (∑ j, a i j * x j)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j))) =
      ∑ i, ∑ j, a i j * gaussianCentroid means variances p i j := by
  let ν := Measure.pi (fun j => gaussianReal (means j) (variances j))
  have hint (i : ι) (j : κ) : Integrable (fun x => p x i * x j) ν :=
    integrable_weighted_score ν p (fun x _ => x j) i hp (hpmeas i)
      (gaussian_product_coordinate_integrable means variances j)
  have hinner (i : ι) : Integrable (fun x => ∑ j, a i j * (p x i * x j)) ν :=
    integrable_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (a i j))
  calc
    _ = ∫ x, ∑ i, ∑ j, a i j * (p x i * x j) ∂ν := by
      congr 1
      funext x
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∫ x, ∑ j, a i j * (p x i * x j) ∂ν :=
      integral_finsetSum Finset.univ (fun i _ => hinner i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (a i j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      rfl

/-- Choosing the actual centroid matrix as score matrix makes the expected
fractional score exactly its squared Frobenius norm. -/
theorem gaussian_self_centroid_score
    (means : κ → ℝ) (variances : κ → ℝ≥0)
    (p : (κ → ℝ) → ι → ℝ)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i)
      (Measure.pi (fun j => gaussianReal (means j) (variances j)))) :
    (∫ x, ∑ i, p x i * (∑ j, gaussianCentroid means variances p i j * x j)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j))) =
      ∑ i, ∑ j, (gaussianCentroid means variances p i j) ^ 2 := by
  simpa only [pow_two] using gaussian_centroid_pairing means variances p
    (gaussianCentroid means variances p) hp hpmeas

/-- The expected self-centroid routing gap is exactly the expected finite
maximum minus squared centroid norm. Integrability is derived, not assumed. -/
theorem gaussian_expected_centroid_gap [Nonempty ι]
    (means : κ → ℝ) (variances : κ → ℝ≥0)
    (p : (κ → ℝ) → ι → ℝ)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hpmeas : ∀ i, AEMeasurable (fun x => p x i)
      (Measure.pi (fun j => gaussianReal (means j) (variances j)))) :
    (∫ x,
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ j, gaussianCentroid means variances p i j * x j) -
        ∑ i, p x i * (∑ j, gaussianCentroid means variances p i j * x j))
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j))) =
      (∫ x, Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ j, gaussianCentroid means variances p i j * x j)
        ∂Measure.pi (fun j => gaussianReal (means j) (variances j))) -
      ∑ i, ∑ j, (gaussianCentroid means variances p i j) ^ 2 := by
  have hmax := gaussian_linear_max_integrable means variances (gaussianCentroid means variances p)
  have hmix := integrable_score_mixture
    (Measure.pi (fun j => gaussianReal (means j) (variances j))) p
    (fun x i => ∑ j, gaussianCentroid means variances p i j * x j) hp hpmeas
    (fun i => gaussian_linear_score_integrable means variances (gaussianCentroid means variances p i))
  rw [integral_sub hmax hmix, gaussian_self_centroid_score means variances p hp hpmeas]

end NegativeVoting
