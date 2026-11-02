import FSC.Definitions
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! Exact affine-image laws for arbitrary PSD covariances, including zero rank and rectangular linear maps. The proof uses actual Gaussianity, mean and covariance, as prescribed in `docs/pro-return/DOSSIER.md`, section 3. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace FSC

/-- Rectangular matrices act continuously on the ordinary Euclidean coordinates. -/
def lin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Coord n →L[ℝ] Coord m :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

@[simp] theorem lin_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Coord n) (i : Fin m) : lin A x i = (A *ᵥ x) i := rfl

@[simp] theorem lin_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    lin A.transpose = (lin A).adjoint := by
  unfold lin
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Congruence preserves PSD without injectivity or rank assumptions on A. -/
theorem posSemidef_congruence {m n : ℕ} (G : Mat n) (hG : G.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) : (A * G * A.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hG.mul_mul_conjTranspose_same A

/-- A zero-covariance Gaussian is its actual deterministic law. -/
@[simp] theorem multivariateGaussian_zero_cov {n : ℕ} (μ : Coord n) :
    multivariateGaussian μ (0 : Mat n) = Measure.dirac μ := by
  simp [multivariateGaussian]

/-- Exact linear image, with arbitrary means and arbitrary PSD covariance. -/
theorem map_lin_multivariateGaussian {m n : ℕ}
    (μ : Coord n) (G : Mat n) (hG : G.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Measure.map (lin A) (multivariateGaussian μ G) =
      multivariateGaussian (lin A μ) (A * G * A.transpose) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp only [integral_id_multivariateGaussian]
    · exact IsGaussian.integrable_id
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hG,
      covarianceBilin_multivariateGaussian (posSemidef_congruence G hG A),
      ← lin_transpose]
    change (A.transpose *ᵥ x) ⬝ᵥ G *ᵥ (A.transpose *ᵥ y) =
      x ⬝ᵥ (A * G * A.transpose) *ᵥ y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec x A, Matrix.mulVec_transpose]

/-- Exact affine image, including translations and maps that increase codimension. -/
theorem map_affine_multivariateGaussian {m n : ℕ}
    (μ : Coord n) (G : Mat n) (hG : G.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Coord m) :
    Measure.map (fun x ↦ b + lin A x) (multivariateGaussian μ G) =
      multivariateGaussian (b + lin A μ) (A * G * A.transpose) := by
  change Measure.map ((fun x ↦ b + x) ∘ lin A) (multivariateGaussian μ G) = _
  rw [← Measure.map_map (measurable_const_add b) (lin A).measurable,
    map_lin_multivariateGaussian μ G hG A]
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [integral_add (integrable_const b) IsGaussian.integrable_fun_id]
    simp only [integral_const, probReal_univ, one_smul, integral_id_multivariateGaussian]
  · rw [covarianceBilin_map_const_add]
    ext x y
    rw [covarianceBilin_multivariateGaussian (posSemidef_congruence G hG A),
      covarianceBilin_multivariateGaussian (posSemidef_congruence G hG A)]

end FSC
