import GaussianCapCovariance

/-!
Actual Gaussian first-moment / boundary identities for a finite polyhedron.
The concrete support derivative is from Abhijeet Mulgund's MIT-licensed FSC
library. The actual MGF identity and moment bounds are proved in the imported
GaussianCapCovariance module; MGF differentiation is supplied by mathlib.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators ENNReal Topology

namespace NegativeVotingPolyhedral

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moving the cap in a fixed ambient direction changes its mass by the
explicit sum of normal densities, conditional face masses, and velocities. -/
theorem cap_translation_derivative
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (v : FSC.Coord d) :
    HasDerivAt (fun t : ℝ =>
      FSC.capMass w (fun j => b j - t * inner ℝ (w j) v))
      (-(∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * inner ℝ (w j) v))
      0 := by
  have h := support_directional_derivative w hw b
    (fun j => -inner ℝ (w j) v) hsep
  simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul, mul_neg,
    ← sub_eq_add_neg, Finset.sum_neg_distrib] using h

theorem cap_mgf_first_derivative_boundary
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (v : FSC.Coord d) :
    HasDerivAt
      (mgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)))
      (-(∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * inner ℝ (w j) v))
      0 := by
  have hq : HasDerivAt (fun t : ℝ => t ^ 2 * ‖v‖ ^ 2 / 2) 0 0 := by
    simpa [Pi.pow_def, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖v‖ ^ 2)).div_const 2
  have he : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2)) 0 0 := by
    simpa using hq.exp
  have hp := he.mul (cap_translation_derivative w hw b hsep v)
  have heq : (mgf (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) =
      (fun t : ℝ => Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        FSC.capMass w (fun j => b j - t * inner ℝ (w j) v)) := by
    funext t
    exact cap_mgf_translate w b v t
  rw [heq]
  simpa only [Pi.mul_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div,
    Real.exp_zero, one_mul, zero_add] using hp

/-- Actual scalar Gaussian integration by parts. The cap may have zero mass;
all moment and differentiability inputs are derived, not assumed. -/
theorem gaussian_cap_first_moment
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (v : FSC.Coord d) :
    (∫ x in FSC.cap w b, inner ℝ v x ∂stdGaussian (FSC.Coord d)) =
      -(∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * inner ℝ (w j) v) := by
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ 0
  have hm := hasDerivAt_mgf hz
  have hb := cap_mgf_first_derivative_boundary w hw b hsep v
  simpa only [zero_mul, Real.exp_zero, mul_one] using hm.unique hb

theorem gaussian_cap_vector_integrable
    (w : ι → FSC.Coord d) (b : ι → ℝ) :
    Integrable (fun x : FSC.Coord d => x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) :=
  IsGaussian.integrable_id.restrict

/-- Full vector first moment as the outward-normal boundary sum. -/
theorem gaussian_cap_vector_first_moment
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    (∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)) =
      -(∑ j, (WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j) • w j) := by
  apply ext_inner_left ℝ
  intro v
  calc
    inner ℝ v (∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)) =
        ∫ x in FSC.cap w b, inner ℝ v x ∂stdGaussian (FSC.Coord d) :=
      (integral_inner (gaussian_cap_vector_integrable w b) v).symm
    _ = -(∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * inner ℝ (w j) v) :=
      gaussian_cap_first_moment w hw b hsep v
    _ = _ := by simp [inner_sum, real_inner_smul_right, real_inner_comm]

theorem gaussian_cap_coordinate_first_moment
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (k : Fin d) :
    (∫ x in FSC.cap w b, x k ∂stdGaussian (FSC.Coord d)) =
      -(∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * w j k) := by
  calc
    (∫ x in FSC.cap w b, x k ∂stdGaussian (FSC.Coord d)) =
        (EuclideanSpace.proj (𝕜 := ℝ) k)
          (∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) k).integral_comp_comm
        (gaussian_cap_vector_integrable w b)
    _ = _ := by rw [gaussian_cap_vector_first_moment w hw b hsep]; simp

end NegativeVotingPolyhedral
