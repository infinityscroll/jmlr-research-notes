import GaussianCapSecondMoment

/-!
Actual normalized conditional-covariance boundary gap. Every quantity below
is defined by the concrete Gaussian cap or slice integrals. No matrix
factorization or conditional covariance identity is taken as a premise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators ENNReal

namespace NegativeVotingPolyhedral

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def capConditionalCovariance (w : ι → FSC.Coord d) (b : ι → ℝ)
    (u v : FSC.Coord d) : ℝ :=
  (∫ x in FSC.cap w b,
    (inner ℝ u x - (∫ y in FSC.cap w b, inner ℝ u y ∂stdGaussian (FSC.Coord d)) /
      FSC.capMass w b) *
    (inner ℝ v x - (∫ y in FSC.cap w b, inner ℝ v y ∂stdGaussian (FSC.Coord d)) /
      FSC.capMass w b) ∂stdGaussian (FSC.Coord d)) / FSC.capMass w b

def capBoundaryFirstFlux (w : ι → FSC.Coord d) (b : ι → ℝ) (v : FSC.Coord d) : ℝ :=
  ∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * inner ℝ (w j) v

def capBoundarySecondFlux (w : ι → FSC.Coord d) (b : ι → ℝ)
    (u v : FSC.Coord d) : ℝ :=
  ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) *
    (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j))

theorem cap_conditional_covariance_expansion
    (w : ι → FSC.Coord d) (b : ι → ℝ) (hp : 0 < FSC.capMass w b)
    (u v : FSC.Coord d) :
    capConditionalCovariance w b u v =
      (∫ x in FSC.cap w b, inner ℝ u x * inner ℝ v x ∂stdGaussian (FSC.Coord d)) /
        FSC.capMass w b -
      ((∫ x in FSC.cap w b, inner ℝ u x ∂stdGaussian (FSC.Coord d)) *
        (∫ x in FSC.cap w b, inner ℝ v x ∂stdGaussian (FSC.Coord d))) /
        (FSC.capMass w b) ^ 2 := by
  let μ := (stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)
  let p := FSC.capMass w b
  let A := ∫ x, inner ℝ u x ∂μ
  let B := ∫ x, inner ℝ v x ∂μ
  have hu : Integrable (fun x : FSC.Coord d => inner ℝ u x) μ := by
    simpa using cap_score_moment_integrable w b u 1
  have hv : Integrable (fun x : FSC.Coord d => inner ℝ v x) μ := by
    simpa using cap_score_moment_integrable w b v 1
  have hu2 : MemLp (fun x : FSC.Coord d => inner ℝ u x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (cap_score_moment_integrable w b u 2)
  have hv2 : MemLp (fun x : FSC.Coord d => inner ℝ v x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (cap_score_moment_integrable w b v 2)
  have huv : Integrable (fun x : FSC.Coord d => inner ℝ u x * inner ℝ v x) μ :=
    hu2.integrable_mul hv2
  have hm : μ.real Set.univ = p := by simp [μ, p, FSC.capMass, measureReal_def]
  have he (x : FSC.Coord d) :
      (inner ℝ u x - A / p) * (inner ℝ v x - B / p) =
      ((inner ℝ u x * inner ℝ v x - (B / p) * inner ℝ u x) -
        (A / p) * inner ℝ v x) + (A / p) * (B / p) := by ring
  change (∫ x, (inner ℝ u x - A / p) * (inner ℝ v x - B / p) ∂μ) / p =
    (∫ x, inner ℝ u x * inner ℝ v x ∂μ) / p - A * B / p ^ 2
  simp_rw [he]
  have hs1 : Integrable (fun x : FSC.Coord d =>
      inner ℝ u x * inner ℝ v x - (B / p) * inner ℝ u x) μ := by
    simpa only [Pi.sub_def] using huv.sub (hu.const_mul (B / p))
  have hs2 : Integrable (fun x : FSC.Coord d =>
      inner ℝ u x * inner ℝ v x - (B / p) * inner ℝ u x -
        (A / p) * inner ℝ v x) μ := by
    simpa only [Pi.sub_def] using hs1.sub (hv.const_mul (A / p))
  rw [integral_add hs2 (integrable_const _),
    integral_sub hs1 (hv.const_mul (A / p)),
    integral_sub huv (hu.const_mul (B / p)), integral_const_mul, integral_const_mul,
    integral_const, hm]
  change ((∫ x, inner ℝ u x * inner ℝ v x ∂μ) - (B / p) * A - (A / p) * B +
    p * ((A / p) * (B / p))) / p = _
  have hp' : p ≠ 0 := hp.ne'
  field_simp <;> ring

/-- The normalized covariance gap is an actual boundary tensor plus the
rank-one product of the actual boundary first-moment fluxes. -/
theorem gaussian_cap_covariance_boundary_gap
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hp : 0 < FSC.capMass w b)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (u v : FSC.Coord d) :
    inner ℝ u v - capConditionalCovariance w b u v =
      capBoundarySecondFlux w b u v / FSC.capMass w b +
        (capBoundaryFirstFlux w b u * capBoundaryFirstFlux w b v) /
          (FSC.capMass w b) ^ 2 := by
  rw [cap_conditional_covariance_expansion w b hp,
    gaussian_cap_bilinear_second_moment w hw b hsep,
    gaussian_cap_first_moment w hw b hsep u,
    gaussian_cap_first_moment w hw b hsep v]
  unfold capBoundaryFirstFlux capBoundarySecondFlux
  have hp' := hp.ne'
  field_simp <;> ring

/-- Positive semidefiniteness in every direction is derived from the actual
conditional Gaussian variance bound, not assumed of the boundary tensor. -/
theorem gaussian_cap_covariance_boundary_gap_nonneg
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hp : 0 < FSC.capMass w b)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (v : FSC.Coord d) :
    0 ≤ capBoundarySecondFlux w b v v / FSC.capMass w b +
      (capBoundaryFirstFlux w b v) ^ 2 / (FSC.capMass w b) ^ 2 := by
  have hc : capConditionalCovariance w b v v ≤ ‖v‖ ^ 2 := by
    simpa [capConditionalCovariance, pow_two] using
      gaussian_cap_conditional_variance_le w b hp v
  have hgap := gaussian_cap_covariance_boundary_gap w hw b hp hsep v v
  rw [real_inner_self_eq_norm_sq] at hgap
  have h := sub_nonneg.mpr hc
  rw [hgap] at h
  simpa only [pow_two] using h

end NegativeVotingPolyhedral
