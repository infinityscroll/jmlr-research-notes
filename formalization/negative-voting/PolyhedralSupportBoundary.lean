import FSC.Support.QuadraticTangent

/-!
Concrete Gaussian support-calculus interface to Abhijeet Mulgund's
`full-simplex-conjecture-lean` (MIT), commit
ae04e529427c26b18fb89a276c31954176dec6dd.

These are transparent restatements and elementary compositions of the imported
results. They expose all geometric premises. Normals are fixed; only support
thresholds vary. No covariance Hessian or dimension-uniform estimate is asserted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators ENNReal

namespace NegativeVotingPolyhedral

/-- Actual Gaussian disintegration at every real normal pin, including the
singular Gaussian law on that affine hyperplane. -/
theorem normal_slice_disintegration {d : ℕ}
    (w : FSC.Coord d) (hw : ‖w‖ = 1)
    (f : FSC.Coord d × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y : FSC.Coord d, f (y, inner ℝ w y) ∂stdGaussian (FSC.Coord d)) =
      ∫⁻ z : ℝ, ∫⁻ y : FSC.Coord d, f (y, z)
        ∂(stdGaussian (FSC.Coord d)).map
          (fun y => z • w + (y - inner ℝ w y • w))
        ∂gaussianReal 0 1 :=
  FSC.lintegral_normalSlice w hw f hf

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability of the literal finite intersection has an actual Frechet
derivative. Coincident supporting hyperplanes are excluded explicitly. -/
theorem support_frechet_derivative
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    HasFDerivAt
      (fun c : ι → ℝ =>
        (stdGaussian (FSC.Coord d) {y | ∀ j, inner ℝ (w j) y ≤ c j}).toReal)
      (∑ j, (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
        (WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j)) b :=
  FSC.hasFDerivAt_capMass w hw b hsep

/-- C1 regularity holds in an actual open neighborhood of the base supports. -/
theorem support_C1
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ b ∈ U ∧
      ContDiffOn ℝ 1 (FSC.capMass w) U ∧
      ∀ c ∈ U, HasFDerivAt (FSC.capMass w) (FSC.supportGradient w c) c :=
  FSC.capMass_support_C1 w hw b hsep

/-- Along every threshold direction, the derivative is the explicit sum of
one-dimensional density times conditional face probability times velocity. -/
theorem support_directional_derivative
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b v : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    HasDerivAt (fun t : ℝ => FSC.capMass w (b + t • v))
      (∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * v j) 0 := by
  have hf : HasFDerivAt (FSC.capMass w) (FSC.supportGradient w b)
      (b + (0 : ℝ) • v) := by
    simpa using FSC.hasFDerivAt_capMass w hw b hsep
  have hline : HasDerivAt (fun t : ℝ => b + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add b
  simpa [FSC.supportGradient, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hf.comp_hasDerivAt 0 hline

/-- The actual full ambient squared-norm integral follows from dilation and
the proved support derivative; no derivative premise remains. -/
theorem support_dilation_energy
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    (∫ y in {y : FSC.Coord d | ∀ j, inner ℝ (w j) y ≤ b j},
      ‖y‖ ^ 2 ∂stdGaussian (FSC.Coord d)) =
      (d : ℝ) * FSC.capMass w b -
        ∑ j, b j * WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j :=
  FSC.capEnergy_eq_of_hasFDerivAt w b (FSC.hasFDerivAt_capMass w hw b hsep)

/-- Reciprocal-cap-probability convexity gives the concrete support tangent.
Both support arrays must be strictly positive. The comparison array may have
coincident faces; no separation hypothesis is imposed there. -/
theorem positive_support_tangent
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b c : ι → ℝ)
    (hb : ∀ j, 0 < b j) (hc : ∀ j, 0 < c j)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    (∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * (b j - c j)) ≤
      FSC.capMass w b ^ 2 / FSC.capMass w c - FSC.capMass w b := by
  simpa [FSC.supportGradient, mul_comm, mul_left_comm, mul_assoc] using
    FSC.quadratic_support_tangent w hw b c hb hc hsep

/-- Gaussian cap log-concavity makes the actual positive-probability domain
convex; individual support coordinates need not be positive. -/
theorem convex_positive_mass_supports (w : ι → FSC.Coord d) :
    Convex ℝ {b : ι → ℝ | 0 < FSC.capMass w b} := by
  apply convex_iff_forall_pos.mpr
  intro b hb c hc a r ha hr har
  have hbc := FSC.capMass_logConcave w b c a ha (by linarith)
  have hr' : 1 - a = r := by linarith
  rw [hr'] at hbc
  exact lt_of_lt_of_le
    (mul_pos (Real.rpow_pos_of_pos hb a) (Real.rpow_pos_of_pos hc r)) hbc

/-- The reciprocal is convex on the full positive-mass domain, extending the
upstream positive-coordinate domain without changing its imported statements. -/
theorem convexOn_inv_capMass_positive_mass (w : ι → FSC.Coord d) :
    ConvexOn ℝ {b : ι → ℝ | 0 < FSC.capMass w b}
      (fun b => (FSC.capMass w b)⁻¹) := by
  apply convexOn_iff_forall_pos.mpr
  refine ⟨convex_positive_mass_supports w, ?_⟩
  intro b hb c hc a r ha hr har
  have hbc := FSC.capMass_logConcave w b c a ha (by linarith)
  have hr' : 1 - a = r := by linarith
  rw [hr'] at hbc
  have hgeom := mul_pos (Real.rpow_pos_of_pos hb a) (Real.rpow_pos_of_pos hc r)
  have hinv := one_div_le_one_div_of_le hgeom hbc
  have ham := Real.geom_mean_le_arith_mean2_weighted ha.le hr.le
    (inv_pos.mpr hb).le (inv_pos.mpr hc).le har
  rw [Real.inv_rpow hb.le, Real.inv_rpow hc.le, ← mul_inv] at ham
  have hi : (FSC.capMass w (a • b + r • c))⁻¹ ≤
      (FSC.capMass w b ^ a * FSC.capMass w c ^ r)⁻¹ := by
    simpa only [one_div] using hinv
  exact hi.trans ham

/-- Tangent comparison on the actual positive-cap-probability domain. This
includes zero or negative thresholds whenever their caps have positive mass.
Its derivation follows the upstream convex reciprocal-mass proof, with the
larger domain justified above. No differentiability assumption remains. -/
theorem positive_mass_support_tangent
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b c : ι → ℝ)
    (hb : 0 < FSC.capMass w b) (hc : 0 < FSC.capMass w c)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k)) :
    (∑ j, WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j * (b j - c j)) ≤
      FSC.capMass w b ^ 2 / FSC.capMass w c - FSC.capMass w b := by
  let l := FSC.supportGradient w b
  have hcv := (convexOn_inv_capMass_positive_mass w).comp_affineMap
    (AffineMap.lineMap b c)
  have h0 : (0 : ℝ) ∈ (AffineMap.lineMap b c) ⁻¹'
      {s : ι → ℝ | 0 < FSC.capMass w s} := by simpa using hb
  have h1 : (1 : ℝ) ∈ (AffineMap.lineMap b c) ⁻¹'
      {s : ι → ℝ | 0 < FSC.capMass w s} := by simpa using hc
  have hf : HasFDerivAt (FSC.capMass w) l
      ((AffineMap.lineMap b c) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using
      FSC.hasFDerivAt_capMass w hw b hsep
  have hline := hf.comp_hasDerivAt 0
    (AffineMap.hasDerivAt_lineMap (a := b) (b := c))
  have hInv := hline.inv (by simpa using hb.ne')
  have hbound := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num : (0 : ℝ) < 1) hInv
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hbound
  have hl : l (c - b) = -l (b - c) := by simp only [map_sub]; ring
  rw [hl, neg_neg] at hbound
  have hmul := (div_le_iff₀ (sq_pos_of_pos hb)).mp hbound
  have hid : ((FSC.capMass w c)⁻¹ - (FSC.capMass w b)⁻¹) * FSC.capMass w b ^ 2 =
      FSC.capMass w b ^ 2 / FSC.capMass w c - FSC.capMass w b := by
    field_simp
  rw [hid] at hmul
  simpa [l, FSC.supportGradient, mul_comm, mul_left_comm, mul_assoc] using hmul

end NegativeVotingPolyhedral
