import GaussianCapFirstMoment
import GaussianCapMixedMGF

/-!
Actual second-moment Gaussian boundary identity, via fixed-face exponential
tilts. The Gaussian support calculus is credited to Abhijeet Mulgund's FSC
library; the preceding concrete Gaussian identities and mathlib MGF calculus
provide the moment and differentiation inputs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators ENNReal Topology

namespace NegativeVotingPolyhedral

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem noCoincident_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : FSC.NoCoincident w b) (v : FSC.Coord d) (t : ℝ) :
    FSC.NoCoincident w (fun j => b j - t * inner ℝ (w j) v) := by
  intro j k hjk
  constructor
  · intro h heq
    have hi : inner ℝ (w j) v = inner ℝ (w k) v := by rw [h]
    exact (hb j k hjk).1 h (by dsimp at heq; rw [hi] at heq; linarith)
  · intro h heq
    have hi : inner ℝ (w j) v = -inner ℝ (w k) v := by rw [h, inner_neg_left]
    exact (hb j k hjk).2 h (by dsimp at heq; rw [hi] at heq; linarith)

theorem cap_integral_density_test_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) (F : FSC.Coord d → ℝ) :
    (∫ x in FSC.cap w b, (FSC.standardDensity (x - t • v)).toReal * F x) =
      ∫ x in FSC.cap w (fun j => b j - t * inner ℝ (w j) v),
        (FSC.standardDensity x).toReal * F (x + t • v) := by
  rw [← integral_indicator (FSC.measurableSet_cap w b),
    ← integral_indicator (FSC.measurableSet_cap w (fun j => b j - t * inner ℝ (w j) v))]
  calc
    (∫ x, (FSC.cap w b).indicator
        (fun x => (FSC.standardDensity (x - t • v)).toReal * F x) x) =
      ∫ y, (FSC.cap w b).indicator
        (fun x => (FSC.standardDensity (x - t • v)).toReal * F x) (y + t • v) :=
      (integral_add_right_eq_self _ (t • v)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y + t • v ∈ FSC.cap w b
      · have hy' := (translated_cap_membership w b v y t).mp hy
        simp [hy, hy']
      · have hy' := mt (translated_cap_membership w b v y t).mpr hy
        simp [hy, hy']

/-- Exponential tilting transports an actual test-function integral to the
translated cap. This is an identity of total Bochner integrals. -/
theorem cap_tilt_test_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) (F : FSC.Coord d → ℝ) :
    (∫ x in FSC.cap w b, F x * Real.exp (t * inner ℝ v x)
      ∂stdGaussian (FSC.Coord d)) =
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        ∫ x in FSC.cap w (fun j => b j - t * inner ℝ (w j) v),
          F (x + t • v) ∂stdGaussian (FSC.Coord d) := by
  rw [FSC.setIntegral_stdGaussian_eq, FSC.setIntegral_stdGaussian_eq]
  calc
    (∫ x in FSC.cap w b,
        (FSC.standardDensity x).toReal * (F x * Real.exp (t * inner ℝ v x))) =
      ∫ x in FSC.cap w b, Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        ((FSC.standardDensity (x - t • v)).toReal * F x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        _ = ((FSC.standardDensity x).toReal * Real.exp (t * inner ℝ v x)) * F x := by ring
        _ = _ := by rw [standardDensity_shift_tilt v]; ring
    _ = _ := by rw [integral_const_mul, cap_integral_density_test_translate]

def faceEvent (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) : Set (FSC.Coord d) :=
  {x | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k}

def faceResidualNormals (w : ι → FSC.Coord d) (j : ι)
    (k : {k : ι // k ≠ j}) : FSC.Coord d :=
  w k.1 - inner ℝ (w k.1) (w j) • w j

def faceResidualSupports (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (k : {k : ι // k ≠ j}) : ℝ :=
  b k.1 - b j * inner ℝ (w k.1) (w j)

def faceDirection (w : ι → FSC.Coord d) (j : ι) (v : FSC.Coord d) : FSC.Coord d :=
  v - inner ℝ (w j) v • w j

def faceMGF (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (v : FSC.Coord d) (t : ℝ) : ℝ :=
  mgf (fun x : FSC.Coord d => inner ℝ v x)
    ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) t

theorem measurableSet_faceEvent (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    MeasurableSet (faceEvent w b j) := by
  simp only [faceEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (by fun_prop) measurable_const

theorem face_affine_inner (w : ι → FSC.Coord d) (b : ι → ℝ) (j k : ι)
    (y : FSC.Coord d) :
    inner ℝ (w k) (b j • w j + FSC.normalResidual (w j) y) =
      b j * inner ℝ (w k) (w j) +
        inner ℝ (w k - inner ℝ (w k) (w j) • w j) y := by
  simp only [FSC.normalResidual_apply, inner_add_right, inner_sub_right,
    real_inner_smul_right, inner_sub_left, real_inner_smul_left]
  ring

theorem slicePreimage_eq_residual_cap (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    FSC.slicePreimage w b j =
      FSC.cap (faceResidualNormals w j) (faceResidualSupports w b j) := by
  ext y
  simp only [FSC.slicePreimage, FSC.cap, faceResidualNormals, faceResidualSupports,
    Set.mem_setOf_eq, Subtype.forall, face_affine_inner]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  constructor <;> intro h <;> linarith

theorem sliceMass_eq_residual_capMass (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    FSC.sliceMass w b j =
      FSC.capMass (faceResidualNormals w j) (faceResidualSupports w b j) := by
  rw [FSC.sliceMass_eq_stdGaussian, slicePreimage_eq_residual_cap]
  rfl

theorem sliceLaw_isGaussian (w : FSC.Coord d) (z : ℝ) :
    IsGaussian (FSC.sliceLaw w z) := by
  rw [FSC.sliceLaw_eq_map_normalResidual]
  infer_instance

theorem face_integrableExpSet (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (v : FSC.Coord d) :
    integrableExpSet (fun x : FSC.Coord d => inner ℝ v x)
      ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) = Set.univ := by
  letI := sliceLaw_isGaussian (w j) (b j)
  apply Set.eq_univ_of_forall
  intro t
  have h : Integrable (fun s : ℝ => Real.exp (t * s))
      ((FSC.sliceLaw (w j) (b j)).map (innerSL ℝ v)) := by
    rw [IsGaussian.map_eq_gaussianReal]
    exact integrable_exp_mul_gaussianReal t
  have hi : Integrable (fun x : FSC.Coord d => Real.exp (t * inner ℝ v x))
      (FSC.sliceLaw (w j) (b j)) := by
    simpa [Function.comp_def] using h.comp_measurable (innerSL ℝ v).measurable
  exact hi.restrict

theorem hasDerivAt_faceMGF_zero (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (v : FSC.Coord d) :
    HasDerivAt (faceMGF w b j v)
      (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j)) 0 := by
  unfold faceMGF
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j))) := by
    rw [face_integrableExpSet, interior_univ]
    exact mem_univ 0
  simpa only [zero_mul, Real.exp_zero, mul_one] using hasDerivAt_mgf hz

theorem face_affine_test_inner (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (v y : FSC.Coord d) :
    inner ℝ v (b j • w j + FSC.normalResidual (w j) y) =
      b j * inner ℝ (w j) v + inner ℝ (faceDirection w j v) y := by
  simp only [faceDirection, FSC.normalResidual_apply, inner_add_right, inner_sub_right,
    real_inner_smul_right, inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm v (w j)]
  ring

theorem faceMGF_eq_residual_mgf (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι)
    (v : FSC.Coord d) (t : ℝ) :
    faceMGF w b j v t = Real.exp (t * (b j * inner ℝ (w j) v)) *
      mgf (fun y : FSC.Coord d => inner ℝ (faceDirection w j v) y)
        ((stdGaussian (FSC.Coord d)).restrict
          (FSC.cap (faceResidualNormals w j) (faceResidualSupports w b j))) t := by
  unfold faceMGF mgf
  rw [FSC.sliceLaw, setIntegral_map (measurableSet_faceEvent w b j) (by fun_prop) (by fun_prop)]
  change (∫ y in FSC.slicePreimage w b j,
    Real.exp (t * inner ℝ v (b j • w j + FSC.normalResidual (w j) y))
      ∂stdGaussian (FSC.Coord d)) = _
  rw [slicePreimage_eq_residual_cap]
  simp_rw [face_affine_test_inner, mul_add, Real.exp_add]
  rw [integral_const_mul]

theorem faceDirection_norm_sq (w : ι → FSC.Coord d) (j : ι) (hw : ‖w j‖ = 1)
    (v : FSC.Coord d) :
    ‖faceDirection w j v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ (w j) v) ^ 2 := by
  rw [faceDirection, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, hw, one_pow, mul_one,
    real_inner_comm v (w j)]
  ring

theorem faceResidual_inner_direction (w : ι → FSC.Coord d) (j : ι) (hw : ‖w j‖ = 1)
    (v : FSC.Coord d) (k : {k : ι // k ≠ j}) :
    inner ℝ (faceResidualNormals w j k) (faceDirection w j v) =
      inner ℝ (w k.1) v - inner ℝ (w k.1) (w j) * inner ℝ (w j) v := by
  simp only [faceResidualNormals, faceDirection, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, hw]
  ring

theorem faceResidualSupports_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (j : ι) (hw : ‖w j‖ = 1) (v : FSC.Coord d) (t : ℝ) :
    faceResidualSupports w (fun k => b k - t * inner ℝ (w k) v) j =
      (fun k => faceResidualSupports w b j k -
        t * inner ℝ (faceResidualNormals w j k) (faceDirection w j v)) := by
  funext k
  rw [faceResidual_inner_direction w j hw]
  simp only [faceResidualSupports]
  ring

theorem faceMGF_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (j : ι) (hw : ‖w j‖ = 1) (v : FSC.Coord d) (t : ℝ) :
    faceMGF w b j v t =
      Real.exp (t * (b j * inner ℝ (w j) v) +
        t ^ 2 * (‖v‖ ^ 2 - (inner ℝ (w j) v) ^ 2) / 2) *
      FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j := by
  rw [faceMGF_eq_residual_mgf, cap_mgf_translate,
    ← faceResidualSupports_translate w b j hw,
    ← sliceMass_eq_residual_capMass, faceDirection_norm_sq w j hw, Real.exp_add]
  ring

theorem normalPDF_shift_tilt (b a t s : ℝ) :
    WeakSimplex.normalPDF (b - t * a) * Real.exp (t ^ 2 * s / 2) =
      WeakSimplex.normalPDF b * Real.exp (t * (b * a) + t ^ 2 * (s - a ^ 2) / 2) := by
  have hpdf (z : ℝ) : WeakSimplex.normalPDF z =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) := by
    norm_num [WeakSimplex.normalPDF, gaussianPDFReal]
  rw [hpdf, hpdf]
  have he : -(b - t * a) ^ 2 / 2 + t ^ 2 * s / 2 =
      -b ^ 2 / 2 + (t * (b * a) + t ^ 2 * (s - a ^ 2) / 2) := by ring
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(b - t * a) ^ 2 / 2) *
        Real.exp (t ^ 2 * s / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(b - t * a) ^ 2 / 2 + t ^ 2 * s / 2) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

/-- The shifted face coefficient is exactly the exponential tilt of the
original fixed Gaussian face. There is no moving-boundary derivative premise. -/
theorem face_flux_tilt (w : ι → FSC.Coord d) (b : ι → ℝ)
    (j : ι) (hw : ‖w j‖ = 1) (v : FSC.Coord d) (t : ℝ) :
    Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        WeakSimplex.normalPDF (b j - t * inner ℝ (w j) v) *
        FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j =
      WeakSimplex.normalPDF (b j) * faceMGF w b j v t := by
  rw [faceMGF_translate w b j hw]
  calc
    _ = (WeakSimplex.normalPDF (b j - t * inner ℝ (w j) v) *
        Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2)) *
        FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j := by ring
    _ = _ := by rw [normalPDF_shift_tilt]; ring

theorem cap_tilt_first_moment_translate
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) (t : ℝ) :
    (∫ x in FSC.cap w b, inner ℝ u x * Real.exp (t * inner ℝ v x)
      ∂stdGaussian (FSC.Coord d)) =
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        (t * inner ℝ u v * FSC.capMass w (fun k => b k - t * inner ℝ (w k) v) -
          ∑ j, WeakSimplex.normalPDF (b j - t * inner ℝ (w j) v) *
            FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j * inner ℝ (w j) u) := by
  rw [cap_tilt_test_translate]
  apply congrArg (fun z : ℝ => Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) * z)
  let bs : ι → ℝ := fun k => b k - t * inner ℝ (w k) v
  have hi : Integrable (fun x : FSC.Coord d => inner ℝ u x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w bs)) := by
    simpa using cap_score_moment_integrable w bs u 1
  change (∫ x in FSC.cap w bs, inner ℝ u (x + t • v)
    ∂stdGaussian (FSC.Coord d)) = _
  simp_rw [inner_add_right, real_inner_smul_right]
  rw [integral_add hi (integrable_const _),
    gaussian_cap_first_moment w hw bs (noCoincident_translate w b hb v t) u,
    integral_const]
  simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  change (-(∑ j, WeakSimplex.normalPDF (bs j) * FSC.sliceMass w bs j * inner ℝ (w j) u)) +
    FSC.capMass w bs * (t * inner ℝ u v) = _
  ring

/-- Exact first-moment integration by parts under every exponential tilt,
with all Gaussian face measures fixed at their original supports. -/
theorem cap_tilt_first_moment_boundary
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) (t : ℝ) :
    (∫ x in FSC.cap w b, inner ℝ u x * Real.exp (t * inner ℝ v x)
      ∂stdGaussian (FSC.Coord d)) =
      t * inner ℝ u v * mgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t -
      ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) * faceMGF w b j v t := by
  rw [cap_tilt_first_moment_translate w hw b hb, cap_mgf_translate, mul_sub,
    Finset.mul_sum]
  have hj (j : ι) :
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        (WeakSimplex.normalPDF (b j - t * inner ℝ (w j) v) *
          FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j * inner ℝ (w j) u) =
      (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) * faceMGF w b j v t := by
    calc
      _ = (Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
          WeakSimplex.normalPDF (b j - t * inner ℝ (w j) v) *
          FSC.sliceMass w (fun k => b k - t * inner ℝ (w k) v) j) * inner ℝ (w j) u := by ring
      _ = _ := by rw [face_flux_tilt w b j (hw j)]; ring
  simp_rw [hj]
  ring

theorem hasDerivAt_cap_tilt_first_moment_boundary
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) :
    HasDerivAt (fun t : ℝ =>
      ∫ x in FSC.cap w b, inner ℝ u x * Real.exp (t * inner ℝ v x)
        ∂stdGaussian (FSC.Coord d))
      (FSC.capMass w b * inner ℝ u v -
        ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) *
          (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j))) 0 := by
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ 0
  have hfirst : HasDerivAt (fun t : ℝ => t * inner ℝ u v *
      mgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t)
      (FSC.capMass w b * inner ℝ u v) 0 := by
    simpa [Pi.mul_def, id_eq, mgf, FSC.capMass, measureReal_def, mul_comm] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ u v)).mul (hasDerivAt_mgf hz)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) * faceMGF w b j v t)
      (∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) *
        (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j))) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact (hasDerivAt_faceMGF_zero w b j v).const_mul _
  have heq : (fun t : ℝ =>
      ∫ x in FSC.cap w b, inner ℝ u x * Real.exp (t * inner ℝ v x)
        ∂stdGaussian (FSC.Coord d)) =
      (fun t : ℝ => t * inner ℝ u v *
        mgf (fun x : FSC.Coord d => inner ℝ v x)
          ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t -
        ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) * faceMGF w b j v t) := by
    funext t
    exact cap_tilt_first_moment_boundary w hw b hb u v t
  rw [heq]
  simpa only [Pi.sub_def] using hfirst.sub hsum

/-- Actual bilinear Gaussian second-moment / boundary identity. All slice
moments and parameter derivatives come from the concrete Gaussian laws above. -/
theorem gaussian_cap_bilinear_second_moment
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (u v : FSC.Coord d) :
    (∫ x in FSC.cap w b, inner ℝ u x * inner ℝ v x
      ∂stdGaussian (FSC.Coord d)) =
      FSC.capMass w b * inner ℝ u v -
        ∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) *
          (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j)) :=
  (hasDerivAt_cap_mixed_mgf w b u v).unique
    (hasDerivAt_cap_tilt_first_moment_boundary w hw b hsep u v)

theorem gaussian_cap_coordinate_second_moment
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (a c : Fin d) :
    (∫ x in FSC.cap w b, x a * x c ∂stdGaussian (FSC.Coord d)) =
      FSC.capMass w b * (if a = c then 1 else 0) -
        ∑ j, (WeakSimplex.normalPDF (b j) * w j a) *
          (∫ x in faceEvent w b j, x c ∂FSC.sliceLaw (w j) (b j)) := by
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    EuclideanSpace.single_apply, eq_comm] using
    gaussian_cap_bilinear_second_moment w hw b hsep
      (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single c (1 : ℝ))

/-- The actual boundary tensor is symmetric, as forced by the symmetric
Gaussian second moment; no symmetry of separate faces is assumed. -/
theorem gaussian_cap_boundary_tensor_symmetric
    (w : ι → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ)
    (hsep : ∀ j k, j ≠ k →
      (w j = w k → b j ≠ b k) ∧ (w j = -w k → b j ≠ -b k))
    (u v : FSC.Coord d) :
    (∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) u) *
      (∫ x in faceEvent w b j, inner ℝ v x ∂FSC.sliceLaw (w j) (b j))) =
    (∑ j, (WeakSimplex.normalPDF (b j) * inner ℝ (w j) v) *
      (∫ x in faceEvent w b j, inner ℝ u x ∂FSC.sliceLaw (w j) (b j))) := by
  have huv := gaussian_cap_bilinear_second_moment w hw b hsep u v
  have hvu := gaussian_cap_bilinear_second_moment w hw b hsep v u
  have hi : (∫ x in FSC.cap w b, inner ℝ u x * inner ℝ v x
      ∂stdGaussian (FSC.Coord d)) =
      ∫ x in FSC.cap w b, inner ℝ v x * inner ℝ u x ∂stdGaussian (FSC.Coord d) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hc : inner ℝ v u = inner ℝ u v := real_inner_comm _ _
  rw [hc] at hvu
  linarith

end NegativeVotingPolyhedral
