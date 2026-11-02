import PolyhedralSupportBoundary
import Mathlib.Probability.Moments.MGFAnalytic

/-!
Conditional covariance of an actual Gaussian polyhedron.
The support probability/log-concavity input is credited to Abhijeet Mulgund's
MIT-licensed FSC library; the Gaussian MGF calculus is mathlib's.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators ENNReal Topology

namespace NegativeVotingPolyhedral

theorem integrable_exp_inner {d : ℕ} (v : FSC.Coord d) (t : ℝ) :
    Integrable (fun x : FSC.Coord d => Real.exp (t * inner ℝ v x))
      (stdGaussian (FSC.Coord d)) := by
  have h : Integrable (fun s : ℝ => Real.exp (t * s))
      ((stdGaussian (FSC.Coord d)).map (innerSL ℝ v)) := by
    rw [FSC.map_inner_stdGaussian]
    exact integrable_exp_mul_gaussianReal t
  simpa [Function.comp_def] using h.comp_measurable (innerSL ℝ v).measurable

theorem integrable_exp_inner_restrict {d : ℕ} (v : FSC.Coord d) (t : ℝ)
    (s : Set (FSC.Coord d)) :
    Integrable (fun x : FSC.Coord d => Real.exp (t * inner ℝ v x))
      ((stdGaussian (FSC.Coord d)).restrict s) :=
  (integrable_exp_inner v t).restrict

/-- Finite-dimensional Gaussian change-of-density identity, pointwise. -/
theorem standardDensity_shift_tilt {d : ℕ} (v x : FSC.Coord d) (t : ℝ) :
    (FSC.standardDensity x).toReal * Real.exp (t * inner ℝ v x) =
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        (FSC.standardDensity (x - t • v)).toReal := by
  have hn : ‖x - t • v‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * t * inner ℝ v x + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm x v]
    ring
  have he : -‖x‖ ^ 2 / 2 + t * inner ℝ v x =
      t ^ 2 * ‖v‖ ^ 2 / 2 + -‖x - t • v‖ ^ 2 / 2 := by rw [hn]; ring
  rw [FSC.toReal_standardDensity, FSC.toReal_standardDensity]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2) *
        Real.exp (t * inner ℝ v x) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ d *
        Real.exp (-‖x‖ ^ 2 / 2 + t * inner ℝ v x) := by
          rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem translated_cap_membership (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v y : FSC.Coord d) (t : ℝ) :
    y + t • v ∈ FSC.cap w b ↔
      y ∈ FSC.cap w (fun j => b j - t * inner ℝ (w j) v) := by
  simp only [FSC.cap, Set.mem_setOf_eq, inner_add_right, real_inner_smul_right]
  exact forall_congr' fun j => le_sub_iff_add_le.symm

theorem cap_integral_density_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) :
    (∫ x in FSC.cap w b, (FSC.standardDensity (x - t • v)).toReal) =
      ∫ x in FSC.cap w (fun j => b j - t * inner ℝ (w j) v),
        (FSC.standardDensity x).toReal := by
  rw [← integral_indicator (FSC.measurableSet_cap w b),
    ← integral_indicator (FSC.measurableSet_cap w (fun j => b j - t * inner ℝ (w j) v))]
  calc
    (∫ x, (FSC.cap w b).indicator
        (fun x => (FSC.standardDensity (x - t • v)).toReal) x) =
      ∫ y, (FSC.cap w b).indicator
        (fun x => (FSC.standardDensity (x - t • v)).toReal) (y + t • v) :=
      (integral_add_right_eq_self _ (t • v)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y + t • v ∈ FSC.cap w b
      · have hy' := (translated_cap_membership w b v y t).mp hy
        simp [hy, hy']
      · have hy' := mt (translated_cap_membership w b v y t).mpr hy
        simp [hy, hy']

/-- The actual restricted-Gaussian MGF is a translated cap mass times the
ordinary Gaussian quadratic exponential. -/
theorem cap_mgf_translate (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) :
    mgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t =
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) *
        FSC.capMass w (fun j => b j - t * inner ℝ (w j) v) := by
  change (∫ x in FSC.cap w b, Real.exp (t * inner ℝ v x)
    ∂stdGaussian (FSC.Coord d)) = _
  rw [FSC.setIntegral_stdGaussian_eq]
  simp_rw [standardDensity_shift_tilt v]
  rw [integral_const_mul, cap_integral_density_translate,
    ← FSC.capMass_eq_integral_density]

theorem cap_restrict_ne_zero (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : 0 < FSC.capMass w b) :
    (stdGaussian (FSC.Coord d)).restrict (FSC.cap w b) ≠ 0 := by
  intro h
  have hz := Measure.restrict_eq_zero.mp h
  simpa [FSC.capMass, hz] using hb

theorem cap_shift_mass_pos (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : 0 < FSC.capMass w b) (v : FSC.Coord d) (t : ℝ) :
    0 < FSC.capMass w (fun j => b j - t * inner ℝ (w j) v) := by
  have hm := mgf_pos' (cap_restrict_ne_zero w b hb)
    (integrable_exp_inner_restrict v t (FSC.cap w b))
  rw [cap_mgf_translate] at hm
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hm

theorem cap_integrableExpSet (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) :
    integrableExpSet (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact integrable_exp_inner_restrict v t (FSC.cap w b)

theorem cap_cgf_analytic (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) :
    AnalyticAt ℝ
      (cgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) t := by
  apply analyticAt_cgf
  rw [cap_integrableExpSet, interior_univ]
  exact Set.mem_univ t

theorem cap_score_moment_integrable (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (k : ℕ) :
    Integrable (fun x : FSC.Coord d => (inner ℝ v x) ^ k)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ 0
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hz k

theorem cap_centered_square_integrable (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (c : ℝ) :
    Integrable (fun x : FSC.Coord d => (inner ℝ v x - c) ^ 2)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
  have h1 : Integrable (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
    simpa using cap_score_moment_integrable w b v 1
  have h := ((cap_score_moment_integrable w b v 2).sub
    (h1.const_mul (2 * c))).add (integrable_const (c ^ 2))
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Every translated cap has positive mass, and its log mass is concave as
a function of translation distance. No boundary regularity is presumed. -/
theorem cap_log_translate_concave (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : 0 < FSC.capMass w b) (v : FSC.Coord d) :
    ConcaveOn ℝ Set.univ
      (fun t : ℝ => Real.log (FSC.capMass w (fun j => b j - t * inner ℝ (w j) v))) := by
  apply concaveOn_iff_forall_pos.mpr
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a r ha hr har
  have hs := cap_shift_mass_pos w b hb v s
  have ht := cap_shift_mass_pos w b hb v t
  have hbc := FSC.capMass_logConcave w
    (fun j => b j - s * inner ℝ (w j) v)
    (fun j => b j - t * inner ℝ (w j) v) a ha (by linarith)
  have hr' : 1 - a = r := by linarith
  rw [hr'] at hbc
  have heq : a • (fun j => b j - s * inner ℝ (w j) v) +
      r • (fun j => b j - t * inner ℝ (w j) v) =
      (fun j => b j - (a * s + r * t) * inner ℝ (w j) v) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ = (a + r) * b j - (a * s + r * t) * inner ℝ (w j) v := by ring
      _ = _ := by rw [har, one_mul]
  rw [heq] at hbc
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hs a) (Real.rpow_pos_of_pos ht r)) hbc
  rw [Real.log_mul (Real.rpow_pos_of_pos hs a).ne'
      (Real.rpow_pos_of_pos ht r).ne', Real.log_rpow hs a, Real.log_rpow ht r] at hlog
  simpa only [smul_eq_mul] using hlog

/-- Removing the standard Gaussian quadratic term from the actual cap CGF
leaves a concave function. -/
theorem cap_cgf_sub_quadratic_concave (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : 0 < FSC.capMass w b) (v : FSC.Coord d) :
    ConcaveOn ℝ Set.univ (fun t : ℝ =>
      cgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t -
      t ^ 2 * ‖v‖ ^ 2 / 2) := by
  have heq : (fun t : ℝ =>
      cgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) t -
      t ^ 2 * ‖v‖ ^ 2 / 2) =
      (fun t => Real.log (FSC.capMass w (fun j => b j - t * inner ℝ (w j) v))) := by
    funext t
    rw [cgf, cap_mgf_translate, Real.log_mul (Real.exp_ne_zero _)
      (cap_shift_mass_pos w b hb v t).ne', Real.log_exp]
    ring
  rw [heq]
  exact cap_log_translate_concave w b hb v

theorem cap_cgf_second_derivative_le (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hb : 0 < FSC.capMass w b) (v : FSC.Coord d) :
    iteratedDeriv 2
      (cgf (fun x : FSC.Coord d => inner ℝ v x)
        ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) 0 ≤ ‖v‖ ^ 2 := by
  let M := cgf (fun x : FSC.Coord d => inner ℝ v x)
    ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))
  have hm (t : ℝ) : DifferentiableAt ℝ M t :=
    (cap_cgf_analytic w b v t).differentiableAt
  have hq (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 * ‖v‖ ^ 2 / 2)
      (t * ‖v‖ ^ 2) t := by
    convert (((hasDerivAt_id t).pow 2).mul_const (‖v‖ ^ 2)).div_const 2 using 1
    · funext s
      simp only [Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hconc : ConcaveOn ℝ Set.univ (fun t : ℝ => M t - t ^ 2 * ‖v‖ ^ 2 / 2) :=
    cap_cgf_sub_quadratic_concave w b hb v
  have hanti : Antitone (deriv (fun t : ℝ => M t - t ^ 2 * ‖v‖ ^ 2 / 2)) := by
    intro s t hst
    exact hconc.antitoneOn_deriv
      (fun u _ => (hm u).sub (hq u).differentiableAt) (mem_univ s) (mem_univ t) hst
  have hdf : deriv (fun t : ℝ => M t - t ^ 2 * ‖v‖ ^ 2 / 2) =
      (fun t => deriv M t - t * ‖v‖ ^ 2) := by
    funext t
    simpa only [Pi.sub_def] using ((hm t).hasDerivAt.sub (hq t)).deriv
  rw [hdf] at hanti
  have hle := hanti.deriv_nonpos (x := (0 : ℝ))
  have hdm : DifferentiableAt ℝ (deriv M) 0 :=
    (cap_cgf_analytic w b v 0).deriv.differentiableAt
  have hlin := (hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)
  have hdiff : deriv (fun t => deriv M t - t * ‖v‖ ^ 2) 0 =
      deriv (deriv M) 0 - ‖v‖ ^ 2 := by
    simpa only [Pi.sub_def, id_eq, one_mul] using (hdm.hasDerivAt.sub hlin).deriv
  rw [hdiff] at hle
  change iteratedDeriv 2 M 0 ≤ _
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  linarith

/-- Every directional conditional variance of a positive-mass Gaussian cap
is bounded by the unconditioned variance. All moments and differentiability
are derived above. The normals may be arbitrary, even redundant or zero. -/
theorem gaussian_cap_conditional_variance_le
    (w : ι → FSC.Coord d) (b : ι → ℝ) (hb : 0 < FSC.capMass w b)
    (v : FSC.Coord d) :
    (∫ x in FSC.cap w b,
      (inner ℝ v x -
        (∫ y in FSC.cap w b, inner ℝ v y ∂stdGaussian (FSC.Coord d)) /
          FSC.capMass w b) ^ 2 ∂stdGaussian (FSC.Coord d)) /
      FSC.capMass w b ≤ ‖v‖ ^ 2 := by
  have h := cap_cgf_second_derivative_le w b hb v
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ 0
  rw [iteratedDeriv_two_cgf_eq_integral hz, deriv_cgf_zero hz] at h
  simpa [mgf, FSC.capMass, measureReal_def] using h

/-- Equivalent uncentered second-moment form, useful for tensor estimates. -/
theorem gaussian_cap_conditional_second_moment_le
    (w : ι → FSC.Coord d) (b : ι → ℝ) (hb : 0 < FSC.capMass w b)
    (v : FSC.Coord d) :
    (∫ x in FSC.cap w b, (inner ℝ v x) ^ 2 ∂stdGaussian (FSC.Coord d)) /
      FSC.capMass w b ≤ ‖v‖ ^ 2 +
        ((∫ x in FSC.cap w b, inner ℝ v x ∂stdGaussian (FSC.Coord d)) /
          FSC.capMass w b) ^ 2 := by
  have h := cap_cgf_second_derivative_le w b hb v
  have hz : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : FSC.Coord d => inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet, interior_univ]
    exact mem_univ 0
  rw [iteratedDeriv_two_cgf hz, deriv_cgf_zero hz] at h
  simp only [mgf, zero_mul, Real.exp_zero, mul_one, integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ] at h
  change _ / FSC.capMass w b - (_ / FSC.capMass w b) ^ 2 ≤ _ at h
  linarith

end NegativeVotingPolyhedral
