import GaussianEhrhardCurvature

/-! Actual Gaussian first and second moments from translated-polyhedron Ehrhard
concavity. All exponential integrability and differentiation inputs are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology RealInnerProductSpace
open OAI.GaussianPropeller.Quantile OAI.GaussianPropeller.Translation

namespace NegativeVotingEhrhard
variable {ι J : Type*} [Fintype ι] [Fintype J]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

def polyhedronMoment (w : J → E) (b : J → ℝ) (v : E) (n : ℕ) : ℝ :=
  ∫ x in closedPolyhedron w b, (inner ℝ v x) ^ n ∂γ

def polyhedronMass (w : J → E) (b : J → ℝ) : ℝ :=
  (γ (closedPolyhedron w b)).toReal

theorem polyhedron_integrableExpSet (w : J → E) (b : J → ℝ) (v : E) :
    integrableExpSet (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b)) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact (integrable_exp_inner v t).restrict

theorem polyhedron_moment_integrable (w : J → E) (b : J → ℝ) (v : E) (n : ℕ) :
    Integrable (fun x => (inner ℝ v x) ^ n) ((γ).restrict (closedPolyhedron w b)) := by
  have h0 : (0 : ℝ) ∈ interior
      (integrableExpSet (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) := by
    rw [polyhedron_integrableExpSet, interior_univ]
    trivial
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet h0 n

theorem translatedPolyhedronMass_zero (w : J → E) (b : J → ℝ) :
    translatedPolyhedronMass w b 0 = polyhedronMass w b := by
  simp [translatedPolyhedronMass, integral_indicator (measurableSet_closedPolyhedron w b),
    polyhedronMass, measureReal_def]

theorem translatedPolyhedronMass_mgf (w : J → E) (b : J → ℝ) (v : E) (t : ℝ) :
    translatedPolyhedronMass w b (t • v) =
      Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) *
        mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b)) t := by
  rw [translatedPolyhedronMass_eq_map]
  have ht := translated_integral (-(t • v)) (closedPolyhedron w b)
    (measurableSet_closedPolyhedron w b)
  simp only [sub_neg_eq_add, measureReal_def] at ht
  rw [ht]
  unfold mgf
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← Real.exp_add]
  congr 1
  simp only [inner_neg_left, inner_smul_left, norm_neg, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, starRingEnd_apply, star_trivial]
  ring

def polyhedronTiltDerivative (w : J → E) (b : J → ℝ) (v : E) (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) *
    (deriv (mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) t -
      t * ‖v‖ ^ 2 * mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b)) t)

theorem hasDerivAt_gaussian_tilt_prefactor (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 * ‖v‖ ^ 2 / 2))
      (Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) * (-t * ‖v‖ ^ 2)) t := by
  convert (((hasDerivAt_pow 2 t).neg.mul_const (‖v‖ ^ 2)).div_const 2).exp using 1 <;>
    norm_num <;> ring

theorem hasDerivAt_translatedPolyhedronMass_line
    (w : J → E) (b : J → ℝ) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translatedPolyhedronMass w b (s • v))
      (polyhedronTiltDerivative w b v t) t := by
  have ht : t ∈ interior
      (integrableExpSet (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) := by
    rw [polyhedron_integrableExpSet, interior_univ]
    trivial
  have hprod := (hasDerivAt_gaussian_tilt_prefactor v t).mul
    (differentiableAt_mgf ht).hasDerivAt
  have he : Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) * (-t * ‖v‖ ^ 2) *
        mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b)) t +
      Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) *
        deriv (mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) t =
      polyhedronTiltDerivative w b v t := by
    unfold polyhedronTiltDerivative
    ring
  exact (hprod.congr_deriv he).congr_of_eventuallyEq
    (Eventually.of_forall (translatedPolyhedronMass_mgf w b v))

theorem polyhedronTiltDerivative_zero (w : J → E) (b : J → ℝ) (v : E) :
    polyhedronTiltDerivative w b v 0 = polyhedronMoment w b v 1 := by
  have h0 : (0 : ℝ) ∈ interior
      (integrableExpSet (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) := by
    rw [polyhedron_integrableExpSet, interior_univ]
    trivial
  simp [polyhedronTiltDerivative, deriv_mgf_zero h0, polyhedronMoment]

theorem hasDerivAt_polyhedronTiltDerivative_zero (w : J → E) (b : J → ℝ) (v : E) :
    HasDerivAt (polyhedronTiltDerivative w b v)
      (polyhedronMoment w b v 2 - polyhedronMass w b * ‖v‖ ^ 2) 0 := by
  let M := mgf (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))
  have h0 : (0 : ℝ) ∈ interior
      (integrableExpSet (fun x => inner ℝ v x) ((γ).restrict (closedPolyhedron w b))) := by
    rw [polyhedron_integrableExpSet, interior_univ]
    trivial
  have hm : HasDerivAt M (polyhedronMoment w b v 1) 0 := by
    simpa [M, polyhedronMoment] using hasDerivAt_mgf h0
  have hdm : HasDerivAt (deriv M) (polyhedronMoment w b v 2) 0 := by
    simpa [M, polyhedronMoment, iteratedDeriv_one] using hasDerivAt_iteratedDeriv_mgf h0 1
  have hm0 : M 0 = polyhedronMass w b := by
    simp [M, mgf, polyhedronMass, measureReal_def]
  have hlin := ((hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)).mul hm
  have hinner := hdm.sub hlin
  have he := (hasDerivAt_gaussian_tilt_prefactor v (0 : ℝ)).mul hinner
  convert he using 1
  · rfl
  · simp only [id_eq, zero_mul, mul_zero, zero_add, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      neg_zero, zero_div, Real.exp_zero, one_mul, hm0]
    ring

/-- Ehrhard curvature becomes an actual first/second Gaussian moment inequality.
No differentiability or moment premise remains in this concrete endpoint. -/
theorem gaussian_polyhedron_ehrhard_moment_bound (w : J → E) (b : J → ℝ)
    (hp : polyhedronMass w b ∈ Ioo (0 : ℝ) 1) (v : E) :
    φ (q (polyhedronMass w b)) *
        (polyhedronMoment w b v 2 - polyhedronMass w b * ‖v‖ ^ 2) +
      q (polyhedronMass w b) * (polyhedronMoment w b v 1) ^ 2 ≤ 0 := by
  have hconc : ConcaveOn ℝ univ
      (fun t : ℝ => q (translatedPolyhedronMass w b (t • v))) := by
    refine ⟨convex_univ, ?_⟩
    intro t _ s _ a c ha hc hac
    have he := (gaussian_polyhedron_ehrhard_concave w b hp).2
      (mem_univ (t • v)) (mem_univ (s • v)) ha hc hac
    simpa only [smul_smul, smul_eq_mul, add_smul] using he
  have hh := ehrhard_curve_curvature
    (fun t : ℝ => translatedPolyhedronMass w b (t • v)) (polyhedronTiltDerivative w b v)
    (polyhedronMoment w b v 2 - polyhedronMass w b * ‖v‖ ^ 2)
    (fun t => translatedPolyhedronMass_mem w b hp (t • v))
    (hasDerivAt_translatedPolyhedronMass_line w b v)
    (hasDerivAt_polyhedronTiltDerivative_zero w b v) hconc
  simpa only [zero_smul, translatedPolyhedronMass_zero, polyhedronTiltDerivative_zero] using hh

theorem gaussian_polyhedron_ehrhard_second_moment_le (w : J → E) (b : J → ℝ)
    (hp : polyhedronMass w b ∈ Ioo (0 : ℝ) 1) (v : E) :
    polyhedronMoment w b v 2 ≤ polyhedronMass w b * ‖v‖ ^ 2 -
      q (polyhedronMass w b) / φ (q (polyhedronMass w b)) * (polyhedronMoment w b v 1) ^ 2 := by
  have hb := gaussian_polyhedron_ehrhard_moment_bound w b hp v
  have hφ := φ_pos (q (polyhedronMass w b))
  have hh : polyhedronMoment w b v 2 ≤
      (φ (q (polyhedronMass w b)) * (polyhedronMass w b * ‖v‖ ^ 2) -
        q (polyhedronMass w b) * (polyhedronMoment w b v 1) ^ 2) /
        φ (q (polyhedronMass w b)) := by
    apply (le_div_iff₀ hφ).mpr
    nlinarith
  convert hh using 1 <;> field_simp [hφ.ne'] <;> ring

def polyhedronConditionalVariance (w : J → E) (b : J → ℝ) (v : E) : ℝ :=
  (∫ x in closedPolyhedron w b,
    (inner ℝ v x - polyhedronMoment w b v 1 / polyhedronMass w b) ^ 2 ∂γ) /
    polyhedronMass w b

theorem polyhedronConditionalVariance_expansion (w : J → E) (b : J → ℝ)
    (hp : 0 < polyhedronMass w b) (v : E) :
    polyhedronConditionalVariance w b v = polyhedronMoment w b v 2 / polyhedronMass w b -
      (polyhedronMoment w b v 1) ^ 2 / (polyhedronMass w b) ^ 2 := by
  let μ := (γ).restrict (closedPolyhedron w b)
  let p := polyhedronMass w b
  let A := polyhedronMoment w b v 1
  have h1 : Integrable (fun x : E => inner ℝ v x) μ := by
    simpa using polyhedron_moment_integrable w b v 1
  have h2 : Integrable (fun x : E => (inner ℝ v x) ^ 2) μ :=
    polyhedron_moment_integrable w b v 2
  have hm : μ.real univ = p := by simp [μ, p, polyhedronMass, measureReal_def]
  have he (x : E) : (inner ℝ v x - A / p)^2 =
      ((inner ℝ v x)^2 - (2*A/p)*inner ℝ v x) + (A/p)^2 := by ring
  change (∫ x, (inner ℝ v x - A/p)^2 ∂μ) / p =
    (∫ x, (inner ℝ v x)^2 ∂μ) / p - A^2/p^2
  simp_rw [he]
  have hsub : Integrable (fun x : E => (inner ℝ v x)^2 - (2*A/p)*inner ℝ v x) μ := by
    simpa only [Pi.sub_def] using h2.sub (h1.const_mul (2*A/p))
  rw [integral_add hsub (integrable_const _), integral_sub h2 (h1.const_mul (2*A/p)),
    integral_const_mul, integral_const, hm]
  have hA : (∫ x, inner ℝ v x ∂μ) = A := by simp [A, μ, polyhedronMoment]
  rw [hA]
  change ((∫ x, (inner ℝ v x)^2 ∂μ) - (2*A/p)*A + p*(A/p)^2)/p = _
  have hp' : p ≠ 0 := hp.ne'
  field_simp
  ring

/-- The actual conditional variance has the Ehrhard rank-one mean correction.
No boundary regularity, unit-normal, noncoincidence or covariance premise is used. -/
theorem gaussian_polyhedron_ehrhard_conditional_variance_le (w : J → E) (b : J → ℝ)
    (hp : polyhedronMass w b ∈ Ioo (0 : ℝ) 1) (v : E) :
    polyhedronConditionalVariance w b v ≤ ‖v‖ ^ 2 -
      (1 + polyhedronMass w b * q (polyhedronMass w b) / φ (q (polyhedronMass w b))) *
        (polyhedronMoment w b v 1 / polyhedronMass w b) ^ 2 := by
  rw [polyhedronConditionalVariance_expansion w b hp.1]
  calc
    _ ≤ (polyhedronMass w b * ‖v‖ ^ 2 -
        q (polyhedronMass w b) / φ (q (polyhedronMass w b)) * (polyhedronMoment w b v 1)^2) /
          polyhedronMass w b - (polyhedronMoment w b v 1)^2 / (polyhedronMass w b)^2 :=
      sub_le_sub_right (div_le_div_of_nonneg_right
        (gaussian_polyhedron_ehrhard_second_moment_le w b hp v) hp.1.le) _
    _ = _ := by
      field_simp [hp.1.ne', (φ_pos (q (polyhedronMass w b))).ne']
      ring

end NegativeVotingEhrhard
