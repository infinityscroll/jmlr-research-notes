import FSC.Support.Dilation
import FSC.Support.Differentiation
import WeakSimplexConjectureLean.LogConcavity.Prekopa
import WeakSimplexConjectureLean.LogConcavity.Indicators
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-! Support log-concavity and the quadratic tangent at the actual support.
The pinned public Prekopa theorem supplies marginal log-concavity. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace FSC

theorem standardDensity_eq_kernel {d : ℕ} (y : Coord d) :
    standardDensity y = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d) *
      WeakSimplex.gaussianQuadraticKernel (1 : Mat d) y := by
  apply (ENNReal.toReal_eq_toReal_iff' (standardDensity_ne_top y) (by
    unfold WeakSimplex.gaussianQuadraticKernel
    finiteness)).mp
  rw [toReal_standardDensity, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), WeakSimplex.gaussianQuadraticKernel,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp [WeakSimplex.qform, WeakSimplex.matrixMul]

theorem isLogConcave_standardDensity (d : ℕ) :
    WeakSimplex.IsLogConcave (standardDensity (n := d)) := by
  have heq : (standardDensity (n := d)) =
      (fun _ : Coord d ↦ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d)) *
      WeakSimplex.gaussianQuadraticKernel (1 : Mat d) :=
    funext standardDensity_eq_kernel
  rw [heq]
  exact (WeakSimplex.isLogConcave_const _).mul
    (WeakSimplex.isLogConcave_gaussianQuadraticKernel Matrix.PosSemidef.one)

def jointCap {d : ℕ} {ι : Type*} (w : ι → Coord d) :
    Set ((ι → ℝ) × (Fin d → ℝ)) :=
  {p | ∀ i, inner ℝ (w i) (WithLp.toLp 2 p.2) ≤ p.1 i}

theorem convex_jointCap {d : ℕ} {ι : Type*} (w : ι → Coord d) :
    Convex ℝ (jointCap w) := by
  intro x hx y hy a b ha hb _ i
  change inner ℝ (w i) (a • WithLp.toLp 2 x.2 + b • WithLp.toLp 2 y.2) ≤
    a * x.1 i + b * y.1 i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
    (mul_le_mul_of_nonneg_left (hy i) hb)

theorem measurableSet_jointCap {d : ℕ} {ι : Type*} [Fintype ι] (w : ι → Coord d) :
    MeasurableSet (jointCap w) := by
  simp only [jointCap, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le (by fun_prop) (by fun_prop)

def supportKernel {d : ℕ} {ι : Type*} (w : ι → Coord d)
    (b : ι → ℝ) (y : Fin d → ℝ) : ℝ≥0∞ :=
  WeakSimplex.convexIndicator (jointCap w) (b, y) * standardDensity (WithLp.toLp 2 y)

theorem measurable_supportKernel {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) : Measurable (Function.uncurry (supportKernel w)) := by
  exact (WeakSimplex.measurable_convexIndicator (measurableSet_jointCap w)).mul
    ((measurable_standardDensity d).comp ((PiLp.continuous_toLp 2 _).measurable.comp measurable_snd))

theorem isLogConcave_supportKernel {d : ℕ} {ι : Type*} (w : ι → Coord d) :
    WeakSimplex.IsLogConcave (Function.uncurry (supportKernel w)) := by
  let A : ((ι → ℝ) × (Fin d → ℝ)) →ₗ[ℝ] Coord d :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap.comp (LinearMap.snd ℝ _ _)
  exact (WeakSimplex.isLogConcave_convexIndicator (convex_jointCap w)).mul
    ((isLogConcave_standardDensity d).comp_affineMap A.toAffineMap)

theorem capMeasure_eq_lintegral_supportKernel {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) (b : ι → ℝ) :
    stdGaussian (Coord d) (cap w b) = ∫⁻ y, supportKernel w b y := by
  rw [stdGaussian_eq_volume_withDensity,
    withDensity_apply _ (measurableSet_cap w b)]
  rw [← lintegral_indicator (measurableSet_cap w b)]
  have h := (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp
    ((measurable_standardDensity d).indicator (measurableSet_cap w b))
  rw [← h]
  apply lintegral_congr
  intro y
  classical
  by_cases hy : WithLp.toLp 2 y ∈ cap w b
  · have hj : (b, y) ∈ jointCap w := hy
    simp [supportKernel, WeakSimplex.convexIndicator, hy, hj]
  · have hj : (b, y) ∉ jointCap w := hy
    simp [supportKernel, WeakSimplex.convexIndicator, hy, hj]

theorem isLogConcave_capMeasure {d : ℕ} {ι : Type*} [Fintype ι] (w : ι → Coord d) :
    WeakSimplex.IsLogConcave (fun b ↦ stdGaussian (Coord d) (cap w b)) := by
  have hm (b : ι → ℝ) : Measurable (supportKernel w b) := by
    have hpair : Measurable (fun y : Fin d → ℝ ↦ (b, y)) :=
      measurable_const.prodMk measurable_id
    have hh := (measurable_supportKernel w).comp hpair
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hh
  have h := WeakSimplex.isLogConcave_lintegral_right
    (F := supportKernel w)
    hm
    (isLogConcave_supportKernel w)
  simpa only [← capMeasure_eq_lintegral_supportKernel] using h

theorem capMass_logConcave {d : ℕ} {ι : Type*} [Fintype ι] (w : ι → Coord d)
    (b c : ι → ℝ) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    capMass w b ^ a * capMass w c ^ (1 - a) ≤ capMass w (a • b + (1 - a) • c) := by
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (isLogConcave_capMeasure w ha ha1 b c)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow, capMass] using h

theorem capMass_pos {d : ℕ} {ι : Type*} [Fintype ι] (w : ι → Coord d)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) : 0 < capMass w b := by
  let U : Set (Coord d) := {y | ∀ i, inner ℝ (w i) y < b i}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : Coord d) ∈ U := by simpa [U] using hb
  have hpos := stdGaussian_pos_of_isOpen hU ⟨0, h0⟩
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  exact (lt_of_lt_of_le hpos (measure_mono (fun _ hy i ↦ (hy i).le))).ne'

def positiveSupports (ι : Type*) : Set (ι → ℝ) := {b | ∀ i, 0 < b i}

theorem convex_positiveSupports (ι : Type*) : Convex ℝ (positiveSupports ι) := by
  apply convex_iff_forall_pos.mpr
  intro x hx y hy a b ha hb _ i
  exact add_pos (mul_pos ha (hx i)) (mul_pos hb (hy i))

theorem convexOn_inv_capMass {d : ℕ} {ι : Type*} [Fintype ι] (w : ι → Coord d) :
    ConvexOn ℝ (positiveSupports ι) (fun b ↦ (capMass w b)⁻¹) := by
  apply convexOn_iff_forall_pos.mpr
  refine ⟨convex_positiveSupports ι, ?_⟩
  intro b hb c hc a r ha hr har
  have hbc := capMass_logConcave w b c a ha (by linarith)
  have hr' : 1 - a = r := by linarith
  rw [hr'] at hbc
  have hpb := capMass_pos w b hb
  have hpc := capMass_pos w c hc
  have hgeom := mul_pos (Real.rpow_pos_of_pos hpb a) (Real.rpow_pos_of_pos hpc r)
  have hinv := one_div_le_one_div_of_le hgeom hbc
  have ham := Real.geom_mean_le_arith_mean2_weighted ha.le hr.le
    (inv_pos.mpr hpb).le (inv_pos.mpr hpc).le har
  rw [Real.inv_rpow hpb.le, Real.inv_rpow hpc.le, ← mul_inv] at ham
  have hi : (capMass w (a • b + r • c))⁻¹ ≤ (capMass w b ^ a * capMass w c ^ r)⁻¹ := by
    simpa only [one_div] using hinv
  exact hi.trans ham

/-- The reference needs positive supports but may be nondifferentiable because of ties. -/
theorem quadratic_support_tangent_of_hasFDerivAt {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Coord d) (b c : ι → ℝ) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (l : (ι → ℝ) →L[ℝ] ℝ) (hf : HasFDerivAt (capMass w) l b) :
    l (b - c) ≤ capMass w b ^ 2 / capMass w c - capMass w b := by
  have hcv := (convexOn_inv_capMass w).comp_affineMap (AffineMap.lineMap b c)
  have h0 : (0 : ℝ) ∈ (AffineMap.lineMap b c) ⁻¹' positiveSupports ι := by
    simpa [positiveSupports] using hb
  have h1 : (1 : ℝ) ∈ (AffineMap.lineMap b c) ⁻¹' positiveSupports ι := by
    simpa [positiveSupports] using hc
  have hf' : HasFDerivAt (capMass w) l ((AffineMap.lineMap b c) (0 : ℝ)) := by
    simpa using! hf
  have hline := hf'.comp_hasDerivAt 0 (AffineMap.hasDerivAt_lineMap (a := b) (b := c))
  have hpos := capMass_pos w b hb
  have hInv := hline.inv (by simpa using hpos.ne')
  have hbound := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num : (0 : ℝ) < 1) hInv
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hbound
  have hl : l (c - b) = -l (b - c) := by simp only [map_sub]; ring
  rw [hl, neg_neg] at hbound
  have hmul := (div_le_iff₀ (sq_pos_of_pos hpos)).mp hbound
  have hid : ((capMass w c)⁻¹ - (capMass w b)⁻¹) * capMass w b ^ 2 =
      capMass w b ^ 2 / capMass w c - capMass w b := by
    field_simp
  rw [hid] at hmul
  exact hmul

/-- The actual-support quadratic comparison; no no-coincidence condition is needed at c. -/
theorem quadratic_support_tangent {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Coord d) (hw : ∀ i, ‖w i‖ = 1) (b c : ι → ℝ)
    (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) (hsep : NoCoincident w b) :
    supportGradient w b (b - c) ≤ capMass w b ^ 2 / capMass w c - capMass w b :=
  quadratic_support_tangent_of_hasFDerivAt w b c hb hc (supportGradient w b)
    (hasFDerivAt_capMass w hw b hsep)

end FSC
