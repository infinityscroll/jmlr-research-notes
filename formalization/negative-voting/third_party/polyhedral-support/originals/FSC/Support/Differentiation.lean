import FSC.Support.Slicing
import FSC.Analysis.FinitePartialDerivatives
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual finite Gaussian support derivatives, retaining redundant listed constraints. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace Topology ENNReal

namespace FSC

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit residual-sample preimage of the constraints other than the pinned one. -/
def slicePreimage (w : ι → Coord d) (b : ι → ℝ) (j : ι) : Set (Coord d) :=
  {y | ∀ k, k ≠ j → inner ℝ (w k) (b j • w j + normalResidual (w j) y) ≤ b k}

omit [DecidableEq ι] in
theorem measurableSet_slicePreimage (w : ι → Coord d) (b : ι → ℝ) (j : ι) :
    MeasurableSet (slicePreimage w b j) := by
  simp only [slicePreimage, Set.setOf_forall]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le (by fun_prop) measurable_const

omit [DecidableEq ι] in
theorem sliceMass_eq_stdGaussian (w : ι → Coord d) (b : ι → ℝ) (j : ι) :
    sliceMass w b j = (stdGaussian (Coord d) (slicePreimage w b j)).toReal := by
  rw [sliceMass, sliceLaw, Measure.map_apply (by fun_prop) (by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le (by fun_prop) measurable_const)]
  rfl

omit [DecidableEq ι] in
theorem measurable_sliceMass (w : ι → Coord d) (j : ι) :
    Measurable (fun b ↦ sliceMass w b j) := by
  simp_rw [sliceMass_eq_stdGaussian]
  have hS : MeasurableSet {p : (ι → ℝ) × Coord d |
      ∀ k, k ≠ j → inner ℝ (w k) (p.1 j • w j + normalResidual (w j) p.2) ≤ p.1 k} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le (by fun_prop) (by fun_prop)
  exact (measurable_measure_prodMk_left (ν := stdGaussian (Coord d)) hS).ennreal_toReal

omit [Fintype ι] [DecidableEq ι] in
theorem sliceMass_nonneg (w : ι → Coord d) (b : ι → ℝ) (j : ι) :
    0 ≤ sliceMass w b j := ENNReal.toReal_nonneg

omit [DecidableEq ι] in
theorem sliceMass_le_one (w : ι → Coord d) (b : ι → ℝ) (j : ι) :
    sliceMass w b j ≤ 1 := by
  rw [sliceMass_eq_stdGaussian]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using
    (prob_le_one (μ := stdGaussian (Coord d)) (s := slicePreimage w b j)))

/-- No coincident boundary hyperplanes is an open condition in the listed supports. -/
theorem NoCoincident.eventually {w : ι → Coord d} {b : ι → ℝ}
    (hb : NoCoincident w b) : ∀ᶠ b' in 𝓝 b, NoCoincident w b' := by
  unfold NoCoincident at hb ⊢
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases hjk : j = k
  · exact Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have h₁ : ∀ᶠ b' in 𝓝 b, w j = w k → b' j ≠ b' k := by
      by_cases hw : w j = w k
      · exact ((continuous_apply j).continuousAt.ne_iff_eventually_ne
          (continuous_apply k).continuousAt).mp ((hb j k hjk).1 hw) |>.mono
          fun _ h _ ↦ h
      · exact Eventually.of_forall fun _ h ↦ (hw h).elim
    have h₂ : ∀ᶠ b' in 𝓝 b, w j = -w k → b' j ≠ -b' k := by
      by_cases hw : w j = -w k
      · exact ((continuous_apply j).continuousAt.ne_iff_eventually_ne
          (continuous_apply k).continuousAt.neg).mp ((hb j k hjk).2 hw) |>.mono
          fun _ h _ ↦ h
      · exact Eventually.of_forall fun _ h ↦ (hw h).elim
    filter_upwards [h₁, h₂] with b' h₁ h₂
    exact fun _ ↦ ⟨h₁, h₂⟩

/-- Vanishing unit-normal residual forces parallel or antiparallel normals. -/
theorem eq_or_eq_neg_of_normalResidual_eq_zero {u v : Coord d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hz : u - inner ℝ u v • v = 0) : u = v ∨ u = -v := by
  have heq : u = inner ℝ u v • v := sub_eq_zero.mp hz
  have hn := congrArg norm heq
  rw [hu, norm_smul, hv, mul_one, Real.norm_eq_abs] at hn
  have hc : inner ℝ u v = 1 ∨ inner ℝ u v = -1 := by
    apply sq_eq_one_iff.mp
    nlinarith [sq_abs (inner ℝ u v)]
  rcases hc with hc | hc
  · left
    simpa only [hc, one_smul] using heq
  · right
    simpa only [hc, neg_one_smul] using heq

omit [Fintype ι] [DecidableEq ι] in
/-- Every unpinned boundary is null under the explicit slice realization at an untied support. -/
theorem ae_slice_boundary_ne (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) (j k : ι) (hkj : k ≠ j) :
    ∀ᵐ y ∂stdGaussian (Coord d),
      inner ℝ (w k) (b j • w j + normalResidual (w j) y) ≠ b k := by
  have heq (y : Coord d) :
      inner ℝ (w k) (b j • w j + normalResidual (w j) y) =
      b j * inner ℝ (w k) (w j) + inner ℝ (w k - inner ℝ (w k) (w j) • w j) y := by
    simp only [normalResidual_apply, inner_add_right, inner_sub_right, inner_sub_left,
      real_inner_smul_right, real_inner_smul_left]
    ring
  by_cases hz : w k - inner ℝ (w k) (w j) • w j = 0
  · rcases eq_or_eq_neg_of_normalResidual_eq_zero (hw k) (hw j) hz with h | h
    · apply Eventually.of_forall
      intro y
      simp only [heq, hz, inner_zero_left, add_zero]
      have hc : inner ℝ (w k) (w j) = 1 :=
        (inner_eq_one_iff_of_norm_eq_one (hw k) (hw j)).mpr h
      rw [hc, mul_one]
      exact ((hb k j hkj).1 h).symm
    · apply Eventually.of_forall
      intro y
      simp only [heq, hz, inner_zero_left, add_zero]
      have hc : inner ℝ (w k) (w j) = -1 :=
        (inner_eq_neg_one_iff_of_norm_eq_one (hw k) (hw j)).mpr h
      rw [hc, mul_neg_one]
      exact ((hb k j hkj).2 h).symm
  · filter_upwards [ae_inner_ne _ hz (b k - b j * inner ℝ (w k) (w j))] with y hy
    rw [heq]
    exact fun h ↦ hy (by linarith)

/-- Slice probabilities vary continuously at every actual untied support. -/
theorem continuousAt_sliceMass (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) (j : ι) :
    ContinuousAt (fun b' ↦ sliceMass w b' j) b := by
  simp_rw [sliceMass_eq_stdGaussian]
  have ht : Tendsto (fun b' ↦ stdGaussian (Coord d) (slicePreimage w b' j))
      (𝓝 b) (𝓝 (stdGaussian (Coord d) (slicePreimage w b j))) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 b)
      (measurableSet_slicePreimage w b j) (fun b' ↦ measurableSet_slicePreimage w b' j)
    have ha : ∀ᵐ y ∂stdGaussian (Coord d), ∀ k, k ≠ j →
        inner ℝ (w k) (b j • w j + normalResidual (w j) y) ≠ b k := by
      apply ae_all_iff.mpr
      intro k
      by_cases hkj : k = j
      · exact Eventually.of_forall fun _ h ↦ (h hkj).elim
      · exact (ae_slice_boundary_ne w hw b hb j k hkj).mono fun _ h _ ↦ h
    filter_upwards [ha] with y hy
    have he : ∀ k, ∀ᶠ b' in 𝓝 b,
        (k ≠ j → inner ℝ (w k) (b' j • w j + normalResidual (w j) y) ≤ b' k) ↔
        (k ≠ j → inner ℝ (w k) (b j • w j + normalResidual (w j) y) ≤ b k) := by
      intro k
      by_cases hkj : k = j
      · exact Eventually.of_forall fun _ ↦ by simp [hkj]
      · have hc : ContinuousAt
            (fun b' : ι → ℝ ↦ inner ℝ (w k) (b' j • w j + normalResidual (w j) y)) b := by
          exact continuousAt_const.inner
            (((continuous_apply j).continuousAt.smul continuousAt_const).add continuousAt_const)
        rcases lt_or_gt_of_ne (hy k hkj) with h | h
        · filter_upwards [hc.eventually_lt (continuous_apply k).continuousAt h] with b' hb'
          simp only [hb'.le, h.le]
        · filter_upwards [(continuous_apply k).continuousAt.eventually_lt hc h] with b' hb'
          simp only [not_le.mpr hb', not_le.mpr h]
    filter_upwards [eventually_all.mpr he] with b' hb'
    exact forall_congr' hb'
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp ht

/-- Exact one-dimensional Gaussian integral for every support vector, including ties. -/
theorem capMass_slicing_gaussian (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (j : ι) :
    capMass w b = ∫ z in Set.Iic (b j), sliceMass w (Function.update b j z) j
      ∂gaussianReal 0 1 := by
  classical
  let s : Set (Coord d) := {y | ∀ k, k ≠ j → inner ℝ (w k) y ≤ b k}
  have hs : MeasurableSet s := by
    simp only [s, Set.setOf_forall]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le (by fun_prop) measurable_const
  let A : Set (Coord d × ℝ) := {p | p.2 ≤ b j ∧ p.1 ∈ s}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_snd measurable_const).inter (hs.preimage measurable_fst)
  let g : ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (sliceMass w (Function.update b j z) j)
  have hgm : Measurable g :=
    ((measurable_sliceMass w j).comp (by fun_prop)).ennreal_ofReal
  have hslice (z : ℝ) : sliceLaw (w j) z s = g z := by
    letI : IsProbabilityMeasure (sliceLaw (w j) z) := by
      unfold sliceLaw
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    have he : {y : Coord d | ∀ k, k ≠ j → inner ℝ (w k) y ≤ Function.update b j z k} = s := by
      ext y
      simp only [s, Set.mem_setOf_eq]
      apply forall_congr'
      intro k
      by_cases hkj : k = j
      · simp [hkj]
      · simp [hkj]
    simp only [g, sliceMass, Function.update_self, he]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have h := lintegral_normalSlice (w j) (hw j) (A.indicator (1 : Coord d × ℝ → ℝ≥0∞))
    (measurable_const.indicator hA)
  have hleft : (fun y : Coord d ↦ A.indicator (1 : Coord d × ℝ → ℝ≥0∞)
      (y, inner ℝ (w j) y)) = (cap w b).indicator (1 : Coord d → ℝ≥0∞) := by
    funext y
    have he : (y, inner ℝ (w j) y) ∈ A ↔ y ∈ cap w b := by
      change (inner ℝ (w j) y ≤ b j ∧ ∀ k, k ≠ j → inner ℝ (w k) y ≤ b k) ↔
        ∀ k, inner ℝ (w k) y ≤ b k
      constructor
      · rintro ⟨hj, hrest⟩ k
        by_cases hkj : k = j
        · simpa [hkj] using hj
        · exact hrest k hkj
      · intro hall
        exact ⟨hall j, fun k _ ↦ hall k⟩
    by_cases hy : y ∈ cap w b
    · rw [Set.indicator_of_mem (he.mpr hy), Set.indicator_of_mem hy]
      rfl
    · rw [Set.indicator_of_notMem (mt he.mp hy), Set.indicator_of_notMem hy]
  have hright (z : ℝ) : (∫⁻ y : Coord d,
      A.indicator (1 : Coord d × ℝ → ℝ≥0∞) (y, z) ∂sliceLaw (w j) z) =
      (Set.Iic (b j)).indicator g z := by
    by_cases hz : z ≤ b j
    · have he : (fun y : Coord d ↦ A.indicator (1 : Coord d × ℝ → ℝ≥0∞) (y, z)) =
          s.indicator (1 : Coord d → ℝ≥0∞) := by
        funext y
        simp [A, hz, Set.indicator_apply]
      rw [he, lintegral_indicator_one hs, hslice]
      simp [hz]
    · have he : (fun y : Coord d ↦ A.indicator (1 : Coord d × ℝ → ℝ≥0∞) (y, z)) =
          fun _ ↦ 0 := by
        funext y
        simp [A, hz]
      rw [he, lintegral_zero]
      simp [hz]
  rw [hleft, lintegral_indicator_one (measurableSet_cap w b)] at h
  simp_rw [hright] at h
  rw [capMass, h, ← integral_toReal (hgm.indicator measurableSet_Iic).aemeasurable (by
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ Set.Iic (b j) <;> simp [hz, g])]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ Set.Iic (b j) <;>
    simp [hz, g, ENNReal.toReal_ofReal (sliceMass_nonneg w _ j)]

/-- The same exact slicing with the standard real Gaussian density against volume. -/
theorem capMass_slicing (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (j : ι) :
    capMass w b = ∫ z in Set.Iic (b j),
      WeakSimplex.normalPDF z * sliceMass w (Function.update b j z) j := by
  rw [capMass_slicing_gaussian w hw b j, ← integral_indicator measurableSet_Iic,
    integral_gaussianReal_eq_integral_smul (by norm_num), ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ Set.Iic (b j) <;>
    simp [hz, WeakSimplex.normalPDF, smul_eq_mul]

theorem integrable_normalPDF_mul_sliceMass (w : ι → Coord d) (b : ι → ℝ) (j : ι) :
    Integrable (fun z : ℝ ↦ WeakSimplex.normalPDF z * sliceMass w (Function.update b j z) j) := by
  have hp : Integrable WeakSimplex.normalPDF := integrable_gaussianPDFReal 0 1
  have hcp : Continuous WeakSimplex.normalPDF :=
    continuous_iff_continuousAt.mpr fun x ↦ (WeakSimplex.hasDerivAt_normalPDF x).continuousAt
  refine hp.mono' (hcp.measurable.mul
    ((measurable_sliceMass w j).comp (by fun_prop))).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (WeakSimplex.normalPDF_pos z).le (sliceMass_nonneg w _ j))]
  exact mul_le_of_le_one_right (WeakSimplex.normalPDF_pos z).le (sliceMass_le_one w _ j)

private theorem hasDerivAt_integral_Iic_of_continuousAt (g : ℝ → ℝ)
    (hg : Integrable g) (a : ℝ) (hc : ContinuousAt g a) :
    HasDerivAt (fun z : ℝ ↦ ∫ x in Set.Iic z, g x) (g a) a := by
  have hFTC : HasDerivAt (fun u ↦ ∫ x in a..u, g x) (g a) a :=
    intervalIntegral.integral_hasDerivAt_right hg.intervalIntegrable
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hc
  have heq : (fun z : ℝ ↦ ∫ x in Set.Iic z, g x) =
      fun z ↦ (∫ x in Set.Iic a, g x) + ∫ x in a..z, g x := by
    funext z
    have h := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := z)
      hg.integrableOn hg.integrableOn
    linarith
  rw [heq]
  simpa only [zero_add] using! (hasDerivAt_const a (∫ x in Set.Iic a, g x)).add hFTC

/-- The exact partial derivative uses the frozen Gaussian slice, including zero face mass. -/
theorem hasDerivAt_capMass_update (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) (j : ι) :
    HasDerivAt (fun z : ℝ ↦ capMass w (Function.update b j z))
      (WeakSimplex.normalPDF (b j) * sliceMass w b j) (b j) := by
  have heq : (fun z : ℝ ↦ capMass w (Function.update b j z)) =
      fun z ↦ ∫ a in Set.Iic z,
        WeakSimplex.normalPDF a * sliceMass w (Function.update b j a) j := by
    funext z
    simpa only [Function.update_self, Function.update_idem] using
      capMass_slicing w hw (Function.update b j z) j
  have hup : Tendsto (Function.update b j) (𝓝 (b j)) (𝓝 b) := by
    simpa using! (contDiff_update (𝕜 := ℝ) 1 b j).continuous.tendsto (b j)
  have hcs : ContinuousAt (fun z : ℝ ↦ sliceMass w (Function.update b j z) j) (b j) := by
    simpa only [ContinuousAt, Function.update_eq_self, Function.comp_def] using!
      (continuousAt_sliceMass w hw b hb j).tendsto.comp hup
  rw [heq]
  simpa using! hasDerivAt_integral_Iic_of_continuousAt _
    (integrable_normalPDF_mul_sliceMass w b j) (b j)
    ((WeakSimplex.hasDerivAt_normalPDF (b j)).continuousAt.mul hcs)

omit [DecidableEq ι] in
private theorem piGradient_eq_supportGradient (w : ι → Coord d) (b : ι → ℝ) :
    piGradient (fun j ↦ WeakSimplex.normalPDF (b j) * sliceMass w b j) =
      supportGradient w b := by
  apply ContinuousLinearMap.ext
  intro h
  simp [piGradient_apply, supportGradient, mul_comm]

/-- Actual finite-support Frechet derivative with the frozen explicit slice gradient. -/
theorem hasFDerivAt_capMass (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) :
    HasFDerivAt (capMass w) (supportGradient w b) b := by
  rw [← piGradient_eq_supportGradient]
  apply hasFDerivAt_pi_of_partials
    (p := fun b' j ↦ WeakSimplex.normalPDF (b' j) * sliceMass w b' j)
  · intro j
    exact hb.eventually.mono fun b' hb' ↦ hasDerivAt_capMass_update w hw b' hb' j
  · intro j
    exact ((WeakSimplex.hasDerivAt_normalPDF (b j)).continuousAt.comp (f := fun b' : ι → ℝ ↦ b' j)
      (continuous_apply j).continuousAt).mul (continuousAt_sliceMass w hw b hb j)

/-- The support probability is C1 on a neighborhood of every untied actual support. -/
theorem contDiffAt_one_capMass (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) : ContDiffAt ℝ 1 (capMass w) b := by
  apply contDiffAt_one_pi_of_partials
    (p := fun b' j ↦ WeakSimplex.normalPDF (b' j) * sliceMass w b' j)
  · intro j
    exact hb.eventually.mono fun b' hb' ↦ hasDerivAt_capMass_update w hw b' hb' j
  · intro j
    filter_upwards [hb.eventually] with b' hb'
    exact ((WeakSimplex.hasDerivAt_normalPDF (b' j)).continuousAt.comp (f := fun c : ι → ℝ ↦ c j)
      (continuous_apply j).continuousAt).mul (continuousAt_sliceMass w hw b' hb' j)

/-- An explicit common open neighborhood carries C1 and every slice-gradient identity. -/
theorem capMass_support_C1 (w : ι → Coord d) (hw : ∀ k, ‖w k‖ = 1)
    (b : ι → ℝ) (hb : NoCoincident w b) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ b ∈ U ∧ ContDiffOn ℝ 1 (capMass w) U ∧
      ∀ b' ∈ U, HasFDerivAt (capMass w) (supportGradient w b') b' := by
  refine ⟨{b' | NoCoincident w b'}, ?_, hb, ?_, ?_⟩
  · exact isOpen_iff_mem_nhds.mpr fun _ h ↦ h.eventually
  · exact fun b' hb' ↦ (contDiffAt_one_capMass w hw b' hb').contDiffWithinAt
  · exact fun b' hb' ↦ hasFDerivAt_capMass w hw b' hb'

end FSC
