import GaussianCapTailAndStrip
import WeakSimplexConjectureLean.Normal.TruncatedMoments

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ProbabilityTheory WeakSimplex Filter Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace NegativeVotingMassCentroid

/-- The upper-threshold indicator of an actual real score. -/
def upperIndicator {X : Type*} (z : X → ℝ) (t : ℝ) : X → ℝ :=
  {x | t < z x}.indicator (fun _ => 1)

theorem upperIndicator_comp {X : Type*} (z : X → ℝ) (t : ℝ) (x : X) :
    upperIndicator (fun y : ℝ => y) t (z x) = upperIndicator z t x := by
  by_cases hx : t < z x <;> simp [upperIndicator, hx]

theorem fractional_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → ℝ) (hf : AEMeasurable f μ)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [h01] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

theorem fractional_mul_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f z : X → ℝ) (hf : AEMeasurable f μ)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (hz : Integrable z μ) :
    Integrable (fun x => f x * z x) μ := by
  apply hz.bdd_mul (c := 1) hf.aestronglyMeasurable
  filter_upwards [h01] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- The fractional bathtub comparison, derived pointwise from the threshold
ordering, retaining the exact mass remainder. It does not assume a Gaussian
isoperimetric theorem. -/
theorem fractional_threshold_remainder_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f z : X → ℝ) (t : ℝ)
    (hf : AEMeasurable f μ) (hz : Measurable z) (hzi : Integrable z μ)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    (∫ x, f x * z x ∂μ) ≤ (∫ x, upperIndicator z t x * z x ∂μ) +
      t * ((∫ x, f x ∂μ) - ∫ x, upperIndicator z t x ∂μ) := by
  have hs : MeasurableSet {x | t < z x} := measurableSet_lt measurable_const hz
  have hfi := fractional_integrable μ f hf h01
  have hfzi := fractional_mul_integrable μ f z hf h01 hzi
  have hIi : Integrable (upperIndicator z t) μ := (integrable_const (1 : ℝ)).indicator hs
  have hIz : Integrable (fun x => upperIndicator z t x * z x) μ := by
    convert hzi.indicator hs using 1
    funext x
    by_cases hx : t < z x <;> simp [upperIndicator, hx]
  have hb : ∀ᵐ x ∂μ, f x * z x ≤
      upperIndicator z t x * z x + t * (f x - upperIndicator z t x) := by
    filter_upwards [h01] with x hx
    by_cases ht : t < z x
    · have hI : upperIndicator z t x = 1 := by simp [upperIndicator, ht]
      rw [hI]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sub_nonneg.mpr ht.le)]
    · have hI : upperIndicator z t x = 0 := by simp [upperIndicator, ht]
      rw [hI]
      have hzt : z x ≤ t := le_of_not_gt ht
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.1 (sub_nonpos.mpr hzt)]
  calc
    _ ≤ ∫ x, upperIndicator z t x * z x + t * (f x - upperIndicator z t x) ∂μ :=
      integral_mono_ae hfzi (hIz.add ((hfi.sub hIi).const_mul t)) hb
    _ = _ := by
      change (∫ x, upperIndicator z t x * z x + t * ((f - upperIndicator z t) x) ∂μ) = _
      rw [integral_add hIz ((hfi.sub hIi).const_mul t), integral_const_mul]
      simp only [Pi.sub_apply]
      rw [integral_sub hfi hIi]

/-- Equal mass cancels the threshold remainder exactly. -/
theorem fractional_threshold_comparison {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f z : X → ℝ) (t : ℝ)
    (hf : AEMeasurable f μ) (hz : Measurable z) (hzi : Integrable z μ)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂μ) = ∫ x, upperIndicator z t x ∂μ) :
    (∫ x, f x * z x ∂μ) ≤ ∫ x, upperIndicator z t x * z x ∂μ := by
  simpa only [hmass, sub_self, mul_zero, add_zero] using
    fractional_threshold_remainder_bound μ f z t hf hz hzi h01

/-- The Gaussian lower-halfspace moment from the checked one-dimensional
truncated-moment identity. -/
theorem gaussian_lower_first_moment (t : ℝ) :
    (∫ x in Iic t, x ∂gaussianReal 0 1) = -normalPDF t := by
  calc
    _ = ∫ x, (Iic t).indicator (fun x : ℝ => x) x ∂gaussianReal 0 1 :=
      (integral_indicator measurableSet_Iic).symm
    _ = ∫ x, gaussianPDFReal 0 1 x * (Iic t).indicator (fun x : ℝ => x) x := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      rfl
    _ = ∫ x, (Iic t).indicator (fun x : ℝ => x * normalPDF x) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Iic t <;> simp [hx, normalPDF, mul_comm]
    _ = -normalPDF t := by rw [integral_indicator measurableSet_Iic, truncated_first_moment]

/-- Exact first moment of the actual Gaussian upper half-line. -/
theorem gaussian_upper_first_moment (t : ℝ) :
    (∫ x in Ioi t, x ∂gaussianReal 0 1) = normalPDF t := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  have hh := integral_add_compl (s := Iic t) measurableSet_Iic hid
  rw [compl_Iic, gaussian_lower_first_moment, integral_id_gaussianReal] at hh
  linarith

/-- The actual Gaussian upper-threshold mass is 1 minus its CDF. -/
theorem gaussian_upper_mass (t : ℝ) :
    (∫ x, upperIndicator (fun x : ℝ => x) t x ∂gaussianReal 0 1) = 1 - normalCDF t := by
  have hlo : (gaussianReal 0 1 (Iic t)).toReal = normalCDF t := by
    rw [← normalCDF_eq_measure_Iic, ENNReal.toReal_ofReal (normalCDF_pos t).le]
  have hh := integral_add_compl (s := Iic t) measurableSet_Iic
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1))
  simp only [compl_Iic, integral_const, measureReal_def, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one, measure_univ, ENNReal.toReal_one] at hh
  rw [hlo] at hh
  change (∫ x, (Ioi t).indicator (1 : ℝ → ℝ) x ∂gaussianReal 0 1) = _
  rw [integral_indicator_one measurableSet_Ioi]
  change (gaussianReal 0 1 (Ioi t)).toReal = _
  linarith

/-- Direct one-dimensional sharp threshold comparison for a fractional Gaussian
weight of the same mass as an upper half-line. -/
theorem gaussian_fractional_threshold_bound (f : ℝ → ℝ) (t : ℝ)
    (hf : AEMeasurable f (gaussianReal 0 1))
    (h01 : ∀ᵐ x ∂gaussianReal 0 1, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂gaussianReal 0 1) = 1 - normalCDF t) :
    (∫ x, f x * x ∂gaussianReal 0 1) ≤ normalPDF t := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  have hh := fractional_threshold_comparison (gaussianReal 0 1) f (fun x => x) t hf
    measurable_id hi h01 (hmass.trans (gaussian_upper_mass t).symm)
  have heq : (fun x : ℝ => upperIndicator (fun x : ℝ => x) t x * x) =
      (Ioi t).indicator (fun x => x) := by
    funext x
    by_cases hx : t < x <;> simp [upperIndicator, hx]
  rwa [heq, integral_indicator measurableSet_Ioi, gaussian_upper_first_moment] at hh

/-- The Gaussian density is even. -/
theorem normalPDF_even (t : ℝ) : normalPDF (-t) = normalPDF t := by
  simp [normalPDF, gaussianPDFReal]

/-- The CDF is continuous and strictly increasing, with no quantile hypothesis. -/
theorem continuous_normalCDF : Continuous normalCDF :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_normalCDF x).continuousAt)

theorem strictMono_normalCDF : StrictMono normalCDF :=
  strictMono_of_hasDerivAt_pos hasDerivAt_normalCDF normalPDF_pos

/-- Every probability strictly between zero and one has a unique Gaussian
threshold. Existence is derived from the actual CDF endpoint limits. -/
theorem exists_normalCDF_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ t : ℝ, normalCDF t = p := by
  have hlow : ∃ x, normalCDF x < p :=
    (tendsto_normalCDF_atBot.eventually (gt_mem_nhds hp)).exists
  have hhigh : ∃ x, p < normalCDF x :=
    (tendsto_normalCDF_atTop.eventually (lt_mem_nhds hp1)).exists
  exact mem_range_of_exists_le_of_exists_ge continuous_normalCDF
    (hlow.imp (fun _ h => h.le)) (hhigh.imp (fun _ h => h.le))

/-- Gaussian CDF symmetry, proved from its actual derivative and endpoint limits. -/
theorem normalCDF_neg (t : ℝ) : normalCDF (-t) = 1 - normalCDF t := by
  let g : ℝ → ℝ := fun x => normalCDF x + normalCDF (-x)
  have hd (x : ℝ) : HasDerivAt g 0 x := by
    convert (hasDerivAt_normalCDF x).add
      ((hasDerivAt_normalCDF (-x)).comp x (hasDerivAt_id x).neg) using 1
    · rfl
    · rw [normalPDF_even]
      ring
  have hc (x : ℝ) : g x = g t :=
    is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x t
  have hlim : Tendsto g atTop (𝓝 1) := by
    simpa only [g, add_zero, Function.comp_def] using
      tendsto_normalCDF_atTop.add (tendsto_normalCDF_atBot.comp tendsto_neg_atTop_atBot)
  have heq : g = (fun _ => g t) := funext hc
  rw [heq] at hlim
  have hval : g t = 1 := tendsto_nhds_unique tendsto_const_nhds hlim
  dsimp [g] at hval
  linarith

/-- The fractional threshold principle for any actual standard-normal score.
The score law is the only probability-specific input to this reusable lemma. -/
theorem remainder_bound_of_gaussian_score {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f z : X → ℝ) (t : ℝ)
    (hf : AEMeasurable f μ) (hz : Measurable z)
    (hmap : μ.map z = gaussianReal 0 1)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    (∫ x, f x * z x ∂μ) ≤ normalPDF t +
      t * ((∫ x, f x ∂μ) - (1 - normalCDF t)) := by
  have hmp : MeasurePreserving z μ (gaussianReal 0 1) := ⟨hz, hmap⟩
  have hzi : Integrable z μ := by
    simpa only [Function.comp_def, id_eq] using hmp.integrable_comp_of_integrable
      ((memLp_id_gaussianReal 2).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hlaw (g : ℝ → ℝ) (hg : Measurable g) :
      (∫ x, g (z x) ∂μ) = ∫ y, g y ∂gaussianReal 0 1 := by
    rw [← hmap, integral_map hz.aemeasurable hg.aestronglyMeasurable]
  have hI : Measurable (upperIndicator (fun x : ℝ => x) t) :=
    measurable_const.indicator measurableSet_Ioi
  have hmassI : (∫ x, upperIndicator z t x ∂μ) = 1 - normalCDF t := by
    calc
      _ = ∫ y, upperIndicator (fun x : ℝ => x) t y ∂gaussianReal 0 1 := by
        simpa only [upperIndicator_comp] using hlaw (upperIndicator (fun x : ℝ => x) t) hI
      _ = _ := gaussian_upper_mass t
  have hh := fractional_threshold_remainder_bound μ f z t hf hz hzi h01
  have hmoment : (∫ x, upperIndicator z t x * z x ∂μ) = normalPDF t := by
    calc
      _ = ∫ y, upperIndicator (fun x : ℝ => x) t y * y ∂gaussianReal 0 1 := by
        simpa only [upperIndicator_comp] using hlaw
          (fun y => upperIndicator (fun x : ℝ => x) t y * y) (hI.mul measurable_id)
      _ = ∫ y in Ioi t, y ∂gaussianReal 0 1 := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : t < y <;> simp [upperIndicator, hy]
      _ = _ := gaussian_upper_first_moment t
  simpa only [hmoment, hmassI] using hh

/-- Sharp matched-mass version of the actual Gaussian-score bound. -/
theorem threshold_bound_of_gaussian_score {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f z : X → ℝ) (t : ℝ)
    (hf : AEMeasurable f μ) (hz : Measurable z)
    (hmap : μ.map z = gaussianReal 0 1)
    (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂μ) = 1 - normalCDF t) :
    (∫ x, f x * z x ∂μ) ≤ normalPDF t := by
  simpa only [hmass, sub_self, mul_zero, add_zero] using
    remainder_bound_of_gaussian_score μ f z t hf hz hmap h01

/-- The inverse of the actual Gaussian CDF on (0,1), extended by zero elsewhere. -/
def normalQuantile (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 then Classical.choose (exists_normalCDF_eq h.1 h.2) else 0

theorem normalCDF_normalQuantile {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    normalCDF (normalQuantile p) = p := by
  unfold normalQuantile
  rw [dite_eq_left (show 0 < p ∧ p < 1 from ⟨hp, hp1⟩)]
  exact Classical.choose_spec (exists_normalCDF_eq hp hp1)

theorem normalQuantile_unique {p t : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : normalCDF t = p) : t = normalQuantile p :=
  strictMono_normalCDF.injective (ht.trans (normalCDF_normalQuantile hp hp1).symm)

/-- The sharp Gaussian mass profile φ(Φ⁻¹(p)), with the correct zero values at
both endpoints. Its extension outside the probability interval is also zero. -/
def gaussianMassProfile (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then normalPDF (normalQuantile p) else 0

/-- Exact Gaussian density at the logarithmic threshold used in localization. -/
theorem normalPDF_sqrt_two_log (m : ℝ) (hm : 1 ≤ m) :
    normalPDF (Real.sqrt (2 * Real.log m)) = (Real.sqrt (2 * Real.pi))⁻¹ / m := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hlog : 0 ≤ 2 * Real.log m := mul_nonneg (by norm_num) (Real.log_nonneg hm)
  have hpdf (x : ℝ) : normalPDF x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
    norm_num [normalPDF, gaussianPDFReal]
  rw [hpdf, Real.sq_sqrt hlog]
  have hexp : -(2 * Real.log m) / 2 = -Real.log m := by ring
  rw [hexp, Real.exp_neg, Real.exp_log hm0]
  rfl

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual Gaussian centroid of a fractional cell. -/
def gaussianCentroid (f : E → ℝ) : E := ∫ x, f x • x ∂stdGaussian E

theorem fractional_vector_integrable (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1) :
    Integrable (fun x => f x • x) (stdGaussian E) := by
  have hid : Integrable (fun x : E => x) (stdGaussian E) := IsGaussian.integrable_id
  apply hid.bdd_smul 1 hf.aestronglyMeasurable
  filter_upwards [h01] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- Exact pairing of the actual vector centroid with any direction. -/
theorem inner_gaussianCentroid (f : E → ℝ) (w : E)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1) :
    inner ℝ w (gaussianCentroid f) = ∫ x, f x * inner ℝ w x ∂stdGaussian E := by
  rw [gaussianCentroid, ← integral_inner (fractional_vector_integrable f hf h01)]
  simp only [inner_smul_right]

/-- The sharp directional bound for an actual unit Gaussian projection. -/
theorem unit_direction_threshold_bound (f : E → ℝ) (w : E) (hw : ‖w‖ = 1) (t : ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 1 - normalCDF t) :
    inner ℝ w (gaussianCentroid f) ≤ normalPDF t := by
  rw [inner_gaussianCentroid f w hf h01]
  apply threshold_bound_of_gaussian_score (stdGaussian E) f (fun x => inner ℝ w x) t
    hf (by fun_prop) ?_ h01 hmass
  simpa only [hw, one_pow, Real.toNNReal_one] using NegativeVotingCapTail.gaussian_inner_map w

/-- Sharp mass–centroid inequality at an explicit threshold, for arbitrary
finite-dimensional Euclidean Gaussian space and completed-measurable fractional
cells. The threshold-mass hypothesis is an explicit equality of actual integrals. -/
theorem gaussianCentroid_norm_le_threshold (f : E → ℝ) (t : ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 1 - normalCDF t) :
    ‖gaussianCentroid f‖ ≤ normalPDF t := by
  by_cases hc : gaussianCentroid f = 0
  · simpa only [hc, norm_zero] using (normalPDF_pos t).le
  · let w : E := ‖gaussianCentroid f‖⁻¹ • gaussianCentroid f
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hc
    have hh := unit_direction_threshold_bound f w hw t hf h01 hmass
    have hn : ‖gaussianCentroid f‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hp : inner ℝ w (gaussianCentroid f) = ‖gaussianCentroid f‖ := by
      simp only [w, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
      field_simp
    rwa [hp] at hh

omit [BorelSpace E] in
/-- A zero-mass fractional Gaussian cell vanishes almost everywhere. -/
theorem fractional_ae_zero_of_mass_zero (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 0) : f =ᵐ[stdGaussian E] 0 := by
  exact (integral_eq_zero_iff_of_nonneg_ae (h01.mono fun _ h => h.1)
    (fractional_integrable (stdGaussian E) f hf h01)).mp hmass

omit [BorelSpace E] in
/-- A full-mass fractional Gaussian cell equals one almost everywhere. -/
theorem fractional_ae_one_of_mass_one (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 1) : f =ᵐ[stdGaussian E] 1 := by
  have hfi := fractional_integrable (stdGaussian E) f hf h01
  have hdiff : Integrable (fun x => 1 - f x) (stdGaussian E) := (integrable_const (1 : ℝ)).sub hfi
  have hnonneg : ∀ᵐ x ∂stdGaussian E, 0 ≤ 1 - f x :=
    h01.mono fun _ h => sub_nonneg.mpr h.2
  have hmassdiff : (∫ x, (1 - f x) ∂stdGaussian E) = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hfi, hmass]
    simp
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hdiff).mp hmassdiff
  filter_upwards [hz] with x hx
  change f x = 1
  change 1 - f x = 0 at hx
  linarith

omit [BorelSpace E] in
theorem gaussianCentroid_eq_zero_of_mass_zero (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 0) : gaussianCentroid f = 0 := by
  unfold gaussianCentroid
  calc
    _ = ∫ _ : E, (0 : E) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [fractional_ae_zero_of_mass_zero f hf h01 hmass] with x hx
      simp only [Pi.zero_apply] at hx
      simp only [hx, zero_smul]
    _ = 0 := integral_zero _ _

theorem gaussianCentroid_eq_zero_of_mass_one (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) = 1) : gaussianCentroid f = 0 := by
  unfold gaussianCentroid
  calc
    _ = ∫ x : E, x ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [fractional_ae_one_of_mass_one f hf h01 hmass] with x hx
      change f x = 1 at hx
      simp only [hx, one_smul]
    _ = 0 := integral_id_stdGaussian

/-- A sharp Gaussian centroid bound with the conventional lower quantile. -/
theorem gaussianCentroid_norm_le_quantile (f : E → ℝ) (p : ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) (hmass : (∫ x, f x ∂stdGaussian E) = p) :
    ‖gaussianCentroid f‖ ≤ normalPDF (normalQuantile p) := by
  have hm : (∫ x, f x ∂stdGaussian E) = 1 - normalCDF (-normalQuantile p) := by
    rw [hmass, normalCDF_neg, normalCDF_normalQuantile hp hp1]
    ring
  simpa only [normalPDF_even] using
    gaussianCentroid_norm_le_threshold f (-normalQuantile p) hf h01 hm

/-- The sharp Gaussian mass–centroid bound, including both probability endpoints.
There is no matching-threshold or positive-mass premise on this theorem. -/
theorem gaussianCentroid_norm_le_profile (f : E → ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1) :
    ‖gaussianCentroid f‖ ≤ gaussianMassProfile (∫ x, f x ∂stdGaussian E) := by
  have hfi := fractional_integrable (stdGaussian E) f hf h01
  have hm0 : 0 ≤ ∫ x, f x ∂stdGaussian E := integral_nonneg_of_ae (h01.mono fun _ h => h.1)
  have hm1 : (∫ x, f x ∂stdGaussian E) ≤ 1 := by
    calc
      _ ≤ ∫ _ : E, (1 : ℝ) ∂stdGaussian E :=
        integral_mono_ae hfi (integrable_const (1 : ℝ)) (h01.mono fun _ h => h.2)
      _ = 1 := by simp
  by_cases h0 : (∫ x, f x ∂stdGaussian E) = 0
  · simp only [gaussianCentroid_eq_zero_of_mass_zero f hf h01 h0, norm_zero, h0,
      gaussianMassProfile, lt_self_iff_false, false_and, ↓reduceIte, le_refl]
  by_cases h1 : (∫ x, f x ∂stdGaussian E) = 1
  · simp only [gaussianCentroid_eq_zero_of_mass_one f hf h01 h1, norm_zero, h1,
      gaussianMassProfile, lt_self_iff_false, and_false, ↓reduceIte, le_refl]
  have hp : 0 < ∫ x, f x ∂stdGaussian E := lt_of_le_of_ne hm0 (Ne.symm h0)
  have hp1 : (∫ x, f x ∂stdGaussian E) < 1 := lt_of_le_of_ne hm1 h1
  rw [gaussianMassProfile, ite_eq_left ⟨hp, hp1⟩]
  exact gaussianCentroid_norm_le_quantile f _ hf h01 hp hp1 rfl

/-- A directional bound retaining the exact Gaussian upper-tail remainder. -/
theorem unit_direction_remainder_bound (f : E → ℝ) (w : E) (hw : ‖w‖ = 1) (t : ℝ)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1) :
    inner ℝ w (gaussianCentroid f) ≤ normalPDF t +
      t * ((∫ x, f x ∂stdGaussian E) - (1 - normalCDF t)) := by
  rw [inner_gaussianCentroid f w hf h01]
  apply remainder_bound_of_gaussian_score (stdGaussian E) f (fun x => inner ℝ w x) t
    hf (by fun_prop) ?_ h01
  simpa only [hw, one_pow, Real.toNNReal_one] using NegativeVotingCapTail.gaussian_inner_map w

/-- The quantile-free mass–centroid estimate used by global localization:
choosing t = sqrt(2 log m) turns a mass O(1/m) into centroid O(sqrt(log m)/m). -/
theorem gaussianCentroid_norm_le_mass_threshold (f : E → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1) :
    ‖gaussianCentroid f‖ ≤ t * (∫ x, f x ∂stdGaussian E) + normalPDF t := by
  have hm0 : 0 ≤ ∫ x, f x ∂stdGaussian E := integral_nonneg_of_ae (h01.mono fun _ h => h.1)
  by_cases hc : gaussianCentroid f = 0
  · rw [hc, norm_zero]
    exact add_nonneg (mul_nonneg ht hm0) (normalPDF_pos t).le
  · let w : E := ‖gaussianCentroid f‖⁻¹ • gaussianCentroid f
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hc
    have hh := unit_direction_remainder_bound f w hw t hf h01
    have hn : ‖gaussianCentroid f‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hp : inner ℝ w (gaussianCentroid f) = ‖gaussianCentroid f‖ := by
      simp only [w, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
      field_simp
    rw [hp] at hh
    have htail : 0 ≤ t * (1 - normalCDF t) := mul_nonneg ht (sub_nonneg.mpr (normalCDF_lt_one t).le)
    linarith

/-- A fully explicit localization consequence, with the logarithmic threshold
substituted into the actual Gaussian density and no hidden asymptotic constant. -/
theorem gaussianCentroid_norm_le_logarithmic_mass_bound (f : E → ℝ) (m C : ℝ)
    (hm : 1 ≤ m) (hf : AEMeasurable f (stdGaussian E))
    (h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1)
    (hmass : (∫ x, f x ∂stdGaussian E) ≤ C / m) :
    ‖gaussianCentroid f‖ ≤
      (C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) / m := by
  calc
    _ ≤ Real.sqrt (2 * Real.log m) * (∫ x, f x ∂stdGaussian E) +
        normalPDF (Real.sqrt (2 * Real.log m)) :=
      gaussianCentroid_norm_le_mass_threshold f _ (Real.sqrt_nonneg _) hf h01
    _ ≤ Real.sqrt (2 * Real.log m) * (C / m) + (Real.sqrt (2 * Real.pi))⁻¹ / m := by
      rw [normalPDF_sqrt_two_log m hm]
      exact add_le_add (mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)) le_rfl
    _ = _ := by ring

end Euclidean
end NegativeVotingMassCentroid
