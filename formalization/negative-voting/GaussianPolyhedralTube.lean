import GaussianFacetDisintegration
import WeakSimplexConjectureLean.Normal.PDFCDF

/-! Actual Gaussian tubular bounds for patches in affine hyperplanes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology RealInnerProductSpace
namespace NegativeVotingGaussianTube
open NegativeVotingDisintegration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def planePatch (w : E) (a : ℝ) (C : Set (tangentSpace w)) : Set E :=
  {x | ⟪w,x⟫=a ∧ (tangentSpace w).orthogonalProjectionOnto x ∈ C}

theorem measurableSet_planePatch (w : E) (a : ℝ) (C : Set (tangentSpace w))
    (hC : MeasurableSet C) : MeasurableSet (planePatch w a C) := by
  exact (isClosed_eq (by fun_prop) continuous_const).measurableSet.inter
    (hC.preimage (by fun_prop))

/-- A genuine Euclidean tube is contained in the product of its tangent
thickening and its scalar normal interval. -/
theorem tube_subset_tangent_normal (w : E) (hw : ‖w‖=1) (a ε : ℝ)
    (C : Set (tangentSpace w)) :
    thickening ε (planePatch w a C) ⊆
      tangentNormal w ⁻¹' ((thickening ε C) ×ˢ Ioo (a-ε) (a+ε)) := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
  change ⟪w,y⟫=a ∧ (tangentSpace w).orthogonalProjectionOnto y ∈ C at hy
  have ht : (tangentSpace w).orthogonalProjectionOnto x ∈ thickening ε C := by
    apply mem_thickening_iff.mpr
    refine ⟨(tangentSpace w).orthogonalProjectionOnto y,hy.2,?_⟩
    have hd := (tangentSpace w).lipschitzWith_orthogonalProjectionOnto.dist_le_mul x y
    exact lt_of_le_of_lt (by simpa using hd) hxy
  have hn : |⟪w,x⟫-a| < ε := by
    calc
      _ = |⟪w,x-y⟫| := by rw [inner_sub_right,hy.1]
      _ ≤ ‖w‖*‖x-y‖ := abs_real_inner_le_norm _ _
      _ < ε := by simpa only [hw,one_mul,dist_eq_norm] using hxy
  change (tangentSpace w).orthogonalProjectionOnto x ∈ thickening ε C ∧
    ⟪w,x⟫ ∈ Ioo (a-ε) (a+ε)
  refine ⟨ht,?_⟩
  rcases abs_lt.mp hn with ⟨hl,hu⟩
  constructor <;> linarith

/-- Exact Gaussian product coordinates turn the geometric tube cover into an
actual measure bound; no perimeter or conditional-law premise is supplied. -/
theorem gaussian_tube_measure_le (w : E) (hw : ‖w‖=1) (a ε : ℝ)
    (C : Set (tangentSpace w)) :
    stdGaussian E (thickening ε (planePatch w a C)) ≤
      stdGaussian (tangentSpace w) (thickening ε C) *
        gaussianReal 0 1 (Ioo (a-ε) (a+ε)) := by
  have hm : MeasurableSet ((thickening ε C) ×ˢ Ioo (a-ε) (a+ε)) :=
    isOpen_thickening.measurableSet.prod measurableSet_Ioo
  calc
    _ ≤ stdGaussian E (tangentNormal w ⁻¹' ((thickening ε C) ×ˢ Ioo (a-ε) (a+ε))) :=
      measure_mono (tube_subset_tangent_normal w hw a ε C)
    _ = ((stdGaussian E).map (tangentNormal w))
        ((thickening ε C) ×ˢ Ioo (a-ε) (a+ε)) :=
      (Measure.map_apply (by unfold tangentNormal; fun_prop) hm).symm
    _ = _ := by rw [tangentNormal_map w hw,Measure.prod_prod]

theorem gaussian_interval_real (a ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1 (Ioo (a-ε) (a+ε))).toReal =
      WeakSimplex.normalCDF (a+ε)-WeakSimplex.normalCDF (a-ε) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  change (∫ x in Ioo (a-ε) (a+ε), WeakSimplex.normalPDF x) = _
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith)]
  exact (intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn).symm

theorem gaussian_interval_quotient_tendsto (a : ℝ) :
    Tendsto (fun ε : ℝ => (gaussianReal 0 1 (Ioo (a-ε) (a+ε))).toReal/ε)
      (𝓝[>] 0) (𝓝 (2*WeakSimplex.normalPDF a)) := by
  have hp : HasDerivAt (fun ε : ℝ => WeakSimplex.normalCDF (a+ε))
      (WeakSimplex.normalPDF a) 0 := by
    simpa [Function.comp_def] using (WeakSimplex.hasDerivAt_normalCDF (a+0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_add a)
  have hm : HasDerivAt (fun ε : ℝ => WeakSimplex.normalCDF (a-ε))
      (-WeakSimplex.normalPDF a) 0 := by
    simpa [Function.comp_def] using (WeakSimplex.hasDerivAt_normalCDF (a-0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_sub a)
  have hd : HasDerivAt (fun ε : ℝ => WeakSimplex.normalCDF (a+ε)-WeakSimplex.normalCDF (a-ε))
      (2*WeakSimplex.normalPDF a) 0 := by convert hp.sub hm using 1 <;> ring
  have hl : Tendsto (fun ε : ℝ =>
      (WeakSimplex.normalCDF (a+ε)-WeakSimplex.normalCDF (a-ε))/ε)
      (𝓝[>] 0) (𝓝 (2*WeakSimplex.normalPDF a)) := by
    simpa only [zero_add,add_zero,sub_zero,sub_self,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hd.tendsto_slope_zero_right
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [gaussian_interval_real a ε hε.le]

/-- The explicit Gaussian tube majorant converges to twice the actual
normal density times intrinsic patch mass. -/
theorem gaussian_tube_upper_tendsto (w : E) (a : ℝ) (C : Set (tangentSpace w))
    (hC : IsClosed C) :
    Tendsto (fun ε : ℝ =>
      (stdGaussian (tangentSpace w) (thickening ε C)).toReal *
        ((gaussianReal 0 1 (Ioo (a-ε) (a+ε))).toReal/ε))
      (𝓝[>] 0) (𝓝 ((stdGaussian (tangentSpace w) C).toReal *
        (2*WeakSimplex.normalPDF a))) := by
  have hc := tendsto_measure_thickening_of_isClosed
    (μ := stdGaussian (tangentSpace w)) (s := C)
    (⟨1,by norm_num,measure_ne_top _ _⟩) hC
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hc |>.mul
    (gaussian_interval_quotient_tendsto a)

theorem gaussian_tube_quotient_le (w : E) (hw : ‖w‖=1) (a ε : ℝ)
    (hε : 0 < ε) (C : Set (tangentSpace w)) :
    (stdGaussian E (thickening ε (planePatch w a C))).toReal/ε ≤
      (stdGaussian (tangentSpace w) (thickening ε C)).toReal *
        ((gaussianReal 0 1 (Ioo (a-ε) (a+ε))).toReal/ε) := by
  have hr := ENNReal.toReal_mono (by finiteness)
    (gaussian_tube_measure_le w hw a ε C)
  rw [ENNReal.toReal_mul] at hr
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hr hε.le

/-- The actual tube quotient is eventually bounded by the true normalized
facet mass, with any strictly positive error. -/
theorem gaussian_tube_eventually_le (w : E) (hw : ‖w‖=1) (a : ℝ)
    (C : Set (tangentSpace w)) (hC : IsClosed C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (stdGaussian E (thickening ε (planePatch w a C))).toReal/ε ≤
        (stdGaussian (tangentSpace w) C).toReal*(2*WeakSimplex.normalPDF a)+δ := by
  have hu := (tendsto_order.1 (gaussian_tube_upper_tendsto w a C hC)).2
    ((stdGaussian (tangentSpace w) C).toReal*(2*WeakSimplex.normalPDF a)+δ)
    (by linarith)
  filter_upwards [hu,self_mem_nhdsWithin] with ε hε hpos
  exact (gaussian_tube_quotient_le w hw a ε hpos C).trans hε.le

end NegativeVotingGaussianTube
