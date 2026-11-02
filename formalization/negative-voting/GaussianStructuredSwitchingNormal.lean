import GaussianBoundaryHighChaosTrace

/-! Actual Gaussian OU normal tubes for the structured switching argument.
One common full-measure set controls every point of the whole tube. The
hypercontractive exponent is retained, allowing fixed Holder products later. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped RealInnerProductSpace ENNReal
namespace NegativeVotingStructuredSwitchingNormal
open NegativeVotingDisintegration NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingActualFacetOUTrace NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingSmoothingComposition NegativeVotingHypercontractivity

/-- A single measurable, nonnegative envelope for the actual product-Gaussian
OU value and its actual normal derivative, at every point in a fixed tube. -/
theorem product_normal_tube_envelope {n : ℕ} {τ : ℝ}
    (hτ : 0<τ) (hτ1 : τ<1) (a : ℝ)
    (f : (Fin n→ℝ)×ℝ→ℝ) (hfM : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod (gaussianReal 0 1))) :
    ∃ G : (Fin n→ℝ)→ℝ, Measurable G ∧ (∀x,0 ≤ G x) ∧
      MemLp G (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) ∧
      eLpNorm G (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) ≤
        ENNReal.ofReal (Real.sqrt (normalRowSquare τ (|a|+1))+
          Real.sqrt (normalDerivativeRowSquare τ (|a|+1)))*
            eLpNorm f 2 ((γFin n).prod (gaussianReal 0 1)) ∧
      ∀ᵐ y ∂γFin n,
        ContinuousOn (fun t:ℝ=>productGaussianAverage τ f (y,a+t)) (Icc 0 1) ∧
        ∀t∈Icc (0:ℝ) 1,
          |productGaussianAverage τ f (y,a+t)| ≤ G y ∧
          |deriv (fun s:ℝ=>productGaussianAverage τ f (y,a+s)) t| ≤ G y ∧
          |productGaussianAverage τ f (y,a+t)-productGaussianAverage τ f (y,a)| ≤ G y*t := by
  let A:=|a|+1
  let C:=Real.sqrt (normalRowSquare τ A)+Real.sqrt (normalDerivativeRowSquare τ A)
  let H:=normalFiberNorm f
  let U:=gaussianAverage τ H
  let G:=fun y=>C*U y
  have hsq : τ^2<1 := by nlinarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C:=add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hHm : Measurable H := by
    exact Real.continuous_sqrt.measurable.comp
      (hfM.stronglyMeasurable.pow 2).integral_prod_right'.measurable
  have hUm : Measurable U := by
    have hs : StronglyMeasurable (fun p:(Fin n→ℝ)×(Fin n→ℝ)=>
        H (fun j=>τ*p.1 j+Real.sqrt (1-τ^2)*p.2 j)) :=
      (hHm.comp (by fun_prop)).stronglyMeasurable
    exact hs.integral_prod_right'.measurable
  have hH:=normalFiberNorm_memLp_norm f hf
  have hU : eLpNorm U (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) ≤ eLpNorm H 2 (γFin n):=
    memLp_gaussian_average_l2_to_lq τ hτ hτ1 H hH.1
  have hUmLp : MemLp U (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n):=hU.trans_lt hH.1
  have hU0 y : 0 ≤ U y:=integral_nonneg fun _=>Real.sqrt_nonneg _
  refine ⟨G,hUm.const_mul C,fun y=>mul_nonneg hC (hU0 y),hUmLp.const_mul C,?_,?_⟩
  · change eLpNorm (C • U) _ _ ≤ _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_nonneg hC]
    exact (mul_le_mul' le_rfl hU).trans_eq (by rw [hH.2])
  · filter_upwards [ae_normalTrace_interval_bound_of_measurable hsq hA f hfM hf,
      ae_normalDerivativeTrace_interval_bound_of_measurable hsq hA f hfM hf,
      normalTrace_eq_product_ae_all_parameters hsq f hf,
      ae_hasDerivAt_actual_product_trace hsq f hf] with y hval hder heq hdiff
    have hb (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : |a+t| ≤ A := by
      calc
        _ ≤ |a|+|t|:=abs_add_le _ _
        _ ≤ A:=by rw [abs_of_nonneg ht.1]; exact add_le_add le_rfl ht.2
    have hd (t:ℝ) : HasDerivAt (fun s:ℝ=>productGaussianAverage τ f (y,a+s))
        (normalDerivativeTrace τ (a+t) f y) t := by
      simpa only [one_mul,mul_one,Function.comp_def,productGaussianAverage] using (hdiff (a+t)).comp t ((hasDerivAt_id t).const_add a)
    have hdb (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : |normalDerivativeTrace τ (a+t) f y| ≤ G y := by
      have hh:=hder (a+t) (hb t ht)
      rw [Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (hU0 y))
    refine ⟨fun t _=>(hd t).continuousAt.continuousWithinAt,?_⟩
    intro t ht
    refine ⟨?_,?_,?_⟩
    · have hh:=hval (a+t) (hb t ht)
      rw [heq (a+t),Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (hU0 y))
    · rw [(hd t).deriv]
      exact hdb t ht
    · have hh:=norm_image_sub_le_of_norm_deriv_le_segment' (a:=(0:ℝ)) (b:=1)
        (fun s _=>(hd s).hasDerivWithinAt)
        (fun s hs=>by simpa only [Real.norm_eq_abs] using hdb s ⟨hs.1,hs.2.le⟩) t ht
      simpa only [add_zero,sub_zero,Real.norm_eq_abs] using hh

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

/-- The exact orthogonal tangent coordinate equivalence. -/
def tangentCoordinateEquiv (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (Fin n→ℝ) ≃ᵐ tangentSpace w :=
  (MeasurableEquiv.toLp 2 (Fin n→ℝ)).trans e.symm.toMeasurableEquiv

@[simp] theorem tangentCoordinateEquiv_apply (w : E)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x : Fin n→ℝ) :
    tangentCoordinateEquiv w e x=tangentCoordinatesInverse w e x := rfl

/-- Actual ambient normal-tube estimate. The Gaussian law is on the real
comparison-plane tangent space; no ambient AE equality is restricted to a plane. -/
theorem ambient_normal_tube_envelope (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {τ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (a : ℝ)
    (f : E→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian E)) :
    ∃ G : tangentSpace w→ℝ, Measurable G ∧ (∀y,0 ≤ G y) ∧
      MemLp G (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (tangentSpace w)) ∧
      eLpNorm G (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (Real.sqrt (normalRowSquare τ (|a|+1))+
          Real.sqrt (normalDerivativeRowSquare τ (|a|+1)))*eLpNorm f 2 (stdGaussian E) ∧
      ∀ᵐ y : tangentSpace w ∂stdGaussian (tangentSpace w),
        ContinuousOn (fun t:ℝ=>ambientAverage τ f ((y:E)+(a+t) • w)) (Icc 0 1) ∧
        ∀t∈Icc (0:ℝ) 1,
          |ambientAverage τ f ((y:E)+(a+t) • w)| ≤ G y ∧
          |deriv (fun s:ℝ=>ambientAverage τ f ((y:E)+(a+s) • w)) t| ≤ G y ∧
          |ambientAverage τ f ((y:E)+(a+t) • w)-ambientAverage τ f ((y:E)+a • w)| ≤ G y*t := by
  let T:=tangentCoordinateEquiv w e
  let g:=fun z:(Fin n→ℝ)×ℝ=>f (coordinateReconstruct w e z)
  have hgM : Measurable g:=hfM.comp (by unfold coordinateReconstruct; fun_prop)
  have hgn:=coordinateReconstruct_memLp_and_norm w hw e f 2 hf
  obtain ⟨G,hGM,hG0,hGm,hGn,hG⟩:=product_normal_tube_envelope hτ hτ1 a g hgM hgn.1
  have hmap : (γFin n).map T=stdGaussian (tangentSpace w):=tangentCoordinatesInverse_map w e
  have hmp : MeasurePreserving T (γFin n) (stdGaussian (tangentSpace w)):=⟨T.measurable,hmap⟩
  let U:=G ∘ T.symm
  have hUM : Measurable U:=hGM.comp T.symm.measurable
  have hUn : eLpNorm U (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (tangentSpace w))=
      eLpNorm G (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin n) := by
    rw [←hmap,eLpNorm_map_measure hUM.aestronglyMeasurable T.measurable.aemeasurable]
    simp only [U,Function.comp_def,T.symm_apply_apply]
  refine ⟨U,hUM,fun y=>hG0 _,?_,?_,?_⟩
  · rw [←hmap]
    apply (memLp_map_measure_iff hUM.aestronglyMeasurable T.measurable.aemeasurable).mpr
    simpa only [U,Function.comp_def,T.symm_apply_apply] using hGm
  · rw [hUn]
    exact hGn.trans_eq (congrArg (fun x:ℝ≥0∞=>_ * x) hgn.2)
  · rw [←hmap,T.measurableEmbedding.ae_map_iff]
    filter_upwards [hG] with y hy
    have he (b:ℝ) : ambientAverage τ f (((T y:tangentSpace w):E)+b • w)=
        productGaussianAverage τ g (y,b) :=
      ambientAverage_coordinateReconstruct w hw e τ f hfM (y,b)
    simp only [U,Function.comp_apply,T.symm_apply_apply]
    simpa only [he] using hy

end Ambient
end NegativeVotingStructuredSwitchingNormal
