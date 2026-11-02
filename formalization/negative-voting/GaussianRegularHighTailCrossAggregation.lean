import GaussianRegularHighTailCrossPlane
import GaussianRegularTransportBound

/-! Weighted cross estimates retain the actual facet probability and the
rare-label L2 input norm. No label count or ambient dimension is introduced
by the Cauchy--Schwarz aggregation. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped ENNReal NNReal RealInnerProductSpace BigOperators
namespace NegativeVotingRegularHighTailCrossAggregation
open NegativeVotingNormalTrace NegativeVotingNormalTraceAllExponents
  NegativeVotingRegularHighTailCross NegativeVotingRegularHighTailCrossPlane
  NegativeVotingRegularCrossPlaneGeometry NegativeVotingRegularCrossPlaneOU
  NegativeVotingRegularTransportProducts NegativeVotingRegularTransportBound
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingPolynomialFacetLogBound
  NegativeVotingPolynomialDegree NegativeVotingDisintegration
  NegativeVotingActualFacetOUTrace NegativeVotingFan NegativeVotingWeightedFacet

theorem probability_loss_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hlog : -Real.log p ≤ q) : p^(1-1/q) ≤ Real.exp 1*p := by
  rw [Real.rpow_def_of_pos hp]
  have he : Real.log p*(1-1/q) ≤ Real.log p+1 := by
    have hh := (div_le_one hq).mpr hlog
    calc
      _ = Real.log p+(-Real.log p/q) := by ring
      _ ≤ _ := by linarith only [hh]
  calc
    _ ≤ Real.exp (Real.log p+1) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add,Real.exp_log hp];ring

/-- Two actual L2 factors on a set: one carries its probability factor,
the other an Lq envelope. The logarithmic exponent loses only exp(1). -/
theorem set_product_abs_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : Set X)
    (P Q : X→ℝ) (q C V : ℝ) (hq : 2 ≤ q) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hp : 0 < (μ F).toReal) (hlog : -Real.log (μ F).toReal ≤ q)
    (hP : MemLp P 2 (μ.restrict F)) (hQ : MemLp Q (ENNReal.ofReal q) μ)
    (hPsq : (∫ x in F,P x^2 ∂μ) ≤ (μ F).toReal*C^2)
    (hQnorm : eLpNorm Q (ENNReal.ofReal q) μ ≤ ENNReal.ofReal V) :
    |∫ x in F,P x*Q x ∂μ| ≤ Real.exp 1*(μ F).toReal*C*V := by
  have hq0 : 0 < q := by linarith
  have hQ2 : MemLp Q 2 μ := hQ.mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hq)
  have hqr : MemLp Q 2 (μ.restrict F) := hQ2.restrict F
  have hs := integral_mul_sq_le hP hqr
  have hH := set_integral_sq_le_l2q μ F (q/2) (by linarith) Q
    (by convert hQ using 1 <;> congr 1 <;> ring)
  have hnorm : (eLpNorm Q (ENNReal.ofReal q) μ).toReal ≤ V := by
    simpa only [ENNReal.toReal_ofReal hV] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hQnorm
  have hpow := pow_le_pow_left₀ (ENNReal.toReal_nonneg) hnorm 2
  have hQsq : (∫ x in F,Q x^2 ∂μ) ≤ V^2*(μ F).toReal^(1-2/q) := by
    have he : 2*(q/2)=q := by ring
    rw [he] at hH
    have hdiv : 1/(q/2)=2/q := by ring
    rw [hdiv] at hH
    exact hH.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le _))
  have hh := hs.trans (mul_le_mul hPsq hQsq (integral_nonneg fun _=>sq_nonneg _)
    (mul_nonneg hp.le (sq_nonneg C)))
  have hid : (μ F).toReal*(μ F).toReal^(1-2/q)=((μ F).toReal^(1-1/q))^2 := by
    calc
      _ = (μ F).toReal^(1:ℝ)*(μ F).toReal^(1-2/q) := by rw [Real.rpow_one]
      _ = (μ F).toReal^((1-1/q)*2) := by rw [←Real.rpow_add hp];congr 1;ring
      _ = _ := by rw [Real.rpow_mul hp.le,Real.rpow_two]
  have hbase := probability_loss_le (μ F).toReal q hp hq0 hlog
  have hbase2 := pow_le_pow_left₀ (Real.rpow_nonneg hp.le _) hbase 2
  have hupper : (∫ x in F,P x*Q x ∂μ)^2 ≤ (Real.exp 1*(μ F).toReal*C*V)^2 := by
    calc
      _ ≤ (μ F).toReal*C^2*(V^2*(μ F).toReal^(1-2/q)) := hh
      _ = ((μ F).toReal^(1-1/q))^2*(C*V)^2 := by
        calc
          _ = ((μ F).toReal*(μ F).toReal^(1-2/q))*(C*V)^2 := by ring
          _ = _ := by rw [hid]
      _ ≤ (Real.exp 1*(μ F).toReal)^2*(C*V)^2 :=
        mul_le_mul_of_nonneg_right hbase2 (sq_nonneg _)
      _ = _ := by ring
  nlinarith [sq_abs (∫ x in F,P x*Q x ∂μ),abs_nonneg (∫ x in F,P x*Q x ∂μ),
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le hp.le) hC) hV]

section Plane
variable {d n : ℕ}

theorem planeReconstruct_slice_map (w : FSC.Coord d) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (A : ℝ) :
    ((γFin n).prod (gaussianReal 0 1)).map (planeReconstruct w v e A)=FSC.sliceLaw w A := by
  rw [planeReconstruct_map w v hv e A,FSC.sliceLaw,gaussian_affine_slice_map w hw A]
  congr 1
  funext y
  exact add_comm _ _

/-- Actual degree-two score product on the current plane, paired with an
arbitrary Lq quotient. The probability factor remains linear after q absorbs
its logarithm. -/
theorem plane_scores_quotient_abs_le (w : FSC.Coord d) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A Ac m q V : ℝ) (hm : 1 ≤ m) (hq : 2 ≤ q) (hV : 0 ≤ V)
    (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hprob : m^(-4096:ℝ) ≤ (stdGaussian (tangentSpace w) F).toReal)
    (hlog : -Real.log (stdGaussian (tangentSpace w) F).toReal ≤ q)
    (hA : |A| ≤ Ac*Real.sqrt (1+Real.log m))
    (r t : FSC.Coord d) (b c : ℝ)
    (Q : (Fin n→ℝ)×ℝ→ℝ)
    (hQ : MemLp Q (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)))
    (hQnorm : eLpNorm Q (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1))≤ENNReal.ofReal V) :
    |∫ p in (coordinateReconstruct v e) ⁻¹' F,
        (linearScore r b (planeReconstruct w v e A p)*
          linearScore t c (planeReconstruct w v e A p))*Q p
        ∂(γFin n).prod (gaussianReal 0 1)| ≤
      8*Real.exp 1*(stdGaussian (tangentSpace w) F).toReal*
        Real.sqrt (quarticLogConstant Ac*(1+Real.log m)^4)*
        Real.sqrt (coefficientEnergy r b)*Real.sqrt (coefficientEnergy t c)*V := by
  let μ := (γFin n).prod (gaussianReal 0 1)
  let S := (coordinateReconstruct v e) ⁻¹' F
  let P : (Fin n→ℝ)×ℝ→ℝ := fun p=>linearScore r b (planeReconstruct w v e A p)*
    linearScore t c (planeReconstruct w v e A p)
  let K := quarticLogConstant Ac*(1+Real.log m)^4
  let C := 8*Real.sqrt K*Real.sqrt (coefficientEnergy r b)*Real.sqrt (coefficientEnergy t c)
  have hTm : Measurable (coordinateReconstruct v e) := by unfold coordinateReconstruct;fun_prop
  have hp : μ S=stdGaussian (tangentSpace w) F := by
    rw [←coordinateReconstruct_map v hv e,Measure.map_apply hTm hF]
    rfl
  have hp0 : 0 < (μ S).toReal := by
    rw [hp]
    exact (Real.rpow_pos_of_pos (by linarith : 0 < m) _).trans_le hprob
  have hK : 0 ≤ K := by unfold K quarticLogConstant;positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hC2 : C^2=64*K*coefficientEnergy r b*coefficientEnergy t c := by
    dsimp only [C]
    simp only [mul_pow,Real.sq_sqrt hK,Real.sq_sqrt (coefficientEnergy_nonneg _ _)]
    ring
  have hmap : MeasurePreserving (planeReconstruct w v e A) μ (FSC.sliceLaw w A) :=
    ⟨by unfold planeReconstruct doubleTangent;fun_prop,planeReconstruct_slice_map w hw v hv e A⟩
  letI : IsGaussian (FSC.sliceLaw w A) := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hPm : MemLp P 2 μ := (product_memLp_two (FSC.sliceLaw w A) r t b c).comp_measurePreserving hmap
  have hint : (∫ p in S,P p^2 ∂μ)=∫ y in F,
      (linearScore r b ((y:FSC.Coord d)+A • w)*linearScore t c ((y:FSC.Coord d)+A • w))^2
        ∂stdGaussian (tangentSpace w) := by
    rw [←coordinateReconstruct_map v hv e,setIntegral_map hF (by unfold linearScore;fun_prop) hTm.aemeasurable]
    rfl
  have hpoly := product_degree (reconstructLinear w (canonicalTangentCoordinates w)) r t b c
  have htrace := plane_integral_sq_log_m w hw (canonicalTangentCoordinates w)
    (fun x=>linearScore r b x*linearScore t c x) (by unfold linearScore;fun_prop)
    (polynomialSpace_mono (by norm_num : 2≤4) hpoly) A Ac m F hF hm hprob hA
  have hPsq : (∫ p in S,P p^2 ∂μ) ≤ (μ S).toReal*C^2 := by
    rw [hint,hp,hC2]
    have hh := mul_le_mul_of_nonneg_left (product_integral_sq_le r t b c)
      (show 0≤(stdGaussian (tangentSpace w) F).toReal*K from mul_nonneg ENNReal.toReal_nonneg hK)
    exact htrace.trans (by dsimp only [K] at hh ⊢;nlinarith only [hh])
  have hh := set_product_abs_le μ S P Q q C V hq hC hV hp0 (by rw [hp];exact hlog)
    (hPm.restrict S) hQ hPsq hQnorm
  rw [hp] at hh
  convert hh using 1 <;> dsimp only [P,C,K,μ,S] <;> ring

def quotientNormFactor (τ q A : ℝ) : ℝ :=
  Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2)*(2:ℝ)^(1/q)

theorem quotientNormFactor_nonneg (τ q A : ℝ) : 0 ≤ quotientNormFactor τ q A := by
  unfold quotientNormFactor
  positivity

theorem quotient_norm_le_of_input_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (τ q A V : ℝ) (hq : 0 < q) (hV : 0 ≤ V) (f : X→ℝ)
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (Q : Z→ℝ)
    (hQ : eLpNorm Q (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*(ENNReal.ofReal 2)^(1/q)*eLpNorm f 2 μ)
    (hf : eLpNorm f 2 μ ≤ ENNReal.ofReal V) :
    eLpNorm Q (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (quotientNormFactor τ q A*V) := by
  have hh := hQ.trans (mul_le_mul_right hf _)
  rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0≤(2:ℝ)) (by positivity : 0≤1/q),
    ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)] at hh
  exact hh

/-- The normal factor is the actual row-error score on the current facet.
This is the local quadratic-error mechanism, before taking absolute values. -/
theorem actual_odd_plane_cross_abs_le (w : FSC.Coord d) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1)
    (τ q A Ac m V ell : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hm : 1 ≤ m) (hV : 0 ≤ V) (hell : 0 < ell)
    (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (hprob : m^(-4096:ℝ)≤(stdGaussian (tangentSpace w) F).toReal)
    (hlog : -Real.log (stdGaussian (tangentSpace w) F).toReal≤q)
    (hA : |A|≤Ac*Real.sqrt (1+Real.log m))
    (r t : FSC.Coord d) (b k : ℝ)
    (f : FSC.Coord d→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (stdGaussian (FSC.Coord d)))
    (hfV : eLpNorm f 2 (stdGaussian (FSC.Coord d))≤ENNReal.ofReal V)
    (hodd : ∀ x,ambientAverage τ f
      (x-(2*inner ℝ (c • w+s • (v:FSC.Coord d)) x) • (c • w+s • (v:FSC.Coord d)))=
        -ambientAverage τ f x)
    (hcancel : ∀ y∈F,inner ℝ (c • w+s • (v:FSC.Coord d)) ((y:FSC.Coord d)+A • w)=
      -linearScore r b ((y:FSC.Coord d)+A • w)/ell) :
    |∫ y in F,linearScore t k ((y:FSC.Coord d)+A • w)*
        ambientAverage τ f ((y:FSC.Coord d)+A • w) ∂stdGaussian (tangentSpace w)| ≤
      8*Real.exp 1*(stdGaussian (tangentSpace w) F).toReal*
        Real.sqrt (quarticLogConstant Ac*(1+Real.log m)^4)*
        Real.sqrt (coefficientEnergy r b)*Real.sqrt (coefficientEnergy t k)*
        (quotientNormFactor τ q A*V)/ell := by
  obtain ⟨Q,hQm,hQ,hQnorm,hQeq⟩ := exists_actual_odd_plane_quotient w hw v hv e c s hcs
    τ q A hτ hq hqt f hfm hf hodd
  have hQb := quotient_norm_le_of_input_bound (stdGaussian (FSC.Coord d)) τ q A V
    (by linarith) hV f ((γFin n).prod (gaussianReal 0 1)) Q hQnorm hfV
  have hh := plane_scores_quotient_abs_le w hw v hv e A Ac m q (quotientNormFactor τ q A*V)
    hm hq (mul_nonneg (quotientNormFactor_nonneg _ _ _) hV) F hF hprob hlog hA r t b k Q hQ hQb
  have hTm : Measurable (coordinateReconstruct v e) := by unfold coordinateReconstruct;fun_prop
  let S := (coordinateReconstruct v e) ⁻¹' F
  have hS : MeasurableSet S := hF.preimage hTm
  have heq : (∫ y in F,linearScore t k ((y:FSC.Coord d)+A • w)*
      ambientAverage τ f ((y:FSC.Coord d)+A • w) ∂stdGaussian (tangentSpace w))=
      -(1/ell)*∫ p in S,(linearScore r b (planeReconstruct w v e A p)*
        linearScore t k (planeReconstruct w v e A p))*Q p ∂(γFin n).prod (gaussianReal 0 1) := by
    rw [←coordinateReconstruct_map v hv e,setIntegral_map hF
      (by exact (((show Measurable (fun y:tangentSpace w=>linearScore t k ((y:FSC.Coord d)+A • w)) by
        unfold linearScore;fun_prop).mul ((ambientAverage_measurable τ f hfm).comp (by fun_prop))).aestronglyMeasurable))
      hTm.aemeasurable,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hQeq,ae_restrict_mem hS] with p hp hpS
    have hc := hcancel (coordinateReconstruct v e p) hpS
    change inner ℝ (c • w+s • (v:FSC.Coord d)) (planeReconstruct w v e A p)=
      -linearScore r b (planeReconstruct w v e A p)/ell at hc
    change linearScore t k (planeReconstruct w v e A p)*
      ambientAverage τ f (planeReconstruct w v e A p)=_
    rw [hp,hc]
    ring
  rw [heq,abs_mul,abs_neg,abs_of_pos (one_div_pos.mpr hell)]
  convert mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hell.le) using 1 <;> ring

end Plane

section WinningFacets
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
open NegativeVotingFanHessian NegativeVotingFanJacobian

theorem reference_normal_on_current_facet (B R : ι→FSC.Coord d) (h : ι→ℝ)
    (i j : ι) (x : FSC.Coord d) (hx : x∈affineFacet B h i j) :
    inner ℝ (pairNormal R i j) x=
      -linearScore ((B i-R i)-(B j-R j)) (h i-h j) x/‖R i-R j‖ := by
  have hh := hx.1
  simp only [affineScore] at hh
  simp only [pairNormal,real_inner_smul_left,inner_sub_left,linearScore]
  have he : inner ℝ (R i) x-inner ℝ (R j) x=
    -(inner ℝ (B i) x-inner ℝ (R i) x-(inner ℝ (B j) x-inner ℝ (R j) x)+(h i-h j)) := by linarith
  rw [he]
  ring

/-- Literal winning-facet cross term, with the regular error factor and
the rare-source norm both retained. The only symmetry premise refers to
the actual final smoothed potential. -/
theorem surface_odd_cross_abs_le (B R Z : ι→FSC.Coord d) (h k : ι→ℝ)
    (i j : ι) (hB : B i≠B j) (hR : R i≠R j)
    (hdim : 2 ≤ Module.finrank ℝ (FSC.Coord d))
    (τ q Ac m V : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hm : 1 ≤ m) (hV : 0 ≤ V)
    (hprob : m^(-4096:ℝ) ≤ (stdGaussian (tangentSpace (pairNormal B i j))
      (intrinsicFacet B h i j)).toReal)
    (hlog : -Real.log (stdGaussian (tangentSpace (pairNormal B i j))
      (intrinsicFacet B h i j)).toReal ≤ q)
    (hA : |pairOffset B h i j| ≤ Ac*Real.sqrt (1+Real.log m))
    (f : FSC.Coord d→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (stdGaussian (FSC.Coord d)))
    (hfV : eLpNorm f 2 (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal V)
    (hodd : ∀ x,ambientAverage τ f
      (x-(2*inner ℝ (pairNormal R i j) x) • pairNormal R i j)=-ambientAverage τ f x) :
    |surfaceIntegral B h i j (fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ f x)| ≤
      8*Real.exp 1*facetWeight B h i j*Real.sqrt (quarticLogConstant Ac*(1+Real.log m)^4)*
        Real.sqrt (coefficientEnergy ((B i-R i)-(B j-R j)) (h i-h j))*
        Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j))*
        (quotientNormFactor τ q (pairOffset B h i j)*V)/‖R i-R j‖ := by
  have hw := pairNormal_norm B i j hB
  have hu := pairNormal_norm R i j hR
  obtain ⟨v,hv,c,s,hcs,huEq⟩ := exists_normal_frame (pairNormal B i j) (pairNormal R i j) hw hu hdim
  let e := canonicalTangentCoordinates v
  have hell : 0 < ‖R i-R j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hR)
  have hodd' : ∀ x,ambientAverage τ f
      (x-(2*inner ℝ (c • pairNormal B i j+s • (v:FSC.Coord d)) x) •
        (c • pairNormal B i j+s • (v:FSC.Coord d)))=-ambientAverage τ f x := by
    rw [←huEq]
    exact hodd
  have hcancel : ∀ y∈intrinsicFacet B h i j,
      inner ℝ (c • pairNormal B i j+s • (v:FSC.Coord d))
        ((y:FSC.Coord d)+pairOffset B h i j • pairNormal B i j)=
      -linearScore ((B i-R i)-(B j-R j)) (h i-h j)
        ((y:FSC.Coord d)+pairOffset B h i j • pairNormal B i j)/‖R i-R j‖ := by
    intro y hy
    rw [←huEq]
    exact reference_normal_on_current_facet B R h i j _ hy
  have hh := actual_odd_plane_cross_abs_le (pairNormal B i j) hw v hv e c s hcs
    τ q (pairOffset B h i j) Ac m V ‖R i-R j‖ hτ hq hqt hm hV hell
    (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j).measurableSet
    hprob hlog hA ((B i-R i)-(B j-R j)) (Z i-Z j) (h i-h j) (k i-k j)
    f hfm hf hfV hodd' hcancel
  have hd : 0 ≤ gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖ :=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
  have hchart : Measurable (facetChart B h i j) := by unfold facetChart;fun_prop
  unfold surfaceIntegral
  rw [sliceLaw_eq_facetChart_map B h i j hB,
    setIntegral_map (f:=fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ f x)
      (isClosed_affineFacet B h i j).measurableSet
      (((show Measurable (linearScore (Z i-Z j) (k i-k j)) by unfold linearScore;fun_prop).mul
        (ambientAverage_measurable τ f hfm)).aestronglyMeasurable) hchart.aemeasurable,
    abs_mul,abs_of_nonneg hd]
  convert mul_le_mul_of_nonneg_left hh hd using 1
  · rfl
  · simp only [facetWeight]
    ring

/-- The finite winning-facet aggregation has no factor from the number of
labels or ambient coordinates. Its coefficient hypotheses are the actual
per-facet source norms and normal-gap bounds, not the desired final estimate. -/
theorem ordered_cross_abs_le (B R Z : ι→FSC.Coord d) (h k : ι→ℝ)
    (hB : Function.Injective B) (hR : Function.Injective R)
    (hdim : 2 ≤ Module.finrank ℝ (FSC.Coord d))
    (τ q Ac m V J ell degree : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hm : 1 ≤ m) (hV : 0 ≤ V) (hJ : 0 ≤ J) (hell : 0 < ell) (hdegree0 : 0 ≤ degree)
    (hdegree : ∀ i,∑ j,facetWeight B h i j ≤ degree)
    (hellR : ∀ i j,i≠j→ell ≤ ‖R i-R j‖)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (hlog : ∀ i j,i≠j→-Real.log
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal ≤ q)
    (hA : ∀ i j,i≠j→|pairOffset B h i j| ≤ Ac*Real.sqrt (1+Real.log m))
    (hJnorm : ∀ i j,i≠j→quotientNormFactor τ q (pairOffset B h i j) ≤ J)
    (f : ι→ι→FSC.Coord d→ℝ) (hfm : ∀ i j,Measurable (f i j))
    (hf : ∀ i j,MemLp (f i j) 2 (stdGaussian (FSC.Coord d)))
    (hfV : ∀ i j,i≠j→eLpNorm (f i j) 2 (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal V)
    (hodd : ∀ i j,i≠j→∀ x,ambientAverage τ (f i j)
      (x-(2*inner ℝ (pairNormal R i j) x) • pairNormal R i j)=-ambientAverage τ (f i j) x)
    (e v : FSC.Coord d) (b c : ℝ) :
    |∑ i,∑ j,surfaceIntegral B h i j
      (fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ (f i j) x)| ≤
      32*Real.exp 1*degree*Real.sqrt (quarticLogConstant Ac*(1+Real.log m)^4)*(J*V/ell)*
        Real.sqrt (rowScoreEnergy (fun i=>B i-R i) h e b)*Real.sqrt (rowScoreEnergy Z k v c) := by
  let K := Real.sqrt (quarticLogConstant Ac*(1+Real.log m)^4)
  let T := 8*Real.exp 1*K*(J*V/ell)
  have hT : 0 ≤ T := by dsimp [T,K];positivity
  have heach (i j : ι) :
      |surfaceIntegral B h i j (fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ (f i j) x)| ≤
        T*(facetWeight B h i j*Real.sqrt (coefficientEnergy ((B i-R i)-(B j-R j)) (h i-h j))*
          Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j))) := by
    by_cases hij : i=j
    · subst j
      simp [surfaceIntegral_diagonal,facetWeight_self]
    have hh := surface_odd_cross_abs_le B R Z h k i j (hB.ne hij) (hR.ne hij) hdim
      τ q Ac m V hτ hq hqt hm hV (hprob i j hij) (hlog i j hij) (hA i j hij)
      (f i j) (hfm i j) (hf i j) (hfV i j hij) (hodd i j hij)
    have hratio : quotientNormFactor τ q (pairOffset B h i j)*V/‖R i-R j‖ ≤ J*V/ell := by
      exact div_le_div₀ (mul_nonneg hJ hV)
        (mul_le_mul_of_nonneg_right (hJnorm i j hij) hV) hell (hellR i j hij)
    have hw : 0 ≤ facetWeight B h i j := facetWeight_nonneg B h i j
    have hc := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 8*Real.exp 1*facetWeight B h i j*K*
        Real.sqrt (coefficientEnergy ((B i-R i)-(B j-R j)) (h i-h j))*
          Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j)) by positivity)
    exact hh.trans (by convert hc using 1 <;> dsimp only [T,K] <;> ring)
  have habs : |∑ i,∑ j,surfaceIntegral B h i j
      (fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ (f i j) x)| ≤
      ∑ i,∑ j,|surfaceIntegral B h i j
        (fun x=>linearScore (Z i-Z j) (k i-k j) x*ambientAverage τ (f i j) x)| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _=>Finset.abs_sum_le_sum_abs _ _)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) fun j _=>heach i j
  have hc := facet_sqrt_coefficient_le B (fun i=>B i-R i) Z h k degree hdegree0 hdegree e v b c
  have hfinal := mul_le_mul_of_nonneg_left hc hT
  calc
    _ ≤ _ := habs.trans hsum
    _ = T*(∑ i,∑ j,facetWeight B h i j*
        Real.sqrt (coefficientEnergy ((B i-R i)-(B j-R j)) (h i-h j))*
          Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j))) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := by convert hfinal using 1 <;> dsimp only [T,K] <;> ring

end WinningFacets
end NegativeVotingRegularHighTailCrossAggregation
