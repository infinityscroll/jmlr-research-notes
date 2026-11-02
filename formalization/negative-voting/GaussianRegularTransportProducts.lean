import GaussianRegularReferenceJumpBound

/-! Dimension-free polynomial product estimates used after regular-facet
cancellation, and Cauchy--Schwarz with the actual Gaussian surface weight. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingRegularTransportProducts
open NegativeVotingFan NegativeVotingFanHessian NegativeVotingGlobalTensorTransport
  NegativeVotingFanMassSecondDerivative NegativeVotingFanJacobian
  NegativeVotingPolynomialDegree NegativeVotingPolynomialFacetTrace
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingPolynomialFacetLogBound
  NegativeVotingQuadraticBulkNorm NegativeVotingQuadraticTensorBulkNorm
  NegativeVotingTensorFacetAggregation NegativeVotingDisintegration
  NegativeVotingWeightedFacet NegativeVotingAffineLogMassBound GaussianFin
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def linearScore (v : FSC.Coord d) (c : ℝ) (x : FSC.Coord d) : ℝ := inner ℝ v x+c
def coefficientEnergy (v : FSC.Coord d) (c : ℝ) : ℝ := ‖v‖^2+c^2
def velocityEnergy (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : ℝ :=
  (operatorHilbertSchmidt A)^2+‖z‖^2

theorem coefficientEnergy_nonneg (v : FSC.Coord d) (c : ℝ) : 0 ≤ coefficientEnergy v c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem velocityEnergy_nonneg (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    0 ≤ velocityEnergy A z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem affine_mul_degree {κ : Type*} [Fintype κ] {k : ℕ} {f : (κ→ℝ)→ℝ}
    (hf : f∈polynomialSpace k) (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v : FSC.Coord d) (c : ℝ) :
    (fun x=>linearScore v c (R x)*f x)∈polynomialSpace (k+1) := by
  convert (polynomialSpace (k+1)).add_mem (inner_mul_mem hf R v)
    ((polynomialSpace (k+1)).smul_mem c (polynomialSpace_mono (by omega) hf)) using 1
  funext x
  simp only [linearScore,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem product_degree {κ : Type*} [Fintype κ]
    (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v s : FSC.Coord d) (c b : ℝ) :
    (fun x=>linearScore v c (R x)*linearScore s b (R x))∈polynomialSpace 2 :=
  affine_mul_degree (affine_score_mem R s b) R v c

theorem product_massBulk_degree {κ : Type*} [Fintype κ]
    (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v s : FSC.Coord d) (c b : ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x=>linearScore v c (R x)*linearScore s b (R x)*massBulk A z (R x))∈polynomialSpace 4 := by
  have hm : (fun x=>massBulk A z (R x))∈polynomialSpace 2 := massBulk_expression_mem R A z
  convert affine_mul_degree (affine_mul_degree hm R s b) R v c using 1
  funext x
  ring

theorem linearScore_integral_sq_le (v : FSC.Coord d) (c : ℝ) :
    (∫ x,linearScore v c x^2 ∂stdGaussian (FSC.Coord d)) ≤ 2*coefficientEnergy v c :=
  affine_score_integral_sq_le v c

theorem product_integral_sq_le (v s : FSC.Coord d) (c b : ℝ) :
    (∫ x,(linearScore v c x*linearScore s b x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      64*coefficientEnergy v c*coefficientEnergy s b := by
  let f : (Fin d→ℝ)→ℝ := fun x=>linearScore v c (WithLp.toLp 2 x)
  let g : (Fin d→ℝ)→ℝ := fun x=>linearScore s b (WithLp.toLp 2 x)
  have hf : f∈polynomialSpace 1 := affine_score_mem toEuclideanLinear v c
  have hg : g∈polynomialSpace 1 := affine_score_mem toEuclideanLinear s b
  have hfg : (fun x=>f x*g x)∈polynomialSpace 2 := product_degree toEuclideanLinear v s c b
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  have hfe : norm2 f^2 ≤ 2*coefficientEnergy v c := by
    rw [norm2_sq (polynomial_memLp hf)]
    have hh := linearScore_integral_sq_le v c
    rw [←hmap,integral_map (by fun_prop) (by unfold linearScore; fun_prop)] at hh
    exact hh
  have hge : norm2 g^2 ≤ 2*coefficientEnergy s b := by
    rw [norm2_sq (polynomial_memLp hg)]
    have hh := linearScore_integral_sq_le s b
    rw [←hmap,integral_map (by fun_prop) (by unfold linearScore; fun_prop)] at hh
    exact hh
  have hp := pow_le_pow_left₀ (norm2_nonneg (fun x=>f x*g x)) (norm2_product_le hf hg) 2
  norm_num only at hp
  have he := mul_le_mul hfe hge (sq_nonneg _) (mul_nonneg (by norm_num) (coefficientEnergy_nonneg _ _))
  rw [←hmap,integral_map (by fun_prop) (by unfold linearScore; fun_prop)]
  change (∫ x,(f x*g x)^2 ∂γFin d) ≤ _
  rw [←norm2_sq (polynomial_memLp hfg)]
  nlinarith only [hp,he]

theorem product_massBulk_integral_sq_le (v s : FSC.Coord d) (c b : ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (∫ x,(linearScore v c x*linearScore s b x*massBulk A z x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      131072*coefficientEnergy v c*coefficientEnergy s b*velocityEnergy A z := by
  let f : (Fin d→ℝ)→ℝ := fun x=>linearScore v c (WithLp.toLp 2 x)*linearScore s b (WithLp.toLp 2 x)
  let g : (Fin d→ℝ)→ℝ := fun x=>massBulk A z (WithLp.toLp 2 x)
  have hf : f∈polynomialSpace 2 := product_degree toEuclideanLinear v s c b
  have hg : g∈polynomialSpace 2 := massBulk_expression_mem toEuclideanLinear A z
  have hfg : (fun x=>f x*g x)∈polynomialSpace 4 := product_massBulk_degree toEuclideanLinear v s c b A z
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  have hfe : norm2 f^2 ≤ 64*coefficientEnergy v c*coefficientEnergy s b := by
    rw [norm2_sq (polynomial_memLp hf)]
    have hh := product_integral_sq_le v s c b
    rw [←hmap,integral_map (by fun_prop) (by unfold linearScore; fun_prop)] at hh
    exact hh
  have hge : norm2 g^2 ≤ 8*velocityEnergy A z := by
    rw [norm2_sq (polynomial_memLp hg)]
    have hh := massBulk_integral_sq_le A z
    rw [←hmap,integral_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  have hp := pow_le_pow_left₀ (norm2_nonneg (fun x=>f x*g x)) (norm2_product_le hf hg) 2
  norm_num only at hp
  have he := mul_le_mul hfe hge (sq_nonneg _) (by
    exact mul_nonneg (mul_nonneg (by norm_num) (coefficientEnergy_nonneg _ _)) (coefficientEnergy_nonneg _ _))
  rw [←hmap,integral_map (by fun_prop) (by unfold linearScore massBulk; fun_prop)]
  change (∫ x,(f x*g x)^2 ∂γFin d) ≤ _
  rw [←norm2_sq (polynomial_memLp hfg)]
  nlinarith only [hp,he]

theorem linearScore_memLp (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v : FSC.Coord d) (c : ℝ) (p : ℝ≥0∞) (hp : p≠∞) : MemLp (linearScore v c) p μ :=
  ((IsGaussian.memLp_id μ p hp).const_inner (𝕜:=ℝ) v).add (memLp_const c)

private instance holder442 : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
private instance holder884 : ENNReal.HolderTriple (8:ℝ≥0∞) 8 4 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩

theorem product_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v s : FSC.Coord d) (c b : ℝ) : MemLp (fun x=>linearScore v c x*linearScore s b x) 2 μ :=
  (linearScore_memLp μ v c 4 (by norm_num)).mul (linearScore_memLp μ s b 4 (by norm_num))

theorem product_massBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v s : FSC.Coord d) (c b : ℝ) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    MemLp (fun x=>linearScore v c x*linearScore s b x*massBulk A z x) 2 μ := by
  have hf : MemLp (fun x=>linearScore v c x*linearScore s b x) 4 μ :=
    (linearScore_memLp μ v c 8 (by norm_num)).mul (linearScore_memLp μ s b 8 (by norm_num))
  have hg : MemLp (massBulk A z) 4 μ := by
    convert (quadraticScore_memLp_four μ A).add (linearScore_memLp μ z 0 4 (by norm_num)) using 1
    funext x
    simp only [massBulk,quadraticScore,linearScore,Pi.add_apply,add_zero]
    ring
  exact hf.mul hg

theorem surface_polynomial_sq_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (f : FSC.Coord d→ℝ) (hf : Continuous f)
    (hpoly : (fun x=>f (reconstructLinear (pairNormal B i j)
      (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4)
    (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    surfaceIntegral B h i j (fun x=>f x^2) ≤
      facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4*
        ∫ x,f x^2 ∂stdGaussian (FSC.Coord d) := by
  have hb := plane_integral_sq_log_m _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates (pairNormal B i j)) f hf hpoly
    (pairOffset B h i j) a m (intrinsicFacet B h i j)
    (isClosed_intrinsicFacet B h i j).measurableSet hm hprob ha
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  unfold surfaceIntegral
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    setIntegral_map (isClosed_affineFacet B h i j).measurableSet
      (by fun_prop) hmChart.aemeasurable]
  have hc : 0 ≤ gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖ :=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
  convert mul_le_mul_of_nonneg_left hb hc using 1
  · rfl
  · simp only [facetWeight]; ring

/-- The exact surface normalization is retained in Cauchy--Schwarz. -/
theorem surface_product_abs_le (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (f g : FSC.Coord d→ℝ)
    (hf : MemLp f 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hg : MemLp g 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    |surfaceIntegral B h i j (fun x=>f x*g x)| ≤
      Real.sqrt (surfaceIntegral B h i j (fun x=>f x^2))*
        Real.sqrt (surfaceIntegral B h i j (fun x=>g x^2)) := by
  let c := gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖
  have hc : 0 ≤ c := div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
  have hb := mul_le_mul_of_nonneg_left
    (abs_integral_mul_le_sqrt (hf.restrict (affineFacet B h i j)) (hg.restrict (affineFacet B h i j))) hc
  unfold surfaceIntegral
  rw [abs_mul,abs_of_nonneg hc]
  refine hb.trans_eq ?_
  rw [Real.sqrt_mul hc,Real.sqrt_mul hc]
  calc
    _ = (Real.sqrt c)^2*(Real.sqrt (∫ x in affineFacet B h i j,f x^2
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))*
      Real.sqrt (∫ x in affineFacet B h i j,g x^2
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) := by rw [Real.sq_sqrt hc]
    _ = _ := by ring

theorem surface_product_abs_le_bounds
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (f g : FSC.Coord d→ℝ)
    (hf : MemLp f 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hg : MemLp g 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (w F G : ℝ) (hw : 0 ≤ w) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfb : surfaceIntegral B h i j (fun x=>f x^2) ≤ w*F)
    (hgb : surfaceIntegral B h i j (fun x=>g x^2) ≤ w*G) :
    |surfaceIntegral B h i j (fun x=>f x*g x)| ≤ w*Real.sqrt F*Real.sqrt G := by
  refine (surface_product_abs_le B h i j f g hf hg).trans ?_
  calc
    _ ≤ Real.sqrt (w*F)*Real.sqrt (w*G) :=
      mul_le_mul (Real.sqrt_le_sqrt hfb) (Real.sqrt_le_sqrt hgb)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hw,Real.sqrt_mul hw]
      calc
        _ = (Real.sqrt w)^2*(Real.sqrt F*Real.sqrt G) := by ring
        _ = _ := by rw [Real.sq_sqrt hw]; ring

theorem surface_polynomial_product_abs_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (f g : FSC.Coord d→ℝ) (hfc : Continuous f) (hgc : Continuous g)
    (hfpoly : (fun x=>f (reconstructLinear (pairNormal B i j)
      (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4)
    (hgpoly : (fun x=>g (reconstructLinear (pairNormal B i j)
      (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4)
    (hf : MemLp f 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hg : MemLp g 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (F G : ℝ) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfe : (∫ x,f x^2 ∂stdGaussian (FSC.Coord d)) ≤ F^2)
    (hge : (∫ x,g x^2 ∂stdGaussian (FSC.Coord d)) ≤ G^2)
    (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    |surfaceIntegral B h i j (fun x=>f x*g x)| ≤
      facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4*F*G := by
  let w := facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4
  have hw : 0 ≤ w := mul_nonneg (mul_nonneg (facetWeight_nonneg B h i j)
    (by unfold quarticLogConstant; positivity)) (by positivity)
  have hfb := (surface_polynomial_sq_le B h i j hij f hfc hfpoly a m hm hprob ha).trans
    (mul_le_mul_of_nonneg_left hfe hw)
  have hgb := (surface_polynomial_sq_le B h i j hij g hgc hgpoly a m hm hprob ha).trans
    (mul_le_mul_of_nonneg_left hge hw)
  have hh := surface_product_abs_le_bounds B h i j f g hf hg w (F^2) (G^2)
    hw (sq_nonneg F) (sq_nonneg G) hfb hgb
  simpa only [Real.sqrt_sq hF,Real.sqrt_sq hG,w] using hh

/-- Three affine factors are paired as degrees one and two. -/
theorem surface_three_scores_abs_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (v s r : FSC.Coord d) (c b q a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    |surfaceIntegral B h i j (fun x=>linearScore v c x*(linearScore s b x*linearScore r q x))| ≤
      16*(facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4)*
        Real.sqrt (coefficientEnergy v c)*Real.sqrt (coefficientEnergy s b)*Real.sqrt (coefficientEnergy r q) := by
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hfe : (∫ x,linearScore v c x^2 ∂stdGaussian (FSC.Coord d)) ≤
      (2*Real.sqrt (coefficientEnergy v c))^2 := by
    rw [mul_pow,Real.sq_sqrt (coefficientEnergy_nonneg v c)]
    have hh := linearScore_integral_sq_le v c
    nlinarith [coefficientEnergy_nonneg v c]
  have hge : (∫ x,(linearScore s b x*linearScore r q x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      (8*Real.sqrt (coefficientEnergy s b)*Real.sqrt (coefficientEnergy r q))^2 := by
    simpa only [mul_pow,Real.sq_sqrt (coefficientEnergy_nonneg s b),
      Real.sq_sqrt (coefficientEnergy_nonneg r q),show (8:ℝ)^2=64 by norm_num] using product_integral_sq_le s r b q
  have hh := surface_polynomial_product_abs_le B h i j hij
    (linearScore v c) (fun x=>linearScore s b x*linearScore r q x)
    (by unfold linearScore; fun_prop) (by unfold linearScore; fun_prop)
    (polynomialSpace_mono (by decide : 1≤4) (affine_score_mem _ v c))
    (polynomialSpace_mono (by decide : 2≤4) (product_degree _ s r b q))
    (linearScore_memLp μ v c 2 (by norm_num)) (product_memLp_two μ s r b q)
    _ _ (by positivity) (by positivity) hfe hge a m hm hprob ha
  convert hh using 1 <;> ring

/-- The divergence factor is kept centered. Its energy costs only HS plus
shift energy, even when the trace of the velocity matrix is large. -/
theorem surface_three_scores_massBulk_abs_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (v s r : FSC.Coord d) (c b q : ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    |surfaceIntegral B h i j (fun x=>linearScore v c x*
      (linearScore s b x*linearScore r q x*massBulk A z x))| ≤
      1024*(facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4)*
        Real.sqrt (coefficientEnergy v c)*Real.sqrt (coefficientEnergy s b)*
          Real.sqrt (coefficientEnergy r q)*Real.sqrt (velocityEnergy A z) := by
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hfe : (∫ x,linearScore v c x^2 ∂stdGaussian (FSC.Coord d)) ≤
      (2*Real.sqrt (coefficientEnergy v c))^2 := by
    rw [mul_pow,Real.sq_sqrt (coefficientEnergy_nonneg v c)]
    have hh := linearScore_integral_sq_le v c
    nlinarith [coefficientEnergy_nonneg v c]
  have hge : (∫ x,(linearScore s b x*linearScore r q x*massBulk A z x)^2
      ∂stdGaussian (FSC.Coord d)) ≤
      (512*Real.sqrt (coefficientEnergy s b)*Real.sqrt (coefficientEnergy r q)*
        Real.sqrt (velocityEnergy A z))^2 := by
    simp only [mul_pow,Real.sq_sqrt (coefficientEnergy_nonneg s b),
      Real.sq_sqrt (coefficientEnergy_nonneg r q),Real.sq_sqrt (velocityEnergy_nonneg A z)]
    have hh := product_massBulk_integral_sq_le s r b q A z
    simp only [mul_pow] at hh
    norm_num only [show (512:ℝ)^2=262144 by norm_num]
    nlinarith only [hh,mul_nonneg (mul_nonneg (coefficientEnergy_nonneg s b)
      (coefficientEnergy_nonneg r q)) (velocityEnergy_nonneg A z)]
  have hh := surface_polynomial_product_abs_le B h i j hij
    (linearScore v c) (fun x=>linearScore s b x*linearScore r q x*massBulk A z x)
    (by unfold linearScore; fun_prop) (by unfold linearScore massBulk; fun_prop)
    (polynomialSpace_mono (by decide : 1≤4) (affine_score_mem _ v c))
    (product_massBulk_degree _ s r b q A z)
    (linearScore_memLp μ v c 2 (by norm_num)) (product_massBulk_memLp_two μ s r b q A z)
    _ _ (by positivity) (by positivity) hfe hge a m hm hprob ha
  convert hh using 1 <;> ring

end NegativeVotingRegularTransportProducts
