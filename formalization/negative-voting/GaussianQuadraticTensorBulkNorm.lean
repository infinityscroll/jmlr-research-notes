import GaussianQuadraticBulkNorm

/-! Hilbert--Schmidt control of the centered quadratic tensor test before
coordinate summation. These bounds have no ambient dimension factor. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal
open NegativeVotingQuadraticBulkNorm NegativeVotingPolynomialDegree
open NegativeVotingPolynomialFacetTrace NegativeVotingPolynomialFacetGeometricTrace
open NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl NegativeVotingAffineOperatorDerivative
open GaussianFin

namespace NegativeVotingQuadraticTensorBulkNorm
variable {d : ℕ}

def tensorBulk (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z x : FSC.Coord d) : ℝ :=
  quadraticScore U x * (inner ℝ x (A x)+inner ℝ z x-
    LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)-2*inner ℝ (U x) (A x+z)

/-- The trace pairing is bounded by the product of the two actual HS norms. -/
theorem trace_adjoint_comp_abs_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    |LinearMap.trace ℝ (FSC.Coord d) (U.adjoint.comp A).toLinearMap| ≤
      operatorHilbertSchmidt U*operatorHilbertSchmidt A := by
  have he : LinearMap.trace ℝ (FSC.Coord d) (U.adjoint.comp A).toLinearMap =
      ∑ j:Fin d, inner ℝ (U (EuclideanSpace.basisFun (Fin d) ℝ j))
        (A (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
    rw [←basis_trace_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,real_inner_comm]
  rw [he]
  calc
    _ ≤ ∑ j:Fin d, |inner ℝ (U (EuclideanSpace.basisFun (Fin d) ℝ j))
        (A (EuclideanSpace.basisFun (Fin d) ℝ j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j:Fin d, ‖U (EuclideanSpace.basisFun (Fin d) ℝ j)‖*
        ‖A (EuclideanSpace.basisFun (Fin d) ℝ j)‖ :=
      Finset.sum_le_sum (fun _ _=>abs_real_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ j:Fin d,‖U (EuclideanSpace.basisFun (Fin d) ℝ j)‖^2)*
        Real.sqrt (∑ j:Fin d,‖A (EuclideanSpace.basisFun (Fin d) ℝ j)‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [←operatorHilbertSchmidt_sq,←operatorHilbertSchmidt_sq,
        Real.sqrt_sq (operatorHilbertSchmidt_nonneg _),Real.sqrt_sq (operatorHilbertSchmidt_nonneg _)]

theorem adjoint_comp_HS_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    operatorHilbertSchmidt (U.adjoint.comp A) ≤
      operatorHilbertSchmidt U*operatorHilbertSchmidt A := by
  exact (operatorHilbertSchmidt_comp_le U.adjoint A).trans
    (mul_le_mul_of_nonneg_right
      (by simpa only [LinearIsometryEquiv.norm_map] using operator_norm_le_HilbertSchmidt U)
      (operatorHilbertSchmidt_nonneg A))

theorem norm2_inner_linear_maps_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    norm2 (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x))) ≤
      3*operatorHilbertSchmidt U*operatorHilbertSchmidt A := by
  let T := U.adjoint.comp A
  have he : (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x))) =
      fun x=>quadraticScore T (WithLp.toLp 2 x)+LinearMap.trace ℝ (FSC.Coord d) T.toLinearMap := by
    funext x
    simp only [quadraticScore,T,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right,sub_add_cancel]
  rw [he]
  have hh := norm2_add_le (polynomial_memLp (quadraticScore_degree T))
    (memLp_const (LinearMap.trace ℝ (FSC.Coord d) T.toLinearMap))
  rw [norm2_const] at hh
  have hq := norm2_quadraticScore_le T
  have ht := trace_adjoint_comp_abs_le U A
  have hHS := adjoint_comp_HS_le U A
  nlinarith

theorem inner_field_degree (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x)+z))
      ∈ polynomialSpace 2 := by
  have hh := (polynomialSpace 2).add_mem
    (quadratic_form_mem (toEuclideanLinear (d:=d)) (U.adjoint.comp A))
    (polynomialSpace_mono (by decide : 1≤2)
      (inner_mem (toEuclideanLinear (d:=d)) (U.adjoint z)))
  convert hh using 1
  funext x
  simp only [Pi.add_apply,toEuclideanLinear,LinearMap.coe_mk,AddHom.coe_mk,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left,inner_add_right,real_inner_comm]

theorem norm2_inner_field_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    norm2 (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x)+z)) ≤
      3*operatorHilbertSchmidt U*operatorHilbertSchmidt A+operatorHilbertSchmidt U*‖z‖ := by
  have hq : MemLp (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x))
      (A (WithLp.toLp 2 x))) 2 (γFin d) := by
    have hh := polynomial_memLp (quadratic_form_mem (toEuclideanLinear (d:=d)) (U.adjoint.comp A))
    simpa only [toEuclideanLinear,LinearMap.coe_mk,AddHom.coe_mk,γFin,
      OAI.MinUncut.GaussianHermite.γpi,Gaussian1D.γ,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right] using hh
  have hl : MemLp (fun x : Fin d→ℝ => inner ℝ (U.adjoint z) (WithLp.toLp 2 x)) 2 (γFin d) :=
    polynomial_memLp (inner_mem (toEuclideanLinear (d:=d)) (U.adjoint z))
  have he : (fun x : Fin d→ℝ => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x)+z)) =
      fun x => inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x))+
        inner ℝ (U.adjoint z) (WithLp.toLp 2 x) := by
    funext x
    simp only [inner_add_right,ContinuousLinearMap.adjoint_inner_left,real_inner_comm]
  rw [he]
  refine (norm2_add_le hq hl).trans (add_le_add (norm2_inner_linear_maps_le U A) ?_)
  rw [norm2_inner]
  exact (U.adjoint.le_opNorm z).trans (mul_le_mul_of_nonneg_right
    (by simpa only [LinearIsometryEquiv.norm_map] using operator_norm_le_HilbertSchmidt U) (norm_nonneg z))

theorem norm2_const_mul (c : ℝ) (f : (Fin d→ℝ)→ℝ) :
    norm2 (fun x=>c*f x) = |c| * norm2 f := by
  unfold norm2
  change (eLpNorm (c • f) 2 (γFin d)).toReal = _
  rw [eLpNorm_const_smul]
  simp [ENNReal.toReal_mul,Real.norm_eq_abs]

theorem norm2_tensorBulk_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    norm2 (fun x : Fin d→ℝ => tensorBulk U A z (WithLp.toLp 2 x)) ≤
      72*operatorHilbertSchmidt U*(operatorHilbertSchmidt A+‖z‖) := by
  let q : (Fin d→ℝ)→ℝ := fun x=>quadraticScore U (WithLp.toLp 2 x)
  let s : (Fin d→ℝ)→ℝ := fun x=>inner ℝ (WithLp.toLp 2 x) (A (WithLp.toLp 2 x))+
    inner ℝ z (WithLp.toLp 2 x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap
  let t : (Fin d→ℝ)→ℝ := fun x=>inner ℝ (U (WithLp.toLp 2 x)) (A (WithLp.toLp 2 x)+z)
  have hq : q∈polynomialSpace 2 := quadraticScore_degree U
  have hs : s∈polynomialSpace 2 := massBulk_expression_mem (toEuclideanLinear (d:=d)) A z
  have ht : t∈polynomialSpace 2 := inner_field_degree U A z
  have hqs : MemLp (fun x=>q x*s x) 2 (γFin d) := by
    haveI : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
      norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
    exact (polynomial_memLp_four hq).mul (polynomial_memLp_four hs)
  have h2t : MemLp (fun x=>2*t x) 2 (γFin d) := (polynomial_memLp ht).const_mul 2
  have hprod := norm2_product_le hq hs
  norm_num only at hprod
  have hprod' : norm2 (fun x=>q x*s x) ≤
      16*(2*operatorHilbertSchmidt U)*(2*operatorHilbertSchmidt A+‖z‖) :=
    hprod.trans (mul_le_mul (mul_le_mul_of_nonneg_left (norm2_quadraticScore_le U) (by norm_num))
      (norm2_massBulk_expression_le A z) (norm2_nonneg s) (by positivity [operatorHilbertSchmidt_nonneg U]))
  have hsum := norm2_sub_le hqs h2t
  rw [norm2_const_mul] at hsum
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at hsum
  have htbd := norm2_inner_field_le U A z
  change norm2 (fun x=>q x*s x-2*t x) ≤ _
  refine hsum.trans ?_
  have hU := operatorHilbertSchmidt_nonneg U
  have hA := operatorHilbertSchmidt_nonneg A
  nlinarith [mul_nonneg hU hA,mul_nonneg hU (norm_nonneg z)]

section Degree
variable {κ : Type*} [Fintype κ]

theorem quadratic_form_mul_mem {k : ℕ} {f : (κ→ℝ)→ℝ}
    (hf : f∈polynomialSpace k) (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (fun x=>inner ℝ (R x) (A (R x))*f x) ∈ polynomialSpace (k+2) := by
  have hh := (polynomialSpace (k+2)).sum_mem (fun j (_:j∈Finset.univ) =>
    inner_mul_mem (inner_mul_mem hf R (EuclideanSpace.basisFun (Fin d) ℝ j))
      R (A (EuclideanSpace.basisFun (Fin d) ℝ j)))
  convert hh using 1
  funext x
  simp only [Finset.sum_apply]
  rw [←basis_quadratic_sum A (R x),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mass_expression_mul_mem {k : ℕ} {f : (κ→ℝ)→ℝ}
    (hf : f∈polynomialSpace k) (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x=>(inner ℝ (R x) (A (R x))+inner ℝ z (R x)-
      LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)*f x) ∈ polynomialSpace (k+2) := by
  have hh := (polynomialSpace (k+2)).sub_mem
    ((polynomialSpace (k+2)).add_mem (quadratic_form_mul_mem hf R A)
      (polynomialSpace_mono (by omega : k+1≤k+2) (inner_mul_mem hf R z)))
    ((polynomialSpace (k+2)).smul_mem (LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)
      (polynomialSpace_mono (by omega : k≤k+2) hf))
  convert hh using 1
  funext x
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem tensorBulk_degree (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (fun x=>tensorBulk U A z (R x)) ∈ polynomialSpace 4 := by
  have hq : (fun x=>quadraticScore U (R x)) ∈ polynomialSpace 2 := by
    simpa only [quadraticScore,inner_zero_left,add_zero] using massBulk_expression_mem R U 0
  have hp := mass_expression_mul_mem hq R A z
  have hi := (polynomialSpace 2).add_mem (quadratic_form_mem R (U.adjoint.comp A))
    (polynomialSpace_mono (by decide : 1≤2) (inner_mem R (U.adjoint z)))
  have hh := (polynomialSpace 4).sub_mem hp
    ((polynomialSpace 4).smul_mem 2 (polynomialSpace_mono (by decide : 2≤4) hi))
  convert hh using 1
  funext x
  simp only [tensorBulk,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left,inner_add_right,real_inner_comm]
  ring
end Degree

/-- Centered tensor transport energy is controlled before any coordinate sum. -/
theorem tensorBulk_integral_sq_le (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    (∫ x,tensorBulk U A z x^2 ∂stdGaussian (FSC.Coord d)) ≤
      10368*(operatorHilbertSchmidt U)^2*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
  let f : (Fin d→ℝ)→ℝ := fun x=>tensorBulk U A z (WithLp.toLp 2 x)
  have hf : MemLp f 2 (γFin d) := polynomial_memLp
    (tensorBulk_degree (toEuclideanLinear (d:=d)) U A z)
  have hh := pow_le_pow_left₀ (norm2_nonneg f) (norm2_tensorBulk_le U A z) 2
  have hs : (operatorHilbertSchmidt A+‖z‖)^2 ≤ 2*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
    nlinarith [sq_nonneg (operatorHilbertSchmidt A-‖z‖)]
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by unfold tensorBulk quadraticScore; fun_prop)]
  change (∫ x,f x^2 ∂γFin d) ≤ _
  rw [←norm2_sq hf]
  calc
    _ ≤ (72*operatorHilbertSchmidt U*(operatorHilbertSchmidt A+‖z‖))^2 := hh
    _ = (5184*(operatorHilbertSchmidt U)^2)*(operatorHilbertSchmidt A+‖z‖)^2 := by ring
    _ ≤ (5184*(operatorHilbertSchmidt U)^2)*(2*((operatorHilbertSchmidt A)^2+‖z‖^2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private instance holder884 : ENNReal.HolderTriple (8:ℝ≥0∞) 8 4 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
private instance holder442 : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩

theorem quadraticScore_memLp_four (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) : MemLp (quadraticScore A) 4 μ := by
  have hi := IsGaussian.memLp_id μ 8 (by norm_num)
  have hq : MemLp (fun x=>inner ℝ x (A x)) 4 μ := by
    exact MemLp.of_bilin (inner ℝ) 1 hi (A.comp_memLp' hi) (by fun_prop)
      (.of_forall fun x=>by
        simp only [one_mul]
        exact_mod_cast (norm_inner_le_norm (𝕜:=ℝ) x (A x)))
  exact hq.sub (memLp_const _)

/-- Genuine L2 membership holds also for the degenerate Gaussian facet law. -/
theorem tensorBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : MemLp (tensorBulk U A z) 2 μ := by
  have hi := IsGaussian.memLp_id μ 4 (by norm_num)
  have hs : MemLp (fun x=>inner ℝ x (A x)+inner ℝ z x-
      LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap) 4 μ := by
    have hh := (quadraticScore_memLp_four μ A).add (hi.const_inner (𝕜:=ℝ) z)
    convert hh using 1
    funext x
    simp only [quadraticScore,Pi.add_apply,id_eq]
    ring
  have ht : MemLp (fun x=>inner ℝ (U x) (A x+z)) 2 μ := by
    exact MemLp.of_bilin (inner ℝ) 1 (U.comp_memLp' hi)
      ((A.comp_memLp' hi).add (memLp_const z)) (by fun_prop)
      (.of_forall fun x=>by
        simp only [one_mul]
        exact_mod_cast (norm_inner_le_norm (𝕜:=ℝ) (U x) (A x+z)))
  exact ((quadraticScore_memLp_four μ U).mul hs).sub (ht.const_mul 2)

theorem abs_integral_mul_le_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X→ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x,f x*g x ∂μ| ≤ Real.sqrt (∫ x,f x^2 ∂μ)*Real.sqrt (∫ x,g x^2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) μ by simpa using hf)
    (show MemLp g (ENNReal.ofReal 2) μ by simpa using hg)
  have hn := norm_integral_le_integral_norm (f:=fun x=>f x*g x) (μ:=μ)
  simp only [Real.norm_eq_abs,abs_mul] at hn
  simp only [Real.norm_eq_abs,Real.rpow_two,sq_abs] at hh
  simpa only [Real.sqrt_eq_rpow] using hn.trans hh

section Facets
open NegativeVotingFan NegativeVotingDisintegration NegativeVotingWeightedFacet
open NegativeVotingPolynomialFacetLogBound
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem affine_score_integral_sq_le (v : FSC.Coord d) (c : ℝ) :
    (∫ x,(inner ℝ v x+c)^2 ∂stdGaussian (FSC.Coord d)) ≤ 2*(‖v‖^2+c^2) := by
  have hf : MemLp (fun x : Fin d→ℝ=>inner ℝ v (WithLp.toLp 2 x)+c) 2 (γFin d) :=
    polynomial_memLp (affine_score_mem (toEuclideanLinear (d:=d)) v c)
  have hh := pow_le_pow_left₀ (norm2_nonneg _) (norm2_affine_score_le v c) 2
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by fun_prop),←norm2_sq hf]
  nlinarith [sq_nonneg (‖v‖-|c|),sq_abs c]

theorem affineFacet_affine_score_integral_sq_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (v : FSC.Coord d) (c a m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m)) :
    (∫ x in affineFacet B h i j,(inner ℝ v x+c)^2
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal *
        quarticLogConstant a*(1+Real.log m)^4*(2*(‖v‖^2+c^2)) := by
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    Measure.map_apply hmChart (isClosed_affineFacet B h i j).measurableSet] at hprob ⊢
  rw [setIntegral_map (isClosed_affineFacet B h i j).measurableSet (by fun_prop) hmChart.aemeasurable]
  have ht := plane_affine_score_integral_sq_log_m _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates (pairNormal B i j)) v c (pairOffset B h i j) a m
    (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j).measurableSet hm hprob ha
  exact ht.trans (mul_le_mul_of_nonneg_left (affine_score_integral_sq_le v c)
    (by unfold quarticLogConstant; positivity))

/-- The literal centered tensor bulk on the actual Gaussian facet. Its
coefficient is controlled by HS(U), without a coordinatewise dimension loss. -/
theorem facet_tensorBulk_integral_sq_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      ((stdGaussian (tangentSpace (pairNormal B i j))) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m)) :
    (∫ q in intrinsicFacet B h i j,tensorBulk U A z (facetChart B h i j q)^2
      ∂stdGaussian (tangentSpace (pairNormal B i j))) ≤
      ((stdGaussian (tangentSpace (pairNormal B i j))) (intrinsicFacet B h i j)).toReal *
        quarticLogConstant a*(1+Real.log m)^4 *
        (10368*(operatorHilbertSchmidt U)^2*((operatorHilbertSchmidt A)^2+‖z‖^2)) := by
  have ht := plane_integral_sq_log_m _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates (pairNormal B i j)) (tensorBulk U A z)
    (by unfold tensorBulk quadraticScore; fun_prop)
    (tensorBulk_degree _ U A z) (pairOffset B h i j) a m
    (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j).measurableSet hm hprob ha
  exact ht.trans (mul_le_mul_of_nonneg_left (tensorBulk_integral_sq_le U A z)
    (by unfold quarticLogConstant; positivity))

theorem affineFacet_tensorBulk_integral_sq_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m)) :
    (∫ x in affineFacet B h i j,tensorBulk U A z x^2
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal *
        quarticLogConstant a*(1+Real.log m)^4 *
        (10368*(operatorHilbertSchmidt U)^2*((operatorHilbertSchmidt A)^2+‖z‖^2)) := by
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    Measure.map_apply hmChart (isClosed_affineFacet B h i j).measurableSet] at hprob ⊢
  rw [setIntegral_map (isClosed_affineFacet B h i j).measurableSet
    (by unfold tensorBulk quadraticScore; fun_prop) hmChart.aemeasurable]
  exact facet_tensorBulk_integral_sq_le B h i j hij U A z a m hm hprob ha
/-- Cauchy--Schwarz on the actual affine facet combines the two derived trace
bounds. This is the tensor-bulk times moving-score term of the Hessian. -/
theorem affineFacet_tensorBulk_mul_score_abs_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (z v : FSC.Coord d) (c a m : ℝ) (hm : 1 ≤ m)
    (hprob : m ^ (-4096 : ℝ) ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal)
    (ha : |pairOffset B h i j| ≤ a*Real.sqrt (1+Real.log m)) :
    |∫ x in affineFacet B h i j,tensorBulk U A z x*(inner ℝ v x+c)
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)| ≤
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) (affineFacet B h i j)).toReal *
        quarticLogConstant a*(1+Real.log m)^4 *
        Real.sqrt (10368*(operatorHilbertSchmidt U)^2*((operatorHilbertSchmidt A)^2+‖z‖^2))*
        Real.sqrt (2*(‖v‖^2+c^2)) := by
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  let F := affineFacet B h i j
  let K := (μ F).toReal*quarticLogConstant a*(1+Real.log m)^4
  let C1 := 10368*(operatorHilbertSchmidt U)^2*((operatorHilbertSchmidt A)^2+‖z‖^2)
  let C2 := 2*(‖v‖^2+c^2)
  have hK : 0 ≤ K := by unfold K quarticLogConstant; positivity
  letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hf : MemLp (tensorBulk U A z) 2 (μ.restrict F) := (tensorBulk_memLp_two μ U A z).restrict F
  have hg : MemLp (fun x=>inner ℝ v x+c) 2 (μ.restrict F) :=
    ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) v |>.add (memLp_const c)).restrict F
  have hb1 : (∫ x in F,tensorBulk U A z x^2 ∂μ) ≤ K*C1 :=
    affineFacet_tensorBulk_integral_sq_le B h i j hij U A z a m hm hprob ha
  have hb2 : (∫ x in F,(inner ℝ v x+c)^2 ∂μ) ≤ K*C2 :=
    affineFacet_affine_score_integral_sq_le B h i j hij v c a m hm hprob ha
  refine (abs_integral_mul_le_sqrt hf hg).trans ?_
  calc
    _ ≤ Real.sqrt (K*C1)*Real.sqrt (K*C2) := mul_le_mul
      (Real.sqrt_le_sqrt hb1) (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K*Real.sqrt C1*Real.sqrt C2 := by
      rw [Real.sqrt_mul hK,Real.sqrt_mul hK]
      calc
        _ = (Real.sqrt K)^2*Real.sqrt C1*Real.sqrt C2 := by ring
        _ = _ := by rw [Real.sq_sqrt hK]
end Facets

end NegativeVotingQuadraticTensorBulkNorm
