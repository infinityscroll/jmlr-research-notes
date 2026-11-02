import GaussianReferenceJumpComparison
import GaussianRegularOrbitRepresentation

/-! The actual regular reference jump is bounded on the current facets by
its exact row-error factor, polynomial Gaussian trace, and weighted degree.
All geometric hypotheses remain explicit; there is no dimension or label-count
loss from a coordinatewise tensor estimate. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularReferenceJumpBound
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian NegativeVotingFanHessian
  NegativeVotingSecondChaosFacetGradient NegativeVotingWeightedFacet
  NegativeVotingDisintegration NegativeVotingReferenceJumpComparison
  NegativeVotingTensorFacetAggregation NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingPolynomialFacetLogBound NegativeVotingPolynomialDegree NegativeVotingPolynomialFacetTrace
  NegativeVotingQuadraticBulkNorm NegativeVotingQuadraticTensorBulkNorm NegativeVotingCovarianceCoercivity
  NegativeVotingAffineLogMassBound NegativeVotingRegularFacetCancellation
  NegativeVotingRegularOrbitRepresentation NegativeVotingRegularQuadraticRepresentation
  NegativeVotingSecondChaosMassAdjoint NegativeVotingFacetDegree NegativeVotingCapTail
  NegativeVotingSmoothingComposition GaussianFin
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem affine_linear_product_mem {κ : Type*} [Fintype κ]
    (R : (κ→ℝ)→ₗ[ℝ] FSC.Coord d) (v s : FSC.Coord d) (c : ℝ) :
    (fun x=>(inner ℝ v (R x)+c)*inner ℝ s (R x))∈polynomialSpace 2 := by
  simpa only [mul_comm] using inner_mul_mem (affine_score_mem R v c) R s

/-- A dimension-free Gaussian L2 bound for the literal product on the
current facet. The constant is deliberately conservative. -/
theorem affine_linear_product_integral_sq_le (v s : FSC.Coord d) (c : ℝ) :
    (∫ x,((inner ℝ v x+c)*inner ℝ s x)^2 ∂stdGaussian (FSC.Coord d))≤
      32*‖s‖^2*(‖v‖^2+c^2) := by
  let f : (Fin d→ℝ)→ℝ := fun x=>inner ℝ v (WithLp.toLp 2 x)+c
  let g : (Fin d→ℝ)→ℝ := fun x=>inner ℝ s (WithLp.toLp 2 x)
  have hf : f∈polynomialSpace 1 := affine_score_mem toEuclideanLinear v c
  have hg : g∈polynomialSpace 1 := inner_mem toEuclideanLinear s
  have hfg : (fun x=>f x*g x)∈polynomialSpace 2 :=
    affine_linear_product_mem toEuclideanLinear v s c
  have hb := pow_le_pow_left₀ (norm2_nonneg (fun x=>f x*g x)) (norm2_product_le hf hg) 2
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  have he : norm2 f^2≤2*(‖v‖^2+c^2) := by
    rw [norm2_sq (polynomial_memLp hf)]
    have hh := affine_score_integral_sq_le v c
    rw [←hmap,integral_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  have hge : norm2 g=‖s‖ := norm2_inner s
  rw [hge] at hb
  norm_num only [show 1+1=2 by decide,show (2:ℝ)^2=4 by norm_num] at hb
  rw [←hmap,integral_map (by fun_prop) (by fun_prop)]
  change (∫ x,(f x*g x)^2 ∂γFin d)≤_
  rw [←norm2_sq (polynomial_memLp hfg)]
  calc
    _ ≤ (4*norm2 f*‖s‖)^2 := hb
    _ = 16*‖s‖^2*(norm2 f)^2 := by ring
    _ ≤ 16*‖s‖^2*(2*(‖v‖^2+c^2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The product trace on one actual facet, with the exact surface weight. -/
theorem surface_affine_linear_product_sq_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j)
    (v s : FSC.Coord d) (c a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    surfaceIntegral B h i j (fun x=>((inner ℝ v x+c)*inner ℝ s x)^2)≤
      32*facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4*
        ‖s‖^2*(‖v‖^2+c^2) := by
  have hb := plane_integral_sq_log_m _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates (pairNormal B i j))
    (fun x=>(inner ℝ v x+c)*inner ℝ s x) (by fun_prop)
    (polynomialSpace_mono (by decide : 2≤4) (affine_linear_product_mem _ v s c))
    (pairOffset B h i j) a m (intrinsicFacet B h i j)
    (isClosed_intrinsicFacet B h i j).measurableSet hm hprob ha
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (affine_linear_product_integral_sq_le v s c)
    (by unfold quarticLogConstant; positivity))
  have hc : 0≤gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖ :=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  unfold surfaceIntegral
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    setIntegral_map (isClosed_affineFacet B h i j).measurableSet
      (by fun_prop) hmChart.aemeasurable]
  convert mul_le_mul_of_nonneg_left hb' hc using 1
  · rfl
  · simp only [facetWeight]; ring

/-- The exact regular identity is used only on the integration set. -/
theorem surface_regularJump_sq_eq (B R : ι→FSC.Coord d) (h : ι→ℝ)
    (α γ : ℝ) (hα : α≠0) (i j : ι) :
    surfaceIntegral B h i j (fun x=>(regularJump R γ i j x)^2)=
      (γ/α)^2*surfaceIntegral B h i j (fun x=>
        ((inner ℝ (rowError B R α i-rowError B R α j) x+(h i-h j))*
          inner ℝ (R i+R j) x)^2) := by
  have he : surfaceIntegral B h i j (fun x=>(regularJump R γ i j x)^2)=
      surfaceIntegral B h i j (fun x=>(γ/α)^2*
        ((inner ℝ (rowError B R α i-rowError B R α j) x+(h i-h j))*
          inner ℝ (R i+R j) x)^2) := by
    unfold surfaceIntegral
    congr 1
    apply setIntegral_congr_fun (isClosed_affineFacet B h i j).measurableSet
    intro x hx
    dsimp only
    rw [regularJump_on_facet B R h α γ hα i j x hx]
    simp only [errorGap,inner_add_left]
    ring
  rw [he,surfaceIntegral_const_mul]

/-- Weighted degree controls the entire exact regular jump. This bound
contains the squared perturbation energy, not the size of the reference tensor. -/
theorem regularJumpEnergy_log_le (B R : ι→FSC.Coord d) (h : ι→ℝ)
    (α γ : ℝ) (hα : α≠0) (hR : ∀i,‖R i‖≤1)
    (a m degree : ℝ) (hm : 1 ≤ m) (hinj : Function.Injective B)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    (1/2:ℝ)*(∑i,∑j,surfaceIntegral B h i j (fun x=>(regularJump R γ i j x)^2))≤
      256*degree*quarticLogConstant a*(1+Real.log m)^4*(γ/α)^2*
        ((∑i,‖rowError B R α i-v‖^2)+(∑i,(h i-c)^2)) := by
  let K := quarticLogConstant a*(1+Real.log m)^4
  let D := rowError B R α
  let e := fun i j=>‖D i-D j‖^2+(h i-h j)^2
  have hK : 0≤K := by unfold K quarticLogConstant; positivity
  have hp (i j : ι) : surfaceIntegral B h i j (fun x=>(regularJump R γ i j x)^2)≤
      128*K*(γ/α)^2*(facetWeight B h i j*e i j) := by
    by_cases hij : i=j
    · subst j
      simp [surfaceIntegral_diagonal,facetWeight_self]
    have hb := surface_affine_linear_product_sq_le B h i j (fun he=>hij (hinj he))
      (D i-D j) (R i+R j) (h i-h j) a m hm (hprob i j hij) (ha i j hij)
    have hnorm : ‖R i+R j‖≤2 := (norm_add_le _ _).trans (by linarith [hR i,hR j])
    have hsq : ‖R i+R j‖^2≤4 := by nlinarith [norm_nonneg (R i+R j)]
    have hscale : 0≤32*facetWeight B h i j*K*(‖D i-D j‖^2+(h i-h j)^2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (facetWeight_nonneg B h i j)) hK)
        (by positivity)
    have hb' : surfaceIntegral B h i j (fun x=>
        ((inner ℝ (D i-D j) x+(h i-h j))*inner ℝ (R i+R j) x)^2)≤
        128*K*(facetWeight B h i j*e i j) := by
      calc
        _ ≤ 32*facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4*
            ‖R i+R j‖^2*(‖D i-D j‖^2+(h i-h j)^2) := hb
        _ = (32*facetWeight B h i j*K*(‖D i-D j‖^2+(h i-h j)^2))*‖R i+R j‖^2 := by
          dsimp only [K]; ring
        _ ≤ (32*facetWeight B h i j*K*(‖D i-D j‖^2+(h i-h j)^2))*4 :=
          mul_le_mul_of_nonneg_left hsq hscale
        _ = _ := by dsimp only [e]; ring
    rw [surface_regularJump_sq_eq B R h α γ hα]
    convert mul_le_mul_of_nonneg_left hb' (sq_nonneg (γ/α)) using 1 <;> ring
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) fun j _=>hp i j
  simp only [←Finset.mul_sum] at hs
  have hed := facet_edge_score_coefficient_le B D h h degree hdegree v c
  calc
    _ ≤ (1/2:ℝ)*(128*K*(γ/α)^2*(∑i,∑j,facetWeight B h i j*e i j)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (1/2:ℝ)*(128*K*(γ/α)^2*(4*degree*((∑i,‖D i-v‖^2)+(∑i,(h i-c)^2)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hed (by positivity)) (by norm_num)
    _ = _ := by dsimp only [D,K]; ring

/-- Actual regular Gaussian reference moments, in every ambient dimension,
satisfy the perturbative jump bound on the current fan. -/
theorem referenceJumpEnergy_regular_log_le {n : ℕ} (hn : 1 ≤ n)
    (B R : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (α : ℝ) (hα : α≠0)
    (a m degree : ℝ) (hm : 1 ≤ m) (hinj : Function.Injective B)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    referenceJumpEnergy B R h (fun _=>0)≤
      256*degree*quarticLogConstant a*(1+Real.log m)^4*(momentCoefficient n/α)^2*
        ((∑i,‖rowError B R α i-v‖^2)+(∑i,(h i-c)^2)) := by
  have hR (i : Fin (n+2)) : ‖R i‖≤1 := by
    have hnorm : ‖R i‖^2=1-1/((n+2:ℕ):ℝ) := by
      rw [←real_inner_self_eq_norm_sq,hG]
      simp
    have hpos : 0≤1/((n+2:ℕ):ℝ) := by positivity
    nlinarith [norm_nonneg (R i)]
  have he : referenceJumpEnergy B R h (fun _=>0)=
      (1/2:ℝ)*(∑i,∑j,surfaceIntegral B h i j
        (fun x=>(regularJump R (momentCoefficient n) i j x)^2)) := by
    unfold referenceJumpEnergy
    simp only [regular_quadraticLabelTest_difference_all_dimensions hn R hG,regularJump]
  rw [he]
  exact regularJumpEnergy_log_le B R h α (momentCoefficient n) hα hR
    a m degree hm hinj hprob ha hdegree v c

/-- The mass-adjoint correction is controlled by actual row/offset error
and actual tensor difference, with the reference tensor size canceled first. -/
theorem massAdjoint_norm_sq_regular_log_le {n : ℕ} (hn : 1 ≤ n)
    (B R : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (α : ℝ) (hα : α≠0)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (gap : ℝ) (hgap : 0<gap)
    (hlaplacian : ∀v:Fin (n+2)→ℝ,(∑i,v i)=0 →
      gap*(∑i,(v i)^2) ≤ dotProduct v (offsetJacobian B h *ᵥ v))
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    (∑i,(massAdjoint B h i)^2)≤
      (512*degree*quarticLogConstant a*(1+Real.log m)^4*(momentCoefficient n/α)^2*
        ((∑i,‖rowError B R α i-v‖^2)+(∑i,(h i-c)^2))+
        8*degree*quarticLogConstant a*(1+Real.log m)^4*
          momentDifferenceEnergy B R h (fun _=>0))/gap := by
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hdeg (i : Fin (n+2)) : (∑j∈Finset.univ.erase i,facetWeight B h i j)≤degree :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j _ _=>facetWeight_nonneg B h i j)).trans (hdegree i)
  have hb := massAdjoint_norm_sq_reference_log_le B R h (fun _=>0)
    σ hσ hlower gap hgap hlaplacian a m degree hm hdegree0 hprob ha hdeg
  have hr := referenceJumpEnergy_regular_log_le hn B R hG h α hα
    a m degree hm hinj hprob ha hdegree v c
  refine hb.trans (div_le_div_of_nonneg_right ?_ hgap.le)
  linarith

end NegativeVotingRegularReferenceJumpBound
