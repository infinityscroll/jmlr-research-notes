import GaussianQuadraticTensorBulkNorm
import GaussianFanMassJacobian
import GaussianFiniteGraphRayleigh
import GaussianBoundedCoherentLift

/-! Logarithmic weighted facet aggregation for actual Gaussian polynomial
tests. The summation uses the genuine weighted row degree, with no factor
depending on the ambient dimension or number of labels. Geometric lower
probabilities and normal-coordinate bounds remain explicit. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical

namespace NegativeVotingTensorFacetAggregation
open NegativeVotingFan NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingFanJacobian NegativeVotingPolynomialDegree
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingPolynomialFacetLogBound
  NegativeVotingQuadraticTensorBulkNorm NegativeVotingAffineLogMassBound

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A polynomial label test is traced and then summed using only row degree.
The analytic trace estimate is proved upstream for the literal polynomial. -/
theorem affineWeightedFacetEnergy_polynomial_log_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (f : ι→FSC.Coord d→ℝ)
    (a m degree : ℝ) (hm : 1 ≤ m)
    (hinj : Function.Injective B)
    (hf : ∀ i,Continuous (f i))
    (hpoly : ∀ i j,i≠j→
      (fun x=>f i (reconstructLinear (pairNormal B i j)
        (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j)≤degree) :
    affineWeightedFacetEnergy B h f ≤
      degree*quarticLogConstant a*(1+Real.log m)^4*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  let K := quarticLogConstant a*(1+Real.log m)^4
  let E := fun i=>∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d)
  have hK : 0≤K := by unfold K quarticLogConstant; positivity
  have hE (i : ι) : 0≤E i := integral_nonneg fun _=>sq_nonneg _
  change (∑ i,∑ j∈Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫ x in intrinsicFacet B h i j,(f i (facetChart B h i j x))^2
        ∂stdGaussian (tangentSpace (pairNormal B i j)))≤_
  calc
    _ ≤ ∑ i,∑ j∈Finset.univ.erase i,facetWeight B h i j*K*E i := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
      have hb := plane_integral_sq_log_m _
        (pairNormal_norm B i j (fun he=>hij (hinj he)))
        (canonicalTangentCoordinates (pairNormal B i j)) (f i) (hf i)
        (hpoly i j hij) (pairOffset B h i j) a m (intrinsicFacet B h i j)
        (isClosed_intrinsicFacet B h i j).measurableSet hm (hprob i j hij) (ha i j hij)
      have hc : 0≤gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖ :=
        div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
      convert mul_le_mul_of_nonneg_left hb hc using 1 <;>
        simp only [facetWeight,K,E,facetChart] <;> ring
    _ = ∑ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j)*K*E i := by
      simp only [Finset.sum_mul]
    _ ≤ ∑ i,degree*K*E i := by
      exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hdegree i) hK) (hE i)
    _ = _ := by simp only [K,E,Finset.mul_sum]; ring

/-- The centered matrix-test bulk is aggregated before any coordinate sum. -/
theorem affineWeightedFacetEnergy_tensorBulk_le
    (B : ι→FSC.Coord d) (h : ι→ℝ)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,(∑ j∈Finset.univ.erase i,facetWeight B h i j)≤degree) :
    affineWeightedFacetEnergy B h (fun i=>tensorBulk (U i) A z) ≤
      10368*degree*quarticLogConstant a*(1+Real.log m)^4*
        ((operatorHilbertSchmidt A)^2+‖z‖^2)*∑ i,(operatorHilbertSchmidt (U i))^2 := by
  have hb := affineWeightedFacetEnergy_polynomial_log_le B h
    (fun i=>tensorBulk (U i) A z) a m degree hm hinj
    (fun i=>by unfold tensorBulk NegativeVotingQuadraticBulkNorm.quadraticScore; fun_prop)
    (fun i j _=>tensorBulk_degree _ (U i) A z) hprob ha hdegree
  refine hb.trans ?_
  calc
    _ ≤ degree*quarticLogConstant a*(1+Real.log m)^4*
        ∑ i,10368*(operatorHilbertSchmidt (U i))^2*((operatorHilbertSchmidt A)^2+‖z‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>tensorBulk_integral_sq_le (U i) A z)
        (by unfold quarticLogConstant; positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The finite weighted Schur estimate is valid in any normed space, after
removing an arbitrary common translation. -/
theorem weighted_norm_difference_le_degree {E : Type*} [SeminormedAddCommGroup E]
    (w : ι→ι→ℝ) (hw : ∀ i j,0≤w i j) (hsym : ∀ i j,w i j=w j i)
    (degree : ℝ) (hdegree : ∀ i,∑ j,w i j≤degree) (v : ι→E) (c : E) :
    (∑ i,∑ j,w i j*‖v i-v j‖^2)≤4*degree*∑ i,‖v i-c‖^2 := by
  have hn (i j : ι) : ‖v i-v j‖≤‖v i-c‖+‖v j-c‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (v i-c) (v j-c)
  calc
    _ ≤ ∑ i,∑ j,w i j*(‖v i-c‖+‖v j-c‖)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn i j) 2) (hw i j)
    _ ≤ _ := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using
        NegativeVotingFiniteGraphRayleigh.absolute_pair_energy_le_degree w hw hsym
          degree hdegree (fun i=>‖v i-c‖)

/-- Actual facet weights control all row and offset differences without the
number of labels entering the coefficient. -/
theorem facet_edge_score_coefficient_le (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (degree : ℝ) (hdegree : ∀ i,∑ j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    (∑ i,∑ j,facetWeight B h i j*(‖D i-D j‖^2+(k i-k j)^2))≤
      4*degree*((∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2)) := by
  have hD := weighted_norm_difference_le_degree (facetWeight B h)
    (facetWeight_nonneg B h) (facetWeight_symm B h) degree hdegree D v
  have hk := weighted_norm_difference_le_degree (facetWeight B h)
    (facetWeight_nonneg B h) (facetWeight_symm B h) degree hdegree k c
  simp only [Real.norm_eq_abs,sq_abs] at hk
  simpa only [mul_add,Finset.sum_add_distrib] using add_le_add hD hk

/-- The literal edge-score energy, including both row and offset velocities. -/
def affineWeightedEdgeScoreEnergy (B D : ι→FSC.Coord d) (h k : ι→ℝ) : ℝ :=
  orderedFacetEnergy (fun i j=>tangentSpace (pairNormal B i j))
    (fun i j=>stdGaussian (tangentSpace (pairNormal B i j)))
    (intrinsicFacet B h)
    (fun i j x=>inner ℝ (D i-D j) (facetChart B h i j x)+(k i-k j))
    (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)) (fun i j=>‖B i-B j‖)

/-- Applying the proved affine-polynomial trace and then the weighted Schur
estimate gives an actual edge energy, rather than an assumed L2 bound. -/
theorem affineWeightedEdgeScoreEnergy_log_le
    (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (a m degree : ℝ) (hm : 1 ≤ m) (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    affineWeightedEdgeScoreEnergy B D h k≤
      8*degree*quarticLogConstant a*(1+Real.log m)^4*
        ((∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2)) := by
  let K := quarticLogConstant a*(1+Real.log m)^4
  let e := fun i j=>‖D i-D j‖^2+(k i-k j)^2
  have hK : 0≤K := by unfold K quarticLogConstant; positivity
  change (∑ i,∑ j∈Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫ x in intrinsicFacet B h i j,
        (inner ℝ (D i-D j) (facetChart B h i j x)+(k i-k j))^2
        ∂stdGaussian (tangentSpace (pairNormal B i j)))≤_
  calc
    _ ≤ ∑ i,∑ j∈Finset.univ.erase i,2*K*(facetWeight B h i j*e i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
      have hb := plane_affine_score_integral_sq_log_m _
        (pairNormal_norm B i j (fun he=>hij (hinj he)))
        (canonicalTangentCoordinates (pairNormal B i j)) (D i-D j) (k i-k j)
        (pairOffset B h i j) a m (intrinsicFacet B h i j)
        (isClosed_intrinsicFacet B h i j).measurableSet hm (hprob i j hij) (ha i j hij)
      have hb' := hb.trans (mul_le_mul_of_nonneg_left
        (affine_score_integral_sq_le (D i-D j) (k i-k j))
        (by unfold quarticLogConstant; positivity))
      have hc : 0≤gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖ :=
        div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _)
      convert mul_le_mul_of_nonneg_left hb' hc using 1 <;>
        simp only [facetWeight,K,e,facetChart] <;> ring
    _ ≤ ∑ i,∑ j,2*K*(facetWeight B h i j*e i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro j _ _
      exact mul_nonneg (mul_nonneg (by norm_num) hK)
        (mul_nonneg (facetWeight_nonneg B h i j) (by unfold e; positivity))
    _ = 2*K*(∑ i,∑ j,facetWeight B h i j*e i j) := by simp only [Finset.mul_sum]
    _ ≤ 2*K*(4*degree*((∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2))) :=
      mul_le_mul_of_nonneg_left (facet_edge_score_coefficient_le B D h k degree hdegree v c)
        (mul_nonneg (by norm_num) hK)
    _ = _ := by dsimp only [K]; ring

theorem ordered_sqrt_product_le (a b : ι→ι→ℝ)
    (ha : ∀ i j,0≤a i j) (hb : ∀ i j,0≤b i j) :
    (∑ i,∑ j∈Finset.univ.erase i,Real.sqrt (a i j)*Real.sqrt (b i j))≤
      Real.sqrt (∑ i,∑ j∈Finset.univ.erase i,a i j)*
        Real.sqrt (∑ i,∑ j∈Finset.univ.erase i,b i j) := by
  have hrow (i : ι) := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ.erase i)
    (fun j=>Real.sqrt (a i j)) (fun j=>Real.sqrt (b i j))
  simp_rw [Real.sq_sqrt (ha _ _),Real.sq_sqrt (hb _ _)] at hrow
  calc
    _ ≤ ∑ i,Real.sqrt (∑ j∈Finset.univ.erase i,a i j)*
        Real.sqrt (∑ j∈Finset.univ.erase i,b i j) := Finset.sum_le_sum fun i _=>hrow i
    _ ≤ Real.sqrt (∑ i,(Real.sqrt (∑ j∈Finset.univ.erase i,a i j))^2)*
        Real.sqrt (∑ i,(Real.sqrt (∑ j∈Finset.univ.erase i,b i j))^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp_rw [Real.sq_sqrt (Finset.sum_nonneg fun j _=>ha _ j),
        Real.sq_sqrt (Finset.sum_nonneg fun j _=>hb _ j)]

section IntegralCauchy
variable (X : ι→ι→Type*) [∀ i j,MeasurableSpace (X i j)]
  (μ : ∀ i j,Measure (X i j)) (F : ∀ i j,Set (X i j))
  (f g : ∀ i j,X i j→ℝ)

/-- Cauchy--Schwarz is applied to the actual edge measures, then to the finite
edge sum. No independence or lower facet-mass bound is used here. -/
theorem ordered_integral_mul_abs_le (c : ι→ι→ℝ) (hc : ∀ i j,0≤c i j)
    (hf : ∀ i j,i≠j→MemLp (f i j) 2 ((μ i j).restrict (F i j)))
    (hg : ∀ i j,i≠j→MemLp (g i j) 2 ((μ i j).restrict (F i j))) :
    |∑ i,∑ j∈Finset.univ.erase i,c i j*∫ x in F i j,f i j x*g i j x ∂μ i j|≤
      Real.sqrt (∑ i,∑ j∈Finset.univ.erase i,c i j*∫ x in F i j,(f i j x)^2 ∂μ i j)*
      Real.sqrt (∑ i,∑ j∈Finset.univ.erase i,c i j*∫ x in F i j,(g i j x)^2 ∂μ i j) := by
  let a := fun i j=>c i j*∫ x in F i j,(f i j x)^2 ∂μ i j
  let b := fun i j=>c i j*∫ x in F i j,(g i j x)^2 ∂μ i j
  have ha (i j : ι) : 0≤a i j := mul_nonneg (hc i j) (integral_nonneg fun _=>sq_nonneg _)
  have hb (i j : ι) : 0≤b i j := mul_nonneg (hc i j) (integral_nonneg fun _=>sq_nonneg _)
  calc
    _ ≤ ∑ i,∑ j∈Finset.univ.erase i,
        |c i j*∫ x in F i j,f i j x*g i j x ∂μ i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i,∑ j∈Finset.univ.erase i,Real.sqrt (a i j)*Real.sqrt (b i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
      rw [abs_mul,abs_of_nonneg (hc i j)]
      refine (mul_le_mul_of_nonneg_left
        (abs_integral_mul_le_sqrt (hf i j hij) (hg i j hij)) (hc i j)).trans_eq ?_
      dsimp only [a,b]
      rw [Real.sqrt_mul (hc i j),Real.sqrt_mul (hc i j)]
      calc
        _ = (Real.sqrt (c i j))^2*
            (Real.sqrt (∫ x in F i j,(f i j x)^2 ∂μ i j)*
             Real.sqrt (∫ x in F i j,(g i j x)^2 ∂μ i j)) := by rw [Real.sq_sqrt (hc i j)]
        _ = _ := by ring
    _ ≤ _ := ordered_sqrt_product_le a b ha hb
end IntegralCauchy

/-- Intrinsic and ambient facet energies agree, with exactly one Gaussian
density and one edge length on both sides. -/
theorem orderedFacetEnergy_eq_ambient (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hinj : Function.Injective B) (f : ι→ι→FSC.Coord d→ℝ)
    (hf : ∀ i j,Continuous (f i j)) :
    orderedFacetEnergy (fun _ _=>FSC.Coord d)
      (fun i j=>FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))
      (affineFacet B h) f
      (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)) (fun i j=>‖B i-B j‖)=
    orderedFacetEnergy (fun i j=>tangentSpace (pairNormal B i j))
      (fun i j=>stdGaussian (tangentSpace (pairNormal B i j)))
      (intrinsicFacet B h) (fun i j x=>f i j (facetChart B h i j x))
      (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)) (fun i j=>‖B i-B j‖) := by
  unfold orderedFacetEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : B i≠B j := fun he=>(Finset.mem_erase.mp hj).1 (hinj he).symm
  have hmChart : Measurable (facetChart B h i j) := by unfold facetChart; fun_prop
  dsimp only
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    setIntegral_map (isClosed_affineFacet B h i j).measurableSet
      (by fun_prop) hmChart.aemeasurable]
  rfl

/-- Literal surface tensor-bulk pairing, before orientation pairing of labels. -/
def tensorFacetPairing (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : ℝ :=
  ∑ i,∑ j∈Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫ x in affineFacet B h i j,tensorBulk (U i) A z x*
        (inner ℝ (D i-D j) x+(k i-k j))
        ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)

theorem tensorFacetPairing_abs_le_energies
    (B D : ι→FSC.Coord d) (h k : ι→ℝ) (hinj : Function.Injective B)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    |tensorFacetPairing B D h k U A z|≤
      Real.sqrt (affineWeightedFacetEnergy B h (fun i=>tensorBulk (U i) A z))*
      Real.sqrt (affineWeightedEdgeScoreEnergy B D h k) := by
  have hh := ordered_integral_mul_abs_le (fun _ _=>FSC.Coord d)
    (fun i j=>FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))
    (affineFacet B h) (fun i _=>tensorBulk (U i) A z)
    (fun i j x=>inner ℝ (D i-D j) x+(k i-k j))
    (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖)
    (fun i j=>div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    (fun i j _=>by
      let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact (tensorBulk_memLp_two μ (U i) A z).restrict _)
    (fun i j _=>by
      let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (D i-D j) |>.add
        (memLp_const (k i-k j))).restrict _)
  change |tensorFacetPairing B D h k U A z|≤
    Real.sqrt (orderedFacetEnergy _ _ _ _ _ _)*Real.sqrt (orderedFacetEnergy _ _ _ _ _ _) at hh
  rw [orderedFacetEnergy_eq_ambient B h hinj _
    (fun i _=>by unfold tensorBulk NegativeVotingQuadraticBulkNorm.quadraticScore; fun_prop),
    orderedFacetEnergy_eq_ambient B h hinj _ (fun _ _=>by fun_prop)] at hh
  exact hh

/-- Quantitative aggregation of the literal tensor facet pairing. The only
sum coefficient is the actual weighted degree. -/
theorem tensorFacetPairing_log_le
    (B D : ι→FSC.Coord d) (h k : ι→ℝ) (hinj : Function.Injective B)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j≤degree)
    (v : FSC.Coord d) (c : ℝ) :
    |tensorFacetPairing B D h k U A z|≤
      288*degree*quarticLogConstant a*(1+Real.log m)^4*
        Real.sqrt ((operatorHilbertSchmidt A)^2+‖z‖^2)*
        Real.sqrt (∑ i,(operatorHilbertSchmidt (U i))^2)*
        Real.sqrt ((∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2)) := by
  have hdeg (i : ι) : (∑ j∈Finset.univ.erase i,facetWeight B h i j)≤degree :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j _ _=>facetWeight_nonneg B h i j)).trans (hdegree i)
  have h1 := affineWeightedFacetEnergy_tensorBulk_le B h U A z a m degree hm hdegree0
    hinj hprob ha hdeg
  have h2 := affineWeightedEdgeScoreEnergy_log_le B D h k a m degree hm hinj hprob ha hdegree v c
  refine (tensorFacetPairing_abs_le_energies B D h k hinj U A z).trans ?_
  refine (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq ?_
  let K := degree*quarticLogConstant a*(1+Real.log m)^4
  let E := (operatorHilbertSchmidt A)^2+‖z‖^2
  let S := ∑ i,(operatorHilbertSchmidt (U i))^2
  let T := (∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2)
  have hK : 0≤K := by unfold K quarticLogConstant; positivity
  have hE : 0≤E := by unfold E; positivity
  have hS : 0≤S := Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hT : 0≤T := by unfold T; positivity
  have hs : Real.sqrt (10368*K*E*S)*Real.sqrt (8*K*T)=
      288*K*Real.sqrt E*Real.sqrt S*Real.sqrt T := by
    rw [←Real.sqrt_mul (by positivity : 0≤10368*K*E*S)]
    have he : (10368*K*E*S)*(8*K*T)=(288*K)^2*E*S*T := by ring
    rw [he,Real.sqrt_mul (mul_nonneg (mul_nonneg (sq_nonneg _) hE) hS),
      Real.sqrt_mul (mul_nonneg (sq_nonneg _) hE),Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg (by norm_num) hK)]
  simpa only [K,E,S,T,mul_assoc] using hs

/-- Instantiation with the constructed bounded coherent lift. This retains
the genuine inverse singular-value cost, rather than silently treating it
as a logarithmic constant. -/
theorem tensorFacetPairing_boundedLift_le
    (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (i₀ : ι) (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d)
    (δ : NegativeVotingFanScore.Parameters d ι)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j≤degree)
    (v v' : FSC.Coord d) (c c' : ℝ) :
    let V := NegativeVotingFanQuadraticTransport.velocityMap
      (NegativeVotingBoundedCoherentLift.boundedScoreLift B σ hσ hlower i₀) δ
    |tensorFacetPairing B D h k U V.1 V.2|≤
      288*degree*quarticLogConstant a*(1+Real.log m)^4*
        Real.sqrt (((∑ i,‖δ.1 i-v'‖^2)+(∑ i,(δ.2 i-c')^2))/σ^2)*
        Real.sqrt (∑ i,(operatorHilbertSchmidt (U i))^2)*
        Real.sqrt ((∑ i,‖D i-v‖^2)+(∑ i,(k i-c)^2)) := by
  dsimp only
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij he
  refine (tensorFacetPairing_log_le B D h k hinj U _ _ a m degree hm hdegree0
    hprob ha hdegree v c).trans ?_
  have hb := Real.sqrt_le_sqrt
    (NegativeVotingBoundedCoherentLift.bounded_velocity_energy_le B σ hσ hlower i₀ δ v' c')
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
      (by unfold quarticLogConstant; positivity)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end NegativeVotingTensorFacetAggregation
