import GaussianRegularTransportProducts
import GaussianHessianReferenceRemainder

/-! The regular reference contribution to actual moving-facet transport.
The current-facet identities are applied before absolute values; the inverse
velocity energy is always multiplied by row/offset error energy. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingRegularTransportBound
open NegativeVotingFan NegativeVotingFanHessian NegativeVotingGlobalTensorTransport
  NegativeVotingFanMassSecondDerivative NegativeVotingFanJacobian
  NegativeVotingSecondChaosFacetGradient NegativeVotingRegularFacetCancellation
  NegativeVotingRegularTransportProducts NegativeVotingTensorFacetAggregation
  NegativeVotingWeightedFacet NegativeVotingDisintegration NegativeVotingAffineLogMassBound
  NegativeVotingPolynomialFacetLogBound NegativeVotingAffineNormControl
  NegativeVotingHessianReferenceRemainder NegativeVotingActualMomentOperator
  NegativeVotingCoherentLiftHessian NegativeVotingFanQuadraticTransport
  NegativeVotingRegularOrbitRepresentation NegativeVotingRegularQuadraticRepresentation
  NegativeVotingReferenceJumpComparison NegativeVotingQuadraticBulkNorm
  NegativeVotingCapTail NegativeVotingFanScore
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem field_coefficient_le (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z v : FSC.Coord d) (c : ℝ) :
    coefficientEnergy (A.adjoint v) (inner ℝ v z) ≤ velocityEnergy A z*coefficientEnergy v c := by
  have hn : ‖A.adjoint v‖ ≤ operatorHilbertSchmidt A*‖v‖ :=
    (A.adjoint.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (by simpa only [LinearIsometryEquiv.norm_map] using operator_norm_le_HilbertSchmidt A)
      (norm_nonneg v))
  have hn2 := pow_le_pow_left₀ (norm_nonneg (A.adjoint v)) hn 2
  have hi := pow_le_pow_left₀ (abs_nonneg (inner ℝ v z)) (abs_real_inner_le_norm v z) 2
  simp only [sq_abs,mul_pow] at hi hn2
  dsimp only [coefficientEnergy,velocityEnergy]
  nlinarith only [hi,hn2,mul_nonneg (sq_nonneg (operatorHilbertSchmidt A)) (sq_nonneg c),
    mul_nonneg (sq_nonneg ‖z‖) (sq_nonneg c)]

theorem field_coefficient_sqrt_le (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z v : FSC.Coord d) (c : ℝ) :
    Real.sqrt (coefficientEnergy (A.adjoint v) (inner ℝ v z)) ≤
      Real.sqrt (velocityEnergy A z)*Real.sqrt (coefficientEnergy v c) := by
  simpa only [Real.sqrt_mul (velocityEnergy_nonneg A z)] using
    Real.sqrt_le_sqrt (field_coefficient_le A z v c)

theorem linearScore_field (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z v x : FSC.Coord d) :
    linearScore (A.adjoint v) (inner ℝ v z) x=inner ℝ v (A x+z) := by
  simp only [linearScore,inner_add_right,ContinuousLinearMap.adjoint_inner_left]

def regularMaterial (R : ι→FSC.Coord d) (γ : ℝ) (i j : ι) (x V : FSC.Coord d) : ℝ :=
  2*γ*(inner ℝ (R i) x*inner ℝ (R i) V-inner ℝ (R j) x*inner ℝ (R j) V)

def regularTransportDensity (R Z : ι→FSC.Coord d) (k : ι→ℝ)
    (γ : ℝ) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) (i j : ι) (x : FSC.Coord d) : ℝ :=
  (regularJump R γ i j x*massBulk A z x-regularMaterial R γ i j x (A x+z))*
    linearScore (Z i-Z j) (k i-k j) x-
      regularJump R γ i j x*inner ℝ (Z i-Z j) (A x+z)

/-- Exact five-term expansion on the current facet. The velocity has the
positive convention used by the formal transport formula. -/
theorem regularTransportDensity_on_facet
    (B R Z : ι→FSC.Coord d) (h k : ι→ℝ) (α γ : ℝ) (hα : α≠0)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (i j : ι) (x : FSC.Coord d) (hx : x∈affineFacet B h i j)
    (hV : inner ℝ (B i-B j) (A x+z)=linearScore (Z i-Z j) (k i-k j) x) :
    regularTransportDensity R Z k γ A z i j x =
      -(γ/α)*(
        linearScore (Z i-Z j) (k i-k j) x*
          (linearScore (R i+R j) 0 x*linearScore (Z i-Z j) (k i-k j) x)-
        linearScore (Z i-Z j) (k i-k j) x*
          (linearScore (R i+R j) 0 x*linearScore (A.adjoint (rowError B R α i-rowError B R α j))
            (inner ℝ (rowError B R α i-rowError B R α j) z) x)-
        linearScore (Z i-Z j) (k i-k j) x*
          (linearScore (rowError B R α i-rowError B R α j) (h i-h j) x*
            linearScore (A.adjoint (R i+R j)) (inner ℝ (R i+R j) z) x)+
        linearScore (Z i-Z j) (k i-k j) x*
          (linearScore (rowError B R α i-rowError B R α j) (h i-h j) x*
            linearScore (R i+R j) 0 x*massBulk A z x)-
        linearScore (A.adjoint (Z i-Z j)) (inner ℝ (Z i-Z j) z) x*
          (linearScore (rowError B R α i-rowError B R α j) (h i-h j) x*linearScore (R i+R j) 0 x)) := by
  have hv : inner ℝ (B i-B j) (-(A x+z))= -linearScore (Z i-Z j) (k i-k j) x := by
    rw [inner_neg_right,hV]
  have hd := regularJump_material_on_facet B R h α γ
    (linearScore (Z i-Z j) (k i-k j) x) hα i j x (-(A x+z)) hx hv
  rw [regularTransportDensity,regularJump_on_facet B R h α γ hα i j x hx]
  simp only [linearScore,add_zero,inner_add_left,inner_neg_right,
    regularMaterial,errorGap,ContinuousLinearMap.adjoint_inner_left,inner_add_right] at hd ⊢
  have hd' := congrArg (fun t:ℝ=>t*(inner ℝ (Z i-Z j) x+(k i-k j))) hd
  nlinarith only [hd']

theorem surface_five_abs_le
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (f₁ f₂ f₃ f₄ f₅ : FSC.Coord d→ℝ)
    (h₁ : Integrable f₁ (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (h₂ : Integrable f₂ (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (h₃ : Integrable f₃ (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (h₄ : Integrable f₄ (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (h₅ : Integrable f₅ (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    |surfaceIntegral B h i j (fun x=>f₁ x-f₂ x-f₃ x+f₄ x-f₅ x)| ≤
      |surfaceIntegral B h i j f₁|+|surfaceIntegral B h i j f₂|+
      |surfaceIntegral B h i j f₃|+|surfaceIntegral B h i j f₄|+|surfaceIntegral B h i j f₅| := by
  have h12 : Integrable (fun x=>f₁ x-f₂ x) (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := h₁.sub h₂
  have h123 : Integrable (fun x=>f₁ x-f₂ x-f₃ x) (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := h12.sub h₃
  have h1234 : Integrable (fun x=>f₁ x-f₂ x-f₃ x+f₄ x) (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := h123.add h₄
  rw [surfaceIntegral_sub B h i j _ _ h1234 h₅,
    surfaceIntegral_add B h i j _ _ h123 h₄,
    surfaceIntegral_sub B h i j _ _ h12 h₃,
    surfaceIntegral_sub B h i j _ _ h₁ h₂]
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)) le_rfl)

/-- Per-facet transport bound retaining the exact error coefficient. -/
theorem surface_regularTransport_abs_le
    (B R Z : ι→FSC.Coord d) (h k : ι→ℝ) (α γ : ℝ) (hα : α≠0)
    (hR : ∀ i,‖R i‖ ≤ 1) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (hV : ∀ i j x,inner ℝ (B i-B j) (A x+z)=linearScore (Z i-Z j) (k i-k j) x)
    (i j : ι) (hij : B i≠B j) (a m : ℝ) (hm : 1 ≤ m)
    (hprob : m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : |pairOffset B h i j|≤a*Real.sqrt (1+Real.log m)) :
    |surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)| ≤
      |γ/α| *(facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4)*
        (32*coefficientEnergy (Z i-Z j) (k i-k j)+
          2144*Real.sqrt (velocityEnergy A z)*
            Real.sqrt (coefficientEnergy (rowError B R α i-rowError B R α j) (h i-h j))*
              Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j))) := by
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  let v := Z i-Z j
  let c := k i-k j
  let e := rowError B R α i-rowError B R α j
  let b := h i-h j
  let s := R i+R j
  let w := facetWeight B h i j*quarticLogConstant a*(1+Real.log m)^4
  let V := Real.sqrt (velocityEnergy A z)
  let E := Real.sqrt (coefficientEnergy e b)
  let Q := Real.sqrt (coefficientEnergy v c)
  have hw : 0 ≤ w := mul_nonneg (mul_nonneg (facetWeight_nonneg B h i j)
    (by unfold quarticLogConstant; positivity)) (by positivity)
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hQ2 : Q^2=coefficientEnergy v c := Real.sq_sqrt (coefficientEnergy_nonneg v c)
  have hs : Real.sqrt (coefficientEnergy s 0) ≤ 2 := by
    have hn : ‖s‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hR i,hR j])
    simpa [coefficientEnergy,Real.sqrt_sq (norm_nonneg s)] using hn
  have he : Real.sqrt (coefficientEnergy (A.adjoint e) (inner ℝ e z)) ≤ V*E :=
    field_coefficient_sqrt_le A z e b
  have hv : Real.sqrt (coefficientEnergy (A.adjoint v) (inner ℝ v z)) ≤ V*Q :=
    field_coefficient_sqrt_le A z v c
  have hs' : Real.sqrt (coefficientEnergy (A.adjoint s) (inner ℝ s z)) ≤ 2*V := by
    refine (field_coefficient_sqrt_le A z s 0).trans ?_
    change V*Real.sqrt (coefficientEnergy s 0) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hs hV0]
  let f₁ := fun x=>linearScore v c x*(linearScore s 0 x*linearScore v c x)
  let f₂ := fun x=>linearScore v c x*(linearScore s 0 x*linearScore (A.adjoint e) (inner ℝ e z) x)
  let f₃ := fun x=>linearScore v c x*(linearScore e b x*linearScore (A.adjoint s) (inner ℝ s z) x)
  let f₄ := fun x=>linearScore v c x*(linearScore e b x*linearScore s 0 x*massBulk A z x)
  let f₅ := fun x=>linearScore (A.adjoint v) (inner ℝ v z) x*(linearScore e b x*linearScore s 0 x)
  have hp₁ : |surfaceIntegral B h i j f₁| ≤ 32*w*coefficientEnergy v c := by
    have hb := surface_three_scores_abs_le B h i j hij v s v c 0 c a m hm hprob ha
    calc
      _ ≤ 16*w*Q*Real.sqrt (coefficientEnergy s 0)*Q := hb
      _ ≤ 16*w*Q*2*Q := by gcongr
      _ = _ := by nlinarith only [congrArg (fun x:ℝ=>32*w*x) hQ2]
  have hp₂ : |surfaceIntegral B h i j f₂| ≤ 32*w*V*E*Q := by
    have hb := surface_three_scores_abs_le B h i j hij v s (A.adjoint e) c 0 (inner ℝ e z) a m hm hprob ha
    calc
      _ ≤ 16*w*Q*Real.sqrt (coefficientEnergy s 0)*Real.sqrt (coefficientEnergy (A.adjoint e) (inner ℝ e z)) := hb
      _ ≤ 16*w*Q*2*(V*E) := by gcongr
      _ = _ := by ring
  have hp₃ : |surfaceIntegral B h i j f₃| ≤ 32*w*V*E*Q := by
    have hb := surface_three_scores_abs_le B h i j hij v e (A.adjoint s) c b (inner ℝ s z) a m hm hprob ha
    calc
      _ ≤ 16*w*Q*E*Real.sqrt (coefficientEnergy (A.adjoint s) (inner ℝ s z)) := hb
      _ ≤ 16*w*Q*E*(2*V) := by gcongr
      _ = _ := by ring
  have hp₄ : |surfaceIntegral B h i j f₄| ≤ 2048*w*V*E*Q := by
    have hb := surface_three_scores_massBulk_abs_le B h i j hij v e s c b 0 A z a m hm hprob ha
    calc
      _ ≤ 1024*w*Q*E*Real.sqrt (coefficientEnergy s 0)*V := hb
      _ ≤ 1024*w*Q*E*2*V := by gcongr
      _ = _ := by ring
  have hp₅ : |surfaceIntegral B h i j f₅| ≤ 32*w*V*E*Q := by
    have hb := surface_three_scores_abs_le B h i j hij (A.adjoint v) e s (inner ℝ v z) b 0 a m hm hprob ha
    calc
      _ ≤ 16*w*Real.sqrt (coefficientEnergy (A.adjoint v) (inner ℝ v z))*E*Real.sqrt (coefficientEnergy s 0) := hb
      _ ≤ 16*w*(V*Q)*E*2 := by gcongr
      _ = _ := by ring
  have h₁ : Integrable f₁ μ := (linearScore_memLp μ v c 2 (by norm_num)).integrable_mul (product_memLp_two μ s v 0 c)
  have h₂ : Integrable f₂ μ := (linearScore_memLp μ v c 2 (by norm_num)).integrable_mul (product_memLp_two μ s (A.adjoint e) 0 (inner ℝ e z))
  have h₃ : Integrable f₃ μ := (linearScore_memLp μ v c 2 (by norm_num)).integrable_mul (product_memLp_two μ e (A.adjoint s) b (inner ℝ s z))
  have h₄ : Integrable f₄ μ := (linearScore_memLp μ v c 2 (by norm_num)).integrable_mul (product_massBulk_memLp_two μ e s b 0 A z)
  have h₅ : Integrable f₅ μ := (linearScore_memLp μ (A.adjoint v) (inner ℝ v z) 2 (by norm_num)).integrable_mul (product_memLp_two μ e s b 0)
  have hd : surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)=
      -(γ/α)*surfaceIntegral B h i j (fun x=>f₁ x-f₂ x-f₃ x+f₄ x-f₅ x) := by
    rw [←surfaceIntegral_const_mul]
    unfold surfaceIntegral
    congr 1
    apply setIntegral_congr_fun (isClosed_affineFacet B h i j).measurableSet
    intro x hx
    exact regularTransportDensity_on_facet B R Z h k α γ hα A z i j x hx (hV i j x)
  rw [hd,abs_mul,abs_neg]
  have hh := (surface_five_abs_le B h i j f₁ f₂ f₃ f₄ f₅ h₁ h₂ h₃ h₄ h₅).trans
    (add_le_add (add_le_add (add_le_add (add_le_add hp₁ hp₂) hp₃) hp₄) hp₅)
  convert mul_le_mul_of_nonneg_left hh (abs_nonneg (γ/α)) using 1 <;> dsimp only [w,V,E,Q,v,c,e,b] <;> ring

/-- Translation-invariant coefficient energy, with no label-count factor. -/
def rowScoreEnergy (Z : ι→FSC.Coord d) (k : ι→ℝ) (v : FSC.Coord d) (c : ℝ) : ℝ :=
  (∑ i,‖Z i-v‖^2)+(∑ i,(k i-c)^2)

theorem rowScoreEnergy_nonneg (Z : ι→FSC.Coord d) (k : ι→ℝ) (v : FSC.Coord d) (c : ℝ) :
    0 ≤ rowScoreEnergy Z k v c := by unfold rowScoreEnergy; positivity

theorem full_sqrt_product_le (a b : ι→ι→ℝ)
    (ha : ∀ i j,0 ≤ a i j) (hb : ∀ i j,0 ≤ b i j) :
    (∑ i,∑ j,Real.sqrt (a i j)*Real.sqrt (b i j)) ≤
      Real.sqrt (∑ i,∑ j,a i j)*Real.sqrt (∑ i,∑ j,b i j) := by
  have hrow (i : ι) := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j=>Real.sqrt (a i j)) (fun j=>Real.sqrt (b i j))
  simp_rw [Real.sq_sqrt (ha _ _),Real.sq_sqrt (hb _ _)] at hrow
  calc
    _ ≤ ∑ i,Real.sqrt (∑ j,a i j)*Real.sqrt (∑ j,b i j) :=
      Finset.sum_le_sum fun i _=>hrow i
    _ ≤ Real.sqrt (∑ i,(Real.sqrt (∑ j,a i j))^2)*
        Real.sqrt (∑ i,(Real.sqrt (∑ j,b i j))^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp_rw [Real.sq_sqrt (Finset.sum_nonneg fun j _=>ha _ j),
        Real.sq_sqrt (Finset.sum_nonneg fun j _=>hb _ j)]

theorem facet_sqrt_coefficient_le (B E Z : ι→FSC.Coord d) (h k : ι→ℝ)
    (degree : ℝ) (hdegree0 : 0 ≤ degree)
    (hdegree : ∀ i,∑ j,facetWeight B h i j ≤ degree)
    (e v : FSC.Coord d) (b c : ℝ) :
    (∑ i,∑ j,facetWeight B h i j*
      Real.sqrt (coefficientEnergy (E i-E j) (h i-h j))*
      Real.sqrt (coefficientEnergy (Z i-Z j) (k i-k j))) ≤
      4*degree*Real.sqrt (rowScoreEnergy E h e b)*Real.sqrt (rowScoreEnergy Z k v c) := by
  let w := facetWeight B h
  let a := fun i j=>coefficientEnergy (E i-E j) (h i-h j)
  let q := fun i j=>coefficientEnergy (Z i-Z j) (k i-k j)
  have hw (i j : ι) : 0 ≤ w i j := facetWeight_nonneg B h i j
  have ha (i j : ι) : 0 ≤ a i j := coefficientEnergy_nonneg _ _
  have hq (i j : ι) : 0 ≤ q i j := coefficientEnergy_nonneg _ _
  have he := facet_edge_score_coefficient_le B E h h degree hdegree e b
  have hz := facet_edge_score_coefficient_le B Z h k degree hdegree v c
  have hcross := full_sqrt_product_le (fun i j=>w i j*a i j) (fun i j=>w i j*q i j)
    (fun i j=>mul_nonneg (hw i j) (ha i j)) (fun i j=>mul_nonneg (hw i j) (hq i j))
  have hrewrite (i j : ι) : Real.sqrt (w i j*a i j)*Real.sqrt (w i j*q i j)=
      w i j*Real.sqrt (a i j)*Real.sqrt (q i j) := by
    rw [Real.sqrt_mul (hw i j),Real.sqrt_mul (hw i j)]
    nlinarith only [congrArg (fun t:ℝ=>t*Real.sqrt (a i j)*Real.sqrt (q i j))
      (Real.sq_sqrt (hw i j))]
  simp_rw [hrewrite] at hcross
  calc
    _ ≤ Real.sqrt (∑ i,∑ j,w i j*a i j)*Real.sqrt (∑ i,∑ j,w i j*q i j) := hcross
    _ ≤ Real.sqrt (4*degree*rowScoreEnergy E h e b)*
        Real.sqrt (4*degree*rowScoreEnergy Z k v c) := by
      apply mul_le_mul (Real.sqrt_le_sqrt he) (Real.sqrt_le_sqrt hz) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 4*degree),Real.sqrt_mul (by positivity : 0 ≤ 4*degree)]
      nlinarith only [congrArg (fun t:ℝ=>t*Real.sqrt (rowScoreEnergy E h e b)*Real.sqrt (rowScoreEnergy Z k v c))
        (Real.sq_sqrt (by positivity : 0 ≤ 4*degree))]

/-- The complete reference transport estimate before specializing its labels
to actual regular Gaussian moment tensors. The velocity energy appears only
with the error energy. -/
theorem regularTransport_log_le
    (B R Z : ι→FSC.Coord d) (h k : ι→ℝ) (α γ : ℝ) (hα : α≠0)
    (hR : ∀ i,‖R i‖ ≤ 1) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (hV : ∀ i j x,inner ℝ (B i-B j) (A x+z)=linearScore (Z i-Z j) (k i-k j) x)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree) (hinj : Function.Injective B)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j ≤ degree)
    (e v : FSC.Coord d) (b c : ℝ) :
    |(1/2:ℝ)*(∑ i,∑ j,surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j))| ≤
      8192*degree*quarticLogConstant a*(1+Real.log m)^4*|γ/α| *
        (rowScoreEnergy Z k v c+Real.sqrt (velocityEnergy A z)*
          Real.sqrt (rowScoreEnergy (rowError B R α) h e b)*Real.sqrt (rowScoreEnergy Z k v c)) := by
  let K := quarticLogConstant a*(1+Real.log m)^4
  let E := rowScoreEnergy (rowError B R α) h e b
  let Q := rowScoreEnergy Z k v c
  let V := Real.sqrt (velocityEnergy A z)
  let w := facetWeight B h
  let eq := fun i j=>coefficientEnergy (Z i-Z j) (k i-k j)
  let ee := fun i j=>coefficientEnergy (rowError B R α i-rowError B R α j) (h i-h j)
  have hK : 0 ≤ K := by unfold K quarticLogConstant; positivity
  have hE : 0 ≤ E := rowScoreEnergy_nonneg _ _ _ _
  have hQ : 0 ≤ Q := rowScoreEnergy_nonneg _ _ _ _
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hp (i j : ι) : |surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)| ≤
      |γ/α| *K*(32*(w i j*eq i j)+2144*V*(w i j*Real.sqrt (ee i j)*Real.sqrt (eq i j))) := by
    by_cases hij : i=j
    · subst j
      simp [surfaceIntegral_diagonal,w,facetWeight_self]
    have hh := surface_regularTransport_abs_le B R Z h k α γ hα hR A z hV i j
      (fun he=>hij (hinj he)) a m hm (hprob i j hij) (ha i j hij)
    convert hh using 1 <;> dsimp only [K,V,w,eq,ee] <;> ring
  have hs : |∑ i,∑ j,surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)| ≤
      |γ/α| *K*(32*(∑ i,∑ j,w i j*eq i j)+
        2144*V*(∑ i,∑ j,w i j*Real.sqrt (ee i j)*Real.sqrt (eq i j))) := by
    calc
      _ ≤ ∑ i,|∑ j,surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,∑ j,|surfaceIntegral B h i j (regularTransportDensity R Z k γ A z i j)| :=
        Finset.sum_le_sum fun i _=>Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,∑ j,|γ/α| *K*(32*(w i j*eq i j)+2144*V*(w i j*Real.sqrt (ee i j)*Real.sqrt (eq i j))) :=
        Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>hp i j
      _ = _ := by
        simp only [mul_add,Finset.mul_sum,←Finset.sum_add_distrib]
  have hsq : (∑ i,∑ j,w i j*eq i j) ≤ 4*degree*Q :=
    facet_edge_score_coefficient_le B Z h k degree hdegree v c
  have hcross : (∑ i,∑ j,w i j*Real.sqrt (ee i j)*Real.sqrt (eq i j)) ≤
      4*degree*Real.sqrt E*Real.sqrt Q :=
    facet_sqrt_coefficient_le B (rowError B R α) Z h k degree hdegree0 hdegree e v b c
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2:ℝ)*(|γ/α| *K*(32*(4*degree*Q)+2144*V*(4*degree*Real.sqrt E*Real.sqrt Q))) := by
      apply mul_le_mul_of_nonneg_left (hs.trans _) (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) hK)
      exact add_le_add (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (mul_le_mul_of_nonneg_left hcross (by positivity))
    _ ≤ 8192*degree*K*|γ/α| *(Q+V*Real.sqrt E*Real.sqrt Q) := by
      nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hdegree0 hK) (abs_nonneg (γ/α))) hQ,
        mul_nonneg (mul_nonneg (mul_nonneg hdegree0 hK) (abs_nonneg (γ/α)))
          (mul_nonneg (mul_nonneg hV0 (Real.sqrt_nonneg E)) (Real.sqrt_nonneg Q))]
    _ = _ := by dsimp only [K,E,Q,V]; ring

/-- Equality of the literal Gaussian moment material derivative with the
explicit regular material derivative, in every ambient dimension. -/
theorem actual_regularMaterial_eq {n : ℕ} (hn : 1 ≤ n)
    (R : Fin (n+2)→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (i j : Fin (n+2)) (x V : FSC.Coord d) :
    2*inner ℝ ((momentOperator R (fun _=>0) i-momentOperator R (fun _=>0) j) x) V=
      regularMaterial R (momentCoefficient n) i j x V := by
  have hd := actualLabelJump_hasDerivAt_line R (fun _=>0) i j x V
  have he : (fun t:ℝ=>quadraticLabelTest R (fun _=>0) i (x+t • V)-
      quadraticLabelTest R (fun _=>0) j (x+t • V))=
      (fun t:ℝ=>regularJump R (momentCoefficient n) i j (x+t • V)) := by
    funext t
    exact regular_quadraticLabelTest_difference_all_dimensions hn R hG i j _
  rw [he] at hd
  exact hd.unique (hasDerivAt_regularJump_line R (momentCoefficient n) i j x V)

/-- The exact regular reference term from the actual Hessian split equals
the signed transport density estimated above. -/
theorem referenceTransport_eq_regular {n : ℕ} (hn : 1 ≤ n)
    (B R : Fin (n+2)→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (δ : Parameters d (Fin (n+2))) :
    referenceTransport B R h (fun _=>0) L δ=
      (1/2:ℝ)*(∑ i,∑ j,surfaceIntegral B h i j
        (regularTransportDensity R δ.1 δ.2 (momentCoefficient n) (velocityMap L δ).1 (velocityMap L δ).2 i j)) := by
  unfold referenceTransport
  rw [global_correctedTensorHessian_surface B h σ hσ hlower L hL _
    (fun i=>momentOperator_symmetric R (fun _=>0) i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext x
  rw [corrected_transport_density]
  have hv : correctedLabelValue (momentOperator R (fun _=>0) i) 0 x-
      correctedLabelValue (momentOperator R (fun _=>0) j) 0 x=
      regularJump R (momentCoefficient n) i j x := by
    simp only [correctedLabelValue,sub_zero,momentOperator_quadraticScore]
    exact regular_quadraticLabelTest_difference_all_dimensions hn R hG i j x
  have hs : affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x=
      linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x := by
    simp only [affineScore,linearScore,inner_sub_left]
    ring
  rw [hv,hs,actual_regularMaterial_eq hn R hG]
  unfold regularTransportDensity
  ring

/-- Dimension-free quantitative estimate for the literal regular-reference
part of the balanced second-chaos Hessian. There is no abstract replacement
of its tensors or facets, and no factor counting coordinates or labels. -/
theorem referenceTransport_regular_log_le {n : ℕ} (hn : 1 ≤ n)
    (B R : Fin (n+2)→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (h : Fin (n+2)→ℝ) (α : ℝ) (hα : α≠0)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (δ : Parameters d (Fin (n+2)))
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0 ≤ degree)
    (hprob : ∀ i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀ i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀ i,∑ j,facetWeight B h i j ≤ degree)
    (e v : FSC.Coord d) (b c : ℝ) :
    |referenceTransport B R h (fun _=>0) L δ| ≤
      8192*degree*quarticLogConstant a*(1+Real.log m)^4*|momentCoefficient n/α| *
        (rowScoreEnergy δ.1 δ.2 v c+Real.sqrt (velocityEnergy (velocityMap L δ).1 (velocityMap L δ).2)*
          Real.sqrt (rowScoreEnergy (rowError B R α) h e b)*Real.sqrt (rowScoreEnergy δ.1 δ.2 v c)) := by
  have hR (i : Fin (n+2)) : ‖R i‖ ≤ 1 := by
    have hnorm : ‖R i‖^2=1-1/((n+2:ℕ):ℝ) := by
      rw [←real_inner_self_eq_norm_sq,hG]
      simp
    have hpos : 0 ≤ 1/((n+2:ℕ):ℝ) := by positivity
    nlinarith [norm_nonneg (R i)]
  have hV (i j : Fin (n+2)) (x : FSC.Coord d) :
      inner ℝ (B i-B j) ((velocityMap L δ).1 x+(velocityMap L δ).2)=
        linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x := by
    rw [inner_add_right,velocityMap_first,velocityMap_second,hL,hL]
    simp only [linearScore,inner_sub_left]
  rw [referenceTransport_eq_regular hn B R hG h σ hσ hlower L hL δ]
  exact regularTransport_log_le B R δ.1 h δ.2 α (momentCoefficient n) hα hR
    (velocityMap L δ).1 (velocityMap L δ).2 hV a m degree hm hdegree0
    (affineIndependent_of_centered_lower B σ hσ hlower).injective hprob ha hdegree e v b c

end NegativeVotingRegularTransportBound
