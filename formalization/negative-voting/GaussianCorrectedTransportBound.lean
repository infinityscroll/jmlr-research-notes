import GaussianBalancedOffsetComparison
import GaussianAdjustedTensorBulkNorm

/-! Quantitative actual facet transport for a centered-tensor remainder and
one scalar mass-adjoint correction. The reference regular part must be split
before this generic bound is used. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCorrectedTransportBound
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingGlobalTensorTransport NegativeVotingCoherentLiftHessian
  NegativeVotingFanQuadraticTransport NegativeVotingFanMassSecondDerivative
  NegativeVotingTensorFacetAggregation NegativeVotingAdjustedTensorBulkNorm
  NegativeVotingQuadraticBulkNorm NegativeVotingQuadraticTensorBulkNorm
  NegativeVotingReferenceJumpComparison NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound NegativeVotingFanJacobian
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingPolynomialFacetLogBound
  NegativeVotingPolynomialDegree NegativeVotingWeightedFacet NegativeVotingDisintegration
  NegativeVotingCapTail NegativeVotingSecondChaosFacetGradient
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def rowFacetPairing (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (f : ι→FSC.Coord d→ℝ) : ℝ :=
  ∑i,∑j,surfaceIntegral B h i j (fun x=>f i x*
    (inner ℝ (D i-D j) x+(k i-k j)))

/-- Finite Cauchy--Schwarz over the actual oriented surfaces. -/
theorem rowFacetPairing_abs_le_energies (B D : ι→FSC.Coord d) (h k : ι→ℝ)
    (hinj : Function.Injective B) (f : ι→FSC.Coord d→ℝ)
    (hfc : ∀i,Continuous (f i))
    (hf : ∀i j,MemLp (f i) 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    |rowFacetPairing B D h k f|≤Real.sqrt (affineWeightedFacetEnergy B h f)*
      Real.sqrt (affineWeightedEdgeScoreEnergy B D h k) := by
  have hh := ordered_integral_mul_abs_le (fun _ _=>FSC.Coord d)
    (fun i j=>FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))
    (affineFacet B h) (fun i _=>f i)
    (fun i j x=>inner ℝ (D i-D j) x+(k i-k j))
    (fun i j=>gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖)
    (fun i j=>div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    (fun i j _=>(hf i j).restrict _)
    (fun i j _=>by
      let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (D i-D j) |>.add
        (memLp_const (k i-k j))).restrict _)
  have he : rowFacetPairing B D h k f=
      ∑i,∑j∈Finset.univ.erase i,gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
        ∫x in affineFacet B h i j,f i x*(inner ℝ (D i-D j) x+(k i-k j))
          ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) := by
    unfold rowFacetPairing
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),surfaceIntegral_diagonal,add_zero]
    rfl
  change _ ≤ Real.sqrt (orderedFacetEnergy _ _ _ _ _ _)*
    Real.sqrt (orderedFacetEnergy _ _ _ _ _ _) at hh
  rw [orderedFacetEnergy_eq_ambient B h hinj _ (fun i _=>hfc i),
    orderedFacetEnergy_eq_ambient B h hinj _ (fun _ _=>by fun_prop)] at hh
  rw [he]
  exact hh

/-- Ambient norm of the corrected scalar label, retaining cancellation in
its centered quadratic score. -/
theorem correctedLabelValue_integral_sq_le
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) :
    (∫x,(correctedLabelValue U c x)^2 ∂stdGaussian (FSC.Coord d))≤
      4*((operatorHilbertSchmidt U)^2+c^2) := by
  let μ := stdGaussian (FSC.Coord d)
  have hq := (quadraticScore_memLp_four μ U).mono_exponent (by norm_num : (2:ENNReal)≤4)
  have hf := squared_integrable hq
  have hc : Integrable (fun _ : FSC.Coord d=>c^2) μ := integrable_const _
  have hh := integral_mono (squared_integrable (correctedLabelValue_memLp_two μ U c))
    ((hf.const_mul 2).add (hc.const_mul 2)) (fun x=>by
      dsimp only [correctedLabelValue,Pi.add_apply]
      nlinarith only [sq_nonneg (quadraticScore U x+c)])
  simp only [Pi.add_apply] at hh
  rw [integral_add (hf.const_mul 2) (hc.const_mul 2),integral_const_mul,integral_const_mul,
    integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  have hb := quadraticScore_integral_sq_le U
  change (∫x,quadraticScore U x^2 ∂μ)≤_ at hb
  nlinarith only [hh,hb,sq_nonneg c]

/-- The actual corrected label trace is controlled by weighted degree. -/
theorem affineWeightedFacetEnergy_correctedLabelValue_le
    (B : ι→FSC.Coord d) (h : ι→ℝ)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d) (c : ι→ℝ)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree) (hinj : Function.Injective B)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,(∑j∈Finset.univ.erase i,facetWeight B h i j)≤degree) :
    affineWeightedFacetEnergy B h (fun i=>correctedLabelValue (U i) (c i))≤
      4*degree*quarticLogConstant a*(1+Real.log m)^4*
        ∑i,((operatorHilbertSchmidt (U i))^2+(c i)^2) := by
  have hpoly (i j : ι) (_ : i≠j) :
      (fun x=>correctedLabelValue (U i) (c i) (reconstructLinear (pairNormal B i j)
        (canonicalTangentCoordinates (pairNormal B i j)) x))∈polynomialSpace 4 := by
    let R := reconstructLinear (pairNormal B i j) (canonicalTangentCoordinates (pairNormal B i j))
    have hq : (fun x=>quadraticScore (U i) (R x))∈polynomialSpace 2 := by
      simpa only [quadraticScore,inner_zero_left,add_zero] using massBulk_expression_mem R (U i) 0
    apply polynomialSpace_mono (by decide : 2≤4)
    convert (polynomialSpace 2).sub_mem hq
      ((polynomialSpace 2).smul_mem (c i) (one_mem (κ:=Fin (_+1)) 2)) using 1
    funext x
    simp [correctedLabelValue,R]
  have hb := affineWeightedFacetEnergy_polynomial_log_le B h
    (fun i=>correctedLabelValue (U i) (c i)) a m degree hm hinj
    (fun i=>by unfold correctedLabelValue quadraticScore; fun_prop) hpoly hprob ha hdegree
  refine hb.trans ?_
  calc
    _ ≤ degree*quarticLogConstant a*(1+Real.log m)^4*
        ∑i,4*((operatorHilbertSchmidt (U i))^2+(c i)^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>
        correctedLabelValue_integral_sq_le (U i) (c i)) (by unfold quarticLogConstant; positivity)
    _ = _ := by simp only [Finset.mul_sum]; ring

/-- Coefficients of a score composed with the global affine velocity cost
only the velocity's Hilbert--Schmidt-plus-shift energy. -/
theorem composed_score_coefficient_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z : FSC.Coord d) (D : ι→FSC.Coord d) (v : FSC.Coord d) :
    ((∑i,‖A.adjoint (D i)-A.adjoint v‖^2)+
      ∑i,(inner ℝ (D i) z-inner ℝ v z)^2)≤
      ((operatorHilbertSchmidt A)^2+‖z‖^2)*∑i,‖D i-v‖^2 := by
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hn : ‖A.adjoint (D i-v)‖≤operatorHilbertSchmidt A*‖D i-v‖ :=
    (A.adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [LinearIsometryEquiv.norm_map] using operator_norm_le_HilbertSchmidt A)
      (norm_nonneg _))
  have hi := pow_le_pow_left₀ (abs_nonneg (inner ℝ (D i-v) z))
    (abs_real_inner_le_norm (D i-v) z) 2
  have hn' := pow_le_pow_left₀ (norm_nonneg (A.adjoint (D i-v))) hn 2
  simp only [map_sub,inner_sub_left,sq_abs,mul_pow] at hi hn'
  nlinarith only [hi,hn']

/-- The composed score energy has no label-count or dimension factor. -/
theorem composed_edgeScoreEnergy_log_le
    (B D : ι→FSC.Coord d) (h : ι→ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree) (hinj : Function.Injective B)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree) (v : FSC.Coord d) :
    affineWeightedEdgeScoreEnergy B (fun i=>A.adjoint (D i)) h (fun i=>inner ℝ (D i) z)≤
      8*degree*quarticLogConstant a*(1+Real.log m)^4*
        ((operatorHilbertSchmidt A)^2+‖z‖^2)*∑i,‖D i-v‖^2 := by
  have hh := affineWeightedEdgeScoreEnergy_log_le B (fun i=>A.adjoint (D i)) h
    (fun i=>inner ℝ (D i) z) a m degree hm hinj hprob ha hdegree (A.adjoint v) (inner ℝ v z)
  refine hh.trans ?_
  convert mul_le_mul_of_nonneg_left (composed_score_coefficient_le A z D v)
    (by unfold quarticLogConstant; positivity : 0≤8*degree*quarticLogConstant a*(1+Real.log m)^4)
    using 1 <;> ring

/-- A scalar bound in terms of the two literal actual facet energies.
This is stated for arbitrary symmetric tensor tests, so it can be applied to
the actual moment difference before any inverse-lift bound is substituted. -/
theorem correctedTensorHessian_sum_abs_le_energies
    (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (U : ι→FSC.Coord d→L[ℝ]FSC.Coord d) (hU : ∀i,(U i).toLinearMap.IsSymmetric)
    (c : ι→ℝ) (ε δ : Parameters d ι) :
    let V := velocityMap L δ
    |∑i,correctedTensorHessian B h L i (U i) (c i) ε δ|≤
      Real.sqrt (affineWeightedFacetEnergy B h (fun i=>correctedLabelBulk (U i) (c i) V.1 V.2))*
        Real.sqrt (affineWeightedEdgeScoreEnergy B ε.1 h ε.2)+
      Real.sqrt (affineWeightedFacetEnergy B h (fun i=>correctedLabelValue (U i) (c i)))*
        Real.sqrt (affineWeightedEdgeScoreEnergy B (fun i=>V.1.adjoint (ε.1 i)) h
          (fun i=>inner ℝ (ε.1 i) V.2)) := by
  dsimp only
  let V := velocityMap L δ
  let F := fun i=>correctedLabelBulk (U i) (c i) V.1 V.2
  let G := fun i=>correctedLabelValue (U i) (c i)
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij he
  have hF (i j : ι) : MemLp (F i) 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
    letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
    exact correctedLabelBulk_memLp_two _ _ _ _ _
  have hG (i j : ι) : MemLp (G i) 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
    letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
    exact correctedLabelValue_memLp_two _ _ _
  have he : (∑i,correctedTensorHessian B h L i (U i) (c i) ε δ)=
      rowFacetPairing B ε.1 h ε.2 F-
        rowFacetPairing B (fun i=>V.1.adjoint (ε.1 i)) h (fun i=>inner ℝ (ε.1 i) V.2) G := by
    simp_rw [correctedTensorHessian_surface B h σ hσ hlower L hL _ _ (hU _)]
    unfold rowFacetPairing
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
    have hs : MemLp (fun x:FSC.Coord d=>inner ℝ (ε.1 i-ε.1 j) x+(ε.2 i-ε.2 j)) 2 μ :=
      ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (ε.1 i-ε.1 j)).add (memLp_const _)
    have ht : MemLp (fun x:FSC.Coord d=>inner ℝ (V.1.adjoint (ε.1 i)-V.1.adjoint (ε.1 j)) x+
        (inner ℝ (ε.1 i) V.2-inner ℝ (ε.1 j) V.2)) 2 μ :=
      ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) _).add (memLp_const _)
    have hfs : Integrable (fun x=>F i x*(inner ℝ (ε.1 i-ε.1 j) x+(ε.2 i-ε.2 j))) μ :=
      (hF i j).integrable_mul hs
    have hgt : Integrable (fun x=>G i x*(inner ℝ (V.1.adjoint (ε.1 i)-V.1.adjoint (ε.1 j)) x+
        (inner ℝ (ε.1 i) V.2-inner ℝ (ε.1 j) V.2))) μ := (hG i j).integrable_mul ht
    dsimp only
    rw [←surfaceIntegral_sub B h i j _ _ hfs hgt]
    congr 1
    funext x
    simp only [F,G,V,affineScore,inner_sub_left,inner_add_right,
      ContinuousLinearMap.adjoint_inner_left]
    ring
  rw [he]
  refine (abs_sub _ _).trans (add_le_add
    (rowFacetPairing_abs_le_energies B ε.1 h ε.2 hinj F
      (fun i=>by unfold F correctedLabelBulk tensorBulk NegativeVotingFanMassSecondDerivative.massBulk quadraticScore; fun_prop) hF)
    (rowFacetPairing_abs_le_energies B (fun i=>V.1.adjoint (ε.1 i)) h
      (fun i=>inner ℝ (ε.1 i) V.2) hinj G
      (fun i=>by unfold G correctedLabelValue quadraticScore; fun_prop) hG))

set_option maxHeartbeats 800000 in
/-- An actual quantitative remainder estimate with no dimension or number-of-
labels factor. The velocity inverse cost remains explicit until the bounded
coherent lift is substituted. -/
theorem correctedTensorHessian_sum_log_le
    (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift B L)
    (U : ι→FSC.Coord d→L[ℝ]FSC.Coord d) (hU : ∀i,(U i).toLinearMap.IsSymmetric)
    (c : ι→ℝ) (ε δ : Parameters d ι)
    (a m degree : ℝ) (hm : 1 ≤ m) (hdegree0 : 0≤degree)
    (hprob : ∀i j,i≠j→m^(-4096:ℝ)≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (ha : ∀i j,i≠j→|pairOffset B h i j|≤a*Real.sqrt (1+Real.log m))
    (hdegree : ∀i,∑j,facetWeight B h i j≤degree) (v : FSC.Coord d) (b : ℝ) :
    let V := velocityMap L δ
    |∑i,correctedTensorHessian B h L i (U i) (c i) ε δ|≤
      520*degree*quarticLogConstant a*(1+Real.log m)^4*
        Real.sqrt ((operatorHilbertSchmidt V.1)^2+‖V.2‖^2)*
        Real.sqrt (∑i,((operatorHilbertSchmidt (U i))^2+(c i)^2))*
        Real.sqrt ((∑i,‖ε.1 i-v‖^2)+(∑i,(ε.2 i-b)^2)) := by
  dsimp only
  let V := velocityMap L δ
  let K := degree*quarticLogConstant a*(1+Real.log m)^4
  let E := (operatorHilbertSchmidt V.1)^2+‖V.2‖^2
  let S : ℝ := ∑i:ι,((operatorHilbertSchmidt (U i))^2+(c i)^2)
  let T : ℝ := (∑i:ι,‖ε.1 i-v‖^2)+(∑i:ι,(ε.2 i-b)^2)
  have hK : 0≤K := by unfold K quarticLogConstant; positivity
  have hE : 0≤E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS : 0≤S := Finset.sum_nonneg fun (i:ι) _=>
    add_nonneg (sq_nonneg (operatorHilbertSchmidt (U i))) (sq_nonneg (c i))
  have hT : 0≤T := add_nonneg (Finset.sum_nonneg fun (i:ι) _=>sq_nonneg ‖ε.1 i-v‖)
    (Finset.sum_nonneg fun (i:ι) _=>sq_nonneg (ε.2 i-b))
  have hinj : Function.Injective B := fun i j he=>by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij he
  have hdeg (i : ι) : (∑j∈Finset.univ.erase i,facetWeight B h i j)≤degree :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j _ _=>facetWeight_nonneg B h i j)).trans (hdegree i)
  have h1 : affineWeightedFacetEnergy B h (fun i=>correctedLabelBulk (U i) (c i) V.1 V.2)≤
      32768*K*E*S := by
    have hh := affineWeightedFacetEnergy_adjustedTensorBulk_le B h U c V.1 V.2
      a m degree hm hdegree0 hinj hprob ha hdeg
    change affineWeightedFacetEnergy B h (fun i=>correctedLabelBulk (U i) (c i) V.1 V.2)≤
      20736*degree*quarticLogConstant a*(1+Real.log m)^4*E*S at hh
    refine hh.trans ?_
    calc
      _ = 20736*K*E*S := by dsimp only [K]; ring
      _ ≤ 32768*K*E*S := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (20736:ℝ)≤32768) hK) hE) hS
  have h2 : affineWeightedEdgeScoreEnergy B ε.1 h ε.2≤8*K*T := by
    simpa only [K,T,mul_assoc] using
      affineWeightedEdgeScoreEnergy_log_le B ε.1 h ε.2 a m degree hm hinj hprob ha hdegree v b
  have h3 : affineWeightedFacetEnergy B h (fun i=>correctedLabelValue (U i) (c i))≤8*K*S := by
    have hh := affineWeightedFacetEnergy_correctedLabelValue_le B h U c
      a m degree hm hdegree0 hinj hprob ha hdeg
    change affineWeightedFacetEnergy B h (fun i=>correctedLabelValue (U i) (c i))≤
      4*degree*quarticLogConstant a*(1+Real.log m)^4*S at hh
    refine hh.trans ?_
    calc
      _ = 4*K*S := by dsimp only [K]; ring
      _ ≤ 8*K*S := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ)≤8) hK) hS
  have h4 : affineWeightedEdgeScoreEnergy B (fun i=>V.1.adjoint (ε.1 i)) h
      (fun i=>inner ℝ (ε.1 i) V.2)≤8*K*E*T := by
    have hh := composed_edgeScoreEnergy_log_le B ε.1 h V.1 V.2 a m degree hm hdegree0
      hinj hprob ha hdegree v
    have ht : (∑i,‖ε.1 i-v‖^2)≤T := by
      dsimp only [T]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>sq_nonneg _)
    refine hh.trans ?_
    convert mul_le_mul_of_nonneg_left ht
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) hK) hE) using 1 <;>
      dsimp only [K,E] <;> ring
  have hh := correctedTensorHessian_sum_abs_le_energies B h σ hσ hlower L hL U hU c ε δ
  refine hh.trans ((add_le_add
    (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).trans_eq ?_)
  have he1 : Real.sqrt (32768*K*E*S)*Real.sqrt (8*K*T)=
      512*K*Real.sqrt E*Real.sqrt S*Real.sqrt T := by
    rw [←Real.sqrt_mul (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hE) hS)]
    have he : (32768*K*E*S)*(8*K*T)=(512*K)^2*E*S*T := by ring
    rw [he,Real.sqrt_mul (mul_nonneg (mul_nonneg (sq_nonneg _) hE) hS),
      Real.sqrt_mul (mul_nonneg (sq_nonneg _) hE),Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg (by norm_num) hK)]
  have he2 : Real.sqrt (8*K*S)*Real.sqrt (8*K*E*T)=
      8*K*Real.sqrt E*Real.sqrt S*Real.sqrt T := by
    rw [←Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num) hK) hS)]
    have he : (8*K*S)*(8*K*E*T)=(8*K)^2*E*S*T := by ring
    rw [he,Real.sqrt_mul (mul_nonneg (mul_nonneg (sq_nonneg _) hE) hS),
      Real.sqrt_mul (mul_nonneg (sq_nonneg _) hE),Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg (by norm_num) hK)]
  rw [he1,he2]
  dsimp only [K,E,S,T,V]
  ring

end NegativeVotingCorrectedTransportBound
