import GaussianTensorHessianContraction
import GaussianSecondChaosFacetGradient

/-! Exact global affine transport cancellation for quadratic label tests.
This module does not estimate the terms separately. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingGlobalTensorTransport
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingMovingCap NegativeVotingFacetDegree NegativeVotingCapTail
  NegativeVotingQuadraticAffineTransport NegativeVotingAffineOperatorDerivative
  NegativeVotingFanMassSecondDerivative NegativeVotingFanQuadraticMoments
  NegativeVotingTensorHessianContraction NegativeVotingCoherentLiftHessian
  NegativeVotingSecondChaosHessian NegativeVotingQuadraticBulkNorm
  NegativeVotingQuadraticTensorBulkNorm NegativeVotingFanHessian
  NegativeVotingSecondChaosFacetGradient NegativeVotingFanQuarticMoments
  NegativeVotingQuadraticBulkDifferential NegativeVotingAffineLogMassBound
  NegativeVotingWeightedFacet
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Row/offset variation induced by one fixed positive affine field. -/
def affineParameterVelocity (B : ι→FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : Parameters d ι :=
  (fun i=>A.adjoint (B i),fun i=>inner ℝ (B i) z)

theorem fanParameterMap_affineParameterVelocity (B : ι→FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) (i : ι) :
    fanParameterMap B i (affineParameterVelocity B A z)=affineVelocity (cellNormals B i) A z := by
  apply Prod.ext
  · funext j
    change ‖B j.1-B i‖⁻¹ • (A.adjoint (B j.1)-A.adjoint (B i))=
      A.adjoint (‖B j.1-B i‖⁻¹ • (B j.1-B i))
    simp only [map_smul,map_sub]
  · funext j
    change ‖B j.1-B i‖⁻¹*(inner ℝ (B i) z-inner ℝ (B j.1) z)=
      -inner ℝ (‖B j.1-B i‖⁻¹ • (B j.1-B i)) z
    rw [real_inner_smul_left,inner_sub_left]
    ring

theorem testedCellDerivative_bilinear_affineParameters (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    testedCellDerivative B h i (fun x=>inner ℝ v x*inner ℝ y x)
      (affineParameterVelocity B A z)=
      ∫ x in winningCell B h i,affineBulk v y A z x ∂stdGaussian (FSC.Coord d) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i)
    (fun x=>inner ℝ v x*inner ℝ y x) (fanParameterMap B i (affineParameterVelocity B A z))=_
  rw [fanParameterMap_affineParameterVelocity,
    capJointDerivative_bilinear_affine_bulk _ (cellNormals_unit B σ hσ hlower i) _
      (cellNormals_noCoincident B h σ hσ hlower i)]
  have hB : Function.Injective B := fun j k he=>by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have he := normalized_cap_eq_winningCell B hB i (B,h)
  rw [fanParameterMap_base] at he
  rw [he]

theorem testedCellDerivative_one_affineParameters (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    testedCellDerivative B h i (fun _=>1) (affineParameterVelocity B A z)=
      ∫ x in winningCell B h i,massBulk A z x ∂stdGaussian (FSC.Coord d) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i)
    (fun _=>1) (fanParameterMap B i (affineParameterVelocity B A z))=_
  rw [fanParameterMap_affineParameterVelocity,
    capJointDerivative_one_affine_bulk _ (cellNormals_unit B σ hσ hlower i) _
      (cellNormals_noCoincident B h σ hσ hlower i)]
  have hB : Function.Injective B := fun j k he=>by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have he := normalized_cap_eq_winningCell B hB i (B,h)
  rw [fanParameterMap_base] at he
  rw [he]

theorem quadraticScore_growth (U : FSC.Coord d→L[ℝ] FSC.Coord d) :
    PolynomialGrowth (quadraticScore U) 2 := by
  have hh := PolynomialGrowth.finsetSum Finset.univ
    (fun j:Fin d=>fun x=>∑ k,operatorEntries U j k*tensorTest j k x) 2 (fun j _=>
      PolynomialGrowth.finsetSum Finset.univ _ 2 (fun k _=>
        (show PolynomialGrowth (tensorTest j k) 2 from ⟨by unfold tensorTest; fun_prop,
          1,by norm_num,(by
            intro x
            simp only [one_mul]
            exact (tensorTest_growth j k x).trans (by nlinarith [norm_nonneg x]))⟩).const_mul _))
  have he : quadraticScore U=(fun x=>∑ j,∑ k,operatorEntries U j k*tensorTest j k x) := by
    funext x
    exact quadratic_score_eq_entries U x
  rw [he]
  exact hh

theorem integral_quadraticScore_entries (U : FSC.Coord d→L[ℝ] FSC.Coord d)
    (s : Set (FSC.Coord d)) :
    (∫ x in s,quadraticScore U x ∂stdGaussian (FSC.Coord d))=
      ∑ j,∑ k,operatorEntries U j k*
        ∫ x in s,tensorTest j k x ∂stdGaussian (FSC.Coord d) := by
  have he : quadraticScore U=(fun x=>∑ j,∑ k,operatorEntries U j k*tensorTest j k x) := by
    funext x
    exact quadratic_score_eq_entries U x
  rw [he]
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum Finset.univ
    (fun k _=>((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable (by norm_num)).const_mul
      (operatorEntries U j k) |>.restrict))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>
    ((tensorTest_memLp (stdGaussian (FSC.Coord d)) j k).integrable (by norm_num)).const_mul
      (operatorEntries U j k) |>.restrict)]
  simp only [integral_const_mul]

theorem testedCellDerivative_quadraticScore_entries (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) :
    testedCellDerivative B h i (quadraticScore U)=
      ∑ j,∑ k,operatorEntries U j k • testedCellDerivative B h i (tensorTest j k) := by
  obtain ⟨C,hC,hF⟩ := (quadraticScore_growth U).2
  have hd := NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B h σ hσ hlower i _
    (quadraticScore_growth U).1 (2*C) (by positivity) (fun x=>(hF x).trans (by
      have hr := norm_nonneg x
      nlinarith [mul_nonneg hC (sq_nonneg (‖x‖-1))]))
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) fun j _=>
    HasFDerivAt.fun_sum (u:=Finset.univ) fun k _=>
      (hasFDerivAt_secondMomentTensor B h σ hσ hlower i j k).const_smul (operatorEntries U j k)
  apply hd.unique
  apply hs.congr_of_eventuallyEq
  filter_upwards with p
  simpa only [Pi.smul_apply,smul_eq_mul,secondMomentTensor] using
    integral_quadraticScore_entries U (winningCell p.1 p.2 i)

/-- The apparent volume correction is itself an actual first facet derivative.
The affine field is arbitrary: no surjectivity of the chosen score lift is assumed. -/
theorem integral_tensorBulk_eq_derivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (hU : U.toLinearMap.IsSymmetric) (z : FSC.Coord d) :
    (∫ x in winningCell B h i,tensorBulk U A z x ∂stdGaussian (FSC.Coord d))=
      testedCellDerivative B h i (quadraticScore U) (affineParameterVelocity B A z) := by
  rw [integral_tensorBulk_contraction U A hU z,
    testedCellDerivative_quadraticScore_entries B h σ hσ hlower i U]
  simp only [sum_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have ht : tensorTest j k=centeredBilinearTest (EuclideanSpace.basisFun (Fin d) ℝ j)
      (EuclideanSpace.basisFun (Fin d) ℝ k) := by
    funext x
    simp only [tensorTest,centeredBilinearTest,EuclideanSpace.basisFun_inner,
      (EuclideanSpace.basisFun (Fin d) ℝ).inner_eq_ite]
  rw [ht,testedCellDerivative_centered_eq B h σ hσ hlower]
  change _ = testedCellDerivative B h i (fun x=>inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) x *
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ k) x) (affineParameterVelocity B A z) -
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k) *
    testedCellDerivative B h i (fun _=>1) (affineParameterVelocity B A z)
  rw [testedCellDerivative_bilinear_affineParameters B h σ hσ hlower,
    testedCellDerivative_one_affineParameters B h σ hσ hlower]



/-- The quartic version of the actual oriented surface derivative formula. -/
theorem testedCellDerivative_quartic_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d→ℝ) (hF : PolynomialGrowth F 4) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ=∑ j,surfaceIntegral B h i j
      (fun x=>F x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)) := by
  obtain ⟨C,hC,hFb⟩ := hF.quartic_bound
  rw [NegativeVotingFanQuarticMoments.testedCellDerivative_apply_ambient B h σ hσ hlower i F hF.1 C hC hFb]
  have he (j : ι) : (fun x : FSC.Coord d=>F x*(inner ℝ (δ.1 i-δ.1 j) x+δ.2 i-δ.2 j))=
      fun x=>F x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x) := by
    funext x
    simp only [affineScore,inner_sub_left]
    ring
  simp_rw [he]
  change (∑ j : {j : ι // j ≠ i},surfaceIntegral B h j.1 i
    (fun x=>F x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j.1 x)))=_
  calc
    _ = ∑ j : {j : ι // j ≠ i},surfaceIntegral B h i j.1
        (fun x=>F x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j.1 x)) :=
      Finset.sum_congr rfl (fun j _=>surfaceIntegral_reverse B h i j.1 _)
    _ = _ := by
      rw [←Finset.sum_subtype (p:=fun j : ι=>j≠i) (Finset.univ.erase i)
        (fun j=>by simp) (fun j=>surfaceIntegral B h i j
          (fun x=>F x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)))]
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro j _ hj
      have hji : j=i := by simpa using hj
      rw [hji,surfaceIntegral_diagonal]

theorem testedCellDerivative_quadraticScore_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (δ : Parameters d ι) :
    testedCellDerivative B h i (quadraticScore U) δ=∑ j,surfaceIntegral B h i j
      (fun x=>quadraticScore U x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)) := by
  obtain ⟨C,hC,hF⟩ := (quadraticScore_growth U).2
  exact testedCellDerivative_apply_surface B h σ hσ hlower i _
    (quadraticScore_growth U).1 (2*C) (by positivity) (fun x=>(hF x).trans (by
      have hr := norm_nonneg x
      nlinarith [mul_nonneg hC (sq_nonneg (‖x‖-1))])) δ.1 δ.2

/-- Coherence converts the composed bulk correction into the derivative of
one score gap along the SAME global affine field. -/
theorem composed_affineParameter_score_gap (B : ι→FSC.Coord d)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L)
    (ε δ : Parameters d ι) (i j : ι) (x : FSC.Coord d) :
    let η := affineParameterVelocity B ((velocityMap L ε).1.comp (velocityMap L δ).1)
      ((velocityMap L ε).1 (velocityMap L δ).2)
    affineScore η.1 η.2 i x-affineScore η.1 η.2 j x=
      inner ℝ (ε.1 i-ε.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2) := by
  dsimp only [affineParameterVelocity,affineScore]
  simp only [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.comp_apply]
  rw [←inner_add_right,←inner_add_right,←inner_sub_left,←map_add]
  change inner ℝ (B i-B j) (L (fun k=>inner ℝ (ε.1 k)
    ((velocityMap L δ).1 x+(velocityMap L δ).2)))=_
  rw [hL]
  rw [inner_sub_left]

/-- The actual tensor Hessian with the volume correction converted to facets.
This is still an exact signed formula, before any triangle inequality. -/
theorem centeredHessian_contraction_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (hU : U.toLinearMap.IsSymmetric)
    (ε δ : Parameters d ι) :
    (∑ j,∑ k,operatorEntries U j k*
      centeredHessian B h L i (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ k) ε δ)=
      ∑ j,surfaceIntegral B h i j (fun x=>
        tensorBulk U (velocityMap L δ).1 (velocityMap L δ).2 x *
          (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x) -
        quadraticScore U x * inner ℝ (ε.1 i-ε.1 j)
          ((velocityMap L δ).1 x+(velocityMap L δ).2)) := by
  rw [centeredHessian_contraction_apply B h σ hσ hlower L i U hU,
    integral_tensorBulk_eq_derivative B h σ hσ hlower i U _ hU,
    testedCellDerivative_quartic_surface B h σ hσ hlower i _ (tensorBulk_growth U _ hU _),
    testedCellDerivative_quadraticScore_surface B h σ hσ hlower i U]
  simp_rw [composed_affineParameter_score_gap B L hL ε δ]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  have h1 : Integrable (fun x=>tensorBulk U (velocityMap L δ).1 (velocityMap L δ).2 x *
      (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)) μ :=
    (tensorBulk_memLp_two μ U _ _).integrable_mul
      ((affine_score_slice_memLp B ε.1 h ε.2 i j i).sub (affine_score_slice_memLp B ε.1 h ε.2 i j j))
  have hv : MemLp (fun x:FSC.Coord d=>inner ℝ (ε.1 i-ε.1 j)
      ((velocityMap L δ).1 x+(velocityMap L δ).2)) 2 μ := by
    exact (((velocityMap L δ).1.comp_memLp' IsGaussian.memLp_two_id).add
      (memLp_const (velocityMap L δ).2)).const_inner (𝕜:=ℝ) _
  have h2 : Integrable (fun x=>quadraticScore U x * inner ℝ (ε.1 i-ε.1 j)
      ((velocityMap L δ).1 x+(velocityMap L δ).2)) μ :=
    ((quadraticScore_memLp_four μ U).mono_exponent (by norm_num : (2:ENNReal)≤4)).integrable_mul hv
  unfold surfaceIntegral
  rw [integral_sub h1.restrict h2.restrict,mul_sub]



theorem surfaceIntegral_neg (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F : FSC.Coord d→ℝ) :
    surfaceIntegral B h i j (fun x=>-F x) = -surfaceIntegral B h i j F := by
  simp only [surfaceIntegral,integral_neg,mul_neg]

/-- Pairing opposite orientations exposes label differences before any bound.
The multiplier may be any antisymmetric edge field. -/
theorem surface_sum_label_gap (B : ι→FSC.Coord d) (h : ι→ℝ)
    (F : ι→FSC.Coord d→ℝ) (G : ι→ι→FSC.Coord d→ℝ)
    (hG : ∀ i j x,G j i x = -G i j x)
    (hI : ∀ i j k,Integrable (fun x=>F k x*G i j x)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    (∑ i,∑ j,surfaceIntegral B h i j (fun x=>F i x*G i j x))=
      (1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j (fun x=>(F i x-F j x)*G i j x) := by
  have hs : (∑ i,∑ j,surfaceIntegral B h i j (fun x=>F j x*G i j x))=
      -(∑ i,∑ j,surfaceIntegral B h i j (fun x=>F i x*G i j x)) := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [surfaceIntegral_reverse B h i j]
    have he : (fun x=>F i x*G j i x)=(fun x=>-(F i x*G i j x)) := by
      funext x
      rw [hG,mul_neg]
    rw [he,surfaceIntegral_neg]
  have he (i j : ι) : surfaceIntegral B h i j (fun x=>(F i x-F j x)*G i j x)=
      surfaceIntegral B h i j (fun x=>F i x*G i j x)-
      surfaceIntegral B h i j (fun x=>F j x*G i j x) := by
    simp only [sub_mul,surfaceIntegral]
    rw [integral_sub (hI i j i).restrict (hI i j j).restrict,mul_sub]
  simp_rw [he,Finset.sum_sub_distrib]
  rw [hs]
  ring



/-- Square integrability of the literal Gaussian divergence polynomial. -/
theorem massBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : MemLp (massBulk A z) 2 μ := by
  have hq := (quadraticScore_memLp_four μ A).mono_exponent (by norm_num : (2:ENNReal)≤4)
  have hz := (IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) z
  convert hq.add hz using 1
  funext x
  simp only [massBulk,quadraticScore,Pi.add_apply,id_eq]
  ring

theorem surfaceIntegral_sub (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι)
    (F G : FSC.Coord d→ℝ)
    (hF : Integrable F (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hG : Integrable G (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    surfaceIntegral B h i j (fun x=>F x-G x)=surfaceIntegral B h i j F-surfaceIntegral B h i j G := by
  unfold surfaceIntegral
  rw [integral_sub hF.restrict hG.restrict,mul_sub]

theorem constantHessian_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι)
    (ε δ : Parameters d ι) :
    constantHessian B h L i ε δ=∑ j,surfaceIntegral B h i j (fun x=>
      massBulk (velocityMap L δ).1 (velocityMap L δ).2 x*
        (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)-
      inner ℝ (ε.1 i-ε.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2)) := by
  rw [constantHessian_apply B h σ hσ hlower,massFunctional_apply,
    ←testedCellDerivative_one_affineParameters B h σ hσ hlower,
    testedCellDerivative_quartic_surface B h σ hσ hlower i _ (massBulk_growth _ _),
    testedCellDerivative_apply_surface B h σ hσ hlower i (fun _=>1) continuous_const
      1 (by norm_num) (fun x=>by simp only [abs_one,one_mul]; nlinarith [sq_nonneg ‖x‖])]
  simp_rw [one_mul,composed_affineParameter_score_gap B L hL ε δ]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  apply (surfaceIntegral_sub B h i j _ _ _ _).symm
  · exact (massBulk_memLp_two μ _ _).integrable_mul
      ((affine_score_slice_memLp B ε.1 h ε.2 i j i).sub (affine_score_slice_memLp B ε.1 h ε.2 i j j))
  · exact ((((velocityMap L δ).1.comp_memLp' (IsGaussian.memLp_two_id (μ:=μ))).add
      (memLp_const (velocityMap L δ).2)).const_inner (𝕜:=ℝ) _).integrable (by norm_num)

/-- A frozen scalar offset, including the mass-adjoint correction, is retained
inside the label polynomial until after opposite facets are paired. -/
def correctedLabelValue (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (x : FSC.Coord d) :=
  quadraticScore U x-c

def correctedLabelBulk (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z x : FSC.Coord d) :=
  tensorBulk U A z x-c*massBulk A z x

def correctedTensorHessian (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (ε δ : Parameters d ι) :=
  (∑ j,∑ k,operatorEntries U j k*
    centeredHessian B h L i (EuclideanSpace.basisFun (Fin d) ℝ j)
      (EuclideanSpace.basisFun (Fin d) ℝ k) ε δ)-c*constantHessian B h L i ε δ

theorem correctedLabelValue_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) : MemLp (correctedLabelValue U c) 2 μ :=
  ((quadraticScore_memLp_four μ U).mono_exponent (by norm_num : (2:ENNReal)≤4)).sub (memLp_const c)

theorem correctedLabelBulk_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (c : ℝ) (z : FSC.Coord d) :
    MemLp (correctedLabelBulk U c A z) 2 μ :=
  (tensorBulk_memLp_two μ U A z).sub ((massBulk_memLp_two μ A z).const_mul c)

/-- Exact corrected per-cell Hessian, with the acceleration term still absent:
this is the Hessian along linear row/offset directions. -/
theorem correctedTensorHessian_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (hU : U.toLinearMap.IsSymmetric) (c : ℝ)
    (ε δ : Parameters d ι) :
    correctedTensorHessian B h L i U c ε δ=∑ j,surfaceIntegral B h i j (fun x=>
      correctedLabelBulk U c (velocityMap L δ).1 (velocityMap L δ).2 x*
        (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)-
      correctedLabelValue U c x*inner ℝ (ε.1 i-ε.1 j)
        ((velocityMap L δ).1 x+(velocityMap L δ).2)) := by
  rw [correctedTensorHessian,centeredHessian_contraction_surface B h σ hσ hlower L hL i U hU,
    constantHessian_surface B h σ hσ hlower L hL,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←surfaceIntegral_const_mul]
  let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
  letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  have hg := (affine_score_slice_memLp B ε.1 h ε.2 i j i).sub
    (affine_score_slice_memLp B ε.1 h ε.2 i j j)
  have hv : MemLp (fun x:FSC.Coord d=>inner ℝ (ε.1 i-ε.1 j)
      ((velocityMap L δ).1 x+(velocityMap L δ).2)) 2 μ :=
    (((velocityMap L δ).1.comp_memLp' IsGaussian.memLp_two_id).add
      (memLp_const (velocityMap L δ).2)).const_inner (𝕜:=ℝ) _
  have hq := (quadraticScore_memLp_four μ U).mono_exponent (by norm_num : (2:ENNReal)≤4)
  have h1 : Integrable (fun x=>tensorBulk U (velocityMap L δ).1 (velocityMap L δ).2 x *
      (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)-quadraticScore U x *
        inner ℝ (ε.1 i-ε.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2)) μ :=
    ((tensorBulk_memLp_two μ U _ _).integrable_mul hg).sub (hq.integrable_mul hv)
  have h2 : Integrable (fun x=>c*(massBulk (velocityMap L δ).1 (velocityMap L δ).2 x *
      (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)-
        inner ℝ (ε.1 i-ε.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2))) μ :=
    (((massBulk_memLp_two μ _ _).integrable_mul hg).sub (hv.integrable (by norm_num))).const_mul c
  rw [←surfaceIntegral_sub B h i j _ _ h1 h2]
  congr 1
  funext x
  simp only [correctedLabelBulk,correctedLabelValue]
  ring



/-- Two signed label terms are paired together; no separate absolute estimate
is used in this equality. -/
theorem surface_sum_two_label_gaps (B : ι→FSC.Coord d) (h : ι→ℝ)
    (F R : ι→FSC.Coord d→ℝ) (G H : ι→ι→FSC.Coord d→ℝ)
    (hG : ∀ i j x,G j i x = -G i j x) (hH : ∀ i j x,H j i x = -H i j x)
    (hF : ∀ i j k,Integrable (fun x=>F k x*G i j x)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hR : ∀ i j k,Integrable (fun x=>R k x*H i j x)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    (∑ i,∑ j,surfaceIntegral B h i j (fun x=>F i x*G i j x-R i x*H i j x))=
      (1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j (fun x=>
        (F i x-F j x)*G i j x-(R i x-R j x)*H i j x) := by
  have hs (i j : ι) : surfaceIntegral B h i j (fun x=>F i x*G i j x-R i x*H i j x)=
      surfaceIntegral B h i j (fun x=>F i x*G i j x)-
        surfaceIntegral B h i j (fun x=>R i x*H i j x) :=
    surfaceIntegral_sub B h i j _ _ (hF i j i) (hR i j i)
  have hg (i j : ι) : surfaceIntegral B h i j (fun x=>
      (F i x-F j x)*G i j x-(R i x-R j x)*H i j x)=
      surfaceIntegral B h i j (fun x=>(F i x-F j x)*G i j x)-
        surfaceIntegral B h i j (fun x=>(R i x-R j x)*H i j x) := by
    apply surfaceIntegral_sub
    · convert (hF i j i).sub (hF i j j) using 1
      funext x
      change (F i x-F j x)*G i j x=F i x*G i j x-F j x*G i j x
      ring
    · convert (hR i j i).sub (hR i j j) using 1
      funext x
      change (R i x-R j x)*H i j x=R i x*H i j x-R j x*H i j x
      ring
  simp_rw [hs,hg,Finset.sum_sub_distrib]
  rw [surface_sum_label_gap B h F G hG hF,surface_sum_label_gap B h R H hH hR]
  ring

/-- Exact global corrected Hessian formula with paired label jumps. The scalar
correction is frozen at the evaluation point; this theorem does not require
or silently assume differentiability of a mass-adjoint choice. -/
theorem global_correctedTensorHessian_surface (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L)
    (U : ι→FSC.Coord d→L[ℝ] FSC.Coord d) (hU : ∀ i,(U i).toLinearMap.IsSymmetric)
    (c : ι→ℝ) (ε δ : Parameters d ι) :
    (∑ i,correctedTensorHessian B h L i (U i) (c i) ε δ)=
      (1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j (fun x=>
        (correctedLabelBulk (U i) (c i) (velocityMap L δ).1 (velocityMap L δ).2 x-
         correctedLabelBulk (U j) (c j) (velocityMap L δ).1 (velocityMap L δ).2 x)*
          (affineScore ε.1 ε.2 i x-affineScore ε.1 ε.2 j x)-
        (correctedLabelValue (U i) (c i) x-correctedLabelValue (U j) (c j) x)*
          inner ℝ (ε.1 i-ε.1 j) ((velocityMap L δ).1 x+(velocityMap L δ).2)) := by
  simp_rw [correctedTensorHessian_surface B h σ hσ hlower L hL _ _ (hU _)]
  apply surface_sum_two_label_gaps
  · intro i j x
    ring
  · intro i j x
    simp only [inner_sub_left]
    ring
  · intro i j k
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
    exact (correctedLabelBulk_memLp_two μ _ _ _ _).integrable_mul
      ((affine_score_slice_memLp B ε.1 h ε.2 i j i).sub (affine_score_slice_memLp B ε.1 h ε.2 i j j))
  · intro i j k
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
    have hv : MemLp (fun x:FSC.Coord d=>inner ℝ (ε.1 i-ε.1 j)
        ((velocityMap L δ).1 x+(velocityMap L δ).2)) 2 μ :=
      (((velocityMap L δ).1.comp_memLp' IsGaussian.memLp_two_id).add
        (memLp_const (velocityMap L δ).2)).const_inner (𝕜:=ℝ) _
    exact (correctedLabelValue_memLp_two μ _ _).integrable_mul hv

/-- Expansion into the three signed material-transport terms. With the paper's
velocity V=-(A x+z), this is precisely its three-term positive-V convention. -/
theorem corrected_transport_density (U T A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (c b l : ℝ) (z v x : FSC.Coord d) :
    (correctedLabelBulk U c A z x-correctedLabelBulk T b A z x)*l-
      (correctedLabelValue U c x-correctedLabelValue T b x)*inner ℝ v (A x+z)=
      -l*(2*inner ℝ ((U-T) x) (A x+z))-
      (correctedLabelValue U c x-correctedLabelValue T b x)*inner ℝ v (A x+z)+
      (correctedLabelValue U c x-correctedLabelValue T b x)*l*massBulk A z x := by
  simp only [correctedLabelBulk,correctedLabelValue,tensorBulk,massBulk,
    ContinuousLinearMap.sub_apply,inner_sub_left]
  ring

end NegativeVotingGlobalTensorTransport
