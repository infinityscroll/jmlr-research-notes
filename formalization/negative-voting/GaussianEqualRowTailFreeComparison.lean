import GaussianEqualRowFreeMomentBridge
import GaussianRelativeMomentLogAbsorption
import GaussianCovarianceDeficitRectangle

/-! Deficit-relative equal-row second chaos. Both the free maximum comparison
and the balanced-offset payment refer to the actual Gaussian fan. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingEqualRowTailFreeComparison
open NegativeVotingEqualRowFreeMomentBridge NegativeVotingEqualRowLabelAugmentation
  NegativeVotingBalancedEqualRowSecondChaos NegativeVotingCovarianceRealization
  NegativeVotingCovarianceDeficitRectangle NegativeVotingStrongDiagonalCurvature
  NegativeVotingRayDeficit NegativeVotingProcrustes NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingBalancedReference
  NegativeVotingRegularCovarianceDeficit NegativeVotingFan NegativeVotingFanScore
  NegativeVotingFanSelectedOffsets NegativeVotingFanInverse
  NegativeVotingFanQuadraticMoments NegativeVotingBalancedOffsetCertificateCancellation
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumSecondMoment
  NegativeVotingGaussianMaximumLocalization NegativeVotingRelativeMomentAbsorption
  NegativeVotingEqualDiagonalOperatorProjection NegativeVotingCovarianceEnergyRectangle
  NegativeVotingPolynomialFacetLogBound NegativeVotingRegularFacetNeighborhood
  NegativeVotingRelativeMomentLogAbsorption NegativeVotingExteriorReference
  NegativeVotingGaussianMaximumMean
  NegativeVotingRegularSecondGap
variable {n d : ℕ}

theorem normalized_factor_covariance
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric) :
    normalizedRowCovariance n b (fun i=>referenceScale n • T (b i))=T.comp T := by
  have hr : reconstruction b (fun i=>referenceScale n • T (b i))=referenceScale n • T:=by
    apply ContinuousLinearMap.ext
    intro x
    rw [reconstruction_apply]
    simp only [ContinuousLinearMap.smul_apply]
    simp_rw [smul_comm (inner ℝ _ _) (referenceScale n)]
    rw [←Finset.smul_sum]
    congr 1
    simpa only [map_sum,map_smul] using congrArg T (hP x)
  unfold normalizedRowCovariance rowCovariance
  rw [hr,map_smul,hT.clm_adjoint_eq]
  simp only [starRingEnd_apply,star_trivial,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul,smul_smul]
  rw [←sq,inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos (referenceScale_pos n))),one_smul]

theorem normalized_factor_centered (b : Fin (n+2)→FSC.Coord d)
    (hb : ∑i,b i=0) (T : FSC.Coord d→L[ℝ]FSC.Coord d) :
    (∑i,referenceScale n • T (b i))=0 := by
  rw [←Finset.smul_sum,←map_sum,hb,map_zero,smul_zero]

theorem small_factor_curvature (hn : 0<n) (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnear : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤
      operatorHilbertSchmidt (T.comp T-ContinuousLinearMap.id ℝ (FSC.Coord d)))
    (hsize : operatorHilbertSchmidt (T.comp T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤1) :
    (referenceScale n)^2*(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2≤
      (48/facetRadius 64)*((n:ℝ)+2)*(1+Real.log ((n:ℝ)+2))*
        regularCovarianceDeficit n (fun i=>referenceScale n • T (b i)) := by
  let E:=T.comp T-ContinuousLinearMap.id ℝ (FSC.Coord d)
  let L:=1+Real.log ((n:ℝ)+2)
  let R:=regularCovarianceDeficit n (fun i=>referenceScale n • T (b i))
  have hR:0≤R:=regularCovarianceDeficit_nonneg hn _ (normalized_factor_centered b hb T)
  have hc:=facetRadius_bounds 64 (by norm_num)
  have hL:1≤L:=by dsimp [L];linarith [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hraw:=regular_deficit_refined_ray_bound hn hmean b hb hP hG
    (fun i=>referenceScale n • T (b i)) (normalized_factor_centered b hb T)
  rw [normalized_factor_covariance b hP T hT] at hraw
  change (referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2))*
    min 1 ((facetRadius 64/L)/operatorHilbertSchmidt E)≤R at hraw
  have hnorm0:=operatorHilbertSchmidt_nonneg E
  by_cases hz:operatorHilbertSchmidt E=0
  · have ht0:operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))=0:=by
      nlinarith [operatorHilbertSchmidt_nonneg (T-ContinuousLinearMap.id ℝ (FSC.Coord d))]
    rw [ht0]
    simp only [zero_pow (by decide : 2≠0),mul_zero]
    change 0≤(48/facetRadius 64)*((n:ℝ)+2)*L*R
    positivity [hc.1]
  have hx:0<operatorHilbertSchmidt E:=lt_of_le_of_ne hnorm0 (Ne.symm hz)
  have hl0:0<L:=by linarith
  have hmin:facetRadius 64/L ≤ min 1 ((facetRadius 64/L)/operatorHilbertSchmidt E):=by
    refine le_min ?_ ?_
    · apply (div_le_iff₀ hl0).mpr
      linarith [hc.2.1]
    · exact (le_div_iff₀ hx).mpr (mul_le_of_le_one_right (by positivity [hc.1]) hsize)
  have hs:(operatorHilbertSchmidt E)^2≤refinedStrain b E:=by
    unfold refinedStrain
    have hh:0≤∑i,(inner ℝ (b i) (E (b i)))^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
    nlinarith [Nat.cast_nonneg (α:=ℝ) (n+2)]
  have hs':(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2≤
      refinedStrain b E:=(pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hnear 2).trans hs
  have hm0:(0:ℝ)<(n:ℝ)+2:=by positivity
  have hsmall:=mul_le_mul_of_nonneg_left hmin
    (show 0≤(referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2)) by
      positivity [refinedStrain_nonneg b E])
  have hh:=hsmall.trans hraw
  have hscaled:=mul_le_mul_of_nonneg_left hh
    (show 0≤48*((n:ℝ)+2)*L/facetRadius 64 by positivity [hc.1])
  have heq : (48*((n:ℝ)+2)*L/facetRadius 64)*
      ((referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2))*(facetRadius 64/L))=
      (referenceScale n)^2*refinedStrain b E:=by field_simp [hc.1.ne']
  rw [heq] at hscaled
  exact (mul_le_mul_of_nonneg_left hs' (sq_nonneg _)).trans
    (hscaled.trans_eq (by dsimp only [L,R];ring))

theorem factor_free_bound_of_cutoff (hn : 0<n) (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (T : FSC.Coord d≃L[ℝ]FSC.Coord d) (hT : T.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (hinv : ‖T.symm.toContinuousLinearMap‖≤2)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/((n:ℝ)+2))
    (hnear : operatorHilbertSchmidt (T.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d))≤
      operatorHilbertSchmidt (T.toContinuousLinearMap.comp T.toContinuousLinearMap-
        ContinuousLinearMap.id ℝ (FSC.Coord d)))
    (hsize : operatorHilbertSchmidt (T.toContinuousLinearMap.comp T.toContinuousLinearMap-
        ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2)
    (hcut : 9600*(48/facetRadius 64)*((n:ℝ)+2)^2*(1+Real.log ((n:ℝ)+2))*
      Real.exp (-16*(1+Real.log ((n:ℝ)+2)))≤referenceScale n) :
    (referenceScale n)^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-
      scoreSquareSum (fun i=>referenceScale n • T (b i)) 0≤
      (25*(1+Real.log ((n:ℝ)+2)))*referenceScale n*
        regularCovarianceDeficit n (fun i=>referenceScale n • T (b i)) := by
  let B:=fun i=>referenceScale n • T (b i)
  let L:=1+Real.log ((n:ℝ)+2)
  let h:=selectedOffsets B (uniformMass n)
  have hα:=referenceScale_pos n
  have hlower:=mapped_scaled_regular_lower b
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) T hinv (referenceScale n)
  have hinj:Function.Injective B:=fun i j hij=>by
    by_contra hne
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B (referenceScale n/2)
      (by positivity) hlower i j hne hij
  have hmass:∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹:=by
    intro i
    simpa only [h,uniformMass,Nat.cast_add,Nat.cast_ofNat,one_div] using
      congrFun (selectedOffsets_mass B hinj (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)) i
  have hrow i:‖B i‖^2=(referenceScale n)^2*(1-1/((n+2:ℕ):ℝ)):=by
    dsimp [B]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hnorm]
    norm_cast
  have hgap:=regular_deficit_eq_balanced_gap_of_equal_rows B (referenceScale n/2)
    (by positivity) hlower hrow h h.property hmass
  have hdrop:=balanced_drop_nonneg B (referenceScale n/2) (by positivity) hlower h h.property hmass
  have hmean':referenceScale n*maximumMean n-expectedMax B 0≤regularCovarianceDeficit n B:=by
    rw [hgap]
    linarith only [hdrop]
  have hR:=regularCovarianceDeficit_nonneg hn B (normalized_factor_centered b hb T)
  have hL:0≤L:=by dsimp [L];positivity [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hh:=actual_free_score_square_le b hb hP
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) T.toContinuousLinearMap hT
    (by simpa only [Nat.cast_add,Nat.cast_ofNat,ContinuousLinearEquiv.coe_coe] using hnorm) (hnear.trans hsize)
    (referenceScale n) (Real.sqrt (128*L)) hα (Real.sqrt_nonneg _) hinj
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hL)] at hh
  have hexp:-(128*L)/8=-16*L:=by ring
  rw [hexp] at hh
  have hQ : (referenceScale n)^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-scoreSquareSum B 0≤
      2*referenceScale n*Real.sqrt (128*L)*(referenceScale n*maximumMean n-expectedMax B 0)+
        9600*(referenceScale n)^2*((n:ℝ)+2)*
          (operatorHilbertSchmidt (T.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
          Real.exp (-16*L):=by
    refine hh.trans ?_
    push_cast
    have hp:0≤(referenceScale n)^2*
      (operatorHilbertSchmidt (T.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
      Real.exp (-16*L):=by positivity
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hcurv:=small_factor_curvature hn hmean b hb hP hG T.toContinuousLinearMap hT hnear
    (hsize.trans (by norm_num))
  exact physical_relative_moment_paid (referenceScale n) ((n:ℝ)+2) _ _ _ _
    (48/facetRadius 64) hα.le (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hR
    (by positivity [(facetRadius_bounds 64 (by norm_num)).1]) hmean' hcurv hQ hcut

theorem eventually_factor_secondEnergy_lower :
    ∀ᶠ n : ℕ in atTop, ∀(d : ℕ)
      (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)), (∑i,b i=0) →
      (∀x,(∑i,inner ℝ (b i) x • b i)=x) →
      (∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      ∀(T : FSC.Coord d≃L[ℝ]FSC.Coord d),
      T.toContinuousLinearMap.toLinearMap.IsSymmetric → ‖T.symm.toContinuousLinearMap‖≤2 →
      (∀i,‖T (b i)‖^2=1-1/((n:ℝ)+2)) →
      operatorHilbertSchmidt (T.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d))≤
        operatorHilbertSchmidt (T.toContinuousLinearMap.comp T.toContinuousLinearMap-
          ContinuousLinearMap.id ℝ (FSC.Coord d)) →
      operatorHilbertSchmidt (T.toContinuousLinearMap.comp T.toContinuousLinearMap-
          ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2 →
      referenceSecondWeight n-factorEnergy b (referenceScale n) T.toContinuousLinearMap≤
        (375+480*quarticLogConstant 2)*(1+Real.log ((n:ℝ)+2))^5*
          regularCovarianceDeficit n (fun i=>referenceScale n • T (b i)) := by
  have hconst:0≤9600*(48/facetRadius 64):=by
    positivity [(facetRadius_bounds 64 (by norm_num)).1]
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_maximum_mean_sq_ge_one,
    eventually_cutoff_coefficient_log_small _ hconst,
    eventually_reference_secondEnergy_lower_of_free_bound] with n hn hm hcut hcert
  intro d b hb hP hG T hT hinv hnorm hnear hsize
  have hmean:1≤ maximumMean n:=by nlinarith [maximumMean_pos n]
  have hα:0<referenceScale n:=referenceScale_pos n
  have hαlo:1/((n:ℝ)+2)≤referenceScale n:=by
    rw [referenceScale]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hfree:=factor_free_bound_of_cutoff (by omega) hmean b hb hP hG T hT hinv hnorm hnear hsize
    (by convert hcut (referenceScale n) hαlo using 1 <;>ring)
  let B:=fun i=>referenceScale n • T (b i)
  let h:=selectedOffsets B (uniformMass n)
  let L:=1+Real.log ((n:ℝ)+2)
  have hL:1≤L:=by dsimp [L];linarith [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hlower:=mapped_scaled_regular_lower b
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) T hinv (referenceScale n)
  have hinj:Function.Injective B:=fun i j hij=>by
    by_contra hne
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B (referenceScale n/2)
      (by positivity) hlower i j hne hij
  have hmass:∀i,mass B h i=((n+2:ℕ):ℝ)⁻¹:=by
    intro i
    simpa only [h,uniformMass,Nat.cast_add,Nat.cast_ofNat,one_div] using
      congrFun (selectedOffsets_mass B hinj (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)) i
  have hrow i:‖B i‖^2=(referenceScale n)^2*(1-1/((n+2:ℕ):ℝ)):=by
    dsimp [B]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hnorm]
    norm_cast
  have hc:=hcert d B (referenceScale n/2) (25*L) (by positivity) (by positivity) hlower
    hrow (normalized_factor_centered b hb T) (by field_simp;norm_num) h h.property hmass hfree
  have hR:=regularCovarianceDeficit_nonneg (by omega) B (normalized_factor_centered b hb T)
  have hK:0≤quarticLogConstant 2:=by unfold quarticLogConstant;positivity
  have hLpow:L^2≤L^5:=pow_le_pow_right₀ hL (by omega)
  have hcoef:15*L*(25*L+32*quarticLogConstant 2*L^4)≤
      (375+480*quarticLogConstant 2)*L^5:=by nlinarith only [hLpow]
  have hpay:=mul_le_mul_of_nonneg_right hcoef hR
  have he:factorEnergy b (referenceScale n) T.toContinuousLinearMap=secondEnergy B h:=by
    have hp:(fun _ : Fin (n+2)=>((n+2:ℕ):ℝ)⁻¹)=uniformMass n:=by
      funext i;simp only [uniformMass,Nat.cast_add,Nat.cast_ofNat,one_div]
    unfold factorEnergy
    change secondEnergy B (selectedOffsets B (fun _=>((n+2:ℕ):ℝ)⁻¹))=secondEnergy B h
    rw [hp]
  rw [he]
  change referenceSecondWeight n-secondEnergy B h≤(375+480*quarticLogConstant 2)*L^5*
    regularCovarianceDeficit n B
  simp only [Nat.cast_add,Nat.cast_ofNat] at hc
  linarith only [hc,hpay]

end NegativeVotingEqualRowTailFreeComparison
