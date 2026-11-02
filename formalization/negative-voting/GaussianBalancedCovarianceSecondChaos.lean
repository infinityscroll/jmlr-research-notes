import GaussianEqualRowTailFreeComparison
import GaussianSecondEnergyCovarianceLaw
import GaussianNearRegularEnergyLogBound
import GaussianLocalRectangleAbsorption

/-! Local actual balanced second-chaos comparison on the radially normalized
covariance slice. The diagonal part is retained in the curvature payment. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingBalancedCovarianceSecondChaos
open NegativeVotingEqualRowTailFreeComparison NegativeVotingEqualDiagonalOperatorProjection
  NegativeVotingCovarianceEnergyRectangle NegativeVotingCovarianceDeficitRectangle
  NegativeVotingStrongDiagonalCurvature NegativeVotingRegularCovarianceDeficit
  NegativeVotingCovarianceRealization NegativeVotingPositiveCovariance
  NegativeVotingBalancedReference NegativeVotingRayDeficit NegativeVotingProcrustes
  NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
  NegativeVotingSecondEnergyCovarianceLaw NegativeVotingFanQuadraticMoments
  NegativeVotingFanSelectedOffsets NegativeVotingFan NegativeVotingCentroidOptimization
  NegativeVotingCovarianceFactorDistance NegativeVotingRegularFacetNeighborhood
  NegativeVotingNearRegularEnergyComparison NegativeVotingNearRegularEnergyLogBound
  NegativeVotingLocalRectangleAbsorption NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumLocalization
  NegativeVotingExteriorReference NegativeVotingRegularCoefficientBound
  NegativeVotingPolynomialFacetLogBound NegativeVotingNearRegularBalancedGeometry
  NegativeVotingNearRegularGraphGap
variable {n d e : ℕ}

theorem normalized_covariance_entry (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0) (i j : Fin (n+2)) :
    (referenceScale n)^2*inner ℝ (b i) (normalizedRowCovariance n b B (b j))=
      inner ℝ (B i) (B j) := by
  have hh:=congrFun (congrFun (rowCovariance_gram b hG B hB) i) j
  change inner ℝ (b i) (rowCovariance b B (b j))=inner ℝ (B i) (B j) at hh
  rw [rowCovariance_eq_scaled_normalized b B] at hh
  simpa only [ContinuousLinearMap.smul_apply,real_inner_smul_right] using hh

theorem normalized_covariance_trace_zero
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0)
    (henergy : rowEnergy B=referenceFirstWeight n) :
    (∑i,inner ℝ (b i) ((normalizedRowCovariance n b B-
      ContinuousLinearMap.id ℝ (FSC.Coord d)) (b i)))=0 := by
  have hh : (referenceScale n)^2*(∑i,inner ℝ (b i) ((normalizedRowCovariance n b B-
      ContinuousLinearMap.id ℝ (FSC.Coord d)) (b i)))=
      rowEnergy B-rowEnergy (fun i=>referenceScale n • b i) := by
    rw [Finset.mul_sum]
    unfold rowEnergy
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,
      mul_sub,normalized_covariance_entry b hG B hB,real_inner_self_eq_norm_sq,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [henergy,reference_scaled_energy b hG hP,sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt (sq_pos_of_pos (referenceScale_pos n)))

theorem actual_factor_gram (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0)
    (S : FSC.Coord d→L[ℝ]FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (hSS : S.comp S=normalizedRowCovariance n b B) (i j : Fin (n+2)) :
    inner ℝ (referenceScale n • S (b i)) (referenceScale n • S (b j))=
      inner ℝ (B i) (B j) := by
  simp only [real_inner_smul_left,real_inner_smul_right]
  rw [show inner ℝ (S (b i)) (S (b j))=inner ℝ (b i) ((S.comp S) (b j)) from hS _ _]
  rw [hSS]
  nlinarith only [normalized_covariance_entry b hG B hB i j]

theorem equal_row_factor_deficit (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (X : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hTT : T.comp T=ContinuousLinearMap.id ℝ (FSC.Coord d)+X) :
    regularCovarianceDeficit n (fun i=>referenceScale n • T (b i))=
      referenceScale n*regularDefect b X := by
  rw [regularCovarianceDeficit_eq_regularDefect hn b hP hG _
    (normalized_factor_centered b hb T),normalized_factor_covariance b hP T hT,hTT,
    add_sub_cancel_left]

theorem normalized_refined_curvature (hn : 0<n) (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0)
    (henergy : rowEnergy B=referenceFirstWeight n)
    (hsize : operatorHilbertSchmidt (normalizedRowCovariance n b B-
      ContinuousLinearMap.id ℝ (FSC.Coord d))≤1) :
    let E:=normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)
    (referenceScale n)^2*((operatorHilbertSchmidt (diagonalOperator b E))^2/96+
      (operatorHilbertSchmidt (zeroDiagonalOperator b E))^2/(48*((n:ℝ)+2)))≤
      ((1+Real.log ((n:ℝ)+2))/facetRadius 64)*regularCovarianceDeficit n B := by
  intro E
  let L:=1+Real.log ((n:ℝ)+2)
  have hR:=regularCovarianceDeficit_nonneg hn B hB
  have hc:=facetRadius_bounds 64 (by norm_num)
  have hL:1≤L:=by dsimp [L];linarith [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hsym:E.toLinearMap.IsSymmetric:=(normalizedRowCovariance_psd b B).1.sub identity_positive.1
  have htr:=normalized_covariance_trace_zero b hP hG B hB henergy
  have hsplit:=operator_split_refined_strain (by omega : 3≤n+2) b hb hP
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) E hsym htr
  have hraw:=regular_deficit_refined_ray_bound hn hmean b hb hP hG B hB
  change (referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2))*
    min 1 ((facetRadius 64/L)/operatorHilbertSchmidt E)≤regularCovarianceDeficit n B at hraw
  have heq : (referenceScale n)^2*((operatorHilbertSchmidt (diagonalOperator b E))^2/96+
      (operatorHilbertSchmidt (zeroDiagonalOperator b E))^2/(48*((n:ℝ)+2)))=
      (referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2)):=by
    rw [hsplit]
    push_cast
    field_simp
    ring
  rw [heq]
  by_cases hz:operatorHilbertSchmidt E=0
  · have hE:E=0:=(operatorHilbertSchmidt_eq_zero_iff E).mp hz
    have hzero:operatorHilbertSchmidt (0:FSC.Coord d→L[ℝ]FSC.Coord d)=0:=
      (operatorHilbertSchmidt_eq_zero_iff _).mpr rfl
    rw [hE]
    simp only [refinedStrain,hzero,ContinuousLinearMap.zero_apply,
      inner_zero_right,zero_pow (by decide : 2≠0),Finset.sum_const_zero,mul_zero,add_zero,zero_div]
    positivity [hc.1]
  have hx:0<operatorHilbertSchmidt E:=lt_of_le_of_ne (operatorHilbertSchmidt_nonneg E) (Ne.symm hz)
  have hl0:0<L:=by linarith
  have hmin:facetRadius 64/L ≤ min 1 ((facetRadius 64/L)/operatorHilbertSchmidt E):=by
    refine le_min ((div_le_iff₀ hl0).mpr (by linarith [hc.2.1])) ?_
    exact (le_div_iff₀ hx).mpr (mul_le_of_le_one_right (by positivity [hc.1]) hsize)
  have hh:=(mul_le_mul_of_nonneg_left hmin
    (show 0≤(referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2)) by
      positivity [refinedStrain_nonneg b E])).trans hraw
  have hs:=mul_le_mul_of_nonneg_left hh (show 0≤L/facetRadius 64 by positivity [hc.1])
  have hcancel:(L/facetRadius 64)*((referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2))*
      (facetRadius 64/L))=(referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2)):=by
    field_simp [hc.1.ne']
  rw [hcancel] at hs
  exact hs

theorem energyLogConstant_scale_le (a A B t : ℝ) (ha : 0<a) (hB : 0≤B) (ht : 1≤t) :
    energyLogConstant a A (B*t)≤energyLogConstant a A B*t := by
  have hp:=base_nonneg a A B ha hB
  rcases hp with ⟨ht0,_,ho0,hm0,hr0,_,_⟩
  have hbase:0 ≤ momentBase a+8192*traceBase a*ratioBase a*(1+offsetBase a A):=by
    positivity
  have hh:=mul_nonneg hbase (sub_nonneg.mpr ht)
  dsimp only [energyLogConstant] at ⊢
  simp only [div_eq_mul_inv]
  nlinarith only [hh]

def rectangleLogConstant : ℝ :=
  ((375+480*quarticLogConstant 2)*(1+768*degreeBound (1/4))+
    672*energyLogConstant (1/4) 5 5)/facetRadius 64

theorem rectangleLogConstant_nonneg : 0≤rectangleLogConstant := by
  have hh:=base_nonneg (1/4) 5 5 (by norm_num) (by norm_num)
  have hk:0≤energyLogConstant (1/4) 5 5:=hh.2.2.2.2.2.2
  unfold rectangleLogConstant quarticLogConstant degreeBound
  positivity [(facetRadius_bounds 64 (by norm_num)).1]

/-- Actual normalized balanced fan comparison. Every covariance factor,
free-maximum comparison, selected offset, and curvature payment is derived.
The threshold is chosen before both Euclidean dimensions. -/
theorem eventually_normalized_balanced_secondEnergy :
    ∀ᶠ n : ℕ in atTop, ∀(d e : ℕ)
      (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)), (∑i,b i=0) →
      (∀x,(∑i,inner ℝ (b i) x • b i)=x) →
      (∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      ∀(B : Fin (n+2)→FSC.Coord e), (∑i,B i=0) → rowEnergy B=referenceFirstWeight n →
      (operatorHilbertSchmidt (normalizedRowCovariance n b B-
        ContinuousLinearMap.id ℝ (FSC.Coord d)))^2≤1/1024 →
      referenceSecondWeight n-secondEnergy B (selectedOffsets B (uniformMass n))≤
        rectangleLogConstant*(1+Real.log ((n:ℝ)+2))^18*Real.sqrt ((n:ℝ)+2)*
          regularCovarianceDeficit n B := by
  obtain ⟨N,hN⟩:=exists_threshold_coefficient_log_le
  filter_upwards [eventually_ge_atTop (max N 1),eventually_factor_secondEnergy_lower,
    eventually_reference_scale_bounds,NegativeVotingRegularSecondGap.eventually_maximum_mean_sq_ge_one]
    with n hn hequal hscale hmean
  intro d e b hb hP hG B hB henergy hsmall
  let α:=referenceScale n
  let m:ℝ:=(n:ℝ)+2
  let L:=1+Real.log m
  let H:=normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)
  let X:=zeroDiagonalOperator b H
  let V:=diagonalOperator b H
  let a:=operatorHilbertSchmidt V
  let c:=operatorHilbertSchmidt X
  let R:=regularCovarianceDeficit n B
  have hn1:1≤n:=le_trans (le_max_right _ _) hn
  have hn0:0<n:=by omega
  have hα:0<α:=referenceScale_pos n
  have hm:1 ≤ m:=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hm0:0 < m:=by linarith
  have hL:1≤L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hR:0≤R:=regularCovarianceDeficit_nonneg hn0 B hB
  have hfr:=facetRadius_bounds 64 (by norm_num)
  have hG':∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hH:H.toLinearMap.IsSymmetric:=(normalizedRowCovariance_psd b B).1.sub identity_positive.1
  have htr:=normalized_covariance_trace_zero b hP hG B hB henergy
  have hsplit:X+V=H:=by dsimp [X,V,zeroDiagonalOperator];abel
  have hsym:=operator_split_symmetric b H hH
  have hpyth:=operator_split_pythagoras (by omega : 3≤n+2) b hb hP hG' H hH htr
  have ha:0≤a:=operatorHilbertSchmidt_nonneg V
  have hc:0≤c:=operatorHilbertSchmidt_nonneg X
  have hsmall':a^2+c^2≤1/1024:=by dsimp [a,c,V,X];nlinarith only [hpyth,hsmall]
  have hXsize:c≤1/32:=by nlinarith [sq_nonneg a]
  have hHsize:operatorHilbertSchmidt H≤1/32:=by
    nlinarith [operatorHilbertSchmidt_nonneg H]
  obtain ⟨S,hS,hSi,hSS,hInvS,hnearS,hSpos⟩:=exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+H) (identity_positive.1.add hH)
    (by simpa only [add_sub_cancel_left] using hHsize.trans (by norm_num))
  obtain ⟨T,hT,hTi,hTT,hInvT,hnearT,hTpos⟩:=exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+X) (identity_positive.1.add hsym.2)
    (by simpa only [add_sub_cancel_left] using hXsize.trans (by norm_num))
  simp only [add_sub_cancel_left] at hnearS hnearT
  have hST:=positive_half_factor_distance S.toContinuousLinearMap T.toContinuousLinearMap
    hS.1 hT.1 hSpos hTpos
  rw [hSS,hTT,show (ContinuousLinearMap.id ℝ (FSC.Coord d)+H)-
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+X)=V by rw [←hsplit];abel] at hST
  have hαlo:Real.sqrt L/m≤α:=by
    apply (div_le_iff₀ hm0).mpr
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh:=(div_le_iff₀ (sq_pos_of_pos hm0)).mp hscale.1
    nlinarith only [hh]
  have hαup:α≤5*Real.sqrt L/m:=by
    apply (le_div_iff₀ hm0).mpr
    have hh:=(le_div_iff₀ (sq_pos_of_pos hm0)).mp hscale.2
    have hs:=Real.sq_sqrt (show 0≤L by linarith)
    nlinarith [Real.sqrt_nonneg L]
  have hsc:(1/4:ℝ)*Real.sqrt L/m≤α/2:=by
    have hp:0≤Real.sqrt L/m:=by positivity
    calc
      _=(Real.sqrt L/m)/4:=by ring
      _≤α/2:=by linarith only [hαlo,hp]
  have hrect:=factorEnergy_rectangle_le hn1 b hP hG' S.toContinuousLinearMap T.toContinuousLinearMap
    c a α (1/4) hc ha hα (by norm_num) hnearT hST (by nlinarith only [hsmall'])
    (by simpa only [m,L,Nat.cast_add,Nat.cast_ofNat] using hsc)
  have hnormT:∀i,‖T (b i)‖^2=1-1/m:=by
    intro i
    have hh:=zero_diagonal_factor_row_norm (by omega : 3≤n+2) b hG' H htr
      T.toContinuousLinearMap hT.1 hTT 1 i
    simpa only [one_smul,one_pow,one_mul,Nat.cast_add,Nat.cast_ofNat,ContinuousLinearEquiv.coe_coe,m] using hh
  have hfree:=hequal d b hb hP hG T hT.1 hInvT hnormT
    (by simpa only [hTT,add_sub_cancel_left] using hnearT)
    (by simpa only [hTT,add_sub_cancel_left] using hXsize.trans (by norm_num))
  have hSSactual:S.toContinuousLinearMap.comp S.toContinuousLinearMap=normalizedRowCovariance n b B:=by
    rw [hSS];dsimp [H];abel
  have hGramS:=actual_factor_gram b hG B hB S.toContinuousLinearMap hS.1 hSSactual
  have hlowerS:=mapped_scaled_regular_lower b hG' S hInvS α
  have henergyS:factorEnergy b α S.toContinuousLinearMap=
      secondEnergy B (selectedOffsets B (uniformMass n)):=by
    have hp:(fun _:Fin (n+2)=>((n+2:ℕ):ℝ)⁻¹)=uniformMass n:=by
      funext i;simp only [uniformMass,Nat.cast_add,Nat.cast_ofNat,one_div]
    unfold factorEnergy
    rw [hp]
    exact selected_secondEnergy_eq_of_equal_gram _ B (α/2) (by positivity) hlowerS
      hGramS (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  have hRsid:=equal_row_factor_deficit hn0 b hb hP hG T.toContinuousLinearMap hT.1 X hTT
  have hpos:ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V)∈pdCone:=by
    rw [hsplit,←hSS]
    exact NegativeVotingCovarianceSegmentGeometry.symmetric_square_positive S hS.1
  have hdef:=physical_regularDefect_rectangle_le hn0 b hP hG X V hsym.2 hsym.1 hXsize hpos
    (1/4) (by norm_num) hsc
  rw [hsplit,←regularCovarianceDeficit_eq_regularDefect hn0 b hP hG B hB] at hdef
  have hRsid':regularCovarianceDeficit n (fun i=>referenceScale n • T (b i))=
      referenceScale n*regularDefect b X:=by
    simpa only [ContinuousLinearEquiv.coe_coe] using hRsid
  rw [hRsid'] at hfree
  have hcurv:=normalized_refined_curvature hn0 (by nlinarith [maximumMean_pos n])
    b hb hP hG B hB henergy (hHsize.trans (by norm_num))
  change α^2*(a^2/96+c^2/(48*m))≤(L/facetRadius 64)*R at hcurv
  have hRle:R≤(L/facetRadius 64)*R:=by
    have hh:1≤L/facetRadius 64:=(le_div_iff₀ hfr.1).mpr (by linarith [hfr.2.1])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh hR
  have hdef':referenceScale n*regularDefect b X≤(L/facetRadius 64)*R+
      8*degreeBound (1/4)*α^2*a*c:=by
    change _≤R+8*degreeBound (1/4)*α^2*c*a at hdef
    nlinarith only [hdef,hRle]
  have hcoefbase:=base_nonneg (1/4) 5 5 (by norm_num) (by norm_num)
  have hK0:0≤energyLogConstant (1/4) 5 5:=hcoefbase.2.2.2.2.2.2
  have hF0:0≤4*α^2*(c^2+a^2):=by positivity
  have hFsize:4*α^2*(c^2+a^2)≤(5*Real.sqrt L)^2/m^2:=by
    have hh:=(le_div_iff₀ (sq_pos_of_pos hm0)).mp hscale.2
    have hs:=Real.sq_sqrt (show 0≤L by linarith)
    apply (le_div_iff₀ (sq_pos_of_pos hm0)).mpr
    have hmul:=mul_le_mul_of_nonneg_left hsmall' (show 0≤4*α^2*m^2 by positivity)
    nlinarith only [hh,hs,hmul]
  have hk:=hN n (le_trans (le_max_left _ _) hn) α (1/4) 5 (5*Real.sqrt L)
    (4*α^2*(c^2+a^2)) hα (by norm_num) (by norm_num) (by positivity) hF0
    (by simpa only [m,L,Nat.cast_add,Nat.cast_ofNat] using hsc)
    (by simpa only [m,L,Nat.cast_add,Nat.cast_ofNat] using hαup)
    (by simpa only [m,Nat.cast_add,Nat.cast_ofNat] using hFsize)
  have hsL:1≤Real.sqrt L:=(Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hL)
  have hsL':Real.sqrt L≤L:=by nlinarith [Real.sq_sqrt (show 0≤L by linarith),Real.sqrt_nonneg L]
  have hk0:energyLogConstant (1/4) 5 (5*Real.sqrt L)≤energyLogConstant (1/4) 5 5*L:=
    (energyLogConstant_scale_le (1/4) 5 5 (Real.sqrt L) (by norm_num) (by norm_num) hsL).trans
      (mul_le_mul_of_nonneg_left hsL' hK0)
  have hk':energyComparisonCoefficient n α (1/4) (4*α^2*(c^2+a^2))≤
      energyLogConstant (1/4) 5 5*L^17:=by
    simp only [Nat.cast_add,Nat.cast_ofNat] at hk
    exact hk.trans ((mul_le_mul_of_nonneg_right hk0 (by positivity : 0≤L^16)).trans_eq (by ring))
  have hrect':|factorEnergy b α S.toContinuousLinearMap-factorEnergy b α T.toContinuousLinearMap|≤
      (energyLogConstant (1/4) 5 5*L^17)*α^2*(a^2+6*a*c):=by
    have hh:=mul_le_mul_of_nonneg_right hk' (show 0≤α^2*(a^2+6*c*a) by positivity)
    exact hrect.trans (by nlinarith only [hh])
  have hK2:0≤quarticLogConstant 2:=by unfold quarticLogConstant;positivity
  have hout:=rectangle_second_loss α a c m ((L/facetRadius 64)*R)
    (referenceScale n*regularDefect b X) (referenceSecondWeight n)
    (factorEnergy b α S.toContinuousLinearMap) (factorEnergy b α T.toContinuousLinearMap)
    ((375+480*quarticLogConstant 2)*L^5) (degreeBound (1/4))
    (energyLogConstant (1/4) 5 5*L^17) ha hc hm hcurv (by positivity)
    (degreeBound_pos (1/4) (by norm_num)).le (by positivity) hdef' hfree hrect'
  rw [henergyS] at hout
  have hroot:1≤Real.sqrt m:=(Real.le_sqrt (by norm_num) hm0.le).mpr (by simpa using hm)
  have hG0:0≤degreeBound (1/4):=(degreeBound_pos (1/4) (by norm_num)).le
  have hpow:L^5≤L^17:=pow_le_pow_right₀ hL (by omega)
  have hfac:1+768*degreeBound (1/4)*Real.sqrt m≤(1+768*degreeBound (1/4))*Real.sqrt m:=by
    nlinarith only [hroot]
  have hpart:=mul_le_mul hpow hfac (by positivity : 0≤1+768*degreeBound (1/4)*Real.sqrt m)
    (by positivity : 0≤L^17)
  have hcoef:((375+480*quarticLogConstant 2)*L^5*(1+768*degreeBound (1/4)*Real.sqrt m)+
      672*(energyLogConstant (1/4) 5 5*L^17)*Real.sqrt m)*((L/facetRadius 64)*R)≤
        rectangleLogConstant*L^18*Real.sqrt m*R:=by
    have hp:=mul_le_mul_of_nonneg_left hpart (show 0≤375+480*quarticLogConstant 2 by positivity)
    have hp':=mul_le_mul_of_nonneg_right hp (show 0≤(L/facetRadius 64)*R by positivity [hfr.1])
    unfold rectangleLogConstant
    simp only [div_eq_mul_inv] at hp' ⊢
    nlinarith only [hp']
  exact hout.trans hcoef

end NegativeVotingBalancedCovarianceSecondChaos
