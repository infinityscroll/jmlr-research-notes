import GaussianCovarianceFactorDistance
import GaussianNearRegularEnergyRectangle
import GaussianCovariancePriceDerivative
import GaussianLocalCurvatureAlgebra
import GaussianOperatorHSNorm

/-! Actual covariance-Hessian upper control near the regular covariance.
The lower bound on the Hessian uses positivity of the minimized offset
quadratic form. Thus no nuclear-norm acceleration or ambient dimension
factor is needed for this side of the rectangle estimate. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingCovarianceDeficitRectangle
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanHessian NegativeVotingFanJacobian
  NegativeVotingFanCanonicalOffset NegativeVotingFanCovarianceEnvelope
  NegativeVotingFanCycleHessian NegativeVotingTensorFacetAggregation
  NegativeVotingWeightedFacet NegativeVotingCapTail NegativeVotingAffineBasisLower
  NegativeVotingPositiveCovariance NegativeVotingCovarianceRefinement
  NegativeVotingLocalCurvatureAlgebra NegativeVotingCovarianceConcavity
  NegativeVotingFanCovarianceValue NegativeVotingCovarianceFactorDistance
  NegativeVotingProcrustes NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
variable {d m : ℕ} [NeZero m]

/-- Both signs of the actual optimized covariance Hessian are controlled.
The graph degree is a literal facet-weight degree, not a Hessian premise. -/
theorem covarianceHessianValue_abs_le_degree
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (h : Fin m→ℝ)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (G : ℝ)
    (hdegree : ∀i,∑j,facetWeight b h i j ≤ G) :
    |covarianceHessianValue b h H| ≤ (G/2)*∑i,‖H (b i)‖^2 := by
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have he:=canonicalOffset_elimination_formula b (rowsOfOperator b H) h σ hσ hlower
  have hn:=quadraticForm_nonneg b (rowsOfOperator b H) h
    (canonicalOffsetVariation b h (rowsOfOperator b H))
  have hneg:=covarianceHessianValue_nonpos b h σ hσ hlower H
  have hedge:=weighted_norm_difference_le_degree (facetWeight b h)
    (facetWeight_nonneg b h) (facetWeight_symm b h) G hdegree (fun i=>H (b i)) 0
  simp only [sub_zero,←map_sub] at hedge
  rw [abs_of_nonpos hneg]
  unfold covarianceHessianValue
  rw [←he]
  linarith

/-- Coordinate congruence transfers the bound to the actual covariance
functional. A bounded inverse costs a constant, not the ambient rank. -/
theorem operator_second_derivative_abs_le_factor
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (C H : FSC.Coord d→L[ℝ]FSC.Coord d)
    (R : FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hH : H.toLinearMap.IsSymmetric) (hInv : ‖R.symm.toContinuousLinearMap‖ ≤ 2)
    (G : ℝ) (hG : 0 ≤ G)
    (hdegree : ∀i,∑j,facetWeight (mappedBasis b R)
      (selectedOffsets (mappedBasis b R) p) i j ≤ G) :
    |deriv (deriv (fun t:ℝ=>operatorValue b p (C+t•H))) 0| ≤
      2*G*∑i,‖H (b i)‖^2 := by
  let K:=conjugatedDirection R H
  have hK : K.toLinearMap.IsSymmetric:=symmetric_conjugate _ _ hRi hH
  obtain ⟨h,hm,_,hd2,_⟩:=exists_actual_covariance_derivatives (mappedBasis b R) p hp hs K hK
  have heh : h=selectedOffsets (mappedBasis b R) p:=by
    obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound (mappedBasis b R)
    exact (selectedOffsets_eq _ _ σ hσ hlower h hm).symm
  subst h
  have heq : (fun t:ℝ=>operatorValue b p (C+t•H))=
      (fun t:ℝ=>covarianceValue (Matrix.gram ℝ (mappedBasis b R)+
        t•gramVelocity (mappedBasis b R) K) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 1
    have hg:=factor_gram b C R hR hRR
    have hv:=conjugate_gramVelocity b H R hR
    change Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C at hg
    change gramVelocity (mappedBasis b R) K=gramVelocity b H at hv
    rw [hg,hv]
  rw [heq,hd2.deriv]
  have hh:=covarianceHessianValue_abs_le_degree (mappedBasis b R)
    (selectedOffsets (mappedBasis b R) p) K G hdegree
  have hsum : (∑i,‖K (mappedBasis b R i)‖^2) ≤ 4*∑i,‖H (b i)‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ‖conjugatedDirection R H (R (b i))‖^2 ≤ _
    rw [conjugatedDirection_factor]
    have hn:=R.symm.toContinuousLinearMap.le_opNorm (H (b i))
    have hb:=hn.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
    change ‖R.symm (H (b i))‖ ≤ 2*‖H (b i)‖ at hb
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (by ring)
  exact hh.trans ((mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ G/2)).trans_eq (by ring))

/-- All graph and inverse bounds in the normalized regular covariance ball
are supplied by the actual Gaussian geometry. `β` is the physical reference
scale, retained in the coefficient for the later deficit comparison. -/
theorem near_identity_second_derivative_abs_le
    (hm : 3 ≤ m) (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hGram : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (C H : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/16)
    (hH : H.toLinearMap.IsSymmetric) (β e : ℝ) (hβ : 0<β) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ β/2) :
    |deriv (deriv (fun t:ℝ=>operatorValue b (fun _=>(m:ℝ)⁻¹) (C+t•H))) 0| ≤
      2*degreeBound e*β*(operatorHilbertSchmidt H)^2 := by
  obtain ⟨R,hR,hRi,hRR,hInv,hnear,hpos⟩:=exists_near_factor C hC (by linarith)
  let D : Fin m→FSC.Coord d:=fun i=>R (b i)-b i
  have hD : (∑i,‖D i‖^2) ≤ (1:ℝ)^2/256 := by
    have heq : (∑i,‖D i‖^2)=(operatorHilbertSchmidt
        (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2 := by
      rw [parseval_operator_HilbertSchmidt_sq b hP]
      rfl
    rw [heq]
    have hs:=hnear.trans hsize
    nlinarith [operatorHilbertSchmidt_nonneg
      (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d))]
  have hrow : (1:ℝ)•(b:Fin m→FSC.Coord d)+(1:ℝ)•D=(mappedBasis b R:Fin m→FSC.Coord d) := by
    funext i
    simp only [one_smul,Pi.add_apply,D,mappedBasis_apply]
    abel
  have hscale' : (e/β)*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ (1:ℝ)/2 := by
    have hh:=(div_le_div_of_nonneg_right hscale hβ.le)
    convert hh using 1 <;> field_simp
  have hdegree i : (∑j,facetWeight (mappedBasis b R)
      (selectedOffsets (mappedBasis b R) (fun _=>(m:ℝ)⁻¹)) i j) ≤ degreeBound e*β := by
    have hd:=selected_segment_degree_all hm b D hGram 1 (by norm_num) hD
      (e/β) (div_pos he hβ) hscale' 1 ⟨by norm_num,le_rfl⟩ i
    dsimp only [NegativeVotingBalancedSecondChaosDerivative.selectedRowOffsets] at hd
    rw [hrow] at hd
    have heq : degreeBound (e/β)=degreeBound e*β := by unfold degreeBound;field_simp
    rwa [heq] at hd
  have hh:=operator_second_derivative_abs_le_factor b (fun _=>(m:ℝ)⁻¹)
    (fun _=>by positivity) (by simp [NeZero.ne m]) C H R hR.1 hRi hRR hH hInv
    (degreeBound e*β) (mul_nonneg (degreeBound_pos e he).le hβ.le) hdegree
  rw [←parseval_operator_HilbertSchmidt_sq b hP] at hh
  convert hh using 1; ring

/-- Elementary scalar integration used below on the actual covariance ray. -/
theorem scalar_sub_linear_abs_le (f : ℝ→ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hfirst : ∀t∈Icc (0:ℝ) 1,DifferentiableAt ℝ f t)
    (hsecond : ∀t∈Icc (0:ℝ) 1,DifferentiableAt ℝ (deriv f) t)
    (hbound : ∀t∈Ico (0:ℝ) 1,|deriv (deriv f) t| ≤ K) :
    |f 1-f 0-deriv f 0| ≤ K := by
  have hd (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
      HasDerivWithinAt (deriv f) (deriv (deriv f) t) (Icc (0:ℝ) 1) t:=
    (hsecond t ht).hasDerivAt.hasDerivWithinAt
  have hb (t:ℝ) (ht:t∈Ico (0:ℝ) 1) : ‖deriv (deriv f) t‖ ≤ K:=by
    simpa only [Real.norm_eq_abs] using hbound t ht
  have hg:=norm_image_sub_le_of_norm_deriv_le_segment' hd hb
  let g:=fun t:ℝ=>f t-t*deriv f 0
  have hgd (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
      HasDerivWithinAt g (deriv f t-deriv f 0) (Icc (0:ℝ) 1) t:=by
    convert ((hfirst t ht).hasDerivAt.sub ((hasDerivAt_id t).mul_const (deriv f 0))).hasDerivWithinAt using 1
    · rfl
    · simp only [one_mul]
  have hgb (t:ℝ) (ht:t∈Ico (0:ℝ) 1) : ‖deriv f t-deriv f 0‖ ≤ K:=by
    have hh:=hg t ⟨ht.1,ht.2.le⟩
    simp only [sub_zero] at hh
    exact hh.trans (mul_le_of_le_one_right hK ht.2.le)
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' hgd hgb
  simpa only [g,one_mul,zero_mul,sub_zero,Real.norm_eq_abs,sub_sub,add_comm] using hh

open NegativeVotingRayDeficit NegativeVotingOperatorHS
  NegativeVotingBalancedReference NegativeVotingCovarianceCoercivity

/-- The actual radial tangent remainder has a dimension-free quadratic upper
bound. It is this upper bound, together with convexity, that pays the rectangle. -/
theorem actual_ray_tangent_abs_le
    (hm : 3 ≤ m) (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hGram : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt H ≤ 1/16)
    (β e : ℝ) (hβ : 0<β) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ β/2) :
    let f:=fun t:ℝ=>operatorValue b (fun _=>(m:ℝ)⁻¹)
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t•H)
    |f 1-f 0-deriv f 0| ≤ 2*degreeBound e*β*(operatorHilbertSchmidt H)^2 := by
  intro f
  let C:=fun t:ℝ=>ContinuousLinearMap.id ℝ (FSC.Coord d)+t•H
  have hCsym t : (C t).toLinearMap.IsSymmetric:=
    (show (ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap.IsSymmetric from fun x y=>rfl).add
      (hH.smul (by rfl : starRingEnd ℝ t=t))
  have hCsize t (ht:t∈Icc (0:ℝ) 1) :
      operatorHilbertSchmidt (C t-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/16:=by
    have hh : C t-ContinuousLinearMap.id ℝ (FSC.Coord d)=t•H:=by dsimp [C];abel
    rw [hh,operatorHilbertSchmidt_smul,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (operatorHilbertSchmidt_nonneg H) ht.2).trans hsize
  have hCpos t (ht:t∈Icc (0:ℝ) 1) : C t∈pdCone:=by
    obtain ⟨R,hR,_,hRR,_,_,_⟩:=exists_near_factor (C t) (hCsym t) ((hCsize t ht).trans (by norm_num))
    rw [←hRR]
    exact NegativeVotingCovarianceSegmentGeometry.symmetric_square_positive R hR.1
  have hder t (ht:t∈Icc (0:ℝ) 1) :
      DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t:=by
    obtain ⟨a,q,ha,hq,_⟩:=exists_line_derivatives b (fun _=>(m:ℝ)⁻¹)
      (fun _=>by positivity) (by simp [NeZero.ne m])
      (ContinuousLinearMap.id ℝ (FSC.Coord d)) H hH t (hCpos t ht)
    exact ⟨ha.differentiableAt,hq.differentiableAt⟩
  apply scalar_sub_linear_abs_le f _ (by positivity [degreeBound_pos e he])
    (fun t ht=>(hder t ht).1) (fun t ht=>(hder t ht).2)
  intro t ht
  have hh:=near_identity_second_derivative_abs_le hm b hP hGram (C t) H (hCsym t)
    (hCsize t ⟨ht.1,ht.2.le⟩) hH β e hβ he hscale
  have heq : (fun u:ℝ=>operatorValue b (fun _=>(m:ℝ)⁻¹) (C t+u•H))=
      (fun u:ℝ=>f (t+u)):=by
    funext u
    congr 1
    dsimp [C]
    module
  rw [heq,second_deriv_const_add] at hh
  exact hh

variable {n : ℕ}

/-- The literal tangent defect of the optimized normalized covariance value.
Multiplication by `referenceScale n` is the physical regular deficit. -/
def regularDefect (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (E : FSC.Coord d→L[ℝ]FSC.Coord d) : ℝ :=
  operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))+
    referenceScale n*operatorTrace E/2-
    operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d)+E)

@[simp] theorem regularDefect_zero (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) :
    regularDefect b 0=0 := by
  simp [regularDefect,operatorTrace]

theorem regularDefect_nonneg (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (E : FSC.Coord d→L[ℝ]FSC.Coord d) (hE : E.toLinearMap.IsSymmetric)
    (hpos : ContinuousLinearMap.id ℝ (FSC.Coord d)+E∈pdCone) :
    0 ≤ regularDefect b E := by
  have hc:=operatorValue_segment_concave b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (ContinuousLinearMap.id ℝ (FSC.Coord d)) (ContinuousLinearMap.id ℝ (FSC.Coord d)+E)
    identity_positive hpos
  simp only [add_sub_cancel_left] at hc
  have hd:=normalized_reference_derivative hn b hG hP E hE
  have hh:=hc.slope_le_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1) hd
  simp only [slope_def_field,sub_zero,one_smul,div_one] at hh
  have hz : (0:ℝ)•E=0:=by ext x;simp
  rw [hz,add_zero] at hh
  dsimp [regularDefect]
  linarith

theorem regularDefect_quadratic_upper (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (E : FSC.Coord d→L[ℝ]FSC.Coord d) (hE : E.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt E ≤ 1/16) (e : ℝ) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n/2) :
    regularDefect b E ≤ 2*degreeBound e*referenceScale n*(operatorHilbertSchmidt E)^2 := by
  have hh:=actual_ray_tangent_abs_le (show 3 ≤ n+2 by omega) b hP
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) E hE hsize (referenceScale n) e
    (referenceScale_pos n) he (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale)
  dsimp only at hh
  have hp : (fun _:Fin (n+2)=>(n+2:ℕ)⁻¹ : Fin (n+2)→ℝ)=uniformMass n:=by
    funext i;simp [uniformMass]
  rw [hp] at hh
  have hd:=(normalized_reference_derivative hn b hG hP E hE).deriv
  change deriv (fun t:ℝ=>operatorValue b (uniformMass n)
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+t•E)) 0=referenceScale n*operatorTrace E/2 at hd
  change |operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d)+(1:ℝ)•E)-
    operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d)+(0:ℝ)•E)-
    deriv (fun t:ℝ=>operatorValue b (uniformMass n)
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t•E)) 0| ≤ _ at hh
  rw [hd] at hh
  simp only [one_smul] at hh
  have hz : (0:ℝ)•E=0:=by ext x;simp
  rw [hz,add_zero] at hh
  have hb:=abs_le.mp hh
  dsimp [regularDefect]
  linarith

/-- Convexity here is the proved concavity of the actual optimized Gaussian
value, together with its exact linear Price term. -/
theorem regularDefect_convex_combination
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (X Y : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hX : ContinuousLinearMap.id ℝ (FSC.Coord d)+X∈psdCone)
    (hY : ContinuousLinearMap.id ℝ (FSC.Coord d)+Y∈psdCone)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a+c=1) :
    regularDefect b (a•X+c•Y) ≤ a*regularDefect b X+c*regularDefect b Y := by
  have hh:=(operatorValue_concaveOn_psd b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)).2
    hX hY ha hc hac
  have hpoint : a•(ContinuousLinearMap.id ℝ (FSC.Coord d)+X)+
      c•(ContinuousLinearMap.id ℝ (FSC.Coord d)+Y)=
      ContinuousLinearMap.id ℝ (FSC.Coord d)+(a•X+c•Y) := by
    have ha' : a=1-c:=by linarith
    rw [ha']
    module
  rw [hpoint] at hh
  have htr : operatorTrace (a•X+c•Y)=a*operatorTrace X+c*operatorTrace Y := by
    change LinearMap.trace ℝ (FSC.Coord d) (a•X.toLinearMap+c•Y.toLinearMap)=_
    simp only [map_add,map_smul,smul_eq_mul,operatorTrace]
  have hv : a*operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))+
      c*operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))=
      operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d)):=by
    rw [←add_mul,hac,one_mul]
  simp only [regularDefect,htr,smul_eq_mul] at *
  nlinarith only [hh,hv]

/-- The local covariance ball consists of strictly positive covariances. -/
theorem identity_add_positive_of_small
    (E : FSC.Coord d→L[ℝ]FSC.Coord d) (hE : E.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt E ≤ 1/8) :
    ContinuousLinearMap.id ℝ (FSC.Coord d)+E∈pdCone := by
  obtain ⟨R,hR,_,hRR,_,_,_⟩:=exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+E)
    (identity_positive.1.add hE) (by simpa only [add_sub_cancel_left] using hsize)
  rw [←hRR]
  exact NegativeVotingCovarianceSegmentGeometry.symmetric_square_positive R hR.1

/-- The actual tangent defect rectangle, obtained from convexity and the
proved quadratic upper bound. In particular the error vanishes when either
side of the rectangle vanishes; there is no additive tail. -/
theorem regularDefect_rectangle_le (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (X V : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hX : X.toLinearMap.IsSymmetric) (hV : V.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt X ≤ 1/32)
    (hpos : ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V)∈pdCone)
    (e : ℝ) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n/2) :
    regularDefect b X ≤ regularDefect b (X+V)+
      8*degreeBound e*referenceScale n*operatorHilbertSchmidt X*operatorHilbertSchmidt V := by
  let a:=operatorHilbertSchmidt X
  let c:=operatorHilbertSchmidt V
  have ha : 0 ≤ a:=operatorHilbertSchmidt_nonneg X
  have hc : 0 ≤ c:=operatorHilbertSchmidt_nonneg V
  have hzero : operatorHilbertSchmidt (0:FSC.Coord d→L[ℝ]FSC.Coord d)=0:=
    (operatorHilbertSchmidt_eq_zero_iff _).mpr rfl
  by_cases hc0 : c=0
  · have hV0 : V=0:=(operatorHilbertSchmidt_eq_zero_iff V).mp hc0
    simp [hV0,hzero]
  have hcpos : 0<c:=lt_of_le_of_ne hc (Ne.symm hc0)
  by_cases ha0 : a=0
  · have hX0 : X=0:=(operatorHilbertSchmidt_eq_zero_iff X).mp ha0
    subst X
    simp only [regularDefect_zero,zero_add,hzero,mul_zero,zero_mul,add_zero]
    exact regularDefect_nonneg hn b hP hG V hV (by simpa only [zero_add] using hpos)
  have hapos : 0<a:=lt_of_le_of_ne ha (Ne.symm ha0)
  let t:=a/c
  have ht : 0<t:=div_pos hapos hcpos
  let Z:=X-t•V
  have hZ : Z.toLinearMap.IsSymmetric:=hX.sub (hV.smul (by rfl : starRingEnd ℝ t=t))
  have hZsize : operatorHilbertSchmidt Z ≤ 1/16:=by
    have hb:=operatorHilbertSchmidt_sub_le X (t•V)
    rw [operatorHilbertSchmidt_smul,abs_of_pos ht] at hb
    have heq : t*operatorHilbertSchmidt V=a:=by change (a/c)*c=a;field_simp
    rw [heq] at hb
    dsimp [Z]
    linarith
  have hZpos:=identity_add_positive_of_small Z hZ (hZsize.trans (by norm_num))
  have hXpos:=identity_add_positive_of_small X hX (hsize.trans (by norm_num))
  have hnX:=regularDefect_nonneg hn b hP hG X hX hXpos
  have hu:=regularDefect_quadratic_upper hn b hP hG Z hZ hZsize e he hscale
  have hzBound : regularDefect b Z ≤
      8*degreeBound e*referenceScale n*a^2:=by
    have hb:=operatorHilbertSchmidt_sub_le X (t•V)
    rw [operatorHilbertSchmidt_smul,abs_of_pos ht] at hb
    have heq : t*operatorHilbertSchmidt V=a:=by change (a/c)*c=a;field_simp
    rw [heq] at hb
    have hn:=operatorHilbertSchmidt_nonneg Z
    have hK:=mul_pos (degreeBound_pos e he) (referenceScale_pos n)
    have hs : operatorHilbertSchmidt Z ≤ 2*a:=by change operatorHilbertSchmidt Z ≤ _ at hb;linarith
    have hp:=pow_le_pow_left₀ hn hs 2
    nlinarith
  have hcmb:=regularDefect_convex_combination b (X+V) Z (pdCone_subset_psdCone hpos)
    (pdCone_subset_psdCone hZpos) (t/(1+t)) (1/(1+t))
    (by positivity) (by positivity) (by field_simp;ring)
  have hpoint : (t/(1+t))•(X+V)+(1/(1+t))•Z=X:=by
    have hden : 1+t ≠ 0:=ne_of_gt (by linarith)
    have hcoef1 : t/(1+t)+1/(1+t)=1:=by field_simp;ring
    have hcoef2 : t/(1+t)-(1/(1+t))*t=0:=by ring
    calc
      _ = (t/(1+t)+1/(1+t))•X+(t/(1+t)-(1/(1+t))*t)•V := by dsimp [Z];module
      _ = X := by rw [hcoef1,hcoef2];ext x;simp
  rw [hpoint] at hcmb
  have hm:=mul_le_mul_of_nonneg_left hcmb (by linarith : 0 ≤ 1+t)
  have heq : (1+t)*(t/(1+t)*regularDefect b (X+V)+1/(1+t)*regularDefect b Z)=
      t*regularDefect b (X+V)+regularDefect b Z:=by field_simp
  rw [heq] at hm
  have hbase : t*(regularDefect b X-regularDefect b (X+V)) ≤
      8*degreeBound e*referenceScale n*a^2:=by nlinarith
  have hmul:=mul_le_mul_of_nonneg_left hbase hc
  have htc : c*t=a:=by change c*(a/c)=a;field_simp
  have hout : a*(regularDefect b X-regularDefect b (X+V)) ≤
      a*(8*degreeBound e*referenceScale n*a*c):=by
    rw [←mul_assoc,htc] at hmul
    convert hmul using 1; ring
  have hh:=le_of_mul_le_mul_left hout hapos
  dsimp [a,c] at hh
  linarith

/-- Exact identification with the existing actual row-covariance deficit.
The identity remains valid for singular row systems; positivity is needed
only by the separate local rectangle estimate. -/
theorem regularCovarianceDeficit_eq_regularDefect (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    {k : ℕ} (B : Fin (n+2)→FSC.Coord k) (hB : ∑i,B i=0) :
    NegativeVotingRegularCovarianceDeficit.regularCovarianceDeficit n B=
      referenceScale n*regularDefect b
        (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)) := by
  rw [regularCovarianceDeficit_eq_scaled_tangent hn b hG hP B hB]
  have hE : (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap.IsSymmetric:=
    (normalizedRowCovariance_psd b B).1.sub identity_positive.1
  have hd:=(normalized_reference_derivative hn b hG hP _ hE).deriv
  change deriv (covarianceRayValue b (uniformMass n) (normalizedRowCovariance n b B)) 0=
    referenceScale n*operatorTrace
      (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d))/2 at hd
  rw [hd]
  unfold regularDefect
  rw [add_sub_cancel]

/-- Physical-scale rectangle bound for the actual covariance deficit.
The explicit product error preserves the zero-deficit/equality branch. -/
theorem physical_regularDefect_rectangle_le (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (X V : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hX : X.toLinearMap.IsSymmetric) (hV : V.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt X ≤ 1/32)
    (hpos : ContinuousLinearMap.id ℝ (FSC.Coord d)+(X+V)∈pdCone)
    (e : ℝ) (he : 0<e)
    (hscale : e*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n/2) :
    referenceScale n*regularDefect b X ≤ referenceScale n*regularDefect b (X+V)+
      8*degreeBound e*(referenceScale n)^2*operatorHilbertSchmidt X*operatorHilbertSchmidt V := by
  have hh:=mul_le_mul_of_nonneg_left
    (regularDefect_rectangle_le hn b hP hG X V hX hV hsize hpos e he hscale)
    (referenceScale_pos n).le
  convert hh using 1; ring

end NegativeVotingCovarianceDeficitRectangle
