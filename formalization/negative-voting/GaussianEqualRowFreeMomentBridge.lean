import GaussianEqualRowLabelAugmentation
import GaussianThresholdCDFTailComparison
import GaussianRelativeTailMomentComparison
import GaussianBalancedEqualRowSecondChaos

/-! Actual equal-row free moments from the full-rank label CDF path.
The added independent Gaussian is removed exactly, including its variance.
The remainder retains the squared covariance-factor displacement. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical ENNReal NNReal
namespace NegativeVotingEqualRowFreeMomentBridge
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingEqualRowMaximumLaw
  NegativeVotingEqualRowMaximumComparison NegativeVotingEqualRowLabelAugmentation
  NegativeVotingRegularScoreLaw NegativeVotingFanCovarianceLaw
  NegativeVotingThresholdCDFTailComparison NegativeVotingThresholdFan
  NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound
  NegativeVotingRelativeTailMomentComparison NegativeVotingBalancedEqualRowSecondChaos
  NegativeVotingFan NegativeVotingBalancedOffsetCertificateCancellation
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingConditionalSecondMoment
variable {n m d : ℕ} [NeZero m]

theorem coordinate_cdf_eq_label {κ : Type*} [Fintype κ]
    (B : Fin m→κ→ℝ) (S : FSC.Coord m→L[ℝ]FSC.Coord m)
    (hG : ∀i j,inner ℝ (WithLp.toLp 2 (B i)) (WithLp.toLp 2 (B j))=
      inner ℝ (S.adjoint (EuclideanSpace.basisFun (Fin m) ℝ i))
        (S.adjoint (EuclideanSpace.basisFun (Fin m) ℝ j))) (t : ℝ) :
    (standardGaussian κ) {x|maxScore (coordinateScores B x)≤t}=
      (stdGaussian (FSC.Coord m)) (S ⁻¹' orthant t) := by
  let C : Fin m→FSC.Coord m:=fun i=>S.adjoint (EuclideanSpace.basisFun (Fin m) ℝ i)
  have hh:=NegativeVotingFanCovarianceLaw.scoreLaw_eq_of_gram
    (fun i=>WithLp.toLp 2 (B i)) C hG
  have hm:MeasurableSet (orthant (d:=m) t):=orthant_measurable t
  have he:=congrArg (fun μ:Measure (FSC.Coord m)=>μ (orthant t)) hh
  simp only [NegativeVotingFanCovarianceLaw.scoreLaw,Measure.map_apply
    (NegativeVotingFanCovarianceLaw.continuous_scoreVector _).measurable hm] at he
  rw [←map_pi_eq_stdGaussian,Measure.map_apply (by fun_prop)
    (hm.preimage (NegativeVotingFanCovarianceLaw.continuous_scoreVector _).measurable)] at he
  convert he using 1
  · congr 1
    ext x
    simp only [mem_setOf_eq,maxScore,Finset.sup'_le_iff,Finset.mem_univ,forall_const,
      mem_preimage,orthant,NegativeVotingFanCovarianceLaw.scoreVector_apply]
    simp only [coordinateScores,PiLp.inner_apply,Real.inner_apply]
  · congr 1
    ext x
    simp only [mem_preimage,orthant,mem_setOf_eq,
      NegativeVotingFanCovarianceLaw.scoreVector_apply,C,
      ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner]

theorem standard_cdf_eq_orthant (t : ℝ) :
    (standardGaussian (Fin m)) {x|maximum x≤t}=
      (stdGaussian (FSC.Coord m)) (orthant t) := by
  rw [←map_pi_eq_stdGaussian,Measure.map_apply (by fun_prop) (orthant_measurable t)]
  congr 1
  ext x
  simp only [mem_setOf_eq,maximum,maxScore,Finset.sup'_le_iff,Finset.mem_univ,
    forall_const,mem_preimage,orthant]

theorem added_cdf_eq_augmented (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (c : ℝ) (hc : c^2=1/(m:ℝ)) (t : ℝ) :
    (standardGaussian (Fin d⊕Fin 1)) {x|addedMaximum (fun i=>T (b i)) c x≤t}=
      (stdGaussian (FSC.Coord m)) (augmentedFactor b T ⁻¹' orthant t) := by
  have hS: (augmentedFactor b T).adjoint=augmentedFactor b T:=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (augmentedFactor_symmetric b T hT)
  apply coordinate_cdf_eq_label
  intro i j
  rw [hS,addedRows_gram,augmentedFactor_gram b hP hG,hc]

theorem added_cdf_difference_abs_le (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/(m:ℝ))
    (hsize : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2)
    (a a' : Fin m) (haa' : a≠a') (c : ℝ) (hc : c^2=1/(m:ℝ)) (t : ℝ) :
    |(standardGaussian (Fin d⊕Fin 1)).real {x|addedMaximum (fun i=>T (b i)) c x≤t}-
      (standardGaussian (Fin m)).real {x|maximum x≤t}|≤
      600*((m:ℝ)+1)*(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
        Real.exp (-t^2/4) := by
  let F:=liftOperator b (T-ContinuousLinearMap.id ℝ (FSC.Coord d))
  have hd:=augmented_path_data b hb hP hG T hT hnorm
  change F.toLinearMap.IsSymmetric ∧ _ at hd
  have hF:‖F‖≤1/2:=(operator_norm_le_HilbertSchmidt F).trans (hd.2.2.1.trans_le hsize)
  have hS:(ContinuousLinearMap.id ℝ (FSC.Coord m)+F).adjoint=
      ContinuousLinearMap.id ℝ (FSC.Coord m)+F:=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ((show
      (ContinuousLinearMap.id ℝ (FSC.Coord m)).toLinearMap.IsSymmetric from fun _ _=>rfl).add hd.1)
  have hh:=actual_CDF_difference_abs_le F hF hd.1 hd.2.1
    (by simpa only [hS] using hd.2.2.2) a a' haa' t
  rw [hd.2.2.1] at hh
  simpa only [Measure.real_def,added_cdf_eq_augmented b hP hG T hT c hc,
    standard_cdf_eq_orthant,augmentedFactor,F] using hh

theorem normalized_free_second_moment_le (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/(m:ℝ))
    (hsize : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2)
    (a a' : Fin m) (haa' : a≠a') (t : ℝ) (ht : 0≤t) :
    ((∫y : Fin m→ℝ,(maximum y)^2 ∂standardGaussian (Fin m))-1/(m:ℝ))-
      (∫x,(rowMaximum (fun i=>T (b i)) x)^2 ∂standardGaussian (Fin d))≤
      2*t*((∫y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m))-
        (∫x,rowMaximum (fun i=>T (b i)) x ∂standardGaussian (Fin d)))+
      4800*((m:ℝ)+1)*(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
        Real.exp (-t^2/8) := by
  let c:=Real.sqrt (1/(m:ℝ))
  have hc:c^2=1/(m:ℝ):=Real.sq_sqrt (by positivity)
  have hrow i : inner ℝ (T (b i)) (T (b i))=1-1/(m:ℝ):=by
    rw [real_inner_self_eq_norm_sq,hnorm]
  have hh:=second_moment_difference_relative
    (standardGaussian (Fin d⊕Fin 1)) (standardGaussian (Fin m))
    (addedMaximum (fun i=>T (b i)) c) maximum
    (addedMaximum_measurable _ c) maximum_measurable
    (addedMaximum_memLp_two _ c) maximum_memLp_two
    (addedMaximum_cdf_ge _ hrow c hc) t
    (600*((m:ℝ)+1)*(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2)
    ht (by positivity)
    (fun s _ => (le_abs_self _).trans
      (added_cdf_difference_abs_le b hb hP hG T hT hnorm hsize a a' haa' c hc s))
  rw [addedMaximum_mean,addedMaximum_second_moment,hc] at hh
  linarith only [hh]

theorem physical_free_second_moment_le (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/(m:ℝ))
    (hsize : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2)
    (a a' : Fin m) (haa' : a≠a') (α t : ℝ) (hα : 0<α) (ht : 0≤t) :
    α^2*((∫y : Fin m→ℝ,(maximum y)^2 ∂standardGaussian (Fin m))-1/(m:ℝ))-
      (∫x,(rowMaximum (fun i=>α • T (b i)) x)^2 ∂standardGaussian (Fin d))≤
      2*α*t*(α*(∫y : Fin m→ℝ,maximum y ∂standardGaussian (Fin m))-
        (∫x,rowMaximum (fun i=>α • T (b i)) x ∂standardGaussian (Fin d)))+
      4800*α^2*((m:ℝ)+1)*(operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
        Real.exp (-t^2/8) := by
  have hh:=mul_le_mul_of_nonneg_left
    (normalized_free_second_moment_le b hb hP hG T hT hnorm hsize a a' haa' t ht) (sq_nonneg α)
  have he: (fun i=>α • T (b i))=α • (fun i=>T (b i)):=rfl
  simp only [he,rowMaximum_pos_smul _ α hα,mul_pow,integral_const_mul]
  nlinarith only [hh]

theorem scoreSquareSum_zero_eq_rowMaximum (B : Fin (n+2)→FSC.Coord d)
    (hB : Function.Injective B) :
    scoreSquareSum B 0=∫x,(rowMaximum B x)^2 ∂standardGaussian (Fin d) := by
  rw [scoreSquareSum_eq_weightedRowSquare B hB 0]
  apply integral_congr_ae
  filter_upwards with x
  have hs : NegativeVotingFan.scores B 0 (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)=
      coordinateScores (fun i j=>B i j) x:=by
    funext i
    simp only [NegativeVotingFan.scores,Pi.zero_apply,add_zero,PiLp.inner_apply,Real.inner_apply]
    rfl
  change (∑i,maxWeights (NegativeVotingFan.scores B 0
    (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) i*(∑j,B i j*x j)^2)=_
  rw [hs]
  exact NegativeVotingRegularQuadratic.maxWeights_observable
    (coordinateScores (fun i j=>B i j) x) (fun z:ℝ=>z^2)

/-- Physical, literal score-square input for the balanced quadratic
certificate. The only geometric smallness is the actual core factor norm. -/
theorem actual_free_score_square_le (b : Fin (n+2)→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/((n+2:ℕ):ℝ))
    (hsize : operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d))≤1/2)
    (α t : ℝ) (hα : 0<α) (ht : 0≤t)
    (hinj : Function.Injective (fun i=>α • T (b i))) :
    α^2*(maximumSecondMoment n-1/((n+2:ℕ):ℝ))-
      scoreSquareSum (fun i=>α • T (b i)) 0≤
      2*α*t*(α*maximumMean n-expectedMax (fun i=>α • T (b i)) 0)+
      4800*α^2*(((n+2:ℕ):ℝ)+1)*
        (operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2*
        Real.exp (-t^2/8) := by
  rw [scoreSquareSum_zero_eq_rowMaximum _ hinj,expectedMax_zero_eq_rowMaximum]
  exact physical_free_second_moment_le b hb hP hG T hT hnorm hsize
    ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp) α t hα ht

end NegativeVotingEqualRowFreeMomentBridge
