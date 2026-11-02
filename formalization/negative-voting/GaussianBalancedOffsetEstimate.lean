import GaussianBalancedOffsetControl

/-! A numerical, dimension-uniform bound for the genuine balanced covariance
response, retaining the literal Euclidean label norm. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingBalancedOffsetEstimate
open NegativeVotingBalancedOffset NegativeVotingBalancedReference
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean NegativeVotingFanJacobian
  NegativeVotingFanSelectedOffsets NegativeVotingCovarianceOffsets
  NegativeVotingPositiveCovariance NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl

theorem balanced_response_coefficient_bound (n:ℕ) (hmean:1≤ maximumMean n):
    8*(1+(5*Real.sqrt (1+Real.log (1/((referenceScale n/((n:ℝ)+2))/2))))^2)≤
      1024*(1+Real.log ((n:ℝ)+2)):=by
  let m:ℝ:=(n:ℝ)+2
  let w:ℝ:=referenceScale n/m
  have hm:0< m:=by dsimp [m];positivity
  have hm1:1≤ m:=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hw:0< w:=div_pos (referenceScale_pos n) hm
  have hlogm:0≤ Real.log m:=Real.log_nonneg hm1
  have ha:referenceScale n*((n:ℝ)+1)=maximumMean n:=by
    dsimp [referenceScale]
    field_simp
  have hprod:w*m^2=referenceScale n*m:=by dsimp [w];field_simp
  have hwm:1≤ w*m^2:=by rw [hprod];dsimp [m];nlinarith [referenceScale_pos n]
  have hi:2/w≤2*m^2:=(div_le_iff₀ hw).mpr (by nlinarith)
  have hl:=Real.log_le_log (div_pos (by norm_num:0<(2:ℝ)) hw) hi
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt hm)),Real.log_pow] at hl
  have h2:Real.log (2:ℝ)≤1:=by
    have hh:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    linarith
  have hL:1+Real.log (2/w)≤2*(1+Real.log m):=by norm_num only [Nat.cast_ofNat] at hl;linarith
  have hr:(Real.sqrt (1+Real.log (2/w)))^2≤2*(1+Real.log m):=by
    calc
      _≤(Real.sqrt (2*(1+Real.log m)))^2:=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hL) 2
      _=_:=Real.sq_sqrt (by positivity)
  change 8*(1+(5*Real.sqrt (1+Real.log (1/(w/2))))^2)≤1024*(1+Real.log m)
  have he:1/(w/2)=2/w:=by field_simp
  rw [he]
  nlinarith

/-- The covariance direction is A itself. The factor1/2 in the true offset
response has already been included. -/
theorem balanced_operator_offset_l2_sq_bound (n d:ℕ)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hmean:1≤ maximumMean n)
    (C A:FSC.Coord d→L[ℝ]FSC.Coord d) (hA:A.toLinearMap.IsSymmetric)
    (R:FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) (hRi:R.symm.toLinearMap.IsSymmetric)
    (hRC:R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hN:‖R.symm.toContinuousLinearMap‖≤2)
    (hlower:∀i j,i≠j→(referenceScale n/((n:ℝ)+2))/2≤
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j)
    (hupper:∀i j,i≠j→
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j≤
        2*(referenceScale n/((n:ℝ)+2)))
    (hedge:∀i j,i≠j→1≤‖mappedBasis b R i-mappedBasis b R j‖):
    (∑i,(deriv (fun t:ℝ=>(operatorOffsets b (uniformMass n) (C+t • A):Fin (n+2)→ℝ)) 0 i)^2)≤
      1024*(1+Real.log ((n:ℝ)+2))*(operatorHilbertSchmidt A)^2:=by
  let w:ℝ:=referenceScale n/((n:ℝ)+2)
  have hw:0< w:=div_pos (referenceScale_pos n) (by positivity)
  have hb:=operator_offset_l2_bound b hP (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) C A hA R hR hRi hRC 2 hN (w/2) (2*w) 1
    (by positivity) (by positivity) (by norm_num) hlower hupper hedge
  simp only [mul_one] at hb
  have hc:=balanced_response_coefficient_bound n hmean
  have hg:(∑i,(deriv (fun t:ℝ=>(operatorOffsets b (uniformMass n) (C+t • A):Fin (n+2)→ℝ)) 0 i)^2)≤
      8*(1+(5*Real.sqrt (1+Real.log (1/(w/2))))^2)*(operatorHilbertSchmidt A)^2:=by
    apply (mul_le_mul_iff_right₀ hw).mp
    nlinarith [hb]
  exact hg.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

theorem balanced_operator_offset_l2_bound (n d:ℕ)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hmean:1≤ maximumMean n)
    (C A:FSC.Coord d→L[ℝ]FSC.Coord d) (hA:A.toLinearMap.IsSymmetric)
    (R:FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR:R.toLinearMap.IsSymmetric) (hRi:R.symm.toLinearMap.IsSymmetric)
    (hRC:R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hN:‖R.symm.toContinuousLinearMap‖≤2)
    (hlower:∀i j,i≠j→(referenceScale n/((n:ℝ)+2))/2≤
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j)
    (hupper:∀i j,i≠j→
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) (uniformMass n)) i j≤
        2*(referenceScale n/((n:ℝ)+2)))
    (hedge:∀i j,i≠j→1≤‖mappedBasis b R i-mappedBasis b R j‖):
    Real.sqrt (∑i,(deriv (fun t:ℝ=>(operatorOffsets b (uniformMass n) (C+t • A):Fin (n+2)→ℝ)) 0 i)^2)≤
      32*Real.sqrt (1+Real.log ((n:ℝ)+2))*operatorHilbertSchmidt A:=by
  have hb:=balanced_operator_offset_l2_sq_bound n d b hP hmean C A hA R hR hRi hRC hN hlower hupper hedge
  have hlog:0≤1+Real.log ((n:ℝ)+2):=by
    have:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  have hn:=operatorHilbertSchmidt_nonneg A
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _=>sq_nonneg _))]
  nlinarith [Real.sq_sqrt hlog]

end NegativeVotingBalancedOffsetEstimate
