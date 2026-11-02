import GaussianThresholdFan
import GaussianAffineNormControl

/-! Actual first and second derivatives of a Gaussian maximum CDF along a
linear square-root path. Invertibility and the coherent lift are constructed. -/
noncomputable section
set_option maxHeartbeats 4500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingThresholdCDFDerivative
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanMassSecondDerivative NegativeVotingCoherentLiftHessian
  NegativeVotingGlobalTensorTransport NegativeVotingQuadraticBulkNorm
  NegativeVotingFanQuadraticTransport NegativeVotingCapTail NegativeVotingFanJointMass
  NegativeVotingMassHessianBulk NegativeVotingThresholdFan NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound
variable {d : ℕ}

def thresholdPath (F : FSC.Coord d→L[ℝ] FSC.Coord d) (t s : ℝ) : Parameters d (Option (Fin d)) :=
  (thresholdRows (ContinuousLinearMap.id ℝ (FSC.Coord d))+s • thresholdRows F,thresholdOffsets t)

def thresholdDirection (F : FSC.Coord d→L[ℝ] FSC.Coord d) : Parameters d (Option (Fin d)) :=
  (thresholdRows F,0)

lemma thresholdPath_rows (F : FSC.Coord d→L[ℝ] FSC.Coord d) (t s : ℝ) :
    (thresholdPath F t s).1=thresholdRows (nearIdentityMap F s) := by
  funext i
  cases i with
  | none=>simp [thresholdPath,thresholdRows]
  | some i=>simp [thresholdPath,thresholdRows,nearIdentityMap]

lemma thresholdPath_hasDerivAt (F : FSC.Coord d→L[ℝ] FSC.Coord d) (t s : ℝ) :
    HasDerivAt (thresholdPath F t) (thresholdDirection F) s := by
  have hd:=(((hasDerivAt_id s).smul_const (thresholdRows F)).const_add
      (thresholdRows (ContinuousLinearMap.id ℝ (FSC.Coord d)))).prodMk
        (hasDerivAt_const s (thresholdOffsets (d:=d) t))
  simp only [one_smul,id_eq] at hd
  convert hd using 1 <;>rfl

def cdfPath (F : FSC.Coord d→L[ℝ] FSC.Coord d) (t s : ℝ) : ℝ :=
  mass (thresholdPath F t s).1 (thresholdPath F t s).2 none

def cdfFirst (F : FSC.Coord d→L[ℝ] FSC.Coord d) (t s : ℝ) : ℝ :=
  testedCellDerivative (thresholdPath F t s).1 (thresholdPath F t s).2 none (fun _=>1)
    (thresholdDirection F)

def pathVelocity (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (s : ℝ) (hs : |s|≤1) : FSC.Coord d→L[ℝ] FSC.Coord d :=
  (nearIdentityEquiv F hF s hs).symm.toContinuousLinearMap.comp F

lemma pathVelocity_apply_map (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (s : ℝ) (hs : |s|≤1) (x : FSC.Coord d) :
    pathVelocity F hF s hs (nearIdentityMap F s x)=F x := by
  change (nearIdentityEquiv F hF s hs).symm (F (nearIdentityMap F s x))=F x
  have he:F (nearIdentityMap F s x)=nearIdentityMap F s (F x):=by
    simp [nearIdentityMap]
  rw [he]
  exact (nearIdentityEquiv F hF s hs).symm_apply_apply (F x)

lemma pathVelocity_symmetric (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (hFs : F.toLinearMap.IsSymmetric) (s : ℝ) (hs : |s|≤1) :
    (pathVelocity F hF s hs).toLinearMap.IsSymmetric := by
  intro x y
  obtain ⟨u,rfl⟩:∃u,nearIdentityMap F s u=x := (nearIdentityEquiv F hF s hs).surjective x
  obtain ⟨v,rfl⟩:∃v,nearIdentityMap F s v=y := (nearIdentityEquiv F hF s hs).surjective y
  change inner ℝ (pathVelocity F hF s hs (nearIdentityMap F s u)) (nearIdentityMap F s v)=
    inner ℝ (nearIdentityMap F s u) (pathVelocity F hF s hs (nearIdentityMap F s v))
  rw [pathVelocity_apply_map,pathVelocity_apply_map]
  simp only [nearIdentityMap,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right]
  exact congrArg (fun z:ℝ=>z+s*inner ℝ (F u) (F v)) (hFs u v)

lemma pathVelocity_HS_le (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (s : ℝ) (hs : |s|≤1) :
    operatorHilbertSchmidt (pathVelocity F hF s hs)≤2*operatorHilbertSchmidt F :=
  (operatorHilbertSchmidt_comp_le _ F).trans
    (mul_le_mul_of_nonneg_right (nearIdentity_inverse_norm_le F hF s hs)
      (operatorHilbertSchmidt_nonneg F))

lemma thresholdDirection_eq_affine (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (s : ℝ) (hs : |s|≤1) :
    thresholdDirection F=affineParameterVelocity (thresholdRows (nearIdentityMap F s))
      (pathVelocity F hF s hs) 0 := by
  apply Prod.ext
  · funext i
    cases i with
    | none=>simp [thresholdDirection,affineParameterVelocity,thresholdRows]
    | some i=>
      apply ext_inner_right ℝ
      intro x
      simp only [thresholdDirection,affineParameterVelocity,thresholdRows,
        ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner]
      have he:nearIdentityMap F s (pathVelocity F hF s hs x)=F x:=
        (nearIdentityEquiv F hF s hs).apply_symm_apply (F x)
      rw [he]
  · simp only [thresholdDirection,affineParameterVelocity,inner_zero_right]
    rfl

lemma cdfPath_eq_measure (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (t s : ℝ) (hs : |s|≤1) :
    cdfPath F t s=(stdGaussian (FSC.Coord d)).real
      ((nearIdentityMap F s) ⁻¹' (orthant t)) := by
  let T:=nearIdentityEquiv F hF s hs
  have hl:=threshold_singular_lower T
  have hp:0<(‖thresholdLift T‖+1)⁻¹:=by positivity
  have hi:Function.Injective (thresholdRows T.toContinuousLinearMap):=by
    intro i j he
    by_contra hne
    exact NegativeVotingFacetDegree.centered_singular_rows_ne _ _ hp hl i j hne he
  rw [cdfPath,thresholdPath_rows]
  have hi' : Function.Injective (thresholdRows (nearIdentityMap F s)) := hi
  change mass (thresholdRows (nearIdentityMap F s)) (thresholdOffsets t) none=_
  rw [mass_eq_winningCell _ hi',threshold_winningCell]

lemma cdfPath_hasDerivAt (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (t s : ℝ) (hs : |s|≤1) : HasDerivAt (cdfPath F t) (cdfFirst F t s) s := by
  let T:=nearIdentityEquiv F hF s hs
  let σ:ℝ:=(‖thresholdLift T‖+1)⁻¹
  have hp:0<σ:=by dsimp [σ];positivity
  have hl:CenteredSingularLowerBound (thresholdPath F t s).1 σ:=by
    rw [thresholdPath_rows];exact threshold_singular_lower T
  have hd:=(hasFDerivAt_mass_joint_component _ _ σ hp hl none).comp_hasDerivAt s
    (thresholdPath_hasDerivAt F t s)
  rw [jointMassDerivativeAt_eq_tested _ _ σ hp hl] at hd
  exact hd

lemma cdfFirst_hasDerivAt (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (hFs : F.toLinearMap.IsSymmetric) (t s : ℝ) (hs : |s|≤1) :
    HasDerivAt (cdfFirst F t)
      (∫x in (nearIdentityMap F s) ⁻¹' (orthant t),linearMassBulk (pathVelocity F hF s hs) x
        ∂stdGaussian (FSC.Coord d)) s := by
  let T:=nearIdentityEquiv F hF s hs
  let σ:ℝ:=(‖thresholdLift T‖+1)⁻¹
  have hp:0<σ:=by dsimp [σ];positivity
  have hl:CenteredSingularLowerBound (thresholdPath F t s).1 σ:=by
    rw [thresholdPath_rows];exact threshold_singular_lower T
  have hL:CoherentLift (thresholdPath F t s).1 (thresholdLift T):=by
    rw [thresholdPath_rows];exact thresholdLift_coherent T
  have hd:=(hasFDerivAt_constantDerivative _ _ σ hp hl (thresholdLift T) hL none).comp_hasDerivAt s
    (thresholdPath_hasDerivAt F t s)
  have hd':=hd.clm_apply (hasDerivAt_const s (thresholdDirection F))
  have he:constantHessian (thresholdPath F t s).1 (thresholdPath F t s).2 (thresholdLift T)
      none (thresholdDirection F) (thresholdDirection F)=
      ∫x in (nearIdentityMap F s) ⁻¹' (orthant t),linearMassBulk (pathVelocity F hF s hs) x
        ∂stdGaussian (FSC.Coord d):=by
    rw [thresholdPath_rows,thresholdDirection_eq_affine F hF s hs]
    have hh:=constantHessian_eq_linearMassBulk (thresholdRows (nearIdentityMap F s))
      (thresholdOffsets t) σ hp (threshold_singular_lower T) (thresholdLift T) none
      (pathVelocity F hF s hs) (pathVelocity_symmetric F hF hFs s hs) (threshold_velocity T _)
    simpa only [threshold_winningCell,thresholdPath] using hh
  simp only [ContinuousLinearMap.map_zero,add_zero] at hd'
  change HasDerivAt (cdfFirst F t)
    (constantHessian (thresholdPath F t s).1 (thresholdPath F t s).2 (thresholdLift T)
      none (thresholdDirection F) (thresholdDirection F)) s at hd'
  rw [he] at hd'
  exact hd' 

lemma cdfFirst_eq_integral (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (t s : ℝ) (hs : |s|≤1) :
    cdfFirst F t s=∫x in (nearIdentityMap F s) ⁻¹' (orthant t),
      quadraticScore (pathVelocity F hF s hs) x ∂stdGaussian (FSC.Coord d) := by
  let T:=nearIdentityEquiv F hF s hs
  let σ:ℝ:=(‖thresholdLift T‖+1)⁻¹
  have hp:0<σ:=by dsimp [σ];positivity
  unfold cdfFirst
  rw [thresholdPath_rows,thresholdDirection_eq_affine F hF s hs]
  change testedCellDerivative (thresholdRows (nearIdentityMap F s)) (thresholdOffsets t)
    none (fun _=>1) (affineParameterVelocity (thresholdRows (nearIdentityMap F s))
      (pathVelocity F hF s hs) 0)=_
  have hh:=testedCellDerivative_one_affineParameters (thresholdRows (nearIdentityMap F s))
    (thresholdOffsets t) σ hp (threshold_singular_lower T) none (pathVelocity F hF s hs) 0
  simpa only [threshold_winningCell,massBulk_zero_eq] using hh

lemma pathVelocity_zero (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2) :
    pathVelocity F hF 0 (by norm_num)=F := by
  apply ContinuousLinearMap.ext
  intro x
  have he:=pathVelocity_apply_map F hF 0 (by norm_num) x
  simpa [nearIdentityMap] using he

lemma cdfFirst_zero_eq (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2) (t : ℝ) :
    cdfFirst F t 0=∫x in orthant t,quadraticScore F x ∂stdGaussian (FSC.Coord d) := by
  rw [cdfFirst_eq_integral F hF t 0 (by norm_num),pathVelocity_zero]
  simp [nearIdentityMap]

lemma cdfSecond_abs_le (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (hFs : F.toLinearMap.IsSymmetric) (t s : ℝ) (hs : |s|≤1) :
    |deriv (cdfFirst F t) s|≤580*(operatorHilbertSchmidt F)^2*
      Real.sqrt ((stdGaussian (FSC.Coord d)).real ((nearIdentityMap F s) ⁻¹' (orthant t))) := by
  rw [(cdfFirst_hasDerivAt F hF hFs t s hs).deriv]
  refine (linearMassBulk_setIntegral_abs_le _ _).trans ?_
  have hA:=pathVelocity_HS_le F hF s hs
  have hA0:=operatorHilbertSchmidt_nonneg (pathVelocity F hF s hs)
  have hF0:=operatorHilbertSchmidt_nonneg F
  have hh:145*(operatorHilbertSchmidt (pathVelocity F hF s hs))^2≤580*(operatorHilbertSchmidt F)^2:=by
    nlinarith [sq_nonneg (2*operatorHilbertSchmidt F-operatorHilbertSchmidt (pathVelocity F hF s hs))]
  exact mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)

lemma cdfSecond_abs_le_compl (F : FSC.Coord d→L[ℝ] FSC.Coord d) (hF : ‖F‖≤1/2)
    (hFs : F.toLinearMap.IsSymmetric) (t s : ℝ) (hs : |s|≤1) :
    |deriv (cdfFirst F t) s|≤580*(operatorHilbertSchmidt F)^2*
      Real.sqrt ((stdGaussian (FSC.Coord d)).real (((nearIdentityMap F s) ⁻¹' (orthant t))ᶜ)) := by
  rw [(cdfFirst_hasDerivAt F hF hFs t s hs).deriv]
  have hm:MeasurableSet ((nearIdentityMap F s) ⁻¹' (orthant t)):=
    (orthant_measurable t).preimage (nearIdentityMap F s).continuous.measurable
  refine (linearMassBulk_setIntegral_abs_le_compl _ (pathVelocity_symmetric F hF hFs s hs) _ hm).trans ?_
  have hA:=pathVelocity_HS_le F hF s hs
  have hA0:=operatorHilbertSchmidt_nonneg (pathVelocity F hF s hs)
  have hF0:=operatorHilbertSchmidt_nonneg F
  have hh:145*(operatorHilbertSchmidt (pathVelocity F hF s hs))^2≤580*(operatorHilbertSchmidt F)^2:=by
    nlinarith [sq_nonneg (2*operatorHilbertSchmidt F-operatorHilbertSchmidt (pathVelocity F hF s hs))]
  exact mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)

end NegativeVotingThresholdCDFDerivative
