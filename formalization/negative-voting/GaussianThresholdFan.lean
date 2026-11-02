import GaussianMassHessianBulk

/-! Full-rank fan representation of an equal-threshold Gaussian event. The
extra zero score is used only after adding the independent common Gaussian,
so the d score rows and the zero row are affinely independent in dimension d. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingThresholdFan
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanMassSecondDerivative NegativeVotingCoherentLiftHessian
  NegativeVotingGlobalTensorTransport NegativeVotingQuadraticBulkNorm
  NegativeVotingFanQuadraticTransport NegativeVotingCapTail NegativeVotingFanJointMass
  NegativeVotingMassHessianBulk
variable {d : ℕ}

def orthant (t : ℝ) : Set (FSC.Coord d) := {x | ∀i,x i≤t}

def thresholdRows (T : FSC.Coord d→L[ℝ] FSC.Coord d) : Option (Fin d)→FSC.Coord d
  | none=>0
  | some i=>T.adjoint (EuclideanSpace.basisFun (Fin d) ℝ i)

def thresholdOffsets (t : ℝ) : Option (Fin d)→ℝ
  | none=>t
  | some _=>0

lemma threshold_winningCell (T : FSC.Coord d→L[ℝ] FSC.Coord d) (t : ℝ) :
    winningCell (thresholdRows T) (thresholdOffsets t) none = T ⁻¹' (orthant t) := by
  ext x
  change (∀j,scores (thresholdRows T) (thresholdOffsets t) x j ≤ scores (thresholdRows T) (thresholdOffsets t) x none) ↔ _
  have hz : scores (thresholdRows T) (thresholdOffsets t) x none=t := by simp [scores,thresholdRows,thresholdOffsets]
  rw [hz]
  change (∀j,scores (thresholdRows T) (thresholdOffsets t) x j ≤ t) ↔ ∀ i,(T x) i ≤ t
  constructor
  · intro h i
    simpa only [scores,thresholdRows,thresholdOffsets,ContinuousLinearMap.adjoint_inner_left,
      EuclideanSpace.basisFun_inner,add_zero] using h (some i)
  · intro h j
    cases j with
    | none=>simp [scores,thresholdRows,thresholdOffsets]
    | some i=>
      simpa only [scores,thresholdRows,thresholdOffsets,ContinuousLinearMap.adjoint_inner_left,
        EuclideanSpace.basisFun_inner,add_zero] using h i

lemma orthant_measurable (t : ℝ) : MeasurableSet (orthant (d:=d) t) := by
  unfold orthant
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i=>measurableSet_le (by fun_prop) measurable_const

def baseLift (d : ℕ) : (Option (Fin d)→ℝ)→L[ℝ] FSC.Coord d :=
  ∑i:Fin d,((ContinuousLinearMap.proj (some i) : (Option (Fin d)→ℝ)→L[ℝ] ℝ)-
    ContinuousLinearMap.proj none).smulRight (EuclideanSpace.basisFun (Fin d) ℝ i)

lemma baseLift_coordinate (q : Option (Fin d)→ℝ) (i : Fin d) :
    baseLift d q i=q (some i)-q none := by
  simp [baseLift,EuclideanSpace.basisFun_apply,Pi.single_apply,eq_comm]

def thresholdLift (T : FSC.Coord d≃L[ℝ] FSC.Coord d) :
    (Option (Fin d)→ℝ)→L[ℝ] FSC.Coord d := T.symm.toContinuousLinearMap.comp (baseLift d)

lemma thresholdLift_coherent (T : FSC.Coord d≃L[ℝ] FSC.Coord d) :
    CoherentLift (thresholdRows T.toContinuousLinearMap) (thresholdLift T) := by
  intro q i j
  have he (k:Option (Fin d)) : inner ℝ (thresholdRows T.toContinuousLinearMap k) (thresholdLift T q)=
      q k-q none:=by
    cases k with
    | none=>simp [thresholdRows]
    | some k=>
      simp only [thresholdRows,ContinuousLinearMap.adjoint_inner_left,thresholdLift,
        ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply,EuclideanSpace.basisFun_inner]
      exact baseLift_coordinate q k
  rw [inner_sub_left,he i,he j]
  ring

lemma thresholdLift_scores (T : FSC.Coord d≃L[ℝ] FSC.Coord d) (x : FSC.Coord d) :
    thresholdLift T (fun i=>inner ℝ (thresholdRows T.toContinuousLinearMap i) x)=x := by
  apply T.injective
  change T (T.symm (baseLift d (fun i=>inner ℝ (thresholdRows T.toContinuousLinearMap i) x)))=T x
  rw [T.apply_symm_apply]
  ext i
  rw [baseLift_coordinate]
  simp only [thresholdRows,ContinuousLinearMap.adjoint_inner_left,inner_zero_left,sub_zero,EuclideanSpace.basisFun_inner]
  rfl

lemma threshold_velocity (T : FSC.Coord d≃L[ℝ] FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    velocityMap (thresholdLift T) (affineParameterVelocity (thresholdRows T.toContinuousLinearMap) A 0)=(A,0) := by
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    change thresholdLift T (fun i=>inner ℝ (A.adjoint (thresholdRows T.toContinuousLinearMap i)) x)=A x
    simp only [ContinuousLinearMap.adjoint_inner_left]
    exact thresholdLift_scores T (A x)
  · change thresholdLift T (fun i=>inner ℝ (thresholdRows T.toContinuousLinearMap i) 0)=0
    simp only [inner_zero_right]
    exact (thresholdLift T).map_zero

section CoherentLower
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Any actual coherent right inverse implies a positive centered singular
lower bound. The numerical constant is used only for differentiability. -/
lemma coherent_singular_lower (B : ι→FSC.Coord d) (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (hL : CoherentLift B L) : CenteredSingularLowerBound B (‖L‖+1)⁻¹ := by
  intro c hc
  let E:ℝ:=∑i,(c i)^2
  let Y:FSC.Coord d:=∑i,c i • B i
  let K:ℝ:=‖L‖+1
  have hE:0≤E:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hK:0<K:=by dsimp [K];positivity
  have he:inner ℝ Y (L c)=E:=by
    let i₀:ι:=Classical.arbitrary ι
    have hh (i:ι):inner ℝ (B i) (L c)=c i-c i₀+inner ℝ (B i₀) (L c):=by
      have h:=hL c i i₀
      rw [inner_sub_left] at h
      linarith
    dsimp only [Y,E]
    simp only [sum_inner,real_inner_smul_left]
    calc
      (∑ i,c i*inner ℝ (B i) (L c)) = ∑ i,c i*(c i-c i₀+inner ℝ (B i₀) (L c)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hh i]
      _ = _ := by
        simp_rw [mul_add,mul_sub]
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.sum_mul,hc]
        simp only [zero_mul,sub_zero,add_zero,pow_two]
  have hcn:‖c‖≤Real.sqrt E:=by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg E)).mpr
    intro i
    rw [Real.norm_eq_abs,←Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f:=fun j=>(c j)^2) (fun j _=>sq_nonneg _) (Finset.mem_univ i))
  have hLn:‖L c‖≤K*Real.sqrt E:=by
    refine (L.le_opNorm c).trans ?_
    exact mul_le_mul (by dsimp [K];linarith [norm_nonneg L]) hcn (norm_nonneg c) (by positivity)
  have hbound:E≤‖Y‖*K*Real.sqrt E:=by
    calc
      E = inner ℝ Y (L c):=he.symm
      _≤‖Y‖*‖L c‖:=real_inner_le_norm _ _
      _≤_:=by convert mul_le_mul_of_nonneg_left hLn (norm_nonneg Y) using 1 <;>ring
  have hs:Real.sqrt E≤‖Y‖*K:=by
    have hsq:=Real.sq_sqrt hE
    by_cases hz:Real.sqrt E=0
    · rw [hz];positivity
    · have hp:0<Real.sqrt E:=lt_of_le_of_ne (Real.sqrt_nonneg E) (Ne.symm hz)
      nlinarith
  have hs2:=pow_le_pow_left₀ (Real.sqrt_nonneg E) hs 2
  rw [Real.sq_sqrt hE,mul_pow] at hs2
  change K⁻¹^2*E≤‖Y‖^2
  have hm:=mul_le_mul_of_nonneg_left hs2 (sq_nonneg K⁻¹)
  convert hm using 1 <;>field_simp <;>ring

end CoherentLower

lemma threshold_singular_lower (T : FSC.Coord d≃L[ℝ] FSC.Coord d) :
    CenteredSingularLowerBound (thresholdRows T.toContinuousLinearMap) (‖thresholdLift T‖+1)⁻¹ :=
  coherent_singular_lower _ _ (thresholdLift_coherent T)

end NegativeVotingThresholdFan
