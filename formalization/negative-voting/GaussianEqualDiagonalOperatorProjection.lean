import GaussianEqualDiagonalProjection
import GaussianCovarianceEnergyRectangle
import GaussianBalancedOffsetPath

/-! Operator realization of the exact equal-diagonal split. The positive
factors below act on the actual reference span and realize actual Gaussian
rows. The equal-row certificate and its free-maximum input are separate. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingEqualDiagonalOperatorProjection
open NegativeVotingEqualDiagonalProjection NegativeVotingStrongDiagonalCurvature
  NegativeVotingProcrustes NegativeVotingAffineLogMassBound
  NegativeVotingCovarianceEnergyRectangle NegativeVotingCovarianceFactorDistance
  NegativeVotingPositiveCovariance NegativeVotingCapTail NegativeVotingBalancedOffsetPath
  NegativeVotingNearRegularEnergyComparison NegativeVotingAffineNormControl NegativeVotingRayDeficit
variable {m d : ℕ} [NeZero m]

def diagonalOperator (b : Fin m→FSC.Coord d)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  ((m:ℝ)/((m:ℝ)-2)) • (∑i,(inner ℝ (b i) (H (b i)) : ℝ) •
    (InnerProductSpace.rankOne ℝ (b i) (b i) : FSC.Coord d→L[ℝ]FSC.Coord d))

def zeroDiagonalOperator (b : Fin m→FSC.Coord d)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  H-diagonalOperator b H

theorem diagonalOperator_pairing (b : Fin m→FSC.Coord d)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (x y : FSC.Coord d) :
    inner ℝ x (diagonalOperator b H y)=
      ((m:ℝ)/((m:ℝ)-2))*∑i,inner ℝ (b i) (H (b i))*
        inner ℝ (b i) x*inner ℝ (b i) y := by
  simp only [diagonalOperator,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    real_inner_smul_right,inner_sum,InnerProductSpace.rankOne_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm x (b i)]
  ring

theorem diagonalOperator_symmetric (b : Fin m→FSC.Coord d)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) :
    (diagonalOperator b H).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (diagonalOperator b H x) y=inner ℝ x (diagonalOperator b H y)
  rw [real_inner_comm,diagonalOperator_pairing,diagonalOperator_pairing]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem centered_diagonal_pairing (z : Fin m→ℝ) (hz : ∑i,z i=0) (i j : Fin m) :
    (∑k,z k*((if k=i then 1 else 0)-1/(m:ℝ))*
      ((if k=j then 1 else 0)-1/(m:ℝ)))=
      (if i=j then z i else 0)-(z i+z j)/(m:ℝ) := by
  have he k : z k*((if k=i then 1 else 0)-1/(m:ℝ))*
      ((if k=j then 1 else 0)-1/(m:ℝ))=
      (if k=i then (if i=j then z i else 0) else 0)-
        (if k=i then z i/(m:ℝ) else 0)-
        (if k=j then z j/(m:ℝ) else 0)+z k/(m:ℝ)^2 := by
    by_cases hi:k=i <;> by_cases hj:k=j
    · subst k
      subst j
      simp only [ite_true]
      ring
    · subst k
      simp only [ite_true,ite_false,hj]
      ring
    · subst k
      simp only [ite_true,ite_false,hi,Ne.symm hi]
      ring
    · simp only [ite_false,hi,hj]
      ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,←Finset.sum_div,hz,zero_div,add_zero]
  ring

theorem diagonalOperator_entry (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) (i j : Fin m) :
    inner ℝ (b i) (diagonalOperator b H (b j))=
      diagonalPart (fun a c=>inner ℝ (b a) (H (b c))) i j := by
  rw [diagonalOperator_pairing]
  simp_rw [hG]
  rw [centered_diagonal_pairing _ htr]
  rfl

theorem zeroDiagonalOperator_entry (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) (i j : Fin m) :
    inner ℝ (b i) (zeroDiagonalOperator b H (b j))=
      zeroDiagonalPart (fun a c=>inner ℝ (b a) (H (b c))) i j := by
  simp only [zeroDiagonalOperator,ContinuousLinearMap.sub_apply,inner_sub_right,
    diagonalOperator_entry b hG H htr,zeroDiagonalPart,Pi.sub_apply]

theorem zeroDiagonalOperator_diagonal (hm : 3 ≤ m) (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) (i : Fin m) :
    inner ℝ (b i) (zeroDiagonalOperator b H (b i))=0 := by
  rw [zeroDiagonalOperator_entry b hG H htr,zeroDiagonalPart_diagonal hm]

theorem operator_split_symmetric (b : Fin m→FSC.Coord d)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    (diagonalOperator b H).toLinearMap.IsSymmetric ∧
      (zeroDiagonalOperator b H).toLinearMap.IsSymmetric :=
  ⟨diagonalOperator_symmetric b H,hH.sub (diagonalOperator_symmetric b H)⟩

theorem operator_split_pythagoras (hm : 3 ≤ m) (b : Fin m→FSC.Coord d)
    (hb : ∑i,b i=0) (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) :
    (operatorHilbertSchmidt H)^2=(operatorHilbertSchmidt (diagonalOperator b H))^2+
      (operatorHilbertSchmidt (zeroDiagonalOperator b H))^2 := by
  let E:=fun i j=>inner ℝ (b i) (H (b j))
  have hsym (i j : Fin m) : E i j=E j i :=
    (hH (b i) (b j)).symm.trans (real_inner_comm _ _)
  have hrow i : (∑j,E i j)=0 := by
    dsimp [E]
    rw [←inner_sum,←map_sum,hb,map_zero,inner_zero_right]
  simp only [scoreGram_HilbertSchmidt_sq b hP,diagonalOperator_entry b hG H htr,
    zeroDiagonalOperator_entry b hG H htr]
  exact diagonal_parts_pythagoras hm E hsym hrow htr

theorem operator_split_refined_strain (hm : 3 ≤ m) (b : Fin m→FSC.Coord d)
    (hb : ∑i,b i=0) (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) :
    refinedStrain b H=(m:ℝ)/2*(operatorHilbertSchmidt (diagonalOperator b H))^2+
      (operatorHilbertSchmidt (zeroDiagonalOperator b H))^2 := by
  rw [operator_refined_strain_decomposition hm b hb hP H hH htr]
  simp only [scoreGram_HilbertSchmidt_sq b hP,diagonalOperator_entry b hG H htr,
    zeroDiagonalOperator_entry b hG H htr]

theorem symmetric_factor_norm_sq (T : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hT : T.toLinearMap.IsSymmetric) (x : FSC.Coord d) :
    ‖T x‖^2=inner ℝ x ((T.comp T) x) := by
  rw [←real_inner_self_eq_norm_sq]
  exact hT x (T x)

theorem zero_diagonal_factor_row_norm (hm : 3 ≤ m) (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0)
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hTT : T.comp T=ContinuousLinearMap.id ℝ (FSC.Coord d)+zeroDiagonalOperator b H)
    (α : ℝ) (i : Fin m) :
    ‖α • T (b i)‖^2=α^2*(1-1/(m:ℝ)) := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,symmetric_factor_norm_sq T hT,hTT]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,inner_add_right,
    zeroDiagonalOperator_diagonal hm b hG H htr,hG,ite_true,add_zero]

theorem mapped_scaled_regular_lower {n : ℕ} (b : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (T : FSC.Coord d≃L[ℝ]FSC.Coord d) (hT : ‖T.symm.toContinuousLinearMap‖ ≤ 2)
    (α : ℝ) :
    CenteredSingularLowerBound (fun i=>α • T (b i)) (α/2) := by
  have hh := mapped_regular_lower b (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG) T hT
  intro c hc
  have h0 := mul_le_mul_of_nonneg_left (hh c hc) (sq_nonneg α)
  have he : (∑i,c i • (α • T (b i)))=α • ∑i,c i • T (b i) := by
    simp only [Finset.smul_sum,smul_smul]
    congr 1
    funext i
    rw [mul_comm]
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  nlinarith only [h0]

/-- Both actual positive factors are produced from a single trace-zero
covariance displacement. The projected factor has exactly equal row norms,
not merely approximately equal norms, and retains the full inverse bound. -/
theorem exists_actual_equal_diagonal_factors {n : ℕ} (hn : 1 ≤ n)
    (b : Fin (n+2)→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0)
    (hsmall : (operatorHilbertSchmidt H)^2 ≤ 1/1024)
    (α e : ℝ) (hα : 0 < α) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2) :
    ∃ S T : FSC.Coord d≃L[ℝ]FSC.Coord d,
      S.toContinuousLinearMap∈psdCone ∧ T.toContinuousLinearMap∈psdCone ∧
      S.toContinuousLinearMap.comp S.toContinuousLinearMap=ContinuousLinearMap.id ℝ (FSC.Coord d)+H ∧
      T.toContinuousLinearMap.comp T.toContinuousLinearMap=
        ContinuousLinearMap.id ℝ (FSC.Coord d)+zeroDiagonalOperator b H ∧
      ‖S.symm.toContinuousLinearMap‖ ≤ 2 ∧ ‖T.symm.toContinuousLinearMap‖ ≤ 2 ∧
      (∑i,α • T (b i))=0 ∧
      (∀i,‖α • T (b i)‖^2=α^2*(1-1/((n+2:ℕ):ℝ))) ∧
      CenteredSingularLowerBound (fun i=>α • T (b i)) (α/2) ∧
      |factorEnergy b α S.toContinuousLinearMap-factorEnergy b α T.toContinuousLinearMap| ≤
        energyComparisonCoefficient n α e (4*α^2*(operatorHilbertSchmidt H)^2)*α^2*
          ((operatorHilbertSchmidt (diagonalOperator b H))^2+
            6*operatorHilbertSchmidt (zeroDiagonalOperator b H)*operatorHilbertSchmidt (diagonalOperator b H)) := by
  let X:=zeroDiagonalOperator b H
  let V:=diagonalOperator b H
  have hsplit : X+V=H := by dsimp [X,V,zeroDiagonalOperator];abel
  have hsym := operator_split_symmetric b H hH
  have hp := operator_split_pythagoras (by omega : 3 ≤ n+2) b hb hP hG H hH htr
  have hsize : (operatorHilbertSchmidt X)^2+(operatorHilbertSchmidt V)^2 ≤ 1/1024 := by
    dsimp [X,V]
    nlinarith only [hp,hsmall]
  have hx0:=operatorHilbertSchmidt_nonneg X
  have hv0:=operatorHilbertSchmidt_nonneg V
  have hx : operatorHilbertSchmidt X ≤ 1/32 := by nlinarith [sq_nonneg (operatorHilbertSchmidt V)]
  have hh : operatorHilbertSchmidt H ≤ 1/8 := by
    nlinarith [operatorHilbertSchmidt_nonneg H]
  obtain ⟨S,hS,hSi,hSS,hInvS,hnearS,hSpos⟩ := exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+H) (identity_positive.1.add hH)
    (by simpa only [add_sub_cancel_left] using hh)
  obtain ⟨T,hT,hTi,hTT,hInvT,hnearT,hTpos⟩ := exists_near_factor
    (ContinuousLinearMap.id ℝ (FSC.Coord d)+X) (identity_positive.1.add hsym.2)
    (by simpa only [add_sub_cancel_left] using hx.trans (by norm_num))
  have hdist:=positive_half_factor_distance S.toContinuousLinearMap T.toContinuousLinearMap
    hS.1 hT.1 hSpos hTpos
  rw [hSS,hTT] at hdist
  have hdiff : (ContinuousLinearMap.id ℝ (FSC.Coord d)+H)-
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+X)=V := by rw [←hsplit];abel
  rw [hdiff] at hdist
  simp only [add_sub_cancel_left] at hnearT
  have henergy := factorEnergy_rectangle_le hn b hP hG _ _ _ _ α e hx0 hv0 hα he
    hnearT hdist hsize hscale
  have hp' : (operatorHilbertSchmidt X)^2+(operatorHilbertSchmidt V)^2=
      (operatorHilbertSchmidt H)^2 := by dsimp [X,V];nlinarith only [hp]
  rw [hp'] at henergy
  refine ⟨S,T,hS,hT,hSS,hTT,hInvS,hInvT,?_,?_,?_,henergy⟩
  · rw [←Finset.smul_sum,←map_sum,hb,map_zero,smul_zero]
  · exact zero_diagonal_factor_row_norm (by omega) b hG H htr T.toContinuousLinearMap hT.1 hTT α
  · exact mapped_scaled_regular_lower b hG T hInvT α

end NegativeVotingEqualDiagonalOperatorProjection
