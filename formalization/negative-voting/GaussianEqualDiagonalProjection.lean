import GaussianStrongDiagonalCurvature

/-! Exact equal-diagonal decomposition of a centered trace-zero score-Gram
direction. This retains the dimension-weighted strain; analytic rectangle
comparison of the actual second energy is a separate obligation. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators Classical
namespace NegativeVotingEqualDiagonalProjection
variable {m : ℕ}

/-- Entrywise formula for m/(m-2) P diag(z) P when sum z=0. -/
def diagonalLift (z : Fin m→ℝ) (i j : Fin m) : ℝ :=
  (m:ℝ)/((m:ℝ)-2)*((if i=j then z i else 0)-(z i+z j)/(m:ℝ))

def diagonalPart (E : Fin m→Fin m→ℝ) : Fin m→Fin m→ℝ:=diagonalLift (fun i=>E i i)
def zeroDiagonalPart (E : Fin m→Fin m→ℝ) : Fin m→Fin m→ℝ:=E-diagonalPart E

theorem diagonalLift_symmetric (z : Fin m→ℝ) (i j : Fin m) :
    diagonalLift z i j=diagonalLift z j i := by
  by_cases hij:i=j
  · subst j;rfl
  · simp only [diagonalLift,ite_eq_right hij,ite_eq_right (Ne.symm hij),add_comm]

theorem diagonalLift_diagonal (hm : 3 ≤ m) (z : Fin m→ℝ) (i : Fin m) :
    diagonalLift z i i=z i := by
  have hm0 : (m:ℝ)≠0:=by exact_mod_cast (show m≠0 by omega)
  have hm2 : (m:ℝ)-2≠0:=by
    have hh : (3:ℝ) ≤ m:=by exact_mod_cast hm
    linarith
  simp only [diagonalLift,ite_true]
  field_simp
  ring

theorem diagonalLift_centered (hm : 3 ≤ m) (z : Fin m→ℝ) (hz : ∑i,z i=0) (i : Fin m) :
    ∑j,diagonalLift z i j=0 := by
  have hm0 : (m:ℝ)≠0:=by exact_mod_cast (show m≠0 by omega)
  simp only [diagonalLift,←Finset.mul_sum,Finset.sum_sub_distrib,←Finset.sum_div,
    Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hz,add_zero]
  field_simp
  ring

/-- The exact adjoint formula on centered matrices. No independence of the
diagonal and off-diagonal entries is assumed. -/
theorem diagonalLift_pairing (z : Fin m→ℝ) (F : Fin m→Fin m→ℝ)
    (hrow : ∀i,∑j,F i j=0) (hcol : ∀j,∑i,F i j=0) :
    (∑i,∑j,diagonalLift z i j*F i j)=((m:ℝ)/((m:ℝ)-2))*∑i,z i*F i i := by
  have hr : (∑i,∑j,z i*F i j)=0:=by
    simp only [←Finset.mul_sum,hrow,mul_zero,Finset.sum_const_zero]
  have hc : (∑i,∑j,z j*F i j)=0:=by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,hcol,mul_zero,Finset.sum_const_zero]
  have he (i j : Fin m) : diagonalLift z i j*F i j=
      ((m:ℝ)/((m:ℝ)-2))*((if i=j then z i*F i j else 0)-
        (z i*F i j)/(m:ℝ)-(z j*F i j)/(m:ℝ)) := by
    unfold diagonalLift
    split_ifs <;> ring
  simp only [he,←Finset.mul_sum,Finset.sum_sub_distrib,←Finset.sum_div]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,hc,hrow,mul_zero,Finset.sum_const_zero,zero_div,sub_zero]

theorem diagonalLift_norm_sq (hm : 3 ≤ m) (z : Fin m→ℝ) (hz : ∑i,z i=0) :
    (∑i,∑j,(diagonalLift z i j)^2)=((m:ℝ)/((m:ℝ)-2))*∑i,(z i)^2 := by
  have hr:=diagonalLift_centered hm z hz
  have hc j : (∑i,diagonalLift z i j)=0:=by
    simp_rw [diagonalLift_symmetric z]
    exact hr j
  have hh:=diagonalLift_pairing z (diagonalLift z) hr hc
  simpa only [diagonalLift_diagonal hm,pow_two] using hh

theorem zeroDiagonalPart_diagonal (hm : 3 ≤ m) (E : Fin m→Fin m→ℝ) (i : Fin m) :
    zeroDiagonalPart E i i=0 := by
  simp only [zeroDiagonalPart,Pi.sub_apply,diagonalPart,diagonalLift_diagonal hm,sub_self]

theorem zeroDiagonalPart_centered (hm : 3 ≤ m) (E : Fin m→Fin m→ℝ)
    (hrow : ∀i,∑j,E i j=0) (htr : ∑i,E i i=0) (i : Fin m) :
    ∑j,zeroDiagonalPart E i j=0 := by
  simp only [zeroDiagonalPart,Pi.sub_apply,Finset.sum_sub_distrib,hrow,
    diagonalPart,diagonalLift_centered hm _ htr,sub_self]

theorem zeroDiagonalPart_symmetric (E : Fin m→Fin m→ℝ)
    (hsym : ∀i j,E i j=E j i) (i j : Fin m) :
    zeroDiagonalPart E i j=zeroDiagonalPart E j i := by
  simp only [zeroDiagonalPart,Pi.sub_apply,diagonalPart,hsym i j,diagonalLift_symmetric _ i j]

theorem diagonal_parts_orthogonal (hm : 3 ≤ m) (E : Fin m→Fin m→ℝ)
    (hsym : ∀i j,E i j=E j i) (hrow : ∀i,∑j,E i j=0) (htr : ∑i,E i i=0) :
    (∑i,∑j,diagonalPart E i j*zeroDiagonalPart E i j)=0 := by
  have hr:=zeroDiagonalPart_centered hm E hrow htr
  have hc j : (∑i,zeroDiagonalPart E i j)=0:=by
    simp_rw [zeroDiagonalPart_symmetric E hsym]
    exact hr j
  have hh:=diagonalLift_pairing (fun i=>E i i) (zeroDiagonalPart E) hr hc
  simpa only [diagonalPart,zeroDiagonalPart_diagonal hm,mul_zero,Finset.sum_const_zero] using hh

theorem diagonal_parts_pythagoras (hm : 3 ≤ m) (E : Fin m→Fin m→ℝ)
    (hsym : ∀i j,E i j=E j i) (hrow : ∀i,∑j,E i j=0) (htr : ∑i,E i i=0) :
    (∑i,∑j,(E i j)^2)=(∑i,∑j,(diagonalPart E i j)^2)+
      (∑i,∑j,(zeroDiagonalPart E i j)^2) := by
  have ho:=diagonal_parts_orthogonal hm E hsym hrow htr
  have he (i j : Fin m) : (E i j)^2=(diagonalPart E i j)^2+
      (zeroDiagonalPart E i j)^2+2*(diagonalPart E i j*zeroDiagonalPart E i j):=by
    simp only [zeroDiagonalPart,Pi.sub_apply]
    ring
  simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [ho,mul_zero,add_zero]

/-- Exactly the retained strain from StrongDiagonalCurvature: the diagonal
component receives weight m/2, while the zero-diagonal component receives one. -/
theorem refined_strain_decomposition (hm : 3 ≤ m) (E : Fin m→Fin m→ℝ)
    (hsym : ∀i j,E i j=E j i) (hrow : ∀i,∑j,E i j=0) (htr : ∑i,E i i=0) :
    (∑i,∑j,(E i j)^2)+(m:ℝ)/2*(∑i,(E i i)^2)+(∑i,E i i)^2/2=
      (m:ℝ)/2*(∑i,∑j,(diagonalPart E i j)^2)+(∑i,∑j,(zeroDiagonalPart E i j)^2) := by
  have hp:=diagonal_parts_pythagoras hm E hsym hrow htr
  have hn : (∑i,∑j,(diagonalPart E i j)^2)=((m:ℝ)/((m:ℝ)-2))*∑i,(E i i)^2:=
    diagonalLift_norm_sq hm _ htr
  rw [hp,hn,htr]
  have hm2 : (m:ℝ)-2≠0:=by
    have hh : (3:ℝ) ≤ m:=by exact_mod_cast hm
    linarith
  field_simp
  ring

open scoped RealInnerProductSpace
open NegativeVotingStrongDiagonalCurvature NegativeVotingProcrustes
  NegativeVotingAffineLogMassBound

/-- The matrix decomposition is exactly the one seen by the actual Gaussian
covariance curvature, with no comparison of two different norms. -/
theorem operator_refined_strain_decomposition {d : ℕ} [NeZero m]
    (hm : 3 ≤ m) (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H : FSC.Coord d→L[ℝ]FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (htr : ∑i,inner ℝ (b i) (H (b i))=0) :
    let E:=fun i j=>inner ℝ (b i) (H (b j))
    refinedStrain b H=(m:ℝ)/2*(∑i,∑j,(diagonalPart E i j)^2)+
      (∑i,∑j,(zeroDiagonalPart E i j)^2) := by
  intro E
  have hsym (i j : Fin m) : E i j=E j i :=
    (hH (b i) (b j)).symm.trans (real_inner_comm _ _)
  have hrow (i : Fin m) : (∑j,E i j)=0 := by
    dsimp only [E]
    rw [←inner_sum,←map_sum,hb,map_zero,inner_zero_right]
  have hh:=refined_strain_decomposition hm E hsym hrow htr
  unfold refinedStrain
  rw [scoreGram_HilbertSchmidt_sq b hP H]
  exact hh

end NegativeVotingEqualDiagonalProjection
