import GaussianAffineNormControl

/-! Elementary norm structure for the actual coordinate Hilbert--Schmidt norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped RealInnerProductSpace BigOperators
namespace NegativeVotingOperatorHS
open NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl InnerProductSpace
variable {d : ℕ}

def operatorVector (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    EuclideanSpace ℝ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun jk => operatorEntries A jk.1 jk.2)

theorem operatorHilbertSchmidt_eq_norm (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorHilbertSchmidt A=‖operatorVector A‖ := by
  rw [operatorHilbertSchmidt,EuclideanSpace.norm_eq]
  congr 1
  simp only [Real.norm_eq_abs,sq_abs,Fintype.sum_prod_type]
  rfl

theorem operatorVector_add (A B : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorVector (A+B)=operatorVector A+operatorVector B := by
  ext jk
  rfl

theorem operatorVector_sub (A B : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorVector (A-B)=operatorVector A-operatorVector B := by
  ext jk
  rfl

theorem operatorHilbertSchmidt_add_le (A B : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorHilbertSchmidt (A+B) ≤ operatorHilbertSchmidt A+operatorHilbertSchmidt B := by
  rw [operatorHilbertSchmidt_eq_norm,operatorHilbertSchmidt_eq_norm,
    operatorHilbertSchmidt_eq_norm,operatorVector_add]
  exact norm_add_le _ _

theorem operatorHilbertSchmidt_sub_le (A B : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorHilbertSchmidt (A-B) ≤ operatorHilbertSchmidt A+operatorHilbertSchmidt B := by
  rw [operatorHilbertSchmidt_eq_norm,operatorHilbertSchmidt_eq_norm,
    operatorHilbertSchmidt_eq_norm,operatorVector_sub]
  exact norm_sub_le _ _

theorem operatorHilbertSchmidt_rankOne (u v : FSC.Coord d) :
    operatorHilbertSchmidt (rankOne ℝ u v)=‖u‖*‖v‖ := by
  apply (sq_eq_sq₀ (operatorHilbertSchmidt_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [operatorHilbertSchmidt_sq,mul_pow]
  change (∑j,‖inner ℝ v (EuclideanSpace.basisFun (Fin d) ℝ j) • u‖^2)=_
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [←Finset.sum_mul,(EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_inner_left]
  ring

end NegativeVotingOperatorHS
