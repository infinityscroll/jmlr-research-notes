import GaussianAffinePathDerivative

/-! Dimension-free operator/Frobenius bounds and actual near-identity inverses. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffineNormControl
open NegativeVotingAffineLogMassBound
variable {d : ℕ}

theorem operatorHilbertSchmidt_sq (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    (operatorHilbertSchmidt A)^2=∑ j,‖A (EuclideanSpace.basisFun (Fin d) ℝ j)‖^2 := by
  rw [operatorHilbertSchmidt,Real.sq_sqrt (Finset.sum_nonneg (fun j _=>
    Finset.sum_nonneg (fun k _=>sq_nonneg _)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem operatorHilbertSchmidt_nonneg (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    0 ≤ operatorHilbertSchmidt A := Real.sqrt_nonneg _

theorem operatorHilbertSchmidt_comp_le (M A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    operatorHilbertSchmidt (M.comp A) ≤ ‖M‖*operatorHilbertSchmidt A := by
  apply (sq_le_sq₀ (operatorHilbertSchmidt_nonneg _) (mul_nonneg (norm_nonneg _) (operatorHilbertSchmidt_nonneg _))).mp
  rw [operatorHilbertSchmidt_sq,mul_pow,operatorHilbertSchmidt_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖M (A (EuclideanSpace.basisFun (Fin d) ℝ j))‖^2 ≤ _
  have hh := M.le_opNorm (A (EuclideanSpace.basisFun (Fin d) ℝ j))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem operator_norm_le_HilbertSchmidt (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    ‖A‖ ≤ operatorHilbertSchmidt A := by
  apply A.opNorm_le_bound (operatorHilbertSchmidt_nonneg _)
  intro x
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hrep : A x=∑ j,inner ℝ (e j) x • A (e j) := by
    simpa only [map_sum,map_smul] using (congrArg A (e.sum_repr' x)).symm
  calc
    ‖A x‖ = ‖∑ j,inner ℝ (e j) x • A (e j)‖ := by rw [hrep]
    _ ≤ ∑ j,‖inner ℝ (e j) x • A (e j)‖ := norm_sum_le _ _
    _ = ∑ j,|inner ℝ (e j) x| *‖A (e j)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j,|inner ℝ (e j) x|^2)*Real.sqrt (∑ j,‖A (e j)‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = operatorHilbertSchmidt A*‖x‖ := by
      simp only [sq_abs,EuclideanSpace.basisFun_inner,e]
      rw [←EuclideanSpace.real_norm_sq_eq,Real.sqrt_sq (norm_nonneg x),←operatorHilbertSchmidt_sq,
        Real.sqrt_sq (operatorHilbertSchmidt_nonneg A),mul_comm]

def nearIdentityMap (A : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) :
    FSC.Coord d →L[ℝ] FSC.Coord d := ContinuousLinearMap.id ℝ (FSC.Coord d)+t • A

theorem nearIdentity_norm_lower (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : ‖A‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ 1) (x : FSC.Coord d) :
    ‖x‖/2 ≤ ‖nearIdentityMap A t x‖ := by
  have htri : ‖x‖ ≤ ‖nearIdentityMap A t x‖+‖t • A x‖ := by
    have he : x=(nearIdentityMap A t x)-(t • A x) := by simp [nearIdentityMap]
    calc
      _ = ‖nearIdentityMap A t x-t • A x‖ := by rw [←he]
      _ ≤ _ := norm_sub_le _ _
  have hh := A.le_opNorm x
  have hnorm : ‖t • A x‖ ≤ ‖x‖/2 := by
    rw [norm_smul,Real.norm_eq_abs]
    have h1 := mul_le_mul_of_nonneg_left hh (abs_nonneg t)
    have h2 := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
    have h3 := mul_le_mul_of_nonneg_right ht (norm_nonneg (A x))
    nlinarith
  linarith

theorem nearIdentity_injective (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : ‖A‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ 1) :
    Function.Injective (nearIdentityMap A t) := by
  intro x y he
  have hh := nearIdentity_norm_lower A hA t ht (x-y)
  rw [map_sub,he,sub_self,norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x-y)]))

/-- The inverse is constructed from the proved norm lower bound and finite
dimension; it is not supplied as an assumption. -/
def nearIdentityEquiv (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : ‖A‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ 1) : FSC.Coord d ≃L[ℝ] FSC.Coord d :=
  ContinuousLinearEquiv.ofBijective (nearIdentityMap A t)
    (LinearMap.ker_eq_bot.mpr (nearIdentity_injective A hA t ht))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (nearIdentity_injective A hA t ht)))

@[simp] theorem nearIdentityEquiv_coe (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : ‖A‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ 1) :
    (nearIdentityEquiv A hA t ht).toContinuousLinearMap=nearIdentityMap A t := rfl

theorem nearIdentity_inverse_norm_le (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hA : ‖A‖ ≤ 1/2) (t : ℝ) (ht : |t| ≤ 1) :
    ‖(nearIdentityEquiv A hA t ht).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hh := nearIdentity_norm_lower A hA t ht ((nearIdentityEquiv A hA t ht).symm x)
  have he : nearIdentityMap A t ((nearIdentityEquiv A hA t ht).symm x)=x :=
    (nearIdentityEquiv A hA t ht).apply_symm_apply x
  rw [he] at hh
  change ‖(nearIdentityEquiv A hA t ht).symm x‖ ≤ 2*‖x‖
  linarith

end NegativeVotingAffineNormControl
