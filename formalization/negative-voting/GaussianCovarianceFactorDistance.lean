import GaussianProcrustesDistance
import GaussianCovarianceSegmentGeometry

/-! Dimension-free transport between two positive covariance factors.
The Sylvester coercivity proof uses the actual Hilbert--Schmidt pairing,
so it loses no factor depending on the number of Gaussian coordinates. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCovarianceFactorDistance
open NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
  NegativeVotingPositiveCovariance NegativeVotingProcrustes
variable {d : ℕ}

def operatorPair (A B : FSC.Coord d→L[ℝ]FSC.Coord d) : ℝ :=
  ∑i,inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ i))
    (B (EuclideanSpace.basisFun (Fin d) ℝ i))

theorem operatorPair_eq_trace (A B : FSC.Coord d→L[ℝ]FSC.Coord d) :
    operatorPair A B=LinearMap.trace ℝ (FSC.Coord d) (A.adjoint.comp B).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [operatorPair,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem operatorPair_add_right (A B C : FSC.Coord d→L[ℝ]FSC.Coord d) :
    operatorPair A (B+C)=operatorPair A B+operatorPair A C := by
  simp only [operatorPair,ContinuousLinearMap.add_apply,inner_add_right,Finset.sum_add_distrib]

theorem operatorPair_le (A B : FSC.Coord d→L[ℝ]FSC.Coord d) :
    operatorPair A B ≤ operatorHilbertSchmidt A*operatorHilbertSchmidt B := by
  calc
    operatorPair A B ≤ ∑i,‖A (EuclideanSpace.basisFun (Fin d) ℝ i)‖*
        ‖B (EuclideanSpace.basisFun (Fin d) ℝ i)‖ :=
      Finset.sum_le_sum fun i _=>real_inner_le_norm _ _
    _ ≤ _ := by
      have hh:=Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i=>‖A (EuclideanSpace.basisFun (Fin d) ℝ i)‖)
        (fun i=>‖B (EuclideanSpace.basisFun (Fin d) ℝ i)‖)
      simpa only [←operatorHilbertSchmidt_sq,Real.sqrt_sq (operatorHilbertSchmidt_nonneg A),
        Real.sqrt_sq (operatorHilbertSchmidt_nonneg B)] using hh

theorem operatorPair_comp_switch (A T : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hA : A.toLinearMap.IsSymmetric) :
    operatorPair A (A.comp T)=operatorPair A (T.comp A) := by
  rw [operatorPair_eq_trace,operatorPair_eq_trace,hA.clm_adjoint_eq]
  change LinearMap.trace ℝ (FSC.Coord d) (A.toLinearMap*(A.toLinearMap*T.toLinearMap))=
    LinearMap.trace ℝ (FSC.Coord d) (A.toLinearMap*(T.toLinearMap*A.toLinearMap))
  rw [LinearMap.trace_mul_comm ℝ A.toLinearMap (A.toLinearMap*T.toLinearMap),mul_assoc]

/-- Strong positivity of the two factors gives the exact Sylvester lower
bound, without commutativity of the factors or their difference. -/
theorem sylvester_coercive (S T A : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hA : A.toLinearMap.IsSymmetric) (c : ℝ)
    (hS : ∀x,c*‖x‖^2 ≤ inner ℝ x (S x))
    (hT : ∀x,c*‖x‖^2 ≤ inner ℝ x (T x)) :
    2*c*(operatorHilbertSchmidt A)^2 ≤ operatorPair A (S.comp A+A.comp T) := by
  rw [operatorPair_add_right,operatorPair_comp_switch A T hA]
  have hs : c*(operatorHilbertSchmidt A)^2 ≤ operatorPair A (S.comp A) := by
    rw [operatorHilbertSchmidt_sq,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _=>hS _
  have ht : c*(operatorHilbertSchmidt A)^2 ≤ operatorPair A (T.comp A) := by
    rw [operatorHilbertSchmidt_sq,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _=>hT _
  linarith

/-- Actual two-factor square-root transport. The coefficient is `2c` when
both factors are at least `c I`; no simultaneous diagonalization is assumed. -/
theorem positive_factor_distance (S T : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hSsym : S.toLinearMap.IsSymmetric) (hTsym : T.toLinearMap.IsSymmetric)
    (c : ℝ) (hS : ∀x,c*‖x‖^2 ≤ inner ℝ x (S x))
    (hT : ∀x,c*‖x‖^2 ≤ inner ℝ x (T x)) :
    2*c*operatorHilbertSchmidt (S-T) ≤ operatorHilbertSchmidt (S.comp S-T.comp T) := by
  have hA : (S-T).toLinearMap.IsSymmetric:=hSsym.sub hTsym
  have hh:=sylvester_coercive S T (S-T) hA c hS hT
  have he : S.comp (S-T)+(S-T).comp T=S.comp S-T.comp T := by
    ext x
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply,map_sub]
    abel
  rw [he] at hh
  have hb:=hh.trans (operatorPair_le (S-T) (S.comp S-T.comp T))
  by_cases hz : operatorHilbertSchmidt (S-T)=0
  · rw [hz,mul_zero]
    exact operatorHilbertSchmidt_nonneg _
  · have hp : 0<operatorHilbertSchmidt (S-T):=
      lt_of_le_of_ne (operatorHilbertSchmidt_nonneg _) (Ne.symm hz)
    nlinarith

theorem positive_half_factor_distance (S T : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hSsym : S.toLinearMap.IsSymmetric) (hTsym : T.toLinearMap.IsSymmetric)
    (hS : ∀x,‖x‖^2/2 ≤ inner ℝ x (S x))
    (hT : ∀x,‖x‖^2/2 ≤ inner ℝ x (T x)) :
    operatorHilbertSchmidt (S-T) ≤ operatorHilbertSchmidt (S.comp S-T.comp T) := by
  simpa only [mul_one,show (2:ℝ)*(1/2)=1 by norm_num,one_mul] using
    positive_factor_distance S T hSsym hTsym (1/2)
      (fun x=>by linarith [hS x])
      (fun x=>by linarith [hT x])

/-- A symmetric map within one half of the identity is uniformly positive. -/
theorem quadratic_lower_of_near_identity (S : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hS : ‖S-ContinuousLinearMap.id ℝ (FSC.Coord d)‖ ≤ 1/2) (x : FSC.Coord d) :
    ‖x‖^2/2 ≤ inner ℝ x (S x) := by
  have hh:=abs_real_inner_le_norm x ((S-ContinuousLinearMap.id ℝ (FSC.Coord d)) x)
  have hn:=mul_le_mul_of_nonneg_left
    (((S-ContinuousLinearMap.id ℝ (FSC.Coord d)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hS (norm_nonneg x))) (norm_nonneg x)
  have he : inner ℝ x ((S-ContinuousLinearMap.id ℝ (FSC.Coord d)) x)=
      inner ℝ x (S x)-‖x‖^2 := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he] at hh
  have ha:=abs_le.mp (hh.trans hn)
  nlinarith

/-- The actual near-identity covariance has a positive symmetric invertible
factor with a Frobenius bound, inverse bound and quadratic lower bound. -/
theorem exists_near_factor (C : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hC : C.toLinearMap.IsSymmetric)
    (hsize : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/8) :
    ∃ R : FSC.Coord d≃L[ℝ]FSC.Coord d,
      R.toContinuousLinearMap∈psdCone ∧ R.symm.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=C ∧
      ‖R.symm.toContinuousLinearMap‖ ≤ 2 ∧
      operatorHilbertSchmidt (R.toContinuousLinearMap-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤
        operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ∧
      ∀x,‖x‖^2/2 ≤ inner ℝ x (R x) := by
  let H:=C-ContinuousLinearMap.id ℝ (FSC.Coord d)
  have hH : H.toLinearMap.IsSymmetric:=hC.sub (fun x y=>rfl)
  have hnorm : ‖H‖ ≤ 1/8:=(operator_norm_le_HilbertSchmidt H).trans hsize
  obtain ⟨S,V,hS0,hpsd,hall⟩:=NegativeVotingCovarianceSegment.exists_covariance_segment H hH hnorm
  obtain ⟨hsq,_,_,hclose,R,hR,hRi,_,_⟩:=hall 1 (by norm_num)
  have hRc : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C := by
    rw [hR,hsq]
    dsimp only [H]
    simp only [one_smul]
    abel
  have hRpsd : R.toContinuousLinearMap∈psdCone:=by rw [hR];exact hpsd 1
  have hhs:=psd_sqrt_HilbertSchmidt_distance R.toContinuousLinearMap hRpsd
  rw [hRc] at hhs
  refine ⟨R,hRpsd,NegativeVotingCovarianceSegmentGeometry.symmetric_inverse R hRpsd.1,
    hRc,hRi,hhs,?_⟩
  intro x
  exact quadratic_lower_of_near_identity R.toContinuousLinearMap
    (((operator_norm_le_HilbertSchmidt _).trans hhs).trans (by linarith)) x

end NegativeVotingCovarianceFactorDistance
