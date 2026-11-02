import GaussianGlobalTensorTransport
import GaussianAdjustedTensorBulkNorm

/-! Literal quartic bulk of the actual mass Hessian along a linear score
transport. Its Gaussian mean vanishes and its L2 bound retains the square of
the transport size, including in tail-event restrictions. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingMassHessianBulk
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanMassSecondDerivative NegativeVotingCoherentLiftHessian
  NegativeVotingGlobalTensorTransport NegativeVotingQuadraticBulkNorm
  NegativeVotingQuadraticTensorBulkNorm NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingCapTail
variable {d : ℕ}

def linearMassBulk (A : FSC.Coord d→L[ℝ] FSC.Coord d) (x : FSC.Coord d) : ℝ :=
  tensorBulk A A 0 x-massBulk (A.comp A) 0 x

lemma massBulk_zero_eq (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    massBulk A 0=quadraticScore A := by
  funext x;simp only [massBulk,quadraticScore,inner_zero_left,add_zero]

lemma linearMassBulk_memLp_two (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    MemLp (linearMassBulk A) 2 (stdGaussian (FSC.Coord d)) :=
  (tensorBulk_memLp_two _ A A 0).sub (NegativeVotingGlobalTensorTransport.massBulk_memLp_two _ (A.comp A) 0)

lemma integral_tensorBulk_zero (U A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hU : U.toLinearMap.IsSymmetric) :
    (∫x,tensorBulk U A 0 x ∂stdGaussian (FSC.Coord d))=0 := by
  let B:Unit→FSC.Coord d:=fun _=>0
  have hlo:CenteredSingularLowerBound B 1:=by
    intro c hc
    simp only [Fintype.sum_unique] at hc ⊢
    simp [hc,B]
  have he:=integral_tensorBulk_eq_derivative B 0 1 (by norm_num) hlo () U A hU 0
  have hcell:winningCell B 0 ()=univ:=by ext x;simp [winningCell,scores,B]
  have hv:affineParameterVelocity B A 0=0:=by ext i <;>simp [affineParameterVelocity,B]
  simpa only [hcell,Measure.restrict_univ,hv,map_zero] using he

lemma integral_massBulk_zero (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (∫x,massBulk A 0 x ∂stdGaussian (FSC.Coord d))=0 := by
  let B:Unit→FSC.Coord d:=fun _=>0
  have hlo:CenteredSingularLowerBound B 1:=by
    intro c hc
    simp only [Fintype.sum_unique] at hc ⊢
    simp [hc,B]
  have he:=testedCellDerivative_one_affineParameters B 0 1 (by norm_num) hlo () A 0
  have hcell:winningCell B 0 ()=univ:=by ext x;simp [winningCell,scores,B]
  have hv:affineParameterVelocity B A 0=0:=by ext i <;>simp [affineParameterVelocity,B]
  simpa only [hcell,Measure.restrict_univ,hv,map_zero] using he.symm

lemma integral_linearMassBulk_zero (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hA : A.toLinearMap.IsSymmetric) :
    (∫x,linearMassBulk A x ∂stdGaussian (FSC.Coord d))=0 := by
  change (∫x,tensorBulk A A 0 x-massBulk (A.comp A) 0 x ∂stdGaussian (FSC.Coord d))=0
  rw [integral_sub ((tensorBulk_memLp_two _ A A 0).integrable (by norm_num))
    (massBulk_integrable _ (A.comp A) 0),integral_tensorBulk_zero A A hA,integral_massBulk_zero,sub_self]

lemma linearMassBulk_integral_sq_le (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (∫x,(linearMassBulk A x)^2 ∂stdGaussian (FSC.Coord d))≤
      20752*(operatorHilbertSchmidt A)^4 := by
  let μ:=stdGaussian (FSC.Coord d)
  have hf:=(tensorBulk_memLp_two μ A A 0).integrable_sq
  have hg:=(NegativeVotingGlobalTensorTransport.massBulk_memLp_two μ (A.comp A) 0).integrable_sq
  have hi:=(linearMassBulk_memLp_two A).integrable_sq
  have hb:=integral_mono hi ((hf.const_mul 2).add (hg.const_mul 2))
    (fun x=>by dsimp only [linearMassBulk,Pi.add_apply];nlinarith only [sq_nonneg (tensorBulk A A 0 x+massBulk (A.comp A) 0 x)])
  simp only [Pi.add_apply] at hb
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2),integral_const_mul,integral_const_mul] at hb
  have ht:=tensorBulk_integral_sq_le A A 0
  have hm:=massBulk_integral_sq_le (A.comp A) 0
  change (∫x,(massBulk (A.comp A) 0 x)^2 ∂μ)≤_ at hm
  simp only [norm_zero,zero_pow (by norm_num : 2≠0),add_zero] at ht hm
  have hc:operatorHilbertSchmidt (A.comp A)≤(operatorHilbertSchmidt A)^2:=by
    exact (operatorHilbertSchmidt_comp_le A A).trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (operator_norm_le_HilbertSchmidt A) (operatorHilbertSchmidt_nonneg A))
  have hc2:=pow_le_pow_left₀ (operatorHilbertSchmidt_nonneg _) hc 2
  nlinarith [hc2]

lemma linearMassBulk_setIntegral_abs_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (S : Set (FSC.Coord d)) :
    |∫x in S,linearMassBulk A x ∂stdGaussian (FSC.Coord d)|≤
      145*(operatorHilbertSchmidt A)^2*Real.sqrt ((stdGaussian (FSC.Coord d)).real S) := by
  let μ:=stdGaussian (FSC.Coord d)
  have hf:=linearMassBulk_memLp_two A
  have hconst:MemLp (fun _ : FSC.Coord d=>(1:ℝ)) 2 (μ.restrict S):=memLp_const 1
  have hc:=abs_integral_mul_le_sqrt (hf.restrict (s:=S)) hconst
  simp only [mul_one,one_pow,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ] at hc
  have hb: (∫x in S,(linearMassBulk A x)^2 ∂μ)≤20752*(operatorHilbertSchmidt A)^4:=
    (setIntegral_le_integral hf.integrable_sq (ae_of_all _ fun x=>sq_nonneg _)).trans
      (linearMassBulk_integral_sq_le A)
  have hs:Real.sqrt (∫x in S,(linearMassBulk A x)^2 ∂μ)≤145*(operatorHilbertSchmidt A)^2:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [pow_nonneg (operatorHilbertSchmidt_nonneg A) 4]
  exact hc.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))

lemma linearMassBulk_setIntegral_abs_le_compl (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hA : A.toLinearMap.IsSymmetric) (S : Set (FSC.Coord d)) (hS : MeasurableSet S) :
    |∫x in S,linearMassBulk A x ∂stdGaussian (FSC.Coord d)|≤
      145*(operatorHilbertSchmidt A)^2*Real.sqrt ((stdGaussian (FSC.Coord d)).real Sᶜ) := by
  have hsum:=integral_add_compl hS ((linearMassBulk_memLp_two A).integrable (by norm_num))
  rw [integral_linearMassBulk_zero A hA] at hsum
  have he:(∫x in S,linearMassBulk A x ∂stdGaussian (FSC.Coord d))=
      -(∫x in Sᶜ,linearMassBulk A x ∂stdGaussian (FSC.Coord d)):=by linarith
  rw [he,abs_neg]
  exact linearMassBulk_setIntegral_abs_le A Sᶜ

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For a coherent lift realizing the literal field A, this is the actual
second derivative supplied by `hasFDerivAt_constantDerivative`. -/
theorem constantHessian_eq_linearMassBulk (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (hA : A.toLinearMap.IsSymmetric)
    (hv : NegativeVotingFanQuadraticTransport.velocityMap L (affineParameterVelocity B A 0)=(A,0)) :
    constantHessian B h L i (affineParameterVelocity B A 0) (affineParameterVelocity B A 0)=
      ∫x in winningCell B h i,linearMassBulk A x ∂stdGaussian (FSC.Coord d) := by
  rw [constantHessian_apply B h σ hσ hlower L,hv]
  simp only [massBulk_zero_eq,Prod.fst,Prod.snd,map_zero]
  rw [←integral_tensorBulk_eq_derivative B h σ hσ hlower i A A hA 0]
  change _=(∫x in winningCell B h i,tensorBulk A A 0 x-massBulk (A.comp A) 0 x ∂stdGaussian (FSC.Coord d))
  rw [integral_sub ((tensorBulk_memLp_two _ A A 0).integrable (by norm_num)).restrict
    (massBulk_integrable _ (A.comp A) 0).restrict]
  rfl

end NegativeVotingMassHessianBulk
