import GaussianOrthantTraceCancellation
import GaussianRegularSpectatorRepresentation

/-! Actual Gaussian trace cancellation for a centered linear perturbation.
Permutation symmetry is supplied by `GaussianOrthantTraceCancellation`; all
remaining statements are integral or finite-dimensional operator identities. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingOrthantTraceAlgebra
open NegativeVotingOrthantTraceCancellation NegativeVotingQuadraticBulkNorm
  NegativeVotingQuadraticTensorBulkNorm NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingAffineOperatorDerivative
  NegativeVotingOperatorHS InnerProductSpace
variable {d:ℕ}

def ones (d:ℕ) : FSC.Coord d := WithLp.toLp 2 (fun _=>1)

lemma sum_operatorEntries_eq_zero (F:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hF:F (ones d)=0) : (∑i,∑j,operatorEntries F i j)=0 := by
  have ho:(∑i,EuclideanSpace.basisFun (Fin d) ℝ i)=ones d:=by
    simpa only [EuclideanSpace.basisFun_inner,ones,PiLp.toLp_apply,one_smul]
      using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (ones d)
  have he:(∑i,F (EuclideanSpace.basisFun (Fin d) ℝ i))=0:=by rw [←map_sum,ho,hF]
  have hh (j:Fin d):(∑i,operatorEntries F i j)=0:=by
    have hc:=congrArg (EuclideanSpace.proj (𝕜:=ℝ) j) he
    simp only [map_sum,map_zero] at hc
    exact hc
  rw [Finset.sum_comm]
  simp only [hh,Finset.sum_const_zero]

lemma sum_operatorEntries_diagonal (F:FSC.Coord d→L[ℝ]FSC.Coord d) :
    (∑i,operatorEntries F i i)=LinearMap.trace ℝ (FSC.Coord d) F.toLinearMap := by
  simpa only [EuclideanSpace.inner_basisFun_real,operatorEntries] using basis_trace_sum F

lemma quadraticScore_setIntegral_eq_moments (S:Set (FSC.Coord d))
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) :
    (∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d))=
      ∑i,∑j,operatorEntries F i j*centeredMoment S i j := by
  simp_rw [quadraticScore,quadratic_score_eq_entries]
  rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ
    (fun j _=>(coordinate_quadratic_integrable S i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _=>(coordinate_quadratic_integrable S i j).const_mul _)]
  simp only [integral_const_mul,centeredMoment]

/-- The all-ones kernel cancels the off-diagonal constant, leaving exactly
the trace. No selfadjointness or nondegeneracy is required. -/
theorem quadraticScore_setIntegral_trace (S:Set (FSC.Coord d))
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) (c q:ℝ)
    (hmom:∀i j,centeredMoment S i j=if i=j then c else q)
    (hF:F (ones d)=0) :
    (∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d))=
      LinearMap.trace ℝ (FSC.Coord d) F.toLinearMap*(c-q) := by
  rw [quadraticScore_setIntegral_eq_moments]
  simp_rw [hmom]
  have he (i j:Fin d):operatorEntries F i j*(if i=j then c else q)=
      (if i=j then operatorEntries F i j*(c-q) else 0)+operatorEntries F i j*q:=by
    split_ifs <;>ring
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,←Finset.sum_mul]
  rw [sum_operatorEntries_diagonal,sum_operatorEntries_eq_zero F hF]
  ring

lemma quadraticScore_setIntegral_abs_le (S:Set (FSC.Coord d))
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) :
    |∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d)|≤
      2*operatorHilbertSchmidt F*Real.sqrt ((stdGaussian (FSC.Coord d)).real S) := by
  let μ:=stdGaussian (FSC.Coord d)
  have hf:MemLp (quadraticScore F) 2 μ:=
    (quadraticScore_memLp_four μ F).mono_exponent (by norm_num)
  have hc:=abs_integral_mul_le_sqrt (hf.restrict (s:=S))
    (memLp_const (1:ℝ) : MemLp (fun _ : FSC.Coord d=>(1:ℝ)) 2 (μ.restrict S))
  simp only [mul_one,one_pow,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ] at hc
  have hb:(∫x in S,(quadraticScore F x)^2 ∂μ)≤2*(operatorHilbertSchmidt F)^2:=
    (setIntegral_le_integral hf.integrable_sq (ae_of_all _ fun x=>sq_nonneg _)).trans
      (quadraticScore_integral_sq_le F)
  have hs:Real.sqrt (∫x in S,(quadraticScore F x)^2 ∂μ)≤2*operatorHilbertSchmidt F:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity [operatorHilbertSchmidt_nonneg F],?_⟩
    nlinarith [sq_nonneg (operatorHilbertSchmidt F)]
  exact hc.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))

lemma coordinate_rankOne_score (i j:Fin d) (x:FSC.Coord d) :
    quadraticScore (InnerProductSpace.rankOne ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j)) x=
      x i*x j-(if i=j then 1 else 0) := by
  rw [quadraticScore,InnerProductSpace.trace_rankOne]
  simp only [InnerProductSpace.rankOne_apply,real_inner_smul_right,
    EuclideanSpace.basisFun_inner,EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply,eq_comm]
  ring

lemma centeredMoment_abs_le (S:Set (FSC.Coord d)) (i j:Fin d) :
    |centeredMoment S i j|≤2*Real.sqrt ((stdGaussian (FSC.Coord d)).real S) := by
  have hh:=quadraticScore_setIntegral_abs_le S (InnerProductSpace.rankOne ℝ
    (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j))
  simp_rw [coordinate_rankOne_score] at hh
  rw [operatorHilbertSchmidt_rankOne] at hh
  simpa only [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,one_mul,mul_one,centeredMoment] using hh

theorem centeredMoment_difference_abs_le (S:Set (FSC.Coord d)) (a b:Fin d) :
    |centeredMoment S a a-centeredMoment S a b|≤
      4*Real.sqrt ((stdGaussian (FSC.Coord d)).real S) := by
  exact (abs_sub _ _).trans (by linarith [centeredMoment_abs_le S a a,centeredMoment_abs_le S a b])

/-- Unit physical rows of Id+F force the trace defect to be exactly
minus one half of the squared Hilbert--Schmidt norm. -/
theorem trace_eq_neg_half_HS_sq (F:FSC.Coord d→L[ℝ]FSC.Coord d)
    (hF:F.toLinearMap.IsSymmetric)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1) :
    LinearMap.trace ℝ (FSC.Coord d) F.toLinearMap=-(operatorHilbertSchmidt F)^2/2 := by
  have he (i:Fin d):2*inner ℝ (F (EuclideanSpace.basisFun (Fin d) ℝ i))
      (EuclideanSpace.basisFun (Fin d) ℝ i)+‖F (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=0:=by
    have hh:=hrow i
    rw [map_add,ContinuousLinearMap.adjoint_id,hF.clm_adjoint_eq,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,norm_add_sq_real,
      (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one] at hh
    rw [real_inner_comm] at hh
    nlinarith only [hh]
  have hh:=Finset.sum_eq_zero (fun i (_:i∈(Finset.univ:Finset (Fin d)))=>he i)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,basis_trace_sum,←operatorHilbertSchmidt_sq] at hh
  linarith

lemma centeredMoment_univ (i j:Fin d) : centeredMoment (univ:Set (FSC.Coord d)) i j=0 := by
  have hh:=NegativeVotingRegularSpectatorRepresentation.quadraticCoordinate_integral_zero i j
  change (∫x,(x i*x j-(if i=j then 1 else 0)) ∂NegativeVoting.standardGaussian (Fin d))=0 at hh
  rw [NegativeVoting.integral_standardGaussian_eq_euclidean] at hh
  simpa only [centeredMoment,Measure.restrict_univ] using hh

lemma quadraticScore_integral_zero (F:FSC.Coord d→L[ℝ]FSC.Coord d) :
    (∫x,quadraticScore F x ∂stdGaussian (FSC.Coord d))=0 := by
  have hh:=quadraticScore_setIntegral_eq_moments (univ:Set (FSC.Coord d)) F
  simpa only [Measure.restrict_univ,centeredMoment_univ,mul_zero,Finset.sum_const_zero] using hh

theorem invariant_setIntegral_abs_le (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (a b:Fin d) (hab:a≠b)
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:F (ones d)=0) :
    |∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d)|≤
      4*|LinearMap.trace ℝ (FSC.Coord d) F.toLinearMap| *
        Real.sqrt ((stdGaussian (FSC.Coord d)).real S) := by
  rw [quadraticScore_setIntegral_trace S F (centeredMoment S a a) (centeredMoment S a b)
    (centeredMoment_two_values S hS hinv a b hab) hF,abs_mul]
  exact (mul_le_mul_of_nonneg_left (centeredMoment_difference_abs_le S a b) (abs_nonneg _)).trans_eq
    (by ring)

/-- Actual first-variation size for unit-row centered symmetric transports,
with the smaller event probability retained. -/
theorem invariant_setIntegral_unit_rows_abs_le (S:Set (FSC.Coord d)) (hS:MeasurableSet S)
    (hinv:permutationInvariant S) (a b:Fin d) (hab:a≠b)
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:F.toLinearMap.IsSymmetric)
    (hones:F (ones d)=0)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1) :
    |∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d)|≤
      2*(operatorHilbertSchmidt F)^2*
        Real.sqrt (min ((stdGaussian (FSC.Coord d)).real S) ((stdGaussian (FSC.Coord d)).real Sᶜ)) := by
  have htrace:=trace_eq_neg_half_HS_sq F hF hrow
  have ht:|LinearMap.trace ℝ (FSC.Coord d) F.toLinearMap|=(operatorHilbertSchmidt F)^2/2:=by
    rw [htrace,abs_div,abs_neg,abs_sq]
    norm_num
  have hs:=invariant_setIntegral_abs_le S hS hinv a b hab F hones
  have hc:=invariant_setIntegral_abs_le Sᶜ hS.compl (permutationInvariant_compl S hinv) a b hab F hones
  rw [ht] at hs hc
  have hi:Integrable (quadraticScore F) (stdGaussian (FSC.Coord d)):=
    (quadraticScore_memLp_four _ F).integrable (by norm_num)
  have hsum:=integral_add_compl hS hi
  rw [quadraticScore_integral_zero] at hsum
  have he:(∫x in S,quadraticScore F x ∂stdGaussian (FSC.Coord d))=
      -(∫x in Sᶜ,quadraticScore F x ∂stdGaussian (FSC.Coord d)):=by linarith
  rcases le_total ((stdGaussian (FSC.Coord d)).real S) ((stdGaussian (FSC.Coord d)).real Sᶜ) with h|h
  · rw [min_eq_left h]
    nlinarith only [hs]
  · rw [min_eq_right h,he,abs_neg]
    nlinarith only [hc]

theorem orthant_setIntegral_unit_rows_abs_le (t:ℝ) (a b:Fin d) (hab:a≠b)
    (F:FSC.Coord d→L[ℝ]FSC.Coord d) (hF:F.toLinearMap.IsSymmetric)
    (hones:F (ones d)=0)
    (hrow:∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord d)+F).adjoint
      (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2=1) :
    |∫x in orthant d t,quadraticScore F x ∂stdGaussian (FSC.Coord d)|≤
      2*(operatorHilbertSchmidt F)^2*
        Real.sqrt (min ((stdGaussian (FSC.Coord d)).real (orthant d t))
          ((stdGaussian (FSC.Coord d)).real (orthant d t)ᶜ)) :=
  invariant_setIntegral_unit_rows_abs_le _ (measurableSet_orthant d t)
    (orthant_permutationInvariant d t) a b hab F hF hones hrow

end NegativeVotingOrthantTraceAlgebra
