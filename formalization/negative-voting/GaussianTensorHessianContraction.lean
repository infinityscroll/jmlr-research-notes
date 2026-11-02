import GaussianBoundedCoherentLift
import GaussianQuadraticTensorBulkNorm

/-! Exact contraction of the actual centered-cell Hessians into a single
quadratic matrix test. This avoids a dimension-dependent coordinate triangle
inequality in subsequent Hilbert--Schmidt estimates. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingTensorHessianContraction
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanQuarticMoments NegativeVotingFanQuadraticMoments
  NegativeVotingQuadraticAffineTransport NegativeVotingQuadraticBulkDifferential
  NegativeVotingFanMassSecondDerivative NegativeVotingCoherentLiftHessian
  NegativeVotingFanQuadraticTransport NegativeVotingCapTail
  NegativeVotingAffineLogMassBound NegativeVotingQuadraticBulkNorm
  NegativeVotingQuadraticTensorBulkNorm
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance parameterDualNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] ℝ) := inferInstance
local instance parameterDualSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] ℝ) := inferInstance

/-- The coordinate contraction is the literal operator bilinear form. -/
theorem bilinear_entries (U : FSC.Coord d→L[ℝ] FSC.Coord d) (x y : FSC.Coord d) :
    (∑ j,∑ k,operatorEntries U j k*x j*y k)=inner ℝ (U x) y := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hx : (∑ j:Fin d,x j • e j)=x := by
    simpa only [e,EuclideanSpace.basisFun_inner] using e.sum_repr' x
  have hu : (∑ j:Fin d,x j • U (e j))=U x := by
    simpa only [map_sum,map_smul] using congrArg U hx
  have hi (j : Fin d) : inner ℝ (U (e j)) y=∑ k,(U (e j)) k*y k := by
    simp only [PiLp.inner_apply,Real.inner_apply]
  calc
    _ = ∑ j:Fin d,x j*inner ℝ (U (e j)) y := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hi,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change (U (e j)) k*x j*y k=x j*((U (e j)) k*y k)
      ring
    _ = inner ℝ (∑ j:Fin d,x j • U (e j)) y := by
      simp only [sum_inner,real_inner_smul_left]
    _ = inner ℝ (U x) y := by rw [hu]

/-- Exact symmetric matrix contraction of scalar centered transport bulks. -/
theorem tensorBulk_eq_contraction (U A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hU : U.toLinearMap.IsSymmetric) (z x : FSC.Coord d) :
    tensorBulk U A z x=∑ j,∑ k,operatorEntries U j k*
      (affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ k) A z x-
       inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)*
        massBulk A z x) := by
  let w := A x+z
  have he (j k : Fin d) :
      affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ k) A z x-
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)*
        massBulk A z x = tensorTest j k x*massBulk A z x-w j*x k-x j*w k := by
    simp only [affineBulk,massBulk,tensorTest,EuclideanSpace.basisFun_inner,
      (EuclideanSpace.basisFun (Fin d) ℝ).inner_eq_ite]
    dsimp only [w]
    ring
  simp_rw [he,mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  have hq : (∑ j,∑ k,operatorEntries U j k*(tensorTest j k x*massBulk A z x))=
      quadraticScore U x*massBulk A z x := by
    rw [quadraticScore,quadratic_score_eq_entries]
    simp only [Finset.sum_mul,tensorTest,mul_assoc]
  have h1 : (∑ j,∑ k,operatorEntries U j k*(w j*x k))=inner ℝ (U w) x := by
    simpa only [mul_assoc] using bilinear_entries U w x
  have h2 : (∑ j,∑ k,operatorEntries U j k*(x j*w k))=inner ℝ (U x) w := by
    simpa only [mul_assoc] using bilinear_entries U x w
  rw [hq,h1,h2]
  have hs : inner ℝ (U w) x=inner ℝ (U x) w := by
    have hh := hU w x
    change inner ℝ (U w) x=inner ℝ w (U x) at hh
    exact hh.trans (real_inner_comm w (U x)).symm
  rw [hs]
  unfold tensorBulk
  change quadraticScore U x*massBulk A z x-2*inner ℝ (U x) w=
    quadraticScore U x*massBulk A z x-inner ℝ (U x) w-inner ℝ (U x) w
  ring

theorem tensorBulk_growth (U A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hU : U.toLinearMap.IsSymmetric) (z : FSC.Coord d) :
    PolynomialGrowth (tensorBulk U A z) 4 := by
  have hh := PolynomialGrowth.finsetSum Finset.univ
    (fun j:Fin d=>fun x=>∑ k,operatorEntries U j k*
      (affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ k) A z x-
       inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)*
        massBulk A z x)) 4 (fun j _=>
      PolynomialGrowth.finsetSum Finset.univ _ 4 (fun k _=>
        ((affineBulk_growth _ _ A z).sub ((massBulk_growth A z).const_mul _)).const_mul _))
  have he := funext (tensorBulk_eq_contraction U A hU z)
  rw [he]
  exact hh

theorem integral_tensorBulk_contraction (U A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (hU : U.toLinearMap.IsSymmetric) (z : FSC.Coord d) (s : Set (FSC.Coord d)) :
    (∫ x in s,tensorBulk U A z x ∂stdGaussian (FSC.Coord d))=
      ∑ j,∑ k,operatorEntries U j k*
        ((∫ x in s,affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
          (EuclideanSpace.basisFun (Fin d) ℝ k) A z x ∂stdGaussian (FSC.Coord d))-
          inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)*
          ∫ x in s,massBulk A z x ∂stdGaussian (FSC.Coord d)) := by
  have hi (j k : Fin d) : Integrable
      (fun x=>operatorEntries U j k*
        (affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
          (EuclideanSpace.basisFun (Fin d) ℝ k) A z x-
          inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)*
          massBulk A z x)) ((stdGaussian (FSC.Coord d)).restrict s) :=
    ((affineBulk_integrable (stdGaussian (FSC.Coord d))
      (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k) A z).sub
      ((massBulk_integrable (stdGaussian (FSC.Coord d)) A z).const_mul
        (inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)))).const_mul
        (operatorEntries U j k) |>.restrict (s:=s)
  simp_rw [tensorBulk_eq_contraction U A hU z]
  rw [integral_finsetSum Finset.univ (fun j _=>integrable_finsetSum Finset.univ (fun k _=>hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _=>hi j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]
  rw [integral_sub (affineBulk_integrable _ _ _ A z).restrict
    (((massBulk_integrable _ A z).const_mul _).restrict),integral_const_mul]

theorem testedCellDerivative_tensorBulk_contraction (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (U A : FSC.Coord d→L[ℝ] FSC.Coord d) (hU : U.toLinearMap.IsSymmetric) (z : FSC.Coord d) :
    testedCellDerivative B h i (tensorBulk U A z)=
      ∑ j,∑ k,operatorEntries U j k •
        (testedCellDerivative B h i (affineBulk (EuclideanSpace.basisFun (Fin d) ℝ j)
          (EuclideanSpace.basisFun (Fin d) ℝ k) A z)-
          inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k) •
          testedCellDerivative B h i (massBulk A z)) := by
  obtain ⟨C,hC,hF⟩ := (tensorBulk_growth U A hU z).quartic_bound
  have hd := NegativeVotingFanQuarticMoments.hasFDerivAt_testedCell B h σ hσ hlower i _
    (tensorBulk_growth U A hU z).1 C hC hF
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) fun j _=>
    HasFDerivAt.fun_sum (u:=Finset.univ) fun k _=>
      ((hasFDerivAt_affineBulk_testedCell B h σ hσ hlower i
        (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k) A z).sub
        ((hasFDerivAt_massBulk_testedCell B h σ hσ hlower i A z).const_smul
          (inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)))).const_smul
        (operatorEntries U j k)
  apply hd.unique
  apply hs.congr_of_eventuallyEq
  filter_upwards with p
  simpa only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply] using
    integral_tensorBulk_contraction U A hU z (winningCell p.1 p.2 i)

/-- The exact finite contraction of the centered-cell Hessian formula. For a
coherent lift this is the actual Hessian. The right-hand side is one quartic
facet derivative and one bulk correction. -/
theorem centeredHessian_contraction_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι)
    (U : FSC.Coord d→L[ℝ] FSC.Coord d) (hU : U.toLinearMap.IsSymmetric)
    (ε δ : Parameters d ι) :
    (∑ j,∑ k,operatorEntries U j k*
      centeredHessian B h L i (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ k) ε δ)=
      testedCellDerivative B h i (tensorBulk U (velocityMap L δ).1 (velocityMap L δ).2) ε-
      ∫ x in winningCell B h i,
        tensorBulk U ((velocityMap L ε).1.comp (velocityMap L δ).1)
          ((velocityMap L ε).1 (velocityMap L δ).2) x ∂stdGaussian (FSC.Coord d) := by
  rw [testedCellDerivative_tensorBulk_contraction B h σ hσ hlower i U _ hU,
    integral_tensorBulk_contraction U _ hU]
  simp only [centeredHessian,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    sum_apply,smul_eq_mul]
  simp_rw [quadraticHessian_apply B h σ hσ hlower L,
    constantHessian_apply B h σ hσ hlower L,bulkFunctional_apply,massFunctional_apply]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end NegativeVotingTensorHessianContraction
