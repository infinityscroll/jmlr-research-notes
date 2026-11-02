import GaussianFanMassSecondDerivative

/-! The Hessian of the actual degree-two Gaussian chaos energy.  Both the
quadratic-cell term and its constant centering correction are differentiated
from transport identities, with no assumed second derivative. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingSecondChaosHessian
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingFanJointMass NegativeVotingFanQuadraticSecondDerivative
  NegativeVotingFanMassSecondDerivative NegativeVotingFanQuadraticMoments
  NegativeVotingQuadraticAffineTransport NegativeVotingCapTail NegativeVotingModern
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance parameterDualNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] ℝ) := inferInstance
local instance parameterDualSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] ℝ) := inferInstance

/-- Linearity of the actual cell derivative for a centered quadratic test. -/
theorem testedCellDerivative_centered_eq (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i : ι) (v y : FSC.Coord d) :
    testedCellDerivative B h i (centeredBilinearTest v y)=
      testedCellDerivative B h i (fun x=>inner ℝ v x*inner ℝ y x)-
        inner ℝ v y • testedCellDerivative B h i (fun _=>1) := by
  have hq := NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B h σ hσ hlower i
    (fun x=>inner ℝ v x*inner ℝ y x) (by fun_prop) (‖v‖*‖y‖) (by positivity)
    (bilinear_growth v y)
  have h1 := NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B h σ hσ hlower i
    (fun _=>1) continuous_const 1 (by norm_num)
    (fun x=>by simp only [abs_one,one_mul]; nlinarith [sq_nonneg ‖x‖])
  have hc := NegativeVotingFanQuadraticMoments.hasFDerivAt_testedCell B h σ hσ hlower i
    (centeredBilinearTest v y) (by unfold centeredBilinearTest; fun_prop)
    (‖v‖*‖y‖) (by positivity) (centeredBilinearTest_growth v y)
  have hd := hq.sub (h1.const_smul (inner ℝ v y))
  have hd' : HasFDerivAt
      (fun p : Parameters d ι=>∫ x in winningCell p.1 p.2 i,centeredBilinearTest v y x
        ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i (fun x=>inner ℝ v x*inner ℝ y x)-
        inner ℝ v y • testedCellDerivative B h i (fun _=>1)) (B,h) := by
    apply hd.congr_of_eventuallyEq
    filter_upwards with p
    have hi : Integrable (fun x=>inner ℝ v x*inner ℝ y x)
        ((stdGaussian (FSC.Coord d)).restrict (winningCell p.1 p.2 i)) :=
      (((IsGaussian.memLp_two_id (μ:=stdGaussian (FSC.Coord d))).const_inner (𝕜:=ℝ) v).integrable_mul
        ((IsGaussian.memLp_two_id (μ:=stdGaussian (FSC.Coord d))).const_inner (𝕜:=ℝ) y)).restrict
    change (∫ x in winningCell p.1 p.2 i,
      (inner ℝ v x*inner ℝ y x-inner ℝ v y) ∂stdGaussian (FSC.Coord d))=_
    rw [integral_sub hi (integrable_const _)]
    simp [integral_const,smul_eq_mul,mul_comm]
  exact hc.unique hd'

/-- The centering correction is the actual mass Hessian. -/
def centeredCellHessian (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ i : ι) (v y : FSC.Coord d) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  bilinearCellHessian B hB h i₀ i v y-inner ℝ v y • massCellHessian B hB h i₀ i

theorem hasFDerivAt_testedCellDerivative_centered (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i (centeredBilinearTest v y))
      (centeredCellHessian B hB h i₀ i v y) (B,h) := by
  dsimp only
  have hd := (hasFDerivAt_testedCellDerivative_bilinear B h σ hσ hlower i₀ i v y).sub
    ((hasFDerivAt_testedCellDerivative_one B h σ hσ hlower i₀ i).const_smul (inner ℝ v y))
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower] with p hp
  exact testedCellDerivative_centered_eq p.1 p.2 (σ/2) (by positivity) hp i v y

def tensorHessian (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ i : ι) (j k : Fin d) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  centeredCellHessian B hB h i₀ i
    (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)

theorem hasFDerivAt_testedCellDerivative_tensor (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (j k : Fin d) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i (tensorTest j k))
      (tensorHessian B hB h i₀ i j k) (B,h) := by
  have he : centeredBilinearTest (EuclideanSpace.basisFun (Fin d) ℝ j)
      (EuclideanSpace.basisFun (Fin d) ℝ k)=tensorTest j k :=
    funext (centeredBilinearTest_basis j k)
  simpa only [tensorHessian,he] using
    hasFDerivAt_testedCellDerivative_centered B h σ hσ hlower i₀ i
      (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k)

/-- Literal finite-sum Hessian of the degree-two chaos energy. -/
def secondEnergyHessian (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ : ι) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  ∑ i,∑ j,∑ k,(secondMomentTensor B h i j k • tensorHessian B hB h i₀ i j k +
    (testedCellDerivative B h i (tensorTest j k)).smulRight
      (testedCellDerivative B h i (tensorTest j k)))

/-- Actual differentiability of the first second-chaos derivative. -/
theorem hasFDerivAt_secondEnergyDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt (fun p:Parameters d ι=>secondEnergyDerivative p.1 p.2)
      (secondEnergyHessian B hB h i₀) (B,h) := by
  have hh := HasFDerivAt.fun_sum (u:=Finset.univ) fun i _=>
    HasFDerivAt.fun_sum (u:=Finset.univ) fun j _=>
      HasFDerivAt.fun_sum (u:=Finset.univ) fun k _=>
        (hasFDerivAt_secondMomentTensor B h σ hσ hlower i j k).smul
          (hasFDerivAt_testedCellDerivative_tensor B h σ hσ hlower i₀ i j k)
  convert! hh using 1

/-- This is the Hessian of the literal Gaussian chaos energy, not just of a
formal surrogate or an assumed derivative field. -/
theorem hasFDerivAt_fderiv_actual_second_chaos (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt
      (fun p:Parameters d ι=>fderiv ℝ (fun q:Parameters d ι=>chaosEnergy
        (fun x:Fin d→ℝ=>weights q.1 q.2 (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2) p)
      (secondEnergyHessian B hB h i₀) (B,h) := by
  apply (hasFDerivAt_secondEnergyDerivative B h σ hσ hlower i₀).congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower] with p hp
  exact (hasFDerivAt_actual_second_chaos p.1 p.2 (σ/2) (by positivity) hp).fderiv

end NegativeVotingSecondChaosHessian
