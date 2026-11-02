import GaussianFanSecondVariation
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The actual expected-max gradient is Frechet differentiable as a continuous
linear functional, not just after evaluation in one fixed direction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory

namespace NegativeVotingFanGradient
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

abbrev P (d : ℕ) (ι : Type*) := Parameters d ι

private def parameterBasis (d : ℕ) (ι : Type*) [Fintype ι] :=
  Module.finBasis ℝ (P d ι)

private def dualCoord (j : Fin (Module.finrank ℝ (P d ι))) : P d ι →L[ℝ] ℝ :=
  ((parameterBasis d ι).coord j).toContinuousLinearMap

private theorem dual_reconstruction (L : P d ι →L[ℝ] ℝ) :
    L = ∑ j, L (parameterBasis d ι j) • dualCoord j := by
  apply ContinuousLinearMap.coe_injective
  apply (parameterBasis d ι).ext
  intro j
  simp [dualCoord, Finsupp.single_apply]

/-- A concrete continuous bilinear Hessian, reconstructed in a finite basis. -/
def jointHessian (B : ι → FSC.Coord d) (h : ι → ℝ) :
    P d ι →L[ℝ] P d ι →L[ℝ] ℝ :=
  ∑ j, (secondDerivative B h (parameterBasis d ι j).1 (parameterBasis d ι j).2).smulRight
    (dualCoord j)

/-- All tested-cell derivatives determine the actual operator-valued gradient derivative. -/
theorem hasFDerivAt_jointGradient (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt (fun p : P d ι => jointDerivative p.1 p.2) (jointHessian B h) (B,h) := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasFDerivAt_jointDerivative_apply B h σ hσ hlower
      (parameterBasis d ι j).1 (parameterBasis d ι j).2).smul_const (dualCoord j)
  change HasFDerivAt
    (fun p : P d ι => ∑ j, jointDerivative p.1 p.2 (parameterBasis d ι j) • dualCoord j)
    (jointHessian B h) (B,h) at hs
  simpa only [← dual_reconstruction] using hs

/-- The actual bilinear derivative is exactly the derived Gaussian facet form. -/
theorem jointHessian_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (u v : P d ι) :
    jointHessian B h u v = mixedForm B h u.1 u.2 v.1 v.2 := by
  let ev : (P d ι →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hd := ev.hasFDerivAt.comp (B,h) (hasFDerivAt_jointGradient B h σ hσ hlower)
  have he := hasFDerivAt_jointDerivative_apply B h σ hσ hlower v.1 v.2
  have hid : ev.comp (jointHessian B h) = secondDerivative B h v.1 v.2 :=
    hd.unique he
  have ha := congrArg (fun L : P d ι →L[ℝ] ℝ => L u) hid
  exact ha.trans (secondDerivative_apply_eq_mixedForm B u.1 v.1 h u.2 v.2 σ hσ hlower)

theorem jointHessian_symmetric (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (u v : P d ι) : jointHessian B h u v = jointHessian B h v u := by
  rw [jointHessian_apply B h σ hσ hlower, jointHessian_apply B h σ hσ hlower]
  exact mixedForm_symm B u.1 v.1 h u.2 v.2

end NegativeVotingFanGradient
