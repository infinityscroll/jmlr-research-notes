import GaussianCheegerRampAdapter
import GaussianL1Variance

/-! A concrete dimension-free Gaussian Cheeger inequality. The globally
Lipschitz variance premise in the attributed KLS ramp conversion is discharged
by the actual Gaussian rotation theorem, not assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace NegativeVotingGaussianCheeger
variable {n : ℕ}

/-- Actual Gaussian outer Minkowski boundary dominates the smaller side of a
measurable set, with the nonsharp universal Cheeger constant 1/π. -/
theorem gaussian_open_boundary_lower (A : Set (KLS.Space n)) (hA : MeasurableSet A) :
    min (stdGaussian (KLS.Space n) A) (1-stdGaussian (KLS.Space n) A) /
      ENNReal.ofReal Real.pi ≤ KLS.openBoundaryMeasure (stdGaussian (KLS.Space n)) A := by
  have h := NegativeVotingCheegerAdapter.boundedVariance_min_div_le_openBoundaryMeasure
    (μ := stdGaussian (KLS.Space n)) (K := Real.pi/2) (by positivity)
    (fun f hf _ B hB hb => by
      obtain ⟨L,hL⟩ := hf
      exact NegativeVotingGaussianL1.gaussian_bounded_lipschitz_variance hL B hB hb) hA
  simpa only [show 2*(Real.pi/2)=Real.pi by ring] using h

theorem gaussian_open_cheeger_lower :
    ENNReal.ofReal (Real.pi⁻¹) ≤ KLS.openCheegerConstant (stdGaussian (KLS.Space n)) := by
  have h := NegativeVotingCheegerAdapter.boundedVariance_inv_le_openCheegerConstant
    (μ := stdGaussian (KLS.Space n)) (K := Real.pi/2) (by positivity)
    (fun f hf _ B hB hb => by
      obtain ⟨L,hL⟩ := hf
      exact NegativeVotingGaussianL1.gaussian_bounded_lipschitz_variance hL B hB hb)
  simpa only [show 2*(Real.pi/2)=Real.pi by ring] using h

theorem gaussian_cheeger_lower :
    ENNReal.ofReal (Real.pi⁻¹) ≤ KLS.cheegerConstant (stdGaussian (KLS.Space n)) :=
  KLS.le_cheegerConstant_of_le_openCheegerConstant _ gaussian_open_cheeger_lower

end NegativeVotingGaussianCheeger
