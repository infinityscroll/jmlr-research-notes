import WeakSimplexConjectureLean.Orthant.Singular

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NegativeVotingDependencies

/-- Independent restatement of the exact external comparison used by the
manuscript. Covariance, diagonal, rank-one domination and the event are explicit. -/
theorem equalThreshold_gaussian_comparison {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (hrank : (R - (Matrix.of (fun (_ _ : Fin m) => (1 : ℝ) / (m : ℝ)))).PosSemidef) (t : ℝ) :
    (gaussianReal 0 1) (Set.Iic t) ^ m ≤
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R {x | ∀ i, x i ≤ t} := by
  have hcov : WeakSimplex.IsWeakSimplexCov R := by
    refine ⟨⟨hR, hdiag⟩, ?_⟩
    have hmat : (1 / (m : ℝ)) • WeakSimplex.allOnesMatrix m =
        Matrix.of (fun (_ _ : Fin m) => (1 : ℝ) / (m : ℝ)) := by
      ext i j
      simp [WeakSimplex.allOnesMatrix]
    rw [hmat]
    exact hrank
  exact WeakSimplex.lowerOrthant_ge_iid hm R hcov t

end NegativeVotingDependencies

