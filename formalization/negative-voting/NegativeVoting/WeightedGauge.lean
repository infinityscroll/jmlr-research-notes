import Mathlib

/-! Finite-dimensional weighted gauge selection for the covariance argument.
This proves the Hilbert-space minimization step. It does not postulate or prove
the Gaussian stratum factorization to which that step will be applied. -/
noncomputable section
namespace NegativeVoting
open scoped RealInnerProductSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

/-- Every affine gauge class has a representative orthogonal to the gauge
space for the positive definite quadratic form `v ↦ ‖L v‖²`. -/
theorem exists_weighted_orthogonal_gauge (S : Submodule ℝ E)
    (L : E ≃L[ℝ] E) (v : E) :
    ∃ w : E, w - v ∈ S ∧ ∀ z ∈ S, inner ℝ (L w) (L z) = 0 := by
  let U : Submodule ℝ E := S.map L.toLinearEquiv.toLinearMap
  let p : U := U.orthogonalProjectionOnto (L v)
  obtain ⟨a, ha, hpa⟩ := p.property
  refine ⟨v - a, ?_, ?_⟩
  · simpa only [sub_sub_cancel_left] using S.neg_mem ha
  · intro z hz
    have hzU : L z ∈ U := ⟨z, hz, rfl⟩
    have hporth := U.starProjection_inner_eq_zero (L v) (L z) hzU
    change L a = (p : E) at hpa
    rw [map_sub, hpa]
    exact hporth

/-- Weighted gauge selection changes only a boundary-zero vector. The image
of the third boundary need not have a basis of independent generators. -/
theorem exists_weighted_cycle_gauge
    (boundary₂ : E →ₗ[ℝ] F) (boundary₃ : G →ₗ[ℝ] E)
    (hchain : boundary₂.comp boundary₃ = 0)
    (L : E ≃L[ℝ] E) (v : E) :
    ∃ w : E, boundary₂ w = boundary₂ v ∧
      ∀ z : G, inner ℝ (L w) (L (boundary₃ z)) = 0 := by
  obtain ⟨w, hw, horth⟩ := exists_weighted_orthogonal_gauge (LinearMap.range boundary₃) L v
  obtain ⟨a, ha⟩ := hw
  refine ⟨w, ?_, fun z => horth (boundary₃ z) ⟨z, rfl⟩⟩
  have hzero : boundary₂ (w - v) = 0 := by
    rw [← ha]
    exact congrArg (fun f : G →ₗ[ℝ] F => f a) hchain
  simpa only [map_sub, sub_eq_zero] using hzero

end NegativeVoting
