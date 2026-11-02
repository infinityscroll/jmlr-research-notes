import GaussianCovariancePath

/-! Smoothness of the constructed spectral factor near the identity. -/
noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace NegativeVotingCovariancePath
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem contDiffAt_covarianceFactor (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ)
    (t : ℝ) (ht : ∀ i, 0 < 1 + t * ev i) :
    ContDiffAt ℝ ⊤ (covarianceFactor e ev) t := by
  unfold covarianceFactor diagonal
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).sqrt
    (ne_of_gt (ht i))).smul contDiffAt_const

/-- A smooth actual positive symmetric square-root factor, with its two jets. -/
theorem exists_smooth_local_covariance_factor [FiniteDimensional ℝ E]
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    ∃ S : ℝ → E →L[ℝ] E,
      S 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t, (S t).toLinearMap.IsSymmetric) ∧
      (∀ t x, 0 ≤ inner ℝ (S t x) x) ∧
      (∀ᶠ t : ℝ in 𝓝 0, (S t).comp (S t) =
        ContinuousLinearMap.id ℝ E + t • H) ∧
      HasDerivAt S ((1/2 : ℝ) • H) 0 ∧
      HasDerivAt (deriv S) ((-1/4 : ℝ) • H.comp H) 0 ∧
      ContDiffAt ℝ ⊤ S 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, HasDerivAt S (deriv S t) t) := by
  classical
  let e := hH.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let ev := hH.eigenvalues (n := Module.finrank ℝ E) rfl
  have heq : diagonal e ev = H := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change diagonal e ev (e i) = H (e i)
    rw [diagonal_basis]
    exact (hH.apply_eigenvectorBasis rfl i).symm
  refine ⟨covarianceFactor e ev, covarianceFactor_zero e ev,
    (fun t => diagonal_symmetric e _), covarianceFactor_nonnegative e ev,
    ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_positive_coefficients ev] with t ht
    simpa only [heq] using factor_square e ev t (fun i => (ht i).le)
  · simpa only [heq] using hasDerivAt_covarianceFactor_zero e ev
  · simpa only [heq] using hasDerivAt_deriv_covarianceFactor_zero e ev
  · exact contDiffAt_covarianceFactor e ev 0 (by intro i; norm_num)
  · filter_upwards [eventually_positive_coefficients ev] with t ht
    exact (hasDerivAt_covarianceFactor e ev t ht).differentiableAt.hasDerivAt
end NegativeVotingCovariancePath
