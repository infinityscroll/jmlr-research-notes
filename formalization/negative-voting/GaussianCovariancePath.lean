import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! An actual local Gaussian covariance factor and its first two derivatives.
The square-root path is constructed in a proved orthonormal eigenbasis. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace Topology
open Filter

namespace NegativeVotingCovariancePath
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- The diagonal operator in an actual orthonormal basis. -/
def diagonal (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) : E →L[ℝ] E :=
  ∑ i, a i • InnerProductSpace.rankOne ℝ (e i) (e i)

theorem diagonal_apply (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (x : E) :
    diagonal e a x = ∑ i, (a i * inner ℝ (e i) x) • e i := by
  simp [diagonal, smul_smul]

@[simp] theorem diagonal_basis (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (j : ι) :
    diagonal e a (e j) = a j • e j := by
  simp [diagonal_apply, e.inner_eq_ite]

@[simp] theorem diagonal_one (e : OrthonormalBasis ι ℝ E) :
    diagonal e (fun _ => 1) = ContinuousLinearMap.id ℝ E := by
  simp [diagonal, e.sum_rankOne_eq_id]

theorem diagonal_comp (e : OrthonormalBasis ι ℝ E) (a b : ι → ℝ) :
    (diagonal e a).comp (diagonal e b) = diagonal e (fun i => a i * b i) := by
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  simp [smul_smul, mul_comm]

theorem diagonal_smul (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (c : ℝ) :
    diagonal e (fun i => c * a i) = c • diagonal e a := by
  simp [diagonal, Finset.smul_sum, smul_smul]

theorem diagonal_add (e : OrthonormalBasis ι ℝ E) (a b : ι → ℝ) :
    diagonal e (a + b) = diagonal e a + diagonal e b := by
  simp [diagonal, add_smul, Finset.sum_add_distrib]

/-- Spectral square-root factor for the covariance I+tH. -/
def covarianceFactor (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) (t : ℝ) : E →L[ℝ] E :=
  diagonal e (fun i => Real.sqrt (1 + t * ev i))

def factorDerivative (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) (t : ℝ) : E →L[ℝ] E :=
  diagonal e (fun i => ev i / (2 * Real.sqrt (1 + t * ev i)))

@[simp] theorem covarianceFactor_zero (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) :
    covarianceFactor e ev 0 = ContinuousLinearMap.id ℝ E := by
  simp [covarianceFactor]

theorem factor_square (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) (t : ℝ)
    (ht : ∀ i, 0 ≤ 1 + t * ev i) :
    (covarianceFactor e ev t).comp (covarianceFactor e ev t) =
      ContinuousLinearMap.id ℝ E + t • diagonal e ev := by
  unfold covarianceFactor
  rw [diagonal_comp]
  simp_rw [← sq, Real.sq_sqrt (ht _)]
  have he : (fun i => 1 + t * ev i) = (fun _ => (1 : ℝ)) + (fun i => t * ev i) := rfl
  rw [he, diagonal_add, diagonal_one, diagonal_smul]

theorem eventually_positive_coefficients (ev : ι → ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1 + t * ev i := by
  apply eventually_all.mpr
  intro i
  have hc : ContinuousAt (fun t : ℝ => 1 + t * ev i) 0 := by fun_prop
  exact (continuousAt_const.eventually_lt hc (by norm_num))

theorem hasDerivAt_covarianceFactor (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ)
    (t : ℝ) (ht : ∀ i, 0 < 1 + t * ev i) :
    HasDerivAt (covarianceFactor e ev) (factorDerivative e ev t) t := by
  unfold covarianceFactor factorDerivative diagonal
  apply HasDerivAt.fun_sum
  intro i _
  have h : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y * ev i))
      (ev i / (2 * Real.sqrt (1 + t * ev i))) t := by
    simpa using (((hasDerivAt_id t).mul_const (ev i)).const_add 1).sqrt (ne_of_gt (ht i))
  exact h.smul_const (InnerProductSpace.rankOne ℝ (e i) (e i))

/-- The actual first derivative is H/2, including zero eigenvalues. -/
theorem hasDerivAt_covarianceFactor_zero (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) :
    HasDerivAt (covarianceFactor e ev) ((1/2 : ℝ) • diagonal e ev) 0 := by
  have h := hasDerivAt_covarianceFactor e ev 0 (by intro i; norm_num)
  convert h using 1
  simp only [factorDerivative, zero_mul, add_zero, Real.sqrt_one, mul_one]
  rw [← diagonal_smul]
  congr 1
  funext i
  ring

/-- Derivative of the explicit first derivative at zero. -/
theorem hasDerivAt_factorDerivative_zero (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) :
    HasDerivAt (factorDerivative e ev)
      ((-1/4 : ℝ) • (diagonal e ev).comp (diagonal e ev)) 0 := by
  rw [diagonal_comp, ← diagonal_smul]
  unfold factorDerivative diagonal
  apply HasDerivAt.fun_sum
  intro i _
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t * ev i)) (ev i / 2) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).mul_const (ev i)).const_add 1).sqrt (by norm_num))
  have hd := ((hs.const_mul 2).inv (by norm_num)).const_mul (ev i)
  have hc : HasDerivAt (fun y : ℝ => ev i / (2 * Real.sqrt (1 + y * ev i)))
      ((-1/4 : ℝ) * (ev i * ev i)) 0 := by
    convert hd using 1 <;> simp [div_eq_mul_inv] <;> ring
  exact hc.smul_const (InnerProductSpace.rankOne ℝ (e i) (e i))

/-- The second derivative of the actual factor is -H²/4; it is not a supplied jet. -/
theorem hasDerivAt_deriv_covarianceFactor_zero (e : OrthonormalBasis ι ℝ E) (ev : ι → ℝ) :
    HasDerivAt (fun t => deriv (covarianceFactor e ev) t)
      ((-1/4 : ℝ) • (diagonal e ev).comp (diagonal e ev)) 0 := by
  apply (hasDerivAt_factorDerivative_zero e ev).congr_of_eventuallyEq
  filter_upwards [eventually_positive_coefficients ev] with t ht
  exact (hasDerivAt_covarianceFactor e ev t ht).deriv


theorem inner_diagonal (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (x y : E) :
    inner ℝ (diagonal e a x) y =
      ∑ i, a i * inner ℝ (e i) x * inner ℝ (e i) y := by
  simp [diagonal_apply, sum_inner, inner_smul_left]

theorem diagonal_symmetric (e : OrthonormalBasis ι ℝ E) (a : ι → ℝ) :
    (diagonal e a).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (diagonal e a x) y = inner ℝ x (diagonal e a y)
  calc
    _ = inner ℝ (diagonal e a y) x := by
      rw [inner_diagonal, inner_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := real_inner_comm _ _

theorem covarianceFactor_nonnegative (e : OrthonormalBasis ι ℝ E)
    (ev : ι → ℝ) (t : ℝ) (x : E) :
    0 ≤ inner ℝ (covarianceFactor e ev t x) x := by
  rw [covarianceFactor, inner_diagonal]
  apply Finset.sum_nonneg
  intro i _
  simpa only [pow_two, mul_assoc] using
    mul_nonneg (Real.sqrt_nonneg (1 + t * ev i)) (sq_nonneg (inner ℝ (e i) x))

section Spectral
variable [FiniteDimensional ℝ E]

/-- Every actual symmetric covariance direction has a positive symmetric
factor of I+tH near zero, with the exact first and second derivatives. -/
theorem exists_local_covariance_factor (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) :
    ∃ S : ℝ → E →L[ℝ] E,
      S 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t, (S t).toLinearMap.IsSymmetric) ∧
      (∀ t x, 0 ≤ inner ℝ (S t x) x) ∧
      (∀ᶠ t : ℝ in 𝓝 0, (S t).comp (S t) =
        ContinuousLinearMap.id ℝ E + t • H) ∧
      HasDerivAt S ((1/2 : ℝ) • H) 0 ∧
      HasDerivAt (fun t => deriv S t) ((-1/4 : ℝ) • H.comp H) 0 := by
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
    (fun t => diagonal_symmetric e _), covarianceFactor_nonnegative e ev, ?_, ?_, ?_⟩
  · filter_upwards [eventually_positive_coefficients ev] with t ht
    simpa only [heq] using factor_square e ev t (fun i => (ht i).le)
  · simpa only [heq] using hasDerivAt_covarianceFactor_zero e ev
  · simpa only [heq] using hasDerivAt_deriv_covarianceFactor_zero e ev

end Spectral

end NegativeVotingCovariancePath
