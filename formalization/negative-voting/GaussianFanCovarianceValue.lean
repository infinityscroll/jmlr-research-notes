import GaussianFanCovarianceLaw
import GaussianFanCovarianceHessian
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! An intrinsic covariance value and its actual derivative on a straight
Gram-matrix line, including covariance matrices of deficient rank. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set Matrix
open scoped BigOperators Topology RealInnerProductSpace MatrixOrder
namespace NegativeVotingFanCovarianceValue
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingFanCovarianceLaw NegativeVotingFanCovarianceEnvelope
  NegativeVotingOptimizedCovariance NegativeVotingCapTail

section General
variable {d e : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Equality of actual dual values follows from the proved Gaussian score law. -/
theorem optimizedValue_eq_of_gram (B : ι → FSC.Coord d) (C : ι → FSC.Coord e)
    (hGram : ∀ i j, inner ℝ (B i) (B j) = inner ℝ (C i) (C j)) (p : ι → ℝ) :
    optimizedValue B p = optimizedValue C p := by
  have he : (fun h : centeredGauge ι => potential B p h) =
      (fun h : centeredGauge ι => potential C p h) :=
    funext (fun h => potential_eq_of_gram B C hGram p h)
  exact congrArg (fun f : centeredGauge ι → ℝ => sInf (Set.range f)) he

end General

variable {m d : ℕ}

/-- Canonical Euclidean rows representing a positive semidefinite Gram matrix. -/
def covarianceRows (G : Matrix (Fin m) (Fin m) ℝ) : Fin m → FSC.Coord m :=
  fun i => WithLp.toLp 2 (fun j => CFC.sqrt G i j)

theorem covarianceRows_gram (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) :
    Matrix.gram ℝ (covarianceRows G) = G := by
  have hsym : (CFC.sqrt G).IsSymm := (CFC.sqrt_nonneg G).isSelfAdjoint.isHermitian.isSymm
  have hsq := CFC.sqrt_mul_sqrt_self G hG.nonneg
  ext i j
  change (∑ k, CFC.sqrt G j k * CFC.sqrt G i k) = G i j
  have he := congrFun (congrFun hsq i) j
  simp only [Matrix.mul_apply] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  rw [hsym.apply j k]
  ring

variable [Nonempty (Fin m)]

def covarianceValue (G : Matrix (Fin m) (Fin m) ℝ) (p : Fin m → ℝ) : ℝ :=
  optimizedValue (covarianceRows G) p

/-- The intrinsic covariance value equals the literal optimized fan value
for every row system, including coincident rows and singular Gram matrices. -/
theorem covarianceValue_gram (B : Fin m → FSC.Coord d) (p : Fin m → ℝ) :
    covarianceValue (Matrix.gram ℝ B) p = optimizedValue B p := by
  apply optimizedValue_eq_of_gram
  intro i j
  exact congrFun (congrFun (covarianceRows_gram (Matrix.gram ℝ B) (Matrix.posSemidef_gram ℝ B)) i) j

open scoped Matrix.Norms.L2Operator in
/-- The canonical representatives vary continuously on the whole PSD cone,
including its rank-deficient boundary. -/
theorem covarianceRows_continuousOn :
    ContinuousOn (covarianceRows (m := m)) {G | G.PosSemidef} := by
  have hs : ContinuousOn (CFC.sqrt : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ)
      {G | G.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (CFC.continuousOn_sqrt (A := Matrix (Fin m) (Fin m) ℝ))
  have he : Continuous (fun A : Matrix (Fin m) (Fin m) ℝ =>
      fun i => WithLp.toLp 2 (fun j => A i j)) := by
    apply continuous_pi
    intro i
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin m => ℝ)).comp (continuous_apply i)
  exact he.comp_continuousOn hs

open scoped Matrix.Norms.L2Operator in
/-- The actual intrinsic value is continuous through covariance rank loss. -/
theorem covarianceValue_continuousOn (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ContinuousOn (fun G => covarianceValue G p) {G | G.PosSemidef} :=
  (optimizedValue_continuous_rows p hp hs).comp_continuousOn covarianceRows_continuousOn

/-- The actual Gram-matrix velocity induced by a symmetric ambient direction. -/
def gramVelocity (B : Fin m → FSC.Coord d) (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => inner ℝ (B i) (H (B j))

theorem covariance_factor_gram (B : Fin m → FSC.Coord d)
    (H S : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ)
    (hS : S.toLinearMap.IsSymmetric)
    (hsquare : S.comp S = ContinuousLinearMap.id ℝ (FSC.Coord d) + t • H) :
    Matrix.gram ℝ (rowsOfOperator B S) = Matrix.gram ℝ B + t • gramVelocity B H := by
  ext i j
  change inner ℝ (S (B i)) (S (B j)) = inner ℝ (B i) (B j) + t * inner ℝ (B i) (H (B j))
  have he := hS (B i) (S (B j))
  change inner ℝ (S (B i)) (S (B j)) = inner ℝ (B i) (S.comp S (B j)) at he
  rw [he,hsquare]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, real_inner_smul_right]

/-- The derived Hessian differentiates the intrinsic value along the exact
linear covariance path. No factorization or mass-preserving path is supplied. -/
theorem exists_intrinsic_covariance_hessian
    (B : Fin m → FSC.Coord d) (p : Fin m → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    ∃ h₀ : centeredGauge (Fin m), mass B h₀ = p ∧
      HasDerivAt (deriv (fun t : ℝ => covarianceValue (Matrix.gram ℝ B + t • gramVelocity B H) p))
        (covarianceHessianValue B h₀ H) 0 := by
  obtain ⟨h₀,hm,S,hS0,hSsym,hSpos,hSsquare,hSsmooth,hd⟩ :=
    exists_optimized_covariance_hessian B p σ hσ hlower hp hs H hH
  have heq : (fun t : ℝ => covarianceValue (Matrix.gram ℝ B + t • gramVelocity B H) p) =ᶠ[𝓝 0]
      (fun t : ℝ => optimizedValue (rowsOfOperator B (S t)) p) := by
    filter_upwards [hSsquare] with t ht
    rw [← covariance_factor_gram B H (S t) t (hSsym t) ht]
    exact covarianceValue_gram _ p
  exact ⟨h₀,hm,hd.congr_of_eventuallyEq heq.deriv⟩

end NegativeVotingFanCovarianceValue
