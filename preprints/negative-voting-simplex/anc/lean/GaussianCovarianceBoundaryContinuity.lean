import GaussianFanMassContinuity
import GaussianCovarianceOptimizer

/-! Actual joint continuity through covariance rank loss and nonnegative
regularization. Positive mass vectors are allowed to vary simultaneously. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix.Norms.L2Operator
namespace NegativeVotingCovarianceBoundary
open NegativeVotingFanMassContinuity NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceConcavity NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceCoercivity NegativeVotingCovarianceStrict
variable {m d : ℕ} [NeZero m]

abbrev PSDMatrix (m : ℕ) := {G : Matrix (Fin m) (Fin m) ℝ // G.PosSemidef}
abbrev PSDCovariance (d : ℕ) :=
  {C : FSC.Coord d →L[ℝ] FSC.Coord d // C∈psdCone}

/-- Actual matrix covariance continuity, including singular matrices. -/
theorem covarianceValue_continuous_joint_psd :
    Continuous (fun q : PositiveMassVector (Fin m)×PSDMatrix m => covarianceValue (q.2 : Matrix (Fin m) (Fin m) ℝ) (q.1 : Fin m → ℝ)) := by
  have hr : Continuous (fun G : PSDMatrix m => covarianceRows (G : Matrix (Fin m) (Fin m) ℝ)) :=
    covarianceRows_continuousOn.comp_continuous continuous_subtype_val (fun G => G.property)
  have hq : Continuous (fun q : PositiveMassVector (Fin m)×PSDMatrix m =>
      (covarianceRows (q.2 : Matrix (Fin m) (Fin m) ℝ),q.1)) :=
    (hr.comp continuous_snd).prodMk continuous_fst
  have hh := (optimizedValue_continuous_joint (d:=m) (ι:=Fin m)).comp hq
  simpa only [Function.comp_def,covarianceValue] using hh

def operatorGram (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (C : PSDCovariance d) : PSDMatrix m :=
  ⟨gramVelocity b C,gramVelocity_posSemidef b C C.property⟩

theorem continuous_operatorGram (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    Continuous (operatorGram b) := by
  apply Continuous.subtype_mk
  exact (continuous_gramVelocity b).comp continuous_subtype_val

/-- The literal optimized value is jointly continuous in positive masses and
all positive semidefinite operators, including rank-deficient operators. -/
theorem operatorValue_continuous_joint_psd (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    Continuous (fun q : PositiveMassVector (Fin m)×PSDCovariance d => operatorValue b q.1 q.2) := by
  have hq : Continuous (fun q : PositiveMassVector (Fin m)×PSDCovariance d =>
      (q.1,operatorGram b q.2)) :=
    continuous_fst.prodMk ((continuous_operatorGram b).comp continuous_snd)
  have hh := (covarianceValue_continuous_joint_psd (m:=m)).comp hq
  simpa only [Function.comp_def,operatorValue,operatorGram] using hh

theorem penalizedValue_continuous_joint_psd (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    Continuous (fun q : PositiveMassVector (Fin m)×PSDCovariance d => penalizedValue b q.1 q.2) := by
  change Continuous (fun q : PositiveMassVector (Fin m)×PSDCovariance d =>
    2*operatorValue b q.1 q.2-operatorTrace (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d))
  exact ((operatorValue_continuous_joint_psd b).const_mul 2).sub
    (continuous_operatorTrace.comp (continuous_subtype_val.comp continuous_snd))

/-- Nonnegative regularization remains in the actual semidefinite cone. -/
theorem regularize_nonnegative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C : E→L[ℝ]E) (hC : C∈psdCone) (ε : ℝ) (hε : 0 ≤ ε) :
    C+ε•ContinuousLinearMap.id ℝ E ∈ psdCone := by
  refine ⟨hC.1.add (LinearMap.IsSymmetric.smul (by rfl) (fun x y => rfl)),fun x => ?_⟩
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,inner_add_right,real_inner_smul_right]
  exact add_nonneg (hC.2 x) (mul_nonneg hε (real_inner_self_nonneg))

theorem lowerCovarianceCone_subset_psd {ε : ℝ} (hε : 0 ≤ ε) :
    lowerCovarianceCone (E:=FSC.Coord d) ε ⊆ psdCone := by
  intro C hC
  have hh := regularize_nonnegative (C-ε•ContinuousLinearMap.id ℝ (FSC.Coord d)) hC ε hε
  simpa only [sub_add_cancel] using hh

end NegativeVotingCovarianceBoundary
