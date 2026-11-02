import GaussianCovarianceClosedGraph
import GaussianCovarianceRealization

/-! Passing bounds for the actual positive-floor covariance optimizers to every
semidefinite covariance and every feasible Gaussian assignment. The proof uses
objective continuity under C + εI, with no optimizer-convergence premise. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology BigOperators NNReal RealInnerProductSpace

namespace NegativeVotingCovarianceZeroFloorBound
open NegativeVotingCovarianceBoundary NegativeVotingFanMassContinuity
  NegativeVotingCovarianceOptimizer NegativeVotingPositiveCovariance
  NegativeVotingCovarianceStrict NegativeVotingCovarianceRealization
  NegativeVotingAssignmentDuality NegativeVotingCentroidOptimization

variable {m d e : ℕ} [NeZero m]

theorem covariance_bound_of_small_floors
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (B δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ C : FSC.Coord d →L[ℝ] FSC.Coord d, C ∈ lowerCovarianceCone ε →
      IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C →
      penalizedValue b p C ≤ B)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C ∈ psdCone) :
    penalizedValue b p C ≤ B := by
  let pp : PositiveMassVector (Fin m) := ⟨p, hp, hs⟩
  let D : PSDCovariance d := ⟨C, hC⟩
  have hc : Continuous (fun ε : ℝ≥0 => penalizedValue b p (regularizedCovariance ε D)) := by
    have hq : Continuous (fun ε : ℝ≥0 => (pp, regularizedCovariance ε D)) :=
      continuous_const.prodMk ((continuous_regularizedCovariance (d:=d)).comp
        (continuous_id.prodMk continuous_const))
    have hh := (penalizedValue_continuous_joint_psd b).comp hq
    simpa only [Function.comp_def, pp] using hh
  have hlim : Tendsto (fun ε : ℝ≥0 => penalizedValue b p (regularizedCovariance ε D))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (penalizedValue b p C)) := by
    have hh : Tendsto (fun ε : ℝ≥0 => penalizedValue b p (regularizedCovariance ε D))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (penalizedValue b p (regularizedCovariance 0 D))) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hz : (regularizedCovariance 0 D : FSC.Coord d →L[ℝ] FSC.Coord d) = C := by
      change C + (0 : ℝ) • ContinuousLinearMap.id ℝ (FSC.Coord d) = C
      ext x
      simp
    simpa only [hz] using hh
  have hsmall : {ε : ℝ≥0 | (ε : ℝ) < δ} ∈ 𝓝 (0 : ℝ≥0) :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hδ
  apply le_of_tendsto hlim
  filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with ε hεδ hε
  have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨A, hA, hmax⟩ := exists_penalized_maximizer b p (fun i => (hp i).le) hs hεr
  have hD : (regularizedCovariance ε D : FSC.Coord d →L[ℝ] FSC.Coord d) ∈
      lowerCovarianceCone (ε : ℝ) := by
    change C + (ε : ℝ) • ContinuousLinearMap.id ℝ (FSC.Coord d) -
      (ε : ℝ) • ContinuousLinearMap.id ℝ (FSC.Coord d) ∈ psdCone
    simpa only [add_sub_cancel_right] using hC
  exact (hmax hD).trans (hbound ε hεr hεδ A hA.1 hmax)

/-- The bound transfers through the literal centroid covariance of every
feasible rule, in any finite Gaussian ambient dimension. -/
theorem centroidEnergy_bound_of_small_floors
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j, inner ℝ (b i) (b j) = (if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i) = x)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (B δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ C : FSC.Coord d →L[ℝ] FSC.Coord d, C ∈ lowerCovarianceCone ε →
      IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C →
      penalizedValue b p C ≤ B)
    (f : FSC.Coord e → Fin m → ℝ) (hf : Feasible p f) :
    centroidEnergy f ≤ B := by
  calc
    _ ≤ rowObjective (centroidRows f) p := centroidEnergy_le_rowObjective p f hf
    _ = penalizedValue b p (rowCovariance b (centroidRows f)) :=
      (rowCovariance_objective b hG hP _ (centroidRows_sum_zero p f hf) p).symm
    _ ≤ B := covariance_bound_of_small_floors b p hp hs B δ hδ hbound _
      (rowCovariance_psd _ _)

end NegativeVotingCovarianceZeroFloorBound
