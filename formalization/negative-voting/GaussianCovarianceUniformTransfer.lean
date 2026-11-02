import GaussianCovarianceUniformCompact

/-! Uniform transfer from the entire zero-floor optimizer graph. This uses
its actual closedness and the derived common compact covariance region; no
selection or continuous family of zero-floor maximizers is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Filter Set
open scoped Topology BigOperators NNReal RealInnerProductSpace
namespace NegativeVotingCovarianceBoundary
open NegativeVotingFanMassContinuity NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceCoercivity NegativeVotingCovarianceStrict
variable {m d : ℕ} [NeZero m]

/-- Every open neighborhood of all zero-floor maximizers over a compact set
of positive masses contains every sufficiently small-floor maximizer uniformly.
The covariance compactness and the moving-floor closed graph are proved inputs. -/
theorem uniform_optimizer_transfer_at_zero
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (K : Set (PositiveMassVector (Fin m))) (hK : IsCompact K)
    (U : Set (PositiveMassVector (Fin m)×PSDCovariance d)) (hU : IsOpen U)
    (hzero : ∀ p∈K,∀ C : PSDCovariance d,IsOptimizerState b (0,(p,C)) → (p,C)∈U) :
    ∃ δ : ℝ,0 < δ ∧ ∀ ε : ℝ≥0,(ε:ℝ) < δ →
      ∀ p∈K,∀ C : PSDCovariance d,IsOptimizerState b (ε,(p,C)) → (p,C)∈U := by
  let T := K×compactCovarianceSet b
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace (compactCovarianceSet b) :=
    isCompact_iff_compactSpace.mp (compactCovarianceSet_compact b)
  let state (q : ℝ≥0×T) : OptimizerState m d :=
    (q.1,((q.2.1 : PositiveMassVector (Fin m)),(q.2.2 : PSDCovariance d)))
  have hstate : Continuous state :=
    continuous_fst.prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
       (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  let bad : Set (ℝ≥0×T) := {q | IsOptimizerState b (state q) ∧ (state q).2∉U}
  have hbad : IsClosed bad :=
    ((isClosed_optimizerState b).preimage hstate).inter
      (hU.isClosed_compl.preimage (continuous_snd.comp hstate))
  let A : Set ℝ≥0 := Prod.fst '' bad
  have hA : IsClosed A := isClosedMap_fst_of_compactSpace bad hbad
  have h0 : (0:ℝ≥0)∉A := by
    rintro ⟨q,⟨hq,hnot⟩,heq⟩
    have hz : IsOptimizerState b (0,((q.2.1 : PositiveMassVector (Fin m)),(q.2.2 : PSDCovariance d))) := by
      simpa only [state,heq] using hq
    exact hnot (hzero q.2.1 q.2.1.property q.2.2 hz)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hA.isOpen_compl.mem_nhds h0)
  refine ⟨min r 1,lt_min hr zero_lt_one,?_⟩
  intro ε hε p hp C hmax
  have hε1 : ε ≤ 1 := by exact_mod_cast (hε.trans_le (min_le_right r 1)).le
  have hC : C∈compactCovarianceSet b := optimizerState_mem_common_compact b (ε,(p,C)) hε1 hmax
  have hεr : ε∈Metric.ball 0 r := by
    have hh := hε.trans_le (min_le_left r 1)
    simpa [Metric.mem_ball,NNReal.dist_eq] using hh
  have havoid : ε∉A := hball hεr
  by_contra hnot
  apply havoid
  refine ⟨(ε,(⟨p,hp⟩,⟨C,hC⟩)),?_,rfl⟩
  exact ⟨hmax,hnot⟩

end NegativeVotingCovarianceBoundary
