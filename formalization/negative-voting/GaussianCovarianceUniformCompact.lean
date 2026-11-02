import GaussianCovarianceClosedGraph

/-! A derived common compact region for all actual covariance optimizers with
floor between zero and one, uniformly over every positive probability vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Filter Set
open scoped Topology BigOperators NNReal RealInnerProductSpace
namespace NegativeVotingCovarianceBoundary
open NegativeVotingFanMassContinuity NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceCoercivity
  NegativeVotingCovarianceStrict NegativeVotingCovarianceConcavity
variable {m d : ℕ} [NeZero m]

/-- The proved coercive objective estimate extends to every singular PSD
operator by its actual Gaussian regularization limit. -/
theorem penalizedValue_le_trace_cutoff_psd
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0 ≤ p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈psdCone) :
    penalizedValue b p C ≤ 2*‖(b : Fin m→FSC.Coord d)‖^2-(1/2:ℝ)*operatorTrace C := by
  have hline : Tendsto (fun ε : ℝ => C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))
      (𝓝[>] 0) (𝓝 C) := by
    have hc : Continuous (fun ε : ℝ => C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d)) := by fun_prop
    have hh := (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ)) ≤ 𝓝 0)
    have hz : C+(0:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)=C := by ext x; simp
    rw [hz] at hh
    exact hh
  have ht := continuous_operatorTrace.continuousAt.tendsto.comp hline
  have hg := operatorValue_regularization_tendsto b p hp hs C hC
  change 2*operatorValue b p C-operatorTrace C ≤ _
  apply le_of_tendsto_of_tendsto ((hg.const_mul 2).sub ht)
    (tendsto_const_nhds.sub (ht.const_mul (1/2:ℝ)))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact penalizedValue_le_trace_cutoff b p hp hs _ (regularize_positive hC hε)

theorem identity_psd : ContinuousLinearMap.id ℝ (FSC.Coord d)∈psdCone :=
  ⟨fun x y => rfl,fun x => real_inner_self_nonneg⟩

theorem operatorTrace_smul_identity (ε : ℝ) :
    operatorTrace (ε•ContinuousLinearMap.id ℝ (FSC.Coord d))=
      ε*operatorTrace (ContinuousLinearMap.id ℝ (FSC.Coord d)) := by
  change LinearMap.trace ℝ (FSC.Coord d)
    (ε•(ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap)=_
  rw [map_smul]
  rfl

def commonOptimizerCutoff (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) : ℝ :=
  4*‖(b : Fin m→FSC.Coord d)‖^2+
    2*operatorTrace (ContinuousLinearMap.id ℝ (FSC.Coord d))+2

def commonOptimizerRegion (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    Set (FSC.Coord d→L[ℝ]FSC.Coord d) :=
  {C | C∈psdCone ∧ operatorTrace C ≤ commonOptimizerCutoff b}

def compactCovarianceSet (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) : Set (PSDCovariance d) :=
  {C | operatorTrace (C : FSC.Coord d→L[ℝ]FSC.Coord d) ≤ commonOptimizerCutoff b}

theorem commonOptimizerRegion_compact (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    IsCompact (commonOptimizerRegion b) := by
  have hc : IsClosed (commonOptimizerRegion b) :=
    psdCone_closed.inter (isClosed_le continuous_operatorTrace continuous_const)
  apply (isCompact_closedBall (0 : FSC.Coord d→L[ℝ]FSC.Coord d)
    (commonOptimizerCutoff b)).of_isClosed_subset hc
  intro C hC
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (norm_le_trace hC.1).trans hC.2

theorem compactCovarianceSet_compact (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    IsCompact (compactCovarianceSet b) := by
  apply Subtype.isCompact_iff.mpr
  have he : ((↑) '' compactCovarianceSet b : Set (FSC.Coord d→L[ℝ]FSC.Coord d))=
      commonOptimizerRegion b := by
    ext C
    constructor
    · rintro ⟨D,hD,rfl⟩
      exact ⟨D.property,hD⟩
    · intro hC
      exact ⟨⟨C,hC.1⟩,hC.2,rfl⟩
  rw [he]
  exact commonOptimizerRegion_compact b

/-- All actual optimizing states with 0≤ε≤1 lie in the same derived compact
covariance set. The cutoff is independent of the positive mass vector. -/
theorem optimizerState_mem_common_compact
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (s : OptimizerState m d)
    (hε : s.1 ≤ 1) (hmax : IsOptimizerState b s) : s.2.2∈compactCovarianceSet b := by
  have hc := penalizedValue_le_trace_cutoff_psd b s.2.1
    (fun i => (s.2.1.property.1 i).le) s.2.1.property.2 s.2.2 s.2.2.property
  have hb := penalizedValue_ge_neg_trace b s.2.1
    (fun i => (s.2.1.property.1 i).le) s.2.1.property.2
    ((s.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d))
  have hm := hmax.2 (identity_mem_lowerCovarianceCone (s.1:ℝ))
  change penalizedValue b s.2.1 ((s.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ penalizedValue b s.2.1 s.2.2 at hm
  have hi : 0 ≤ operatorTrace (ContinuousLinearMap.id ℝ (FSC.Coord d)) := trace_nonneg identity_psd
  have he : (s.1:ℝ) ≤ 1 := by exact_mod_cast hε
  rw [operatorTrace_smul_identity] at hb
  change operatorTrace (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d) ≤ commonOptimizerCutoff b
  unfold commonOptimizerCutoff
  nlinarith

end NegativeVotingCovarianceBoundary
