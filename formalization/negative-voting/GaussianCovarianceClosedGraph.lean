import GaussianCovarianceBoundaryContinuity

/-! The actual covariance optimizer graph is closed while the positive masses
and the nonnegative covariance floor vary, including a zero limiting floor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open Filter Set
open scoped Topology BigOperators NNReal RealInnerProductSpace
namespace NegativeVotingCovarianceBoundary
open NegativeVotingFanMassContinuity NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceCoercivity NegativeVotingCovarianceStrict
variable {m d : ℕ} [NeZero m]

abbrev OptimizerState (m d : ℕ) :=
  ℝ≥0 × (PositiveMassVector (Fin m) × PSDCovariance d)

def regularizedCovariance (ε : ℝ≥0) (D : PSDCovariance d) : PSDCovariance d :=
  ⟨(D : FSC.Coord d→L[ℝ]FSC.Coord d)+(ε:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d),
    regularize_nonnegative (E:=FSC.Coord d) (D : FSC.Coord d→L[ℝ]FSC.Coord d) D.property (ε:ℝ) ε.property⟩

theorem continuous_regularizedCovariance :
    Continuous (fun q : ℝ≥0×PSDCovariance d => regularizedCovariance (d:=d) q.1 q.2) := by
  have hc : Continuous (fun q : ℝ≥0×PSDCovariance d =>
      (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d)+(q.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)) :=
    (continuous_subtype_val.comp continuous_snd).add
      ((NNReal.continuous_coe.comp continuous_fst).smul continuous_const)
  exact hc.subtype_mk (fun q => regularize_nonnegative
    (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d) q.2.property (q.1:ℝ) q.1.property)

def IsOptimizerState (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (s : OptimizerState m d) : Prop :=
  (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone (s.1:ℝ) ∧
  IsMaxOn (penalizedValue b s.2.1) (lowerCovarianceCone (s.1:ℝ))
    (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d)

theorem isOptimizerState_iff (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (s : OptimizerState m d) :
    IsOptimizerState b s ↔
    (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone (s.1:ℝ) ∧
    ∀ D : PSDCovariance d, penalizedValue b s.2.1 (regularizedCovariance (d:=d) s.1 D) ≤
      penalizedValue b s.2.1 s.2.2 := by
  constructor
  · rintro ⟨hf,hm⟩
    refine ⟨hf,fun D => hm ?_⟩
    change (D : FSC.Coord d→L[ℝ]FSC.Coord d)+(s.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)-
      (s.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)∈psdCone
    simpa only [add_sub_cancel_right] using D.property
  · rintro ⟨hf,hm⟩
    refine ⟨hf,?_⟩
    intro D hD
    let E : PSDCovariance d := ⟨D-(s.1:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d),hD⟩
    have hh := hm E
    change penalizedValue b s.2.1 D ≤ penalizedValue b s.2.1 s.2.2
    simpa only [regularizedCovariance,E,sub_add_cancel] using hh

/-- The entire actual optimizer graph is closed; the objective continuity at
singular covariances and the moving feasible cone have both been discharged. -/
theorem isClosed_optimizerState (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    IsClosed {s : OptimizerState m d | IsOptimizerState b s} := by
  have hfeas : IsClosed {s : OptimizerState m d |
      (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone (s.1:ℝ)} := by
    apply psdCone_closed.preimage
    exact (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).sub
      ((NNReal.continuous_coe.comp continuous_fst).smul continuous_const)
  have hcomp (D : PSDCovariance d) : IsClosed {s : OptimizerState m d |
      penalizedValue b s.2.1 (regularizedCovariance (d:=d) s.1 D) ≤ penalizedValue b s.2.1 s.2.2} := by
    have hq : Continuous (fun s : OptimizerState m d =>
        (s.2.1,regularizedCovariance (d:=d) s.1 D)) :=
      (continuous_fst.comp continuous_snd).prodMk
        ((continuous_regularizedCovariance (d:=d)).comp (continuous_fst.prodMk continuous_const))
    have hl := (penalizedValue_continuous_joint_psd b).comp hq
    have hr := (penalizedValue_continuous_joint_psd b).comp
      (show Continuous (Prod.snd : OptimizerState m d → PositiveMassVector (Fin m)×PSDCovariance d) from continuous_snd)
    exact isClosed_le hl hr
  have he : {s : OptimizerState m d | IsOptimizerState b s}=
      {s | (s.2.2 : FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone (s.1:ℝ)} ∩
      ⋂ D : PSDCovariance d, {s | penalizedValue b s.2.1 (regularizedCovariance (d:=d) s.1 D) ≤
        penalizedValue b s.2.1 s.2.2} := by
    ext s
    simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,isOptimizerState_iff]
  rw [he]
  exact hfeas.inter (isClosed_iInter hcomp)

/-- Limits of genuine optimizing states are still optimizing states. -/
theorem optimizerState_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (s : α → OptimizerState m d)
    (s₀ : OptimizerState m d) (hs : Tendsto s l (𝓝 s₀))
    (hmax : ∀ᶠ a in l,IsOptimizerState b (s a)) : IsOptimizerState b s₀ :=
  (isClosed_optimizerState b).mem_of_tendsto hs hmax

theorem lowerCovarianceCone_zero :
    lowerCovarianceCone (E:=FSC.Coord d) (0:ℝ)=psdCone := by
  ext C
  change (C-(0:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)∈psdCone) ↔ C∈psdCone
  have he : C-(0:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)=C := by
    ext x
    simp
  rw [he]

/-- A zero-floor limit is an actual global maximizer over the whole PSD cone. -/
theorem maximizer_limit_at_zero {α : Type*} {l : Filter α} [l.NeBot]
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : α → ℝ≥0) (p : α → PositiveMassVector (Fin m)) (C : α → PSDCovariance d)
    (p₀ : PositiveMassVector (Fin m)) (C₀ : PSDCovariance d)
    (hε : Tendsto ε l (𝓝 0)) (hp : Tendsto p l (𝓝 p₀)) (hC : Tendsto C l (𝓝 C₀))
    (hmax : ∀ᶠ a in l,IsOptimizerState b (ε a,(p a,C a))) :
    IsMaxOn (penalizedValue b p₀) psdCone (C₀ : FSC.Coord d→L[ℝ]FSC.Coord d) := by
  have hh := optimizerState_of_tendsto b (fun a => (ε a,(p a,C a))) (0,(p₀,C₀))
    (hε.prodMk_nhds (hp.prodMk_nhds hC)) hmax
  have hhmax := hh.2
  change IsMaxOn (penalizedValue b p₀) (lowerCovarianceCone (0:ℝ)) (C₀ : FSC.Coord d→L[ℝ]FSC.Coord d) at hhmax
  rw [lowerCovarianceCone_zero] at hhmax
  exact hhmax

end NegativeVotingCovarianceBoundary
