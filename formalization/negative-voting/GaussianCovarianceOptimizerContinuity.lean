import GaussianCovarianceOptimizer
import GaussianLocalCovarianceFactor
import GaussianCovarianceJointValue

/-! Continuity of the actual unique covariance optimizer. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingCovarianceOptimizerContinuity
open NegativeVotingCovarianceOptimizer NegativeVotingCovarianceStrict
  NegativeVotingPositiveCovariance NegativeVotingCovarianceCoercivity
  NegativeVotingLocalCovarianceFactor NegativeVotingCovarianceJointValue
  NegativeVotingCovarianceConcavity NegativeVotingFanInverse

/-- A compact-target closed-graph proof of the unique-optimizer continuity principle. -/
theorem continuous_unique_maximizer {P K : Type*} [TopologicalSpace P] [TopologicalSpace K]
    [CompactSpace K] (F : P×K→ℝ) (hF : Continuous F) (a : P→K)
    (hmax : ∀ p k,F (p,k)≤F (p,a p))
    (hunique : ∀ p k,(∀ z,F (p,z)≤F (p,k))→k=a p) : Continuous a := by
  apply continuous_of_isClosed_graph
  have he : a.graph=⋂ z:K,{q:P×K | F (q.1,z)≤F q} := by
    ext q
    simp only [Function.graph,mem_setOf_eq,mem_iInter]
    constructor
    · intro hh z
      change F (q.1,z)≤F (q.1,q.2)
      rw [←hh]
      exact hmax q.1 z
    · intro hh
      exact (hunique q.1 q.2 hh).symm
  rw [he]
  exact isClosed_iInter (fun z=>isClosed_le
    (hF.comp (continuous_fst.prodMk continuous_const)) hF)

abbrev PositiveProbability (m : ℕ) :=
  {p : Fin m→ℝ // (∀ i,0<p i) ∧ ∑ i,p i=1}

variable {m d : ℕ} [NeZero m]

def selectedCovariance (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0<ε) (p : PositiveProbability m) : optimizerRegion b ε :=
  ⟨(exists_penalized_maximizer b p (fun i=>(p.property.1 i).le) p.property.2 hε).choose,
   (exists_penalized_maximizer b p (fun i=>(p.property.1 i).le) p.property.2 hε).choose_spec.1⟩

theorem selectedCovariance_isMaxOn (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0<ε) (p : PositiveProbability m) :
    IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) (selectedCovariance b ε hε p) :=
  (exists_penalized_maximizer b p (fun i=>(p.property.1 i).le) p.property.2 hε).choose_spec.2

theorem selectedCovariance_unique_on_region (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0<ε) (p : PositiveProbability m) (C : optimizerRegion b ε)
    (hmax : ∀ D:optimizerRegion b ε,penalizedValue b p D≤penalizedValue b p C) :
    C=selectedCovariance b ε hε p := by
  have hglobal : IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) (C : FSC.Coord d→L[ℝ]FSC.Coord d) := by
    intro D hD
    by_cases hd : D∈optimizerRegion b ε
    · exact hmax ⟨D,hd⟩
    · exact (outside_region_objective_lt_reference b p (fun i=>(p.property.1 i).le)
        p.property.2 hε D hD hd).le.trans (hmax ⟨_,identity_mem_optimizerRegion b hε⟩)
  apply Subtype.ext
  exact ((penalizedValue_strictConcaveOn_positive b p p.property.1 p.property.2).subset
    (lowerCovarianceCone_subset_pd hε) (lowerCovarianceCone_convex ε)).eq_of_isMaxOn
      hglobal (selectedCovariance_isMaxOn b ε hε p) C.property.1
      (selectedCovariance b ε hε p).property.1

theorem selectedCovariance_continuous_of_joint_value
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε)
    (hjoint : Continuous (fun q : PositiveProbability m×optimizerRegion b ε =>
      penalizedValue b q.1 q.2)) : Continuous (selectedCovariance b ε hε) := by
  letI : CompactSpace (optimizerRegion b ε) :=
    isCompact_iff_compactSpace.mp (optimizerRegion_compact b hε)
  exact continuous_unique_maximizer _ hjoint _
    (fun p C=>selectedCovariance_isMaxOn b ε hε p C.property.1)
    (fun p C hh=>selectedCovariance_unique_on_region b ε hε p C hh)


abbrev PositiveCovariance (d : ℕ) :=
  {C : SymmetricOperators (FSC.Coord d) // (C : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone}

/-- Literal joint continuity follows from the proved full covariance/mass C1 chart. -/
theorem operatorValue_continuous_joint_positive
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) :
    Continuous (fun q : PositiveProbability m×PositiveCovariance d =>
      operatorValue b q.1 (q.2.1 : FSC.Coord d→L[ℝ]FSC.Coord d)) := by
  apply continuous_iff_continuousAt.2
  intro q₀
  let p₀ : Fin m→ℝ:=q₀.1
  let C₀ : SymmetricOperators (FSC.Coord d):=q₀.2.1
  let v : PositiveProbability m→centeredGauge (Fin m):=fun p=>
    ⟨(p : Fin m→ℝ)-p₀,by
      change ∑ i,((p : Fin m→ℝ) i-p₀ i)=0
      rw [Finset.sum_sub_distrib,p.property.2,q₀.1.property.2,sub_self]⟩
  have hv : Continuous v := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const
  let Q : PositiveProbability m×PositiveCovariance d→
      SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m):=fun q=>(q.2.1,v q.1)
  have hQ : Continuous Q:=
    (continuous_subtype_val.comp continuous_snd).prodMk (hv.comp continuous_fst)
  have hQ₀ : Q q₀=(C₀,0) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact sub_self _
  have hbase := (operatorValue_joint_C1 b p₀ q₀.1.property.1 q₀.1.property.2 C₀ q₀.2.property).continuousAt
  have hc : ContinuousAt (fun q : PositiveProbability m×PositiveCovariance d=>
      operatorValue b (p₀+((Q q).2 : Fin m→ℝ)) ((Q q).1 : FSC.Coord d→L[ℝ]FSC.Coord d)) q₀ := by
    have hh : ContinuousAt (fun q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)=>
        operatorValue b (p₀+(q.2 : Fin m→ℝ)) (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)) (Q q₀) := by
      rw [hQ₀]
      exact hbase
    exact hh.comp hQ.continuousAt
  change ContinuousAt (fun q : PositiveProbability m×PositiveCovariance d=>
      operatorValue b (p₀+((q.1 : Fin m→ℝ)-p₀)) (q.2.1 : FSC.Coord d→L[ℝ]FSC.Coord d)) q₀ at hc
  have he (p : Fin m→ℝ) : p₀+(p-p₀)=p := by abel
  simpa only [he] using hc

def regionPositiveCovariance
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε)
    (C : optimizerRegion b ε) : PositiveCovariance d :=
  ⟨⟨C,ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (lowerCovarianceCone_subset_pd hε C.property.1).1⟩,
    lowerCovarianceCone_subset_pd hε C.property.1⟩

@[simp] theorem regionPositiveCovariance_coe
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε)
    (C : optimizerRegion b ε) :
    ((regionPositiveCovariance b ε hε C).1 : FSC.Coord d→L[ℝ]FSC.Coord d)=C := rfl

theorem continuous_regionPositiveCovariance
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε) :
    Continuous (regionPositiveCovariance b ε hε) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem penalizedValue_continuous_joint_region
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε) :
    Continuous (fun q : PositiveProbability m×optimizerRegion b ε =>penalizedValue b q.1 q.2) := by
  have hg : Continuous (fun q : PositiveProbability m×optimizerRegion b ε =>
      operatorValue b q.1 (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d)) := by
    have ht : Continuous (fun q : PositiveProbability m×optimizerRegion b ε =>
        (q.1,regionPositiveCovariance b ε hε q.2)) :=
      continuous_fst.prodMk ((continuous_regionPositiveCovariance b ε hε).comp continuous_snd)
    have hh:=(operatorValue_continuous_joint_positive b).comp ht
    simpa only [Function.comp_def,regionPositiveCovariance_coe] using hh
  change Continuous (fun q : PositiveProbability m×optimizerRegion b ε =>
    2*operatorValue b q.1 (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d)-operatorTrace (q.2 : FSC.Coord d→L[ℝ]FSC.Coord d))
  exact (hg.const_mul 2).sub
    (continuous_operatorTrace.comp (continuous_subtype_val.comp continuous_snd))

/-- The actual unique maximizer varies continuously with the positive prescribed masses. -/
theorem selectedCovariance_continuous
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) (hε : 0<ε) :
    Continuous (selectedCovariance b ε hε) :=
  selectedCovariance_continuous_of_joint_value b ε hε
    (penalizedValue_continuous_joint_region b ε hε)

end NegativeVotingCovarianceOptimizerContinuity
