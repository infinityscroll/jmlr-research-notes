import GaussianCovarianceCoercivity

/-! A genuine unique maximizer of 2Γ(C,p)-trace(C) on C≥εI.
The compact trace cutoff is derived and is independent of the positive mass vector. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology
namespace NegativeVotingCovarianceOptimizer
open NegativeVotingPositiveCovariance NegativeVotingCovarianceCoercivity
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingFanCovarianceValue NegativeVotingFanValue

section Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def lowerCovarianceCone (ε : ℝ) : Set (E →L[ℝ] E) :=
  {C | C-ε•ContinuousLinearMap.id ℝ E ∈ psdCone}

theorem psdCone_closed : IsClosed (psdCone (E:=E)) := by
  change IsClosed {C : E→L[ℝ]E | (∀ x y,inner ℝ (C x) y=inner ℝ x (C y)) ∧
    ∀ x, 0 ≤ inner ℝ x (C x)}
  simp only [setOf_and,setOf_forall]
  exact (isClosed_iInter (fun x=>isClosed_iInter (fun y=>
    isClosed_eq (by fun_prop) (by fun_prop)))).inter
    (isClosed_iInter (fun x=>isClosed_le continuous_const (by fun_prop)))

theorem lowerCovarianceCone_closed (ε : ℝ) : IsClosed (lowerCovarianceCone (E:=E) ε) :=
  psdCone_closed.preimage (by fun_prop)

theorem lowerCovarianceCone_convex (ε : ℝ) : Convex ℝ (lowerCovarianceCone (E:=E) ε) := by
  intro C hC D hD a c ha hc hac
  change a•C+c•D-ε•ContinuousLinearMap.id ℝ E ∈ psdCone
  have he : a•(C-ε•ContinuousLinearMap.id ℝ E)+c•(D-ε•ContinuousLinearMap.id ℝ E)=
      a•C+c•D-ε•ContinuousLinearMap.id ℝ E := by
    calc
      _ =a•C+c•D-(a+c)•(ε•ContinuousLinearMap.id ℝ E) := by module
      _ =_ := by rw [hac,one_smul]
  rw [←he]
  exact psdCone_convex hC hD ha hc hac

theorem identity_mem_lowerCovarianceCone (ε : ℝ) :
    ε•ContinuousLinearMap.id ℝ E ∈ lowerCovarianceCone ε := by
  change ε•ContinuousLinearMap.id ℝ E-ε•ContinuousLinearMap.id ℝ E ∈ psdCone
  rw [sub_self]
  exact ⟨fun x y=>by simp,fun x=>by simp⟩

theorem lowerCovarianceCone_subset_pd {ε : ℝ} (hε : 0<ε) :
    lowerCovarianceCone (E:=E) ε ⊆ pdCone := by
  intro C hC
  have hh:=regularize_positive hC hε
  simpa only [sub_add_cancel] using hh

end Operators

variable {m d : ℕ} [NeZero m]

def optimizerTraceCutoff (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) : ℝ :=
  4*‖(b : Fin m→FSC.Coord d)‖^2+
    2*operatorTrace (ε•ContinuousLinearMap.id ℝ (FSC.Coord d))+2

def optimizerRegion (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε : ℝ) :
    Set (FSC.Coord d→L[ℝ]FSC.Coord d) :=
  {C | C∈lowerCovarianceCone ε ∧ operatorTrace C≤optimizerTraceCutoff b ε}

theorem identity_mem_optimizerRegion
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) {ε : ℝ} (hε : 0<ε) :
    ε•ContinuousLinearMap.id ℝ (FSC.Coord d) ∈ optimizerRegion b ε := by
  refine ⟨identity_mem_lowerCovarianceCone ε,?_⟩
  have ht:=trace_nonneg (pdCone_subset_psdCone
    (lowerCovarianceCone_subset_pd (E:=FSC.Coord d) hε (identity_mem_lowerCovarianceCone ε)))
  unfold optimizerTraceCutoff
  nlinarith [sq_nonneg ‖(b : Fin m→FSC.Coord d)‖]

theorem optimizerRegion_compact
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) {ε : ℝ} (hε : 0<ε) :
    IsCompact (optimizerRegion b ε) := by
  have hc : IsClosed (optimizerRegion b ε) :=
    (lowerCovarianceCone_closed ε).inter
      (isClosed_le continuous_operatorTrace continuous_const)
  apply (isCompact_closedBall (0 : FSC.Coord d→L[ℝ]FSC.Coord d)
    (optimizerTraceCutoff b ε)).of_isClosed_subset hc
  intro C hC
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (norm_le_trace (pdCone_subset_psdCone (lowerCovarianceCone_subset_pd hε hC.1))).trans hC.2

theorem operatorValue_nonneg
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (C : FSC.Coord d→L[ℝ]FSC.Coord d) :
    0≤operatorValue b p C := optimizedValue_nonneg _ p hp hs

theorem penalizedValue_ge_neg_trace
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (C : FSC.Coord d→L[ℝ]FSC.Coord d) :
    -operatorTrace C≤penalizedValue b p C := by
  have hh:=operatorValue_nonneg b p hp hs C
  change -operatorTrace C≤2*operatorValue b p C-operatorTrace C
  linarith

theorem penalizedValue_continuousOn_lowerCone
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) {ε : ℝ} (hε : 0<ε) :
    ContinuousOn (penalizedValue b p) (lowerCovarianceCone ε) := by
  change ContinuousOn (fun C=>2*operatorValue b p C-operatorTrace C) _
  exact (((operatorValue_continuousOn b p hp hs).mono
    (fun C hC=>pdCone_subset_psdCone (lowerCovarianceCone_subset_pd hε hC))).const_mul 2).sub
      continuous_operatorTrace.continuousOn

theorem outside_region_objective_lt_reference
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) {ε : ℝ} (hε : 0<ε)
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈lowerCovarianceCone ε)
    (hout : C∉optimizerRegion b ε) :
    penalizedValue b p C<penalizedValue b p (ε•ContinuousLinearMap.id ℝ (FSC.Coord d)) := by
  have ht : optimizerTraceCutoff b ε<operatorTrace C := by
    by_contra! hh
    exact hout ⟨hC,hh⟩
  have hb:=penalizedValue_le_trace_cutoff b p hp hs C (lowerCovarianceCone_subset_pd hε hC)
  have hbase:=penalizedValue_ge_neg_trace b p hp hs
    (ε•ContinuousLinearMap.id ℝ (FSC.Coord d))
  unfold optimizerTraceCutoff at ht
  linarith

/-- The compact set is derived uniformly in p, rather than imposed on the maximization. -/
theorem exists_penalized_maximizer
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) {ε : ℝ} (hε : 0<ε) :
    ∃ C∈optimizerRegion b ε, IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C := by
  obtain ⟨C,hC,hmax⟩:=(optimizerRegion_compact b hε).exists_isMaxOn
    ⟨_,identity_mem_optimizerRegion b hε⟩
    ((penalizedValue_continuousOn_lowerCone b p hp hs hε).mono (fun C hC=>hC.1))
  refine ⟨C,hC,?_⟩
  intro D hD
  by_cases hd : D∈optimizerRegion b ε
  · exact hmax hd
  · exact (outside_region_objective_lt_reference b p hp hs hε D hD hd).le.trans
      (hmax (identity_mem_optimizerRegion b hε))

/-- Literal existence and uniqueness for the unbounded domain C≥εI. -/
theorem exists_unique_penalized_maximizer
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) {ε : ℝ} (hε : 0<ε) :
    ∃! C, C∈lowerCovarianceCone ε ∧
      IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C := by
  obtain ⟨C,hC,hmax⟩:=exists_penalized_maximizer b p (fun i=>(hp i).le) hs hε
  refine ⟨C,⟨hC.1,hmax⟩,?_⟩
  intro D hD
  have hstrict : StrictConcaveOn ℝ (lowerCovarianceCone ε) (penalizedValue b p) := by
    refine ⟨lowerCovarianceCone_convex ε,?_⟩
    intro A hA B hB hAB a c ha hc hac
    exact (penalizedValue_strictConcaveOn_positive b p hp hs).2
      (lowerCovarianceCone_subset_pd hε hA) (lowerCovarianceCone_subset_pd hε hB) hAB ha hc hac
  exact hstrict.eq_of_isMaxOn hD.2 hmax hD.1 hC.1

end NegativeVotingCovarianceOptimizer
