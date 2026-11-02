import GaussianCovarianceUniformTransfer
import GaussianCovarianceRealization
import GaussianTwoCellSeparation

/-! Actual geometric bounds for covariance optimizers, expressed directly in
terms of covariance quadratic forms rather than a selected square root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Filter Set
open scoped Topology BigOperators NNReal RealInnerProductSpace
namespace NegativeVotingCovarianceBoundary
open NegativeVotingFanMassContinuity NegativeVotingPositiveCovariance
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceCoercivity NegativeVotingCovarianceStrict
  NegativeVotingCovarianceRealization NegativeVotingTwoCell NegativeVotingCentroidOptimization
variable {m d : ℕ} [NeZero m]

def operatorEdgeLength (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (i j : Fin m) : ℝ :=
  Real.sqrt (inner ℝ (b i-b j) (C (b i-b j)))

theorem continuous_operatorEdgeLength (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (i j : Fin m) :
    Continuous (fun C : FSC.Coord d→L[ℝ]FSC.Coord d => operatorEdgeLength b C i j) := by
  unfold operatorEdgeLength
  fun_prop

theorem operatorEdgeLength_eq_factor_norm (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C R : FSC.Coord d→L[ℝ]FSC.Coord d) (hR : R∈psdCone) (hRC : R.comp R=C) (i j : Fin m) :
    operatorEdgeLength b C i j=‖R (b i)-R (b j)‖ := by
  have he : inner ℝ (b i-b j) (C (b i-b j))=‖R (b i-b j)‖^2 := by
    rw [←hRC]
    change inner ℝ (b i-b j) (R (R (b i-b j)))=‖R (b i-b j)‖^2
    have hh := hR.1 (b i-b j) (R (b i-b j))
    change inner ℝ (R (b i-b j)) (R (b i-b j))=inner ℝ (b i-b j) (R (R (b i-b j))) at hh
    rw [←hh,real_inner_self_eq_norm_sq]
  unfold operatorEdgeLength
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),map_sub]

/-- Every actual zero-floor covariance maximizer obeys the centroid-derived
edge bounds. The PSD factor and maximizing assignment are both constructed. -/
theorem zero_optimizer_edge_bounds
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : PositiveMassVector (Fin m)) (C : PSDCovariance d)
    (hmax : IsMaxOn (penalizedValue b p) psdCone (C : FSC.Coord d→L[ℝ]FSC.Coord d))
    (hdim : 2 ≤ d) (p0 M A : ℝ) (hp0 : 0 < p0) (hM : 1 ≤ M)
    (hlo : ∀ i,p0 ≤ (p : Fin m→ℝ) i) (hhi : ∀ i,(p : Fin m→ℝ) i ≤ A/M) (i j : Fin m) (hij : i≠j) :
    Real.sqrt (2*Real.pi)*p0^2 ≤ operatorEdgeLength b C i j ∧
    operatorEdgeLength b C i j ≤
      2*(A*Real.sqrt (2*Real.log M)+(Real.sqrt (2*Real.pi))⁻¹)/M := by
  obtain ⟨R,f,hR,hRC,hf,hfm,hfp,hcent,hval,hobj,hglobal⟩ :=
    covariance_maximizer_centroid_assignment b hG hP p p.property.1 p.property.2 C C.property
      (fun D hD => hmax hD)
  have hh := centroid_edges_in_mass_window p f hf (hglobal d) hdim p0 M A hp0 hM hlo hhi i j hij
  have he : operatorEdgeLength b C i j=‖centroidRows f i-centroidRows f j‖ := by
    rw [operatorEdgeLength_eq_factor_norm b C R hR hRC i j]
    rw [←hcent]
  rwa [he]

def edgeWindow (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (lo hi : ℝ) :
    Set (PositiveMassVector (Fin m)×PSDCovariance d) :=
  {q | ∀ i j : Fin m,i≠j → lo < operatorEdgeLength b q.2 i j ∧ operatorEdgeLength b q.2 i j < hi}

theorem edgeWindow_open (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (lo hi : ℝ) :
    IsOpen (edgeWindow b lo hi) := by
  have hpiece (i j : Fin m) : IsOpen {q : PositiveMassVector (Fin m)×PSDCovariance d |
      i≠j → lo < operatorEdgeLength b q.2 i j ∧ operatorEdgeLength b q.2 i j < hi} := by
    by_cases hij : i=j
    · simp [hij]
    · have hc : Continuous (fun q : PositiveMassVector (Fin m)×PSDCovariance d =>
          operatorEdgeLength b q.2 i j) :=
        (continuous_operatorEdgeLength b i j).comp (continuous_subtype_val.comp continuous_snd)
      change IsOpen {q : PositiveMassVector (Fin m)×PSDCovariance d | i≠j → lo < operatorEdgeLength b q.2 i j ∧ operatorEdgeLength b q.2 i j < hi}
      have heq : {q : PositiveMassVector (Fin m)×PSDCovariance d | i≠j → lo < operatorEdgeLength b q.2 i j ∧ operatorEdgeLength b q.2 i j < hi}=
          {q | lo < operatorEdgeLength b q.2 i j} ∩ {q | operatorEdgeLength b q.2 i j < hi} := by
        ext q
        simp [hij]
      rw [heq]
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have he : edgeWindow b lo hi=⋂ i : Fin m,⋂ j : Fin m,
      {q : PositiveMassVector (Fin m)×PSDCovariance d |
        i≠j → lo < operatorEdgeLength b q.2 i j ∧ operatorEdgeLength b q.2 i j < hi} := by
    ext q
    simp [edgeWindow]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (hpiece i))

/-- A literal closed mass box inside the positive probability simplex. -/
def positiveMassBox (p0 p1 : ℝ) : Set (PositiveMassVector (Fin m)) :=
  {p | ∀ i : Fin m,p0 ≤ (p : Fin m→ℝ) i ∧ (p : Fin m→ℝ) i ≤ p1}

theorem positiveMassBox_compact (p0 p1 : ℝ) (hp0 : 0 < p0) :
    IsCompact (positiveMassBox (m:=m) p0 p1) := by
  apply Subtype.isCompact_iff.mpr
  let S : Set (Fin m→ℝ) := {p | (∀ i,p0 ≤ p i ∧ p i ≤ p1) ∧ ∑ i,p i=1}
  have he : ((↑) '' positiveMassBox (m:=m) p0 p1 : Set (Fin m→ℝ))=S := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨hq,q.property.2⟩
    · intro hp
      exact ⟨⟨p,⟨fun i => hp0.trans_le (hp.1 i).1,hp.2⟩⟩,hp.1,rfl⟩
  rw [he]
  have hclosed : IsClosed S := by
    change IsClosed ({p : Fin m→ℝ | ∀ i,p0 ≤ p i ∧ p i ≤ p1} ∩ {p | ∑ i,p i=1})
    apply IsClosed.inter
    · simp only [setOf_forall,setOf_and]
      exact isClosed_iInter (fun i => (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const))
    · exact isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : Fin m→ℝ) |p1|).of_isClosed_subset hclosed
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg p1)).mpr
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hp0.le.trans (hp.1 i).1)]
  exact (hp.1 i).2.trans (le_abs_self p1)

/-- Uniform actual edge geometry at small covariance floors, over the entire
prescribed positive mass box. Existence of a selected optimizer and continuity
of a zero-floor optimizing choice are not hypotheses. -/
theorem uniform_small_floor_edge_bounds
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (hdim : 2 ≤ d) (p0 M A : ℝ) (hp0 : 0 < p0) (hM : 1 ≤ M) (hA : 0 ≤ A) :
    ∃ δ : ℝ,0 < δ ∧ ∀ ε : ℝ≥0,(ε:ℝ) < δ →
      ∀ p∈positiveMassBox (m:=m) p0 (A/M),∀ C : PSDCovariance d,
      IsOptimizerState b (ε,(p,C)) → ∀ i j : Fin m,i≠j →
      Real.sqrt (2*Real.pi)*p0^2/2 < operatorEdgeLength b C i j ∧
      operatorEdgeLength b C i j <
        4*(A*Real.sqrt (2*Real.log M)+(Real.sqrt (2*Real.pi))⁻¹)/M := by
  let L := Real.sqrt (2*Real.pi)*p0^2
  let U := 2*(A*Real.sqrt (2*Real.log M)+(Real.sqrt (2*Real.pi))⁻¹)/M
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hzero : ∀ p∈positiveMassBox (m:=m) p0 (A/M),∀ C : PSDCovariance d,
      IsOptimizerState b (0,(p,C)) → (p,C)∈edgeWindow b (L/2) (2*U) := by
    intro p hp C hmax i j hij
    have hmax0 := hmax.2
    change IsMaxOn (penalizedValue b p) (lowerCovarianceCone (0:ℝ))
      (C : FSC.Coord d→L[ℝ]FSC.Coord d) at hmax0
    rw [lowerCovarianceCone_zero] at hmax0
    have hh := zero_optimizer_edge_bounds b hG hP p C hmax0 hdim p0 M A hp0 hM
      (fun k => (hp k).1) (fun k => (hp k).2) i j hij
    change L ≤ operatorEdgeLength b C i j ∧ operatorEdgeLength b C i j ≤ U at hh
    constructor <;> linarith
  obtain ⟨δ,hδ,hh⟩ := uniform_optimizer_transfer_at_zero b
    (positiveMassBox (m:=m) p0 (A/M)) (positiveMassBox_compact p0 (A/M) hp0)
    (edgeWindow b (L/2) (2*U)) (edgeWindow_open b (L/2) (2*U)) hzero
  refine ⟨δ,hδ,?_⟩
  intro ε hε p hp C hmax i j hij
  have he := hh ε hε p hp C hmax i j hij
  change L/2 < operatorEdgeLength b C i j ∧ operatorEdgeLength b C i j < 2*U at he
  refine ⟨he.1,?_⟩
  have heq : 2*U=4*(A*Real.sqrt (2*Real.log M)+(Real.sqrt (2*Real.pi))⁻¹)/M := by
    dsimp [U]
    ring
  exact he.2.trans_eq heq

end NegativeVotingCovarianceBoundary
