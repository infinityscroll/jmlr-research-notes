import GaussianFanMassValueGradient
import GaussianFanOffsetCovarianceLaw

/-! A globally selected centered offset, with actual local C1 regularity and
Gram invariance proved from the Gaussian mass inverse and uniqueness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingFanSelectedOffsets
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanJointMass
  NegativeVotingFanJointInverse NegativeVotingFanJointOffsets NegativeVotingFanMassValueGradient
  NegativeVotingFanOffsetCovarianceLaw NegativeVotingCapTail NegativeVotingFacetDegree
variable {d e : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The value outside the realizable-mass locus is immaterial. On the actual
full-rank positive-mass domain the selected offset is unique and C1. -/
def selectedOffsets (B : V → FSC.Coord d) (p : V → ℝ) : centeredGauge V :=
  if h : ∃ a : centeredGauge V, mass B a=p then h.choose else 0

theorem selectedOffsets_mass_of_exists (B : V → FSC.Coord d) (p : V → ℝ)
    (he : ∃ a : centeredGauge V, mass B a=p) : mass B (selectedOffsets B p)=p := by
  simp only [selectedOffsets,dif_pos he]
  exact he.choose_spec

theorem selectedOffsets_mass (B : V → FSC.Coord d) (hB : Function.Injective B)
    (p : V → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    mass B (selectedOffsets B p)=p := by
  obtain ⟨h,hh,hm⟩ := exists_offsets_with_prescribed_masses B hB p hp hs
  exact selectedOffsets_mass_of_exists B p ⟨⟨h,hh⟩,funext hm⟩

theorem selectedOffsets_eq (B : V → FSC.Coord d) (p : V → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (h : centeredGauge V) (hm : mass B h=p) : selectedOffsets B p=h := by
  apply Subtype.ext
  exact centered_offsets_unique B σ hσ hlower _ _
    (selectedOffsets B p).property h.property
    ((selectedOffsets_mass_of_exists B p ⟨h,hm⟩).trans hm.symm)

theorem selectedOffsets_eq_of_gram (B : V → FSC.Coord d) (C : V → FSC.Coord e)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (hGram : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j))
    (p : V → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    selectedOffsets B p=selectedOffsets C p := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  apply Subtype.ext
  exact centered_offsets_eq_of_gram B C σ hσ hlower hGram _ _
    (selectedOffsets B p).property (selectedOffsets C p).property
    ((selectedOffsets_mass B hB p hp hs).trans
      (selectedOffsets_mass C (injective_of_gram B C hB hGram) p hp hs).symm)

/-- C1 regularity of the global selection follows from its equality to the
actual local inverse; it is not an extra selection-regularity assumption. -/
theorem selectedOffsets_joint_C1_at_mass (B : V → FSC.Coord d) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun q : JointCoordinates d V =>
      selectedOffsets q.1 (mass B h₀+(q.2 : V → ℝ))) (B,0) := by
  obtain ⟨a,_,haC,ham⟩ := exists_joint_C1_offsets B h₀ σ hσ hlower
  have hlow : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0), CenteredSingularLowerBound q.1 (σ/2) := by
    have hc : ContinuousAt (fun q : JointCoordinates d V => (q.1,(h₀ : V → ℝ))) (B,0) := by fun_prop
    exact hc.eventually (eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  apply haC.congr_of_eventuallyEq
  filter_upwards [ham,hlow] with q hm hl
  exact selectedOffsets_eq q.1 _ (σ/2) (by positivity) hl (a q) hm

theorem selectedOffsets_joint_C1 (B : V → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ContDiffAt ℝ 1 (fun q : JointCoordinates d V =>
      selectedOffsets q.1 (p+(q.2 : V → ℝ))) (B,0) := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hC := selectedOffsets_joint_C1_at_mass B (selectedOffsets B p) σ hσ hlower
  simpa only [selectedOffsets_mass B hB p hp hs] using hC

/-- The global selected offset represents the actual mass derivative. -/
theorem selected_mass_derivative (B : V → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V → ℝ) (u : centeredGauge V)
    (hp : ∀ i,0<(p+(u : V → ℝ)) i) (hs : ∑ i,p i=1) :
    HasFDerivAt (fun v : centeredGauge V => NegativeVotingFanValue.optimizedValue B (p+(v : V → ℝ)))
      (massDerivative (selectedOffsets B (p+(u : V → ℝ)))) u := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hu : ∑ i,(u : V → ℝ) i=0 := u.property
  have hs' : ∑ i,(p+(u : V → ℝ)) i=1 := by simp [Finset.sum_add_distrib,hs,hu]
  exact hasFDerivAt_mass_value B _ σ hσ hlower p u hp
    (selectedOffsets_mass B hB _ hp hs')

end NegativeVotingFanSelectedOffsets
