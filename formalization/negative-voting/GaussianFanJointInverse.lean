import GaussianFanJointMass
import GaussianFanJacobianPseudoInverse

/-! A joint local C1 inverse for literal Gaussian fan masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Topology Classical

namespace NegativeVotingFanJointInverse
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanInverse
open NegativeVotingFanJointMass NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev JointCoordinates (d : ℕ) (ι : Type*) [Fintype ι] :=
  (ι → FSC.Coord d) × centeredGauge ι

def parameterEmbedding : JointCoordinates d ι →L[ℝ] Parameters d ι :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((centeredGauge ι).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem parameterEmbedding_apply (p : JointCoordinates d ι) :
    parameterEmbedding p = (p.1, (p.2 : ι → ℝ)) := rfl

def jointCenteredMass (p : JointCoordinates d ι) : centeredGauge ι :=
  centeredMass p.1 p.2

def jointCenteredMassDerivative (B : ι → FSC.Coord d) (h : centeredGauge ι) :
    JointCoordinates d ι →L[ℝ] centeredGauge ι :=
  centering.comp ((jointMassDerivative B (h : ι → ℝ)).comp parameterEmbedding)

theorem hasFDerivAt_jointCenteredMass (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt jointCenteredMass (jointCenteredMassDerivative B h) (B,h) := by
  have hd := (hasFDerivAt_mass_joint B (h : ι → ℝ) σ hσ hlower).comp (B,h)
    (parameterEmbedding (d := d) (ι := ι)).hasFDerivAt
  exact centering.hasFDerivAt.comp (B,h) hd

theorem contDiffAt_jointCenteredMass (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 jointCenteredMass (B,h) := by
  exact centering.contDiff.contDiffAt.comp (B,h)
    ((contDiffAt_mass_joint B (h : ι → ℝ) σ hσ hlower).comp (B,h)
      parameterEmbedding.contDiff.contDiffAt)

/-- This block equality is derived by uniqueness of the actual derivative. -/
theorem jointCenteredMassDerivative_offset (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    (jointCenteredMassDerivative B h).comp
      (ContinuousLinearMap.inr ℝ (ι → FSC.Coord d) (centeredGauge ι)) =
        centeredMassDerivative B h := by
  have he : HasFDerivAt (fun v : centeredGauge ι => (B,v))
      (ContinuousLinearMap.inr ℝ (ι → FSC.Coord d) (centeredGauge ι)) h :=
    (hasFDerivAt_const B h).prodMk (hasFDerivAt_id h)
  exact ((hasFDerivAt_jointCenteredMass B h σ hσ hlower).comp h he).unique
    (hasFDerivAt_centeredMass B σ hσ hlower h)

/-- Rows are kept as coordinates while the offsets are replaced by actual
centered Gaussian cell masses. -/
def jointMassCoordinates (p : JointCoordinates d ι) : JointCoordinates d ι :=
  (p.1, jointCenteredMass p)

def jointCoordinatesDerivative (B : ι → FSC.Coord d) (h : centeredGauge ι) :
    JointCoordinates d ι →L[ℝ] JointCoordinates d ι :=
  (ContinuousLinearMap.fst ℝ _ _).prod (jointCenteredMassDerivative B h)

theorem hasFDerivAt_jointMassCoordinates (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt jointMassCoordinates (jointCoordinatesDerivative B h) (B,h) :=
  (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.prodMk
    (hasFDerivAt_jointCenteredMass B h σ hσ hlower)

theorem contDiffAt_jointMassCoordinates (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 jointMassCoordinates (B,h) :=
  contDiffAt_fst.prodMk (contDiffAt_jointCenteredMass B h σ hσ hlower)

/-- Injectivity of the actual block Jacobian follows from its identity row
block and the proved strictly positive offset Jacobian on the centered gauge. -/
theorem jointCoordinatesDerivative_injective (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    Function.Injective (jointCoordinatesDerivative B h) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hrow : x.1 = 0 := congrArg Prod.fst hx
  have hmass : jointCenteredMassDerivative B h x = 0 := congrArg Prod.snd hx
  have hxform : x = (0,x.2) := Prod.ext hrow rfl
  have he := congrArg (fun L : centeredGauge ι →L[ℝ] centeredGauge ι => L x.2)
    (jointCenteredMassDerivative_offset B h σ hσ hlower)
  change jointCenteredMassDerivative B h (0,x.2) = centeredMassDerivative B h x.2 at he
  rw [hxform, he] at hmass
  have hoff : x.2 = 0 := (centeredMassDerivative_injective B σ hσ hlower h)
    (hmass.trans (map_zero _).symm)
  exact Prod.ext hrow hoff

/-- The inverse is constructed from the derived bijective block operator. -/
def jointCoordinatesDerivativeEquiv (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    JointCoordinates d ι ≃L[ℝ] JointCoordinates d ι :=
  ContinuousLinearEquiv.ofBijective (jointCoordinatesDerivative B h)
    (LinearMap.ker_eq_bot.mpr (jointCoordinatesDerivative_injective B h σ hσ hlower))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (jointCoordinatesDerivative_injective B h σ hσ hlower)))

@[simp] theorem jointCoordinatesDerivativeEquiv_coe (B : ι → FSC.Coord d)
    (h : centeredGauge ι) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) :
    (jointCoordinatesDerivativeEquiv B h σ hσ hlower :
      JointCoordinates d ι →L[ℝ] JointCoordinates d ι) = jointCoordinatesDerivative B h := rfl


/-- The inverse function theorem is applied to the actual joint map. -/
theorem exists_local_C1_joint_mass_inverse (B : ι → FSC.Coord d) (h : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∃ e : OpenPartialHomeomorph (JointCoordinates d ι) (JointCoordinates d ι),
      (⇑e = jointMassCoordinates) ∧ (B,h) ∈ e.source ∧
      ContDiffAt ℝ 1 e.symm (jointMassCoordinates (B,h)) ∧
      HasFDerivAt e.symm
        ((jointCoordinatesDerivativeEquiv B h σ hσ hlower).symm :
          JointCoordinates d ι →L[ℝ] JointCoordinates d ι)
        (jointMassCoordinates (B,h)) := by
  let L := jointCoordinatesDerivativeEquiv B h σ hσ hlower
  have hc := contDiffAt_jointMassCoordinates B h σ hσ hlower
  have hd : HasFDerivAt jointMassCoordinates
      (L : JointCoordinates d ι →L[ℝ] JointCoordinates d ι) (B,h) :=
    hasFDerivAt_jointMassCoordinates B h σ hσ hlower
  let e := hc.toOpenPartialHomeomorph jointMassCoordinates hd (by norm_num)
  refine ⟨e, rfl, hc.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_, ?_⟩
  · exact hc.to_localInverse hd (by norm_num)
  · exact (hc.hasStrictFDerivAt' hd (by norm_num)).to_localInverse.hasFDerivAt

/-- The inverse retains the prescribed row coordinates and realizes actual
Gaussian cell probabilities throughout its open target. -/
theorem joint_chart_inverse_realizes
    (e : OpenPartialHomeomorph (JointCoordinates d ι) (JointCoordinates d ι))
    (he : ⇑e = jointMassCoordinates) (q : JointCoordinates d ι) (hq : q ∈ e.target) :
    (e.symm q).1 = q.1 ∧
      mass q.1 ((e.symm q).2 : ι → ℝ) =
        fun i => (q.2 : ι → ℝ) i + 1 / (Fintype.card ι : ℝ) := by
  have hh : jointMassCoordinates (e.symm q) = q := by
    rw [← he]
    exact e.right_inv hq
  have hrow := congrArg Prod.fst hh
  change (e.symm q).1 = q.1 at hrow
  have hm : centeredMass (e.symm q).1 (e.symm q).2 = q.2 := congrArg Prod.snd hh
  rw [hrow] at hm
  refine ⟨hrow, ?_⟩
  funext i
  have hi := congrArg (fun x : centeredGauge ι => (x : ι → ℝ) i) hm
  rw [centeredMass_apply] at hi
  linarith

/-- Every positive probability vector has a genuine joint local C1 chart in
both the row variables and the centered probability coordinates. -/
theorem exists_prescribed_joint_C1_chart (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : centeredGauge ι, mass B (h : ι → ℝ) = p ∧
      ∃ e : OpenPartialHomeomorph (JointCoordinates d ι) (JointCoordinates d ι),
        (⇑e = jointMassCoordinates) ∧ (B,h) ∈ e.source ∧
        (B,centering p) ∈ e.target ∧ ContDiffAt ℝ 1 e.symm (B,centering p) ∧
        ∀ q ∈ e.target, (e.symm q).1 = q.1 ∧
          mass q.1 ((e.symm q).2 : ι → ℝ) =
            fun i => (q.2 : ι → ℝ) i + 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨h, ⟨hh, hm⟩, _⟩ := existsUnique_offsets_with_prescribed_masses B σ hσ hlower p hp hs
  let h₀ : centeredGauge ι := ⟨h,hh⟩
  obtain ⟨e, he, hsource, hc, _⟩ := exists_local_C1_joint_mass_inverse B h₀ σ hσ hlower
  have hpoint : jointMassCoordinates (B,h₀) = (B,centering p) := by
    change (B,centering (mass B h)) = (B,centering p)
    rw [hm]
  have htarget := e.map_source hsource
  rw [he, hpoint] at htarget
  rw [hpoint] at hc
  exact ⟨h₀, hm, e, he, hsource, htarget, hc, fun q hq => joint_chart_inverse_realizes e he q hq⟩

/-- Any C1 row curve admits an actual anchored C1 centered-offset curve that
preserves its initial Gaussian cell probabilities on a neighborhood of zero.
No offset path or differentiability of an optimizer is an input. -/
theorem exists_C1_offsets_along_rows (B : ℝ → ι → FSC.Coord d)
    (h₀ : centeredGauge ι) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound (B 0) σ) (hB : ContDiffAt ℝ 1 B 0) :
    ∃ h : ℝ → ι → ℝ, h 0 = (h₀ : ι → ℝ) ∧ ContDiffAt ℝ 1 h 0 ∧
      (∀ t, ∑ i, h t i = 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), mass (B t) (h t) = mass (B 0) (h₀ : ι → ℝ) := by
  obtain ⟨e, he, hsource, hc, _⟩ :=
    exists_local_C1_joint_mass_inverse (B 0) h₀ σ hσ hlower
  let q : centeredGauge ι := centeredMass (B 0) h₀
  have hpoint : jointMassCoordinates (B 0,h₀) = (B 0,q) := rfl
  rw [hpoint] at hc
  let h : ℝ → ι → ℝ := fun t => ((e.symm (B t,q)).2 : ι → ℝ)
  have hinput : ContDiffAt ℝ 1 (fun t => (B t,q)) 0 := hB.prodMk contDiffAt_const
  have hcurve : ContDiffAt ℝ 1 (fun t => e.symm (B t,q)) 0 := hc.comp 0 hinput
  have hoffset : ContDiffAt ℝ 1 h 0 :=
    (centeredGauge ι).subtypeL.contDiff.contDiffAt.comp 0 (contDiffAt_snd.comp 0 hcurve)
  have hbase : e.symm (B 0,q) = (B 0,h₀) := by
    have hi := e.left_inv hsource
    rw [he, hpoint] at hi
    exact hi
  have htarget : (B 0,q) ∈ e.target := by
    have hi := e.map_source hsource
    rwa [he, hpoint] at hi
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), (B t,q) ∈ e.target :=
    hinput.continuousAt.eventually (e.open_target.mem_nhds htarget)
  refine ⟨h, ?_, hoffset, ?_, ?_⟩
  · change ((e.symm (B 0,q)).2 : ι → ℝ) = (h₀ : ι → ℝ)
    rw [hbase]
  · intro t
    exact (e.symm (B t,q)).2.property
  · filter_upwards [hevent] with t ht
    have hm := (joint_chart_inverse_realizes e he (B t,q) ht).2
    simpa only [Prod.fst, Prod.snd, q, centeredMass_apply, sub_add_cancel] using hm

/-- A prescribed positive probability vector is preserved along any C1 row
curve with a nondegenerate base, by an actual derived C1 offset curve. -/
theorem exists_C1_offsets_prescribed_along_rows (B : ℝ → ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound (B 0) σ)
    (hB : ContDiffAt ℝ 1 B 0) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : ℝ → ι → ℝ, ContDiffAt ℝ 1 h 0 ∧ (∀ t, ∑ i, h t i = 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), mass (B t) (h t) = p := by
  obtain ⟨h₀, ⟨hh, hm⟩, _⟩ :=
    existsUnique_offsets_with_prescribed_masses (B 0) σ hσ hlower p hp hs
  obtain ⟨h, _, hc, hz, he⟩ := exists_C1_offsets_along_rows B ⟨h₀,hh⟩ σ hσ hlower hB
  refine ⟨h, hc, hz, ?_⟩
  simpa only [hm] using he

end NegativeVotingFanJointInverse
