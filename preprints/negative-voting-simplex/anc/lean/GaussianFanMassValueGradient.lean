import GaussianFanJointValue

/-! The actual derivative in prescribed Gaussian masses is the negative
centered offset. Its local C1 regularity is inherited from the constructed
joint inverse, including simultaneous movement of rows and masses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology
namespace NegativeVotingFanMassValueGradient
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingFanJointInverse NegativeVotingFanJointOffsets NegativeVotingFanJointValue
  NegativeVotingFanValueDerivative NegativeVotingFanEnvelope NegativeVotingCapTail
  NegativeVotingFacetDegree NegativeVotingFanJointMass
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def massDerivative (h : V → ℝ) : centeredGauge V →L[ℝ] ℝ :=
  -(∑ i, h i • ((ContinuousLinearMap.proj i).comp (centeredGauge V).subtypeL))

@[simp] theorem massDerivative_apply (h : V → ℝ) (v : centeredGauge V) :
    massDerivative h v= -∑ i, h i*(v : V → ℝ) i := by
  simp [massDerivative]

/-- The derivative is at an arbitrary centered mass coordinate, not merely
at the origin of one selected chart. -/
theorem hasFDerivAt_mass_value (B : Rows d V) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V → ℝ) (u : centeredGauge V)
    (hp : ∀ i, 0 < (p+(u : V → ℝ)) i)
    (hm : mass B h₀=p+(u : V → ℝ)) :
    HasFDerivAt (fun v : centeredGauge V => optimizedValue B (p+(v : V → ℝ)))
      (massDerivative h₀) u := by
  have hV := (jointValue_C1_and_derivative B h₀ σ hσ hlower (by simpa only [hm] using hp)).2
  have hshift : HasFDerivAt (fun v : centeredGauge V => (B,v-u))
      (ContinuousLinearMap.inr ℝ (Rows d V) (centeredGauge V)) u :=
    (hasFDerivAt_const B u).prodMk ((hasFDerivAt_id u).sub_const u)
  have hV' : HasFDerivAt (fun q : JointCoordinates d V => optimizedValue q.1
      (mass B h₀+(q.2 : V → ℝ))) (jointValueDerivative B h₀) (B,u-u) := by simpa using hV
  have hd := hV'.comp u hshift
  have hL : (jointValueDerivative B h₀).comp
      (ContinuousLinearMap.inr ℝ (Rows d V) (centeredGauge V))=massDerivative h₀ := by
    apply ContinuousLinearMap.ext
    intro v
    simp [jointValueDerivative_apply]
  rw [hL] at hd
  have heq (v : centeredGauge V) : mass B h₀+((v-u : centeredGauge V) : V → ℝ)=p+(v : V → ℝ) := by
    rw [hm]
    simp only [Submodule.coe_sub]
    abel
  simpa only [Function.comp_def,heq] using hd

/-- The local mass gradient is a genuine C1 map into continuous linear
functionals, and equals the derivative of the actual optimized value at
every point in a neighborhood. -/
theorem exists_local_C1_mass_gradient (B : Rows d V) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < mass B h₀ i) :
    ∃ a : JointCoordinates d V → centeredGauge V,
      a (B,0)=h₀ ∧ ContDiffAt ℝ 1 a (B,0) ∧
      ContDiffAt ℝ 1 (fun q => massDerivative (a q : V → ℝ)) (B,0) ∧
      ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0),
        mass q.1 (a q)=mass B h₀+(q.2 : V → ℝ) ∧
        HasFDerivAt (fun v : centeredGauge V => optimizedValue q.1 (mass B h₀+(v : V → ℝ)))
          (massDerivative (a q : V → ℝ)) q.2 := by
  obtain ⟨a,ha0,haC,ham⟩ := exists_joint_C1_offsets B h₀ σ hσ hlower
  have hAC : ContDiffAt ℝ 1 (fun q => (a q : V → ℝ)) (B,0) :=
    (centeredGauge V).subtypeL.contDiff.contDiffAt.comp (B,0) haC
  have hgrad : ContDiffAt ℝ 1 (fun q => massDerivative (a q : V → ℝ)) (B,0) := by
    letI : IsBoundedSMul ℝ (centeredGauge V →L[ℝ] ℝ) :=
      .of_norm_smul_le (fun c L => ContinuousLinearMap.opNorm_smul_le c L)
    unfold massDerivative
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro i _
    let Z : centeredGauge V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (centeredGauge V).subtypeL
    have hc := (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp (B,0) hAC
    exact hc.smul contDiffAt_const
  have hlow : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0), CenteredSingularLowerBound q.1 (σ/2) := by
    have hc : ContinuousAt (fun q : JointCoordinates d V => (q.1,(h₀ : V → ℝ))) (B,0) := by fun_prop
    exact hc.eventually (eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  have hpos : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0), ∀ i, 0 < (mass B h₀+(q.2 : V → ℝ)) i := by
    apply eventually_all.mpr
    intro i
    let Z : JointCoordinates d V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp massPerturbation
    have hc : ContinuousAt (fun q : JointCoordinates d V => mass B h₀ i+Z q) (B,0) :=
      continuousAt_const.add Z.continuous.continuousAt
    exact hc.eventually (Ioi_mem_nhds (by simpa [Z] using hp i))
  refine ⟨a,ha0,haC,hgrad,?_⟩
  filter_upwards [ham,hlow,hpos] with q hm hl hpq
  exact ⟨hm,hasFDerivAt_mass_value q.1 (a q) (σ/2) (by positivity) hl (mass B h₀) q.2 hpq hm⟩

end NegativeVotingFanMassValueGradient
