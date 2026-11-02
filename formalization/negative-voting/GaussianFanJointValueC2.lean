import GaussianFanHessianContinuity
import GaussianFanSelectedOffsets

/-! The actual optimized Gaussian fan value is jointly C2 in rows and
positive prescribed masses. Its first derivative is obtained from the
actual centered offset, whose C1 regularity has already been proved. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology
namespace NegativeVotingFanJointValueC2
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanInverse
  NegativeVotingFanJointInverse NegativeVotingFanJointMass NegativeVotingFanJointOffsets
  NegativeVotingFanJointValue NegativeVotingFanSelectedOffsets NegativeVotingFanValue
  NegativeVotingFanValueDerivative NegativeVotingFanEnvelope NegativeVotingFanHessianContinuity
  NegativeVotingCapTail NegativeVotingFacetDegree
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem hasFDerivAt_joint_value_at (B : Rows d V) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V→ℝ) (u : centeredGauge V)
    (hp : ∀ i,0<(p+(u : V→ℝ)) i) (hm : mass B h₀=p+(u : V→ℝ)) :
    HasFDerivAt (fun q : JointCoordinates d V=>optimizedValue q.1 (p+(q.2 : V→ℝ)))
      (jointValueDerivative B h₀) (B,u) := by
  have hd := (jointValue_C1_and_derivative B h₀ σ hσ hlower (by simpa only [hm] using hp)).2
  have hd' : HasFDerivAt (fun q : JointCoordinates d V=>optimizedValue q.1
      (mass B h₀+(q.2 : V→ℝ))) (jointValueDerivative B h₀) ((B,u)-(0,u)) := by
    simpa using hd
  have ht := hd'.comp (B,u) ((hasFDerivAt_id (B,u)).sub_const (0,u))
  have heq (q : JointCoordinates d V) : mass B h₀+((q.2-u : centeredGauge V) : V→ℝ)=p+(q.2 : V→ℝ) := by
    rw [hm]
    simp only [Submodule.coe_sub]
    abel
  change HasFDerivAt (fun q : JointCoordinates d V=>optimizedValue (q.1-0)
    (mass B h₀+((q.2-u : centeredGauge V) : V→ℝ)))
    ((jointValueDerivative B h₀).comp (ContinuousLinearMap.id ℝ _)) (B,u) at ht
  simpa only [sub_zero,ContinuousLinearMap.comp_id,heq] using ht

theorem contDiffAt_jointValueDerivative (B : Rows d V) (h : V→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun q : Parameters d V=>jointValueDerivative q.1 q.2) (B,h) := by
  letI : IsBoundedSMul ℝ (Parameters d V→L[ℝ]ℝ) :=
    .of_norm_smul_le (fun c L=>ContinuousLinearMap.opNorm_smul_le c L)
  have hJ:=contDiffAt_jointGradient_one B h σ hσ hlower
  have hO : ContDiffAt ℝ 1 (fun q : Parameters d V=>offsetFunctional (d:=d) q.2) (B,h) := by
    unfold offsetFunctional
    apply ContDiffAt.sum
    intro i _
    have hi : ContDiffAt ℝ 1 (fun q : Parameters d V=>q.2 i) (B,h) :=
      (ContinuousLinearMap.proj i : (V→ℝ)→L[ℝ]ℝ).contDiff.contDiffAt.comp (B,h) contDiffAt_snd
    exact hi.smul contDiffAt_const
  exact ((hJ.clm_comp contDiffAt_const).clm_comp contDiffAt_const).sub
    (hO.clm_comp contDiffAt_const)

/-- The full C2 statement concerns the genuine infimum value and a full
neighborhood of all row and centered mass coordinates. -/
theorem jointValue_C2 (B : Rows d V)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ContDiffAt ℝ 2 (fun q : JointCoordinates d V=>optimizedValue q.1 (p+(q.2 : V→ℝ))) (B,0) := by
  let a : JointCoordinates d V→centeredGauge V:=fun q=>selectedOffsets q.1 (p+(q.2 : V→ℝ))
  have haC : ContDiffAt ℝ 1 a (B,0):=selectedOffsets_joint_C1 B σ hσ hlower p hp hs
  have hAC : ContDiffAt ℝ 1 (fun q=>(a q : V→ℝ)) (B,0):=
    (centeredGauge V).subtypeL.contDiff.contDiffAt.comp (B,0) haC
  have hQ : ContDiffAt ℝ 1 (fun q : JointCoordinates d V=>(q.1,(a q : V→ℝ))) (B,0):=
    contDiffAt_fst.prodMk hAC
  have hgrad : ContDiffAt ℝ 1 (fun q : JointCoordinates d V=>jointValueDerivative q.1 (a q)) (B,0):=
    (contDiffAt_jointValueDerivative B (a (B,0)) σ hσ hlower).comp
      (g:=fun r : Parameters d V=>jointValueDerivative r.1 r.2)
      (f:=fun q : JointCoordinates d V=>(q.1,(a q : V→ℝ))) (B,0) hQ
  have hlow : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0),CenteredSingularLowerBound q.1 (σ/2) := by
    have hc : ContinuousAt (fun q : JointCoordinates d V=>(q.1,(0 : V→ℝ))) (B,0):=by fun_prop
    exact hc.eventually (eventually_centeredSingularLowerBound B 0 σ hσ hlower)
  have hpos : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0),∀ i,0<(p+(q.2 : V→ℝ)) i := by
    apply eventually_all.mpr
    intro i
    let Z : JointCoordinates d V→L[ℝ]ℝ:=(ContinuousLinearMap.proj i).comp massPerturbation
    have hc : ContinuousAt (fun q : JointCoordinates d V=>p i+Z q) (B,0):=
      continuousAt_const.add Z.continuous.continuousAt
    exact hc.eventually (Ioi_mem_nhds (by simpa [Z] using hp i))
  apply (contDiffAt_succ_iff_hasFDerivAt (n:=1)).mpr
  refine ⟨fun q=>jointValueDerivative q.1 (a q),?_,hgrad⟩
  refine ⟨{q : JointCoordinates d V | CenteredSingularLowerBound q.1 (σ/2) ∧
    ∀ i,0<(p+(q.2 : V→ℝ)) i},hlow.and hpos,?_⟩
  intro q hq
  rcases hq with ⟨hl,hpq⟩
  have hB : Function.Injective q.1:=fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne q.1 (σ/2) (by positivity) hl i j hij he
  have hu : ∑ i,(q.2 : V→ℝ) i=0:=q.2.property
  have hsum : ∑ i,(p+(q.2 : V→ℝ)) i=1:=by simp [Finset.sum_add_distrib,hs,hu]
  exact hasFDerivAt_joint_value_at q.1 (a q) (σ/2) (by positivity) hl p q.2 hpq
    (selectedOffsets_mass q.1 hB _ hpq hsum)

end NegativeVotingFanJointValueC2
