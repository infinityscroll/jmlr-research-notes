import GaussianFanJointOffsets

/-! The actual optimized value is jointly C1 in rows and positive prescribed
masses, in the genuine centered probability coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanJointValue
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanInverse
  NegativeVotingFanJointInverse NegativeVotingFanJointMass NegativeVotingFanJointOffsets
  NegativeVotingFanEnvelope NegativeVotingFanValueDerivative NegativeVotingFanValue
  NegativeVotingCapTail NegativeVotingFacetDegree
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def massPerturbation : JointCoordinates d V →L[ℝ] (V → ℝ) :=
  (centeredGauge V).subtypeL.comp (ContinuousLinearMap.snd ℝ (Rows d V) (centeredGauge V))

@[simp] theorem massPerturbation_apply (q : JointCoordinates d V) :
    massPerturbation q=(q.2 : V → ℝ) := rfl

def jointValueDerivative (B : Rows d V) (h : V → ℝ) : JointCoordinates d V →L[ℝ] ℝ :=
  (rowDerivative B h).comp (ContinuousLinearMap.fst ℝ (Rows d V) (centeredGauge V))-
    (offsetFunctional (d := d) h).comp parameterEmbedding

@[simp] theorem jointValueDerivative_apply (B : Rows d V) (h : V → ℝ) (q : JointCoordinates d V) :
    jointValueDerivative B h q=rowDerivative B h q.1-∑ i, h i*(q.2 : V → ℝ) i := by
  simp [jointValueDerivative,offsetFunctional_apply]

/-- Both the actual joint value and its full first derivative are constructed;
no differentiable-optimizer or offset-response premise is supplied. -/
theorem jointValue_C1_and_derivative (B : Rows d V) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < mass B h₀ i) :
    ContDiffAt ℝ 1 (fun q : JointCoordinates d V =>
      optimizedValue q.1 (mass B h₀+(q.2 : V → ℝ))) (B,0) ∧
    HasFDerivAt (fun q : JointCoordinates d V =>
      optimizedValue q.1 (mass B h₀+(q.2 : V → ℝ)))
      (jointValueDerivative B h₀) (B,0) := by
  obtain ⟨a,ha0,haC,ham⟩ := exists_joint_C1_offsets B h₀ σ hσ hlower
  let A : JointCoordinates d V → V → ℝ := fun q => (a q : V → ℝ)
  let Z (i : V) : JointCoordinates d V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp massPerturbation
  have hAC : ContDiffAt ℝ 1 A (B,0) :=
    (centeredGauge V).subtypeL.contDiff.contDiffAt.comp (B,0) haC
  have hA0 : A (B,0)=(h₀ : V → ℝ) := by simp [A,ha0]
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hQ : ContDiffAt ℝ 1 (fun q : JointCoordinates d V => (q.1,A q)) (B,0) :=
    contDiffAt_fst.prodMk hAC
  have hlow : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0), CenteredSingularLowerBound q.1 (σ/2) := by
    have hmap : ContinuousAt (fun q : JointCoordinates d V => (q.1,(h₀ : V → ℝ))) (B,0) := by fun_prop
    exact hmap.eventually (eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  have hpos : ∀ᶠ q : JointCoordinates d V in 𝓝 (B,0), ∀ i, 0 < (mass B h₀+(q.2 : V → ℝ)) i := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun q : JointCoordinates d V => mass B h₀ i+Z i q) (B,0) :=
      continuousAt_const.add (Z i).continuous.continuousAt
    exact hc.eventually (Ioi_mem_nhds (by simpa [Z] using hp i))
  have hsum (q : JointCoordinates d V) : ∑ i, (mass B h₀+(q.2 : V → ℝ)) i=1 := by
    have hz : ∑ i, (q.2 : V → ℝ) i=0 := q.2.property
    simp only [Pi.add_apply,Finset.sum_add_distrib,mass_sum,hz,add_zero]
  have heq : (fun q : JointCoordinates d V => optimizedValue q.1 (mass B h₀+(q.2 : V → ℝ))) =ᶠ[𝓝 (B,0)]
      (fun q => potential q.1 (mass B h₀) (A q)-∑ i, (q.2 : V → ℝ) i*A q i) := by
    filter_upwards [ham,hlow,hpos] with q hmq hlq hpq
    rw [optimizedValue_eq_of_mass q.1 _ (σ/2) (by positivity) hlq hpq (hsum q) (a q) hmq]
    unfold potential
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,A]
    ring
  have hpot : ContDiffAt ℝ 1 (fun q : JointCoordinates d V => potential q.1 (mass B h₀) (A q)) (B,0) := by
    have hh : ContDiffAt ℝ 1 (fun p : Parameters d V => potential p.1 (mass B h₀) p.2) (B,A (B,0)) := by
      simpa only [hA0] using contDiffAt_potential_joint B h₀ (mass B h₀) σ hσ hlower
    simpa only [Function.comp_def] using
      (ContDiffAt.comp (g := fun p : Parameters d V => potential p.1 (mass B h₀) p.2)
        (f := fun q : JointCoordinates d V => (q.1,A q)) (B,0) hh hQ)
  have hauxC : ContDiffAt ℝ 1 (fun q : JointCoordinates d V => ∑ i, (q.2 : V → ℝ) i*A q i) (B,0) := by
    apply ContDiffAt.sum
    intro i _
    exact ((Z i).contDiff.contDiffAt : ContDiffAt ℝ 1 (fun q : JointCoordinates d V => (q.2 : V → ℝ) i) (B,0)).mul
      ((ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp (B,0) hAC)
  have hpotD : HasFDerivAt (fun p : Parameters d V => potential p.1 (mass B h₀) p.2)
      (jointDerivative B h₀-offsetFunctional (mass B h₀)) (B,A (B,0)) := by
    simpa only [hA0] using hasFDerivAt_potential_joint B h₀ (mass B h₀) hB
  have hd := hpotD.comp (B,0)
    ((ContinuousLinearMap.fst ℝ (Rows d V) (centeredGauge V)).hasFDerivAt.prodMk hAC.differentiableAt_one.hasFDerivAt)
  have hcancel : (jointDerivative B h₀-offsetFunctional (mass B h₀)).comp
      ((ContinuousLinearMap.fst ℝ (Rows d V) (centeredGauge V)).prod (fderiv ℝ A (B,0))) =
      (rowDerivative B h₀).comp (ContinuousLinearMap.fst ℝ (Rows d V) (centeredGauge V)) := by
    apply ContinuousLinearMap.ext
    intro q
    exact potential_derivative_at_prescribed_mass B h₀ (mass B h₀) rfl (q.1,fderiv ℝ A (B,0) q)
  rw [hcancel] at hd
  have hauxi (i : V) : HasFDerivAt (fun q : JointCoordinates d V => (q.2 : V → ℝ) i*A q i)
      ((h₀ : V → ℝ) i • Z i) (B,0) := by
    have hZ : HasFDerivAt (fun q : JointCoordinates d V => (q.2 : V → ℝ) i) (Z i) (B,0) :=
      (Z i).hasFDerivAt
    have hAi := (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (B,0)
      hAC.differentiableAt_one.hasFDerivAt
    simpa only [hA0,Submodule.coe_zero,Pi.zero_apply,zero_smul,zero_add,
      ContinuousLinearMap.proj_apply,Function.comp_def,Pi.mul_def] using hZ.mul hAi
  have haux := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hauxi i)
  have hauxL : (∑ i, (h₀ : V → ℝ) i • Z i)=(offsetFunctional (d := d) h₀).comp parameterEmbedding := by
    apply ContinuousLinearMap.ext
    intro q
    simp [Z,offsetFunctional_apply]
  rw [hauxL] at haux
  have hderiv := hd.sub haux
  have hc := (hpot.sub hauxC).congr_of_eventuallyEq heq
  have hderiv' : HasFDerivAt (fun q : JointCoordinates d V =>
      potential q.1 (mass B h₀) (A q)-∑ i, (q.2 : V → ℝ) i*A q i)
      (jointValueDerivative B h₀) (B,0) := by
    simpa [Function.comp_def,jointValueDerivative,Pi.sub_def] using hderiv
  exact ⟨hc,hderiv'.congr_of_eventuallyEq heq⟩

end NegativeVotingFanJointValue
