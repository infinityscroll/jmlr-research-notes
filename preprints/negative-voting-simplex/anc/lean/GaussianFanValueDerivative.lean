import GaussianFanCovarianceHessian

/-! Actual C1 optimized value in the row variables and its envelope derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanValueDerivative
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanGradient
  NegativeVotingFanEnvelope NegativeVotingFanHessian NegativeVotingFanInverse
  NegativeVotingFanJointMass NegativeVotingFanJointInverse NegativeVotingFanValue
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingFanCentroid
  NegativeVotingFanCovarianceEnvelope
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem contDiffAt_expectedMax_joint (B : Rows d ι) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun q : Parameters d ι => expectedMax q.1 q.2) (B,h) := by
  have hh : 0 < σ/2 := by positivity
  apply contDiffAt_one_iff.mpr
  refine ⟨fun q => jointDerivative q.1 q.2,
    {q : Parameters d ι | CenteredSingularLowerBound q.1 (σ/2)},
    eventually_centeredSingularLowerBound B h σ hσ hlower, ?_, ?_⟩
  · intro q hq
    exact (hasFDerivAt_jointGradient q.1 q.2 (σ/2) hh hq).continuousAt.continuousWithinAt
  · intro q hq
    apply hasFDerivAt_expectedMax_joint
    intro i j he
    by_contra hij
    exact centered_singular_rows_ne q.1 (σ/2) hh hq i j hij he

theorem contDiffAt_potential_joint (B : Rows d ι) (h p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun q : Parameters d ι => potential q.1 p q.2) (B,h) := by
  have hc := (contDiffAt_expectedMax_joint B h σ hσ hlower).sub
    (offsetFunctional (d := d) p).contDiff.contDiffAt
  change ContDiffAt ℝ 1 (fun q : Parameters d ι => expectedMax q.1 q.2 - offsetFunctional p q) (B,h) at hc
  simpa only [potential,offsetFunctional_apply] using hc

/-- An actual local offset function on the full row parameter space. -/
theorem exists_C1_offsets_as_rows (B : Rows d ι) (h₀ : centeredGauge ι)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∃ a : Rows d ι → ι → ℝ, a B = (h₀ : ι → ℝ) ∧ ContDiffAt ℝ 1 a B ∧
      (∀ C, ∑ i, a C i = 0) ∧ ∀ᶠ C in 𝓝 B, mass C (a C) = mass B h₀ := by
  obtain ⟨e,he,hsource,hc,_⟩ := exists_local_C1_joint_mass_inverse B h₀ σ hσ hlower
  let q : centeredGauge ι := centeredMass B h₀
  have hpoint : jointMassCoordinates (B,h₀) = (B,q) := rfl
  rw [hpoint] at hc
  let a : Rows d ι → ι → ℝ := fun C => ((e.symm (C,q)).2 : ι → ℝ)
  have hin : ContDiffAt ℝ 1 (fun C : Rows d ι => (C,q)) B := contDiffAt_id.prodMk contDiffAt_const
  have hcurve : ContDiffAt ℝ 1 (fun C : Rows d ι => e.symm (C,q)) B := hc.comp B hin
  have ha : ContDiffAt ℝ 1 a B :=
    (centeredGauge ι).subtypeL.contDiff.contDiffAt.comp B (contDiffAt_snd.comp B hcurve)
  have hbase : e.symm (B,q) = (B,h₀) := by
    have ht := e.left_inv hsource
    rw [he,hpoint] at ht
    exact ht
  have htarget : (B,q) ∈ e.target := by
    have ht := e.map_source hsource
    rwa [he,hpoint] at ht
  have hnear : ∀ᶠ C : Rows d ι in 𝓝 B, (C,q) ∈ e.target :=
    hin.continuousAt.eventually (e.open_target.mem_nhds htarget)
  refine ⟨a,?_,ha,?_,?_⟩
  · change ((e.symm (B,q)).2 : ι → ℝ) = (h₀ : ι → ℝ)
    rw [hbase]
  · intro C
    exact (e.symm (C,q)).2.property
  · filter_upwards [hnear] with C hC
    have hm := (joint_chart_inverse_realizes e he (C,q) hC).2
    simpa only [Prod.fst,Prod.snd,q,centeredMass_apply,sub_add_cancel] using hm

def rowDerivative (B : Rows d ι) (h : ι → ℝ) : Rows d ι →L[ℝ] ℝ :=
  (jointDerivative B h).comp rowLift

theorem rowDerivative_apply (B D : Rows d ι) (h : ι → ℝ) :
    rowDerivative B h D = ∑ i, inner ℝ (D i) (centroid B h i) := by
  simp [rowDerivative, jointDerivative_apply]

/-- The true optimized infimum is C1 in all row variables and its derivative
is the actual Gaussian centroid pairing. -/
theorem optimizedValue_C1_and_derivative (B : Rows d ι) (p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (h₀ : centeredGauge ι)
    (hm : mass B h₀ = p) :
    ContDiffAt ℝ 1 (fun C : Rows d ι => optimizedValue C p) B ∧
      HasFDerivAt (fun C : Rows d ι => optimizedValue C p) (rowDerivative B h₀) B := by
  obtain ⟨a,ha0,haC1,hacenter,ham⟩ := exists_C1_offsets_as_rows B h₀ σ hσ hlower
  have hQ : ContDiffAt ℝ 1 (fun C : Rows d ι => (C,a C)) B := contDiffAt_id.prodMk haC1
  have hnear : ∀ᶠ C : Rows d ι in 𝓝 B, CenteredSingularLowerBound C (σ/2) :=
    hQ.continuousAt.tendsto.eventually (by
      simpa only [ha0] using eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  have heq : (fun C : Rows d ι => optimizedValue C p) =ᶠ[𝓝 B]
      (fun C : Rows d ι => potential C p (a C)) := by
    filter_upwards [hnear,ham] with C hC hmC
    exact optimizedValue_eq_of_mass C p (σ/2) (by positivity) hC hp hs ⟨a C,hacenter C⟩ (hmC.trans hm)
  have hpot : ContDiffAt ℝ 1 (fun q : Parameters d ι => potential q.1 p q.2) (B,a B) := by
    simpa only [ha0] using contDiffAt_potential_joint B h₀ p σ hσ hlower
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hpotD : HasFDerivAt (fun q : Parameters d ι => potential q.1 p q.2)
      (jointDerivative B h₀ - offsetFunctional p) (B,a B) := by
    simpa only [ha0] using hasFDerivAt_potential_joint B h₀ p hB
  have hD := hpotD.comp B ((hasFDerivAt_id B).prodMk haC1.differentiableAt_one.hasFDerivAt)
  have hCLM : (jointDerivative B h₀ - offsetFunctional p).comp
      ((ContinuousLinearMap.id ℝ (Rows d ι)).prod (fderiv ℝ a B)) = rowDerivative B h₀ := by
    ext D
    exact potential_derivative_at_prescribed_mass B h₀ p hm (D,fderiv ℝ a B D)
  rw [hCLM] at hD
  have hC1 : ContDiffAt ℝ 1 (fun C : Rows d ι => potential C p (a C)) B := by
    simpa only [Function.comp_def] using
      (ContDiffAt.comp (g := fun q : Parameters d ι => potential q.1 p q.2)
        (f := fun C : Rows d ι => (C,a C)) B hpot hQ)
  have hD' : HasFDerivAt (fun C : Rows d ι => potential C p (a C)) (rowDerivative B h₀) B := by
    simpa only [Function.comp_def, id_eq] using hD
  exact ⟨hC1.congr_of_eventuallyEq heq,hD'.congr_of_eventuallyEq heq⟩

/-- The exact first Price/envelope pairing, including the ordered-edge factor. -/
theorem covariance_first_derivative_value (B : Rows d ι) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) :
    rowDerivative B h (rowsOfOperator B ((1/2:ℝ) • H)) =
      (1/4:ℝ) * ∑ i, ∑ j, NegativeVotingFanJacobian.facetWeight B h i j *
        inner ℝ (B i-B j) (H (B i-B j)) := by
  rw [rowDerivative_apply]
  simp only [rowsOfOperator_apply, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  have he : (∑ i, inner ℝ (H (B i)) (centroid B h i)) =
      ∑ i, inner ℝ (centroid B h i) (H (B i)) :=
    Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)
  have hs := centroid_linear_pairing B h σ hσ hlower H.toLinearMap
  change (∑ i, inner ℝ (centroid B h i) (H (B i))) =
    (1/2:ℝ) * ∑ i, ∑ j, NegativeVotingFanJacobian.facetWeight B h i j *
      inner ℝ (B i-B j) (H (B i-B j)) at hs
  rw [← Finset.mul_sum,he,hs]
  ring

end NegativeVotingFanValueDerivative
