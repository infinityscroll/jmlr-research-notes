import GaussianFanValueDerivative

/-! Actual jointly smooth offsets for simultaneous row and mass perturbations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix
namespace NegativeVotingFanJointOffsets
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanInverse
  NegativeVotingFanJointInverse NegativeVotingFanJointMass NegativeVotingFanEnvelope
  NegativeVotingFanCanonicalOffset NegativeVotingFanOffsetMinimization
  NegativeVotingFanPseudoInverse NegativeVotingFanJacobian NegativeVotingCapTail
  NegativeVotingFacetDegree
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The actual local inverse supplies offsets for all row and centered mass
parameters simultaneously, on an open neighborhood of their actual base. -/
theorem exists_joint_C1_offsets (B : V → FSC.Coord d) (h₀ : centeredGauge V)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∃ a : JointCoordinates d V → centeredGauge V,
      a (B,0)=h₀ ∧ ContDiffAt ℝ 1 a (B,0) ∧
      ∀ᶠ q in 𝓝 (B,(0:centeredGauge V)),
        mass q.1 (a q)=mass B h₀+(q.2 : V → ℝ) := by
  obtain ⟨e,he,hsource,hC,_⟩ := exists_local_C1_joint_mass_inverse B h₀ σ hσ hlower
  let q₀ := centeredMass B h₀
  let shift : JointCoordinates d V → JointCoordinates d V := fun q => (q.1,q₀+q.2)
  let a : JointCoordinates d V → centeredGauge V := fun q => (e.symm (shift q)).2
  have hpoint : jointMassCoordinates (B,h₀)=(B,q₀) := rfl
  rw [hpoint] at hC
  have hs : shift (B,0)=(B,q₀) := by simp [shift]
  have hshift : ContDiffAt ℝ 1 shift (B,0) :=
    contDiffAt_fst.prodMk (contDiffAt_const.add contDiffAt_snd)
  have hchart : ContDiffAt ℝ 1 e.symm (shift (B,0)) := by simpa only [hs] using hC
  have ha : ContDiffAt ℝ 1 a (B,0) := contDiffAt_snd.comp (B,0) (hchart.comp (B,0) hshift)
  have hbase : e.symm (B,q₀)=(B,h₀) := by
    have ht := e.left_inv hsource
    rwa [he,hpoint] at ht
  have htarget : (B,q₀) ∈ e.target := by
    have ht := e.map_source hsource
    rwa [he,hpoint] at ht
  have htarget' : shift (B,0) ∈ e.target := by rwa [hs]
  have hnear : ∀ᶠ q in 𝓝 (B,(0:centeredGauge V)), shift q ∈ e.target :=
    hshift.continuousAt.eventually (e.open_target.mem_nhds htarget')
  refine ⟨a,?_,ha,?_⟩
  · change (e.symm (shift (B,0))).2=h₀
    rw [hs,hbase]
  · filter_upwards [hnear] with q hq
    have hm := (joint_chart_inverse_realizes e he (shift q) hq).2
    change mass q.1 ((e.symm (shift q)).2 : V → ℝ)=_
    rw [hm]
    funext i
    simp only [shift,Prod.fst,Prod.snd,Submodule.coe_add,Pi.add_apply,q₀,centeredMass_apply]
    ring

/-- The ordinary derivative of the actual mass line is its Jacobian row
response plus its offset response. -/
theorem mass_line_derivative_eq (B D : V → FSC.Coord d) (h v u : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) (u i) 0) :
    offsetJacobian B h *ᵥ v=u-rowMassVariation B h D := by
  funext i
  have hd := hasDerivAt_mass_line B D h v σ hσ hlower i
  have he := hd.unique (hm i)
  rw [massVariation_add_offsets B D h v σ hσ hlower] at he
  change (offsetJacobian B h *ᵥ v) i=u i-rowMassVariation B h D i
  linarith

/-- The full actual first offset response, with no inverse-response assumption. -/
theorem centered_mass_line_response (B D : V → FSC.Coord d) (h v u : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hv : ∑ i, v i=0)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) (u i) 0) :
    v=(offsetJacobian B h).covariancePseudoInverse *ᵥ (u-rowMassVariation B h D) := by
  have hB : AffineIndependent ℝ B := affineIndependent_of_centered_lower B σ hσ hlower
  have he := mass_line_derivative_eq B D h v u σ hσ hlower hm
  rw [← he,Matrix.mulVec_mulVec,pseudoinverse_mul_offsetJacobian B hB h,
    centeringMatrix_mulVec]
  ext i
  simp [centering_apply,hv]

/-- The centered actual mass-preserving tangent is the canonical minimizer,
including its value rather than merely its surface energy. -/
theorem centered_zero_mass_line_response (B D : V → FSC.Coord d) (h v : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hv : ∑ i, v i=0)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    v=canonicalOffsetVariation B h D := by
  exact (canonicalOffset_unique_centered B D h σ hσ hlower v hv).mp
    (mass_preserving_offset_value_eq_canonical B D h v σ hσ hlower hm)

/-- Actual joint row/mass curves inherit a constructed C1 centered offset curve. -/
theorem exists_C1_offsets_along_rows_masses (R : ℝ → V → FSC.Coord d) (p : ℝ → V → ℝ)
    (h₀ : centeredGauge V) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound (R 0) σ)
    (hR : ContDiffAt ℝ 1 R 0) (hp : ContDiffAt ℝ 1 p 0)
    (hm0 : mass (R 0) h₀=p 0) (hs : ∀ᶠ t in 𝓝 (0:ℝ), ∑ i, p t i=1) :
    ∃ a : ℝ → V → ℝ, a 0=(h₀ : V → ℝ) ∧ ContDiffAt ℝ 1 a 0 ∧
      (∀ t, ∑ i, a t i=0) ∧ ∀ᶠ t in 𝓝 (0:ℝ), mass (R t) (a t)=p t := by
  obtain ⟨A,hA0,hAC,hAm⟩ := exists_joint_C1_offsets (R 0) h₀ σ hσ hlower
  let q : ℝ → JointCoordinates d V := fun t => (R t,centering (p t-p 0))
  have hq0 : q 0=(R 0,0) := by simp [q]
  have hq2 : ContDiffAt ℝ 1 (fun t : ℝ => centering (p t-p 0)) 0 := by
    simpa only [Function.comp_def] using
      ((centering : (V → ℝ) →L[ℝ] centeredGauge V).contDiff.contDiffAt.comp 0
        (hp.sub (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => p 0) 0)))
  have hq : ContDiffAt ℝ 1 q 0 := hR.prodMk hq2
  let a : ℝ → V → ℝ := fun t => (A (q t) : V → ℝ)
  have hC : ContDiffAt ℝ 1 A (q 0) := by simpa only [hq0] using hAC
  have ha : ContDiffAt ℝ 1 a 0 :=
    (centeredGauge V).subtypeL.contDiff.contDiffAt.comp 0 (hC.comp 0 hq)
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), mass (q t).1 (A (q t))=
      mass (R 0) h₀+((q t).2 : V → ℝ) := by
    have he : ∀ᶠ x in 𝓝 (q 0), mass x.1 (A x)=mass (R 0) h₀+(x.2 : V → ℝ) := by
      simpa only [hq0] using hAm
    exact hq.continuousAt.eventually he
  refine ⟨a,?_,ha,?_,?_⟩
  · simp [a,hq0,hA0]
  · intro t
    exact (A (q t)).property
  · filter_upwards [hnear,hs] with t ht hst
    change mass (R t) (a t)=mass (R 0) h₀+(centering (p t-p 0) : V → ℝ) at ht
    have hs0 : ∑ i, p 0 i=1 := by rw [← hm0]; exact mass_sum _ _
    rw [ht,hm0]
    funext i
    simp [centering_apply,Finset.sum_sub_distrib,hst,hs0]

/-- Centering fixes the actual covariance offset derivative, with the exact
factor one half required by the covariance square-root clock. -/
theorem covariance_offset_response (B : V → FSC.Coord d) (h p : V → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (S : ℝ → FSC.Coord d →L[ℝ] FSC.Coord d) (a : ℝ → V → ℝ) (v : V → ℝ)
    (hS0 : S 0=ContinuousLinearMap.id ℝ (FSC.Coord d)) (ha0 : a 0=h)
    (hS1 : HasDerivAt S ((1/2:ℝ)•H) 0) (ha : HasDerivAt a v 0)
    (hcenter : ∀ t, ∑ i, a t i=0)
    (hm : ∀ᶠ t in 𝓝 (0:ℝ), mass (NegativeVotingFanCovarianceEnvelope.rowsOfOperator B (S t)) (a t)=p) :
    v=(1/2:ℝ)•canonicalOffsetVariation B h (NegativeVotingFanCovarianceEnvelope.rowsOfOperator B H) := by
  have hd : HasDerivAt (fun t : ℝ => ∑ i, a t i) (∑ i, v i) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => by
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 ha)
  have hz : HasDerivAt (fun t : ℝ => ∑ i, a t i) 0 0 := by
    simpa only [hcenter] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hv := hd.unique hz
  have hv2 : ∑ i, ((2:ℝ)•v) i=0 := by
    simp [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hv]
  have hline := NegativeVotingFanCovarianceEnvelope.covariance_mass_derivatives_zero
    B h p σ hσ hlower H S a v hS0 ha0 hS1 ha hm
  have he := centered_zero_mass_line_response B _ h ((2:ℝ)•v) σ hσ hlower hv2 hline
  funext i
  have hh := congrFun he i
  simp only [Pi.smul_apply,smul_eq_mul] at hh ⊢
  linarith

end NegativeVotingFanJointOffsets
