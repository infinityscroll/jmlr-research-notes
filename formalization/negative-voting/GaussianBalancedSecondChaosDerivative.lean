import GaussianGlobalTensorTransport
import GaussianFanSelectedOffsets
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Second differentiation on the actual mass-balanced path. A vanishing
vertical gradient removes the need to assume an offset acceleration. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedSecondChaosDerivative

section ScalarPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vanishing differentiable functional may be paired with a merely
continuous vector. No derivative of the second factor is needed. -/
theorem hasDerivAt_clm_apply_zero (A : ℝ→E→L[ℝ] ℝ) (A' : E→L[ℝ] ℝ)
    (v : ℝ→E) (t : ℝ) (hA : HasDerivAt A A' t) (hzero : A t=0)
    (hv : ContinuousAt v t) : HasDerivAt (fun s=>A s (v s)) (A' (v t)) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hh := (isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=E) (F:=ℝ)).continuous.tendsto
    (A',v t) |>.comp (hA.tendsto_slope.prodMk_nhds (hv.mono_left nhdsWithin_le_nhds))
  convert hh using 1
  funext s
  simp only [Function.comp_apply,slope_def_module,hzero,zero_apply,sub_zero,smul_apply,smul_eq_mul]

end ScalarPath

open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingFanMassSecondDerivative NegativeVotingFanQuadraticMoments
  NegativeVotingCoherentLiftHessian NegativeVotingSecondChaosHessian
  NegativeVotingSecondChaosMassAdjoint NegativeVotingFanJointMass
  NegativeVotingFanSelectedOffsets NegativeVotingFanJointInverse NegativeVotingFanInverse
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingModern
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance parameterDualNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] ℝ) := inferInstance
local instance parameterDualSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] ℝ) := inferInstance

/-- A scalar mass correction frozen at the base point. -/
def frozenCorrectedEnergy (c : ι→ℝ) (p : Parameters d ι) : ℝ :=
  secondEnergy p.1 p.2-∑ i,c i*mass p.1 p.2 i

def frozenCorrectedGradient (c : ι→ℝ) (p : Parameters d ι) : Parameters d ι→L[ℝ] ℝ :=
  secondEnergyDerivative p.1 p.2-∑ i,c i • testedCellDerivative p.1 p.2 i (fun _=>1)

def frozenCorrectedHessian (c : ι→ℝ) (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  energyHessian B h L-∑ i,c i • constantHessian B h L i

theorem hasFDerivAt_frozenCorrectedEnergy (c : ι→ℝ) (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt (frozenCorrectedEnergy c) (frozenCorrectedGradient c (B,h)) (B,h) := by
  have hm := HasFDerivAt.fun_sum (u:=Finset.univ) fun i _=>
    (hasFDerivAt_mass_joint_component B h σ hσ hlower i).const_smul (c i)
  have hh := (hasFDerivAt_secondEnergy B h σ hσ hlower).sub hm
  simp_rw [jointMassDerivativeAt_eq_tested B h σ hσ hlower] at hh
  convert! hh using 1

theorem hasFDerivAt_frozenCorrectedGradient (c : ι→ℝ) (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    HasFDerivAt (frozenCorrectedGradient c) (frozenCorrectedHessian c B h L) (B,h) := by
  have he := hasFDerivAt_secondEnergyDerivative B h σ hσ hlower (Classical.arbitrary ι)
  dsimp only at he
  rw [←energyHessian_eq_canonical B h σ hσ hlower L hL (Classical.arbitrary ι)] at he
  have hm := HasFDerivAt.fun_sum (u:=Finset.univ) fun i _=>
    (hasFDerivAt_constantDerivative B h σ hσ hlower L hL i).const_smul (c i)
  convert! he.sub hm using 1

theorem frozenCorrectedGradient_eq_adjoint (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    frozenCorrectedGradient (massAdjoint B h) (B,h)=correctedDerivative B h := by
  apply ContinuousLinearMap.ext
  intro δ
  rw [correctedDerivative_apply]
  simp only [frozenCorrectedGradient,sub_apply,sum_apply,smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←jointMassDerivativeAt_eq_tested B h σ hσ hlower]
  rfl



/-- Actual second differentiation along a mass-preserving C1 offset curve.
Only its first derivative and continuity of that derivative are used. -/
theorem hasDerivAt_balanced_energy_deriv (B D : ι→FSC.Coord d) (a : ℝ→ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (ha : ContDiffAt ℝ 1 a 0)
    (hm : ∀ᶠ t in 𝓝 (0:ℝ),mass (B+t•D) (a t)=mass B (a 0))
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    HasDerivAt (deriv (fun t:ℝ=>secondEnergy (B+t•D) (a t)))
      (frozenCorrectedHessian (massAdjoint B (a 0)) B (a 0) L
        (D,deriv a 0) (D,deriv a 0)) 0 := by
  let c := massAdjoint B (a 0)
  let p : ℝ→Parameters d ι := fun t=>(B+t•D,a t)
  let v : ℝ→Parameters d ι := fun t=>(D,deriv a t)
  have hp0 : p 0=(B,a 0) := by simp [p]
  have hr (t : ℝ) : HasDerivAt (fun t:ℝ=>B+t•D) D t := by
    simpa using ((hasDerivAt_id t).smul_const D).const_add B
  have hpC : ContDiffAt ℝ 1 p 0 := (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).prodMk ha
  have hp : HasDerivAt p (v 0) 0 := (hr 0).prodMk ((ha.differentiableAt (by norm_num)).hasDerivAt)
  have hvc : ContinuousAt v 0 := continuousAt_const.prodMk
    ((ha.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const)
  have hgb : HasFDerivAt (frozenCorrectedGradient c) (frozenCorrectedHessian c B (a 0) L) (p 0) := by
    rw [hp0]
    exact hasFDerivAt_frozenCorrectedGradient c B (a 0) σ hσ hlower L hL
  have hg := hgb.comp_hasDerivAt (0:ℝ) hp
  have hg' : HasDerivAt (fun t=>frozenCorrectedGradient c (p t)-frozenCorrectedGradient c (p 0))
      (frozenCorrectedHessian c B (a 0) L (v 0)) 0 := by
    exact hg.sub_const _
  have hz := hasDerivAt_clm_apply_zero _ _ v 0 hg' (sub_self _) hvc
  have hadd := hz.add_const (frozenCorrectedGradient c (p 0) (D,0))
  have hzero (k : ι→ℝ) : frozenCorrectedGradient c (p 0) (0,k)=0 := by
    rw [hp0]
    change frozenCorrectedGradient (massAdjoint B (a 0)) (B,a 0) (0,k)=0
    rw [frozenCorrectedGradient_eq_adjoint B (a 0) σ hσ hlower]
    exact correctedDerivative_annihilates_offsets B (a 0) σ hσ hlower k
  have he (t : ℝ) :
      (frozenCorrectedGradient c (p t)-frozenCorrectedGradient c (p 0)) (v t)+
          frozenCorrectedGradient c (p 0) (D,0)=frozenCorrectedGradient c (p t) (v t) := by
    have hvform : v t=(D,0)+(0,deriv a t) := by simp [v]
    have hh : frozenCorrectedGradient c (p 0) (v t)=frozenCorrectedGradient c (p 0) (D,0) := by
      rw [hvform,map_add,hzero,add_zero]
    simp only [sub_apply,hh]
    ring
  have hgrad : HasDerivAt (fun t=>frozenCorrectedGradient c (p t) (v t))
      (frozenCorrectedHessian c B (a 0) L (v 0) (v 0)) 0 := by
    simpa only [he] using hadd
  have hlow : ∀ᶠ t in 𝓝 (0:ℝ),CenteredSingularLowerBound (p t).1 (σ/2) := by
    have hh := hpC.continuousAt.eventually
      (show ∀ᶠ q:Parameters d ι in 𝓝 (p 0),CenteredSingularLowerBound q.1 (σ/2) from
        hp0.symm ▸ eventually_centeredSingularLowerBound B (a 0) σ hσ hlower)
    exact hh
  have hd : deriv (fun t=>frozenCorrectedEnergy c (p t)) =ᶠ[𝓝 (0:ℝ)]
      fun t=>frozenCorrectedGradient c (p t) (v t) := by
    filter_upwards [hlow,ha.eventually (by norm_num)] with t ht hat
    exact ((hasFDerivAt_frozenCorrectedEnergy c (p t).1 (p t).2 (σ/2) (by positivity) ht).comp_hasDerivAt t
      ((hr t).prodMk ((hat.differentiableAt (by norm_num)).hasDerivAt))).deriv
  have hcorrected : HasDerivAt (deriv (fun t=>frozenCorrectedEnergy c (p t)))
      (frozenCorrectedHessian c B (a 0) L (v 0) (v 0)) 0 :=
    hgrad.congr_of_eventuallyEq hd
  have hmass : (fun t=>frozenCorrectedEnergy c (p t)) =ᶠ[𝓝 (0:ℝ)]
      fun t=>secondEnergy (B+t•D) (a t)-∑ i,c i*mass B (a 0) i := by
    filter_upwards [hm] with t ht
    simp only [frozenCorrectedEnergy,p,ht]
  have hder : deriv (fun t=>frozenCorrectedEnergy c (p t)) =ᶠ[𝓝 (0:ℝ)]
      deriv (fun t:ℝ=>secondEnergy (B+t•D) (a t)) := by
    filter_upwards [hmass.deriv,hlow,ha.eventually (by norm_num)] with t ht hlt hat
    rw [ht]
    have he : DifferentiableAt ℝ (fun t:ℝ=>secondEnergy (B+t•D) (a t)) t := by
      convert! ((hasFDerivAt_secondEnergy (p t).1 (p t).2 (σ/2) (by positivity) hlt).comp_hasDerivAt t
        ((hr t).prodMk ((hat.differentiableAt (by norm_num)).hasDerivAt))).differentiableAt using 1
    exact (he.hasDerivAt.sub_const _).deriv
  exact hcorrected.congr_of_eventuallyEq hder.symm



/-- The literal selected balanced offsets along a linear row path. -/
def selectedRowOffsets (B D : ι→FSC.Coord d) (p : ι→ℝ) (t : ℝ) : ι→ℝ :=
  (selectedOffsets (B+t•D) p : ι→ℝ)

theorem selectedRowOffsets_contDiffAt (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ContDiffAt ℝ 1 (selectedRowOffsets B D p) 0 := by
  have hc := selectedOffsets_joint_C1 B σ hσ hlower p hp hs
  have hr : ContDiffAt ℝ 1 (fun t:ℝ=>((B+t•D),(0:centeredGauge ι))) 0 :=
    (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).prodMk contDiffAt_const
  have hb : ((B+(0:ℝ)•D),(0:centeredGauge ι))=(B,0) := by simp
  have hc' : ContDiffAt ℝ 1 (fun q:JointCoordinates d ι=>
      selectedOffsets q.1 (p+(q.2:ι→ℝ))) ((B+(0:ℝ)•D),(0:centeredGauge ι)) := hb.symm ▸ hc
  have hh := (centeredGauge ι).subtypeL.contDiff.contDiffAt.comp (0:ℝ) (hc'.comp (0:ℝ) hr)
  convert! hh using 1
  all_goals simp only [Function.comp_def,Submodule.subtypeL_apply,Submodule.coe_zero,add_zero]
  rfl

theorem selectedRowOffsets_balanced (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ∀ᶠ t in 𝓝 (0:ℝ),mass (B+t•D) (selectedRowOffsets B D p t)=p := by
  have hc : ContinuousAt (fun t:ℝ=>(B+t•D,(0:ι→ℝ))) 0 := by fun_prop
  have he : ∀ᶠ q:Parameters d ι in 𝓝 (B+(0:ℝ)•D,(0:ι→ℝ)),
      CenteredSingularLowerBound q.1 (σ/2) := by
    simpa using eventually_centeredSingularLowerBound B (0:ι→ℝ) σ hσ hlower
  filter_upwards [hc.eventually he] with t ht
  apply selectedOffsets_mass
  · intro i j hij
    by_contra hne
    exact centered_singular_rows_ne (B+t•D) (σ/2) (by positivity) ht i j hne hij
  · exact hp
  · exact hs

/-- A C1 balanced centered offset curve has the already constructed canonical
first response. Its acceleration is neither supplied nor required. -/
theorem balanced_offset_deriv_eq_canonical (B D : ι→FSC.Coord d) (a : ℝ→ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (ha : ContDiffAt ℝ 1 a 0) (hcenter : ∀ t,∑ i,a t i=0)
    (hm : ∀ᶠ t in 𝓝 (0:ℝ),mass (B+t•D) (a t)=mass B (a 0)) :
    deriv a 0=NegativeVotingFanCanonicalOffset.canonicalOffsetVariation B (a 0) D := by
  have ha' := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    (ContinuousLinearMap.proj i : (ι→ℝ)→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 ha')
  have hs0 : HasDerivAt (fun t=>∑ i,a t i) 0 0 := by
    simpa only [hcenter] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hz : ∑ i,deriv a 0 i=0 := hs.unique hs0
  have hr : HasDerivAt (fun t:ℝ=>B+t•D) D 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const D).const_add B
  have hb : (B+(0:ℝ)•D,a 0)=(B,a 0) := by simp
  have hbase : HasFDerivAt (fun p:Parameters d ι=>mass p.1 p.2)
      (jointMassDerivative B (a 0)) (B+(0:ℝ)•D,a 0) :=
    hb.symm ▸ hasFDerivAt_mass_joint B (a 0) σ hσ hlower
  have hd := hbase.comp_hasDerivAt (0:ℝ) (hr.prodMk ha')
  have hconst : HasDerivAt (fun t:ℝ=>mass (B+t•D) (a t)) 0 0 :=
    (hasDerivAt_const (0:ℝ) (mass B (a 0))).congr_of_eventuallyEq hm
  have hv : jointMassDerivative B (a 0) (D,deriv a 0)=0 := hd.unique hconst
  apply NegativeVotingFanJointOffsets.centered_zero_mass_line_response B D (a 0) (deriv a 0) σ hσ hlower hz
  intro i
  have hoff : HasDerivAt (fun t:ℝ=>a 0+t•deriv a 0) (deriv a 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (deriv a 0)).const_add (a 0)
  have hbase' : HasFDerivAt (fun p:Parameters d ι=>mass p.1 p.2)
      (jointMassDerivative B (a 0)) (B+(0:ℝ)•D,a 0+(0:ℝ)•deriv a 0) := by
    simpa using hasFDerivAt_mass_joint B (a 0) σ hσ hlower
  have hline := hbase'.comp_hasDerivAt (0:ℝ) (hr.prodMk hoff)
  rw [hv] at hline
  convert! (ContinuousLinearMap.proj i : (ι→ℝ)→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hline using 1

/-- The actual selected balanced second-chaos energy is twice differentiable
along every linear row direction, with the full mass-adjoint correction and
canonical first offset response. No second derivative of selectedOffsets is
an assumption. -/
theorem hasDerivAt_selected_balanced_energy_deriv (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    let h : ι→ℝ := selectedOffsets B p
    let δ : Parameters d ι := (D,NegativeVotingFanCanonicalOffset.canonicalOffsetVariation B h D)
    HasDerivAt (deriv (fun t:ℝ=>secondEnergy (B+t•D) (selectedRowOffsets B D p t)))
      (frozenCorrectedHessian (massAdjoint B h) B h L δ δ) 0 := by
  dsimp only
  let a := selectedRowOffsets B D p
  have ha := selectedRowOffsets_contDiffAt B D σ hσ hlower p hp hs
  have hm := selectedRowOffsets_balanced B D σ hσ hlower p hp hs
  have hm0 : mass B (a 0)=p := by
    have hh := hm.self_of_nhds
    simpa only [zero_smul,add_zero,a] using hh
  have hm' : ∀ᶠ t in 𝓝 (0:ℝ),mass (B+t•D) (a t)=mass B (a 0) := by
    simpa only [hm0,a] using hm
  have hcenter (t : ℝ) : ∑ i,a t i=0 := (selectedOffsets (B+t•D) p).property
  have hv := balanced_offset_deriv_eq_canonical B D a σ hσ hlower ha hcenter hm'
  have hh := hasDerivAt_balanced_energy_deriv B D a σ hσ hlower ha hm' L hL
  rw [hv] at hh
  simpa only [a,selectedRowOffsets,zero_smul,add_zero] using hh



/-- The same endpoint for the literal Gaussian degree-two chaos energy of the
actual max-score allocation, rather than only its cell-moment expression. -/
theorem hasDerivAt_selected_actual_chaos_deriv (B D : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι→ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    let h : ι→ℝ := selectedOffsets B p
    let δ : Parameters d ι := (D,NegativeVotingFanCanonicalOffset.canonicalOffsetVariation B h D)
    HasDerivAt (deriv (fun t:ℝ=>chaosEnergy
      (fun x:Fin d→ℝ=>weights (B+t•D) (selectedRowOffsets B D p t)
        (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2))
      (frozenCorrectedHessian (massAdjoint B h) B h L δ δ) 0 := by
  have hd := hasDerivAt_selected_balanced_energy_deriv B D σ hσ hlower p hp hs L hL
  have hB : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hc : ContinuousAt (fun t:ℝ=>(B+t•D,(0:ι→ℝ))) 0 := by fun_prop
  have he : ∀ᶠ q:Parameters d ι in 𝓝 (B+(0:ℝ)•D,(0:ι→ℝ)),Function.Injective q.1 := by
    simpa using eventually_injective_rows B hB (0:ι→ℝ)
  have heq : (fun t:ℝ=>chaosEnergy
      (fun x:Fin d→ℝ=>weights (B+t•D) (selectedRowOffsets B D p t)
        (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2) =ᶠ[𝓝 (0:ℝ)]
      fun t=>secondEnergy (B+t•D) (selectedRowOffsets B D p t) := by
    filter_upwards [hc.eventually he] with t ht
    exact (secondEnergy_eq_actual_chaos _ ht _).symm
  exact hd.congr_of_eventuallyEq heq.deriv

end NegativeVotingBalancedSecondChaosDerivative
