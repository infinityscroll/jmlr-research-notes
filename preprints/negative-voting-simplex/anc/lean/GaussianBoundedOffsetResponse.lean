import GaussianBoundedRowGap
import GaussianFanSelectedOffsets

/-! Actual selected-offset response, with constants independent of the
row-system condition number. This is a full-rank differential step;
no differentiability of a singular selected offset is asserted. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology
namespace NegativeVotingBoundedOffsetResponse
open NegativeVotingBoundedRowGap NegativeVotingFan NegativeVotingFanJacobian
open NegativeVotingFanInverse NegativeVotingFanSelectedOffsets NegativeVotingAffineBasisLower
open NegativeVotingFanJointInverse NegativeVotingCapTail
variable {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V] {d:ℕ}

def massLine (p:V→ℝ) (v:centeredGauge V) (t:ℝ):V→ℝ:=p+t • (v:V→ℝ)
def offsetLine (b:AffineBasis V ℝ (FSC.Coord d)) (p:V→ℝ)
    (v:centeredGauge V) (t:ℝ):centeredGauge V:=selectedOffsets b (massLine p v t)

theorem massLine_sum (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1) (t:ℝ):
    ∑i,massLine p v t i=1:=by
  have hv:∑i,(v:V→ℝ) i=0:=v.property
  simp only [massLine,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,←Finset.mul_sum,hv,hp,mul_zero,add_zero]

theorem offsetLine_C1 (b:AffineBasis V ℝ (FSC.Coord d)) (p:V→ℝ)
    (v:centeredGauge V) (hp:∑i,p i=1) (t:ℝ) (hpos:∀i,0< massLine p v t i):
    ContDiffAt ℝ 1 (offsetLine b p v) t:=by
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have hh:=selectedOffsets_joint_C1 b σ hσ hlower (massLine p v t) hpos (massLine_sum p v hp t)
  have hq:ContDiffAt ℝ 1 (fun s:ℝ=>((b:V→FSC.Coord d),(s-t) • v)) t:=by fun_prop
  have hh':ContDiffAt ℝ 1 (fun q:JointCoordinates d V=>
      selectedOffsets q.1 (massLine p v t+(q.2:V→ℝ)))
      (b,(t-t) • v):=by simpa only [sub_self,zero_smul] using hh
  have ht:=hh'.comp t hq
  have he (s:ℝ):massLine p v s=massLine p v t+(((s-t) • v:centeredGauge V):V→ℝ):=by
    funext i
    change p i+s*(v:V→ℝ) i=p i+t*(v:V→ℝ) i+(s-t)*(v:V→ℝ) i
    ring
  change ContDiffAt ℝ 1 (fun s:ℝ=>selectedOffsets b (massLine p v s)) t
  simpa only [Function.comp_def,←he] using ht

theorem offsetLine_jacobian_response (b:AffineBasis V ℝ (FSC.Coord d))
    (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1)
    (t:ℝ) (hpos:∀i,0< massLine p v t i):
    offsetJacobian b (offsetLine b p v t) *ᵥ ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)=v:=by
  classical
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have hC:=offsetLine_C1 b p v hp t hpos
  have hd:HasDerivAt (offsetLine b p v) (deriv (offsetLine b p v) t) t:=
    (hC.differentiableAt (by norm_num)).hasDerivAt
  have hD:HasDerivAt (fun s:ℝ=>(offsetLine b p v s:V→ℝ))
      ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ) t:=
    (centeredGauge V).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
  have hnear:∀ᶠs:ℝ in 𝓝 t,∀i,0< massLine p v s i:=by
    apply eventually_all.mpr
    intro i
    have hc:ContinuousAt (fun s:ℝ=>massLine p v s i) t:=by unfold massLine;fun_prop
    exact hc.eventually (Ioi_mem_nhds (hpos i))
  ext i
  have hc:HasDerivAt (fun s:ℝ=>mass b (offsetLine b p v s) i)
      (NegativeVotingFanJacobian.massDerivative b (offsetLine b p v t) i
        ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)) t:=by
    simpa only [Function.comp_def] using
      (hasFDerivAt_mass b σ hσ hlower (offsetLine b p v t) i).comp_hasDerivAt t hD
  have hc':HasDerivAt (fun s:ℝ=>p i+s*(v:V→ℝ) i)
      (NegativeVotingFanJacobian.massDerivative b (offsetLine b p v t) i
        ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)) t:=by
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with s hs
    rw [offsetLine,selectedOffsets_mass b b.ind.injective (massLine p v s) hs (massLine_sum p v hp s)]
    rfl
  have hs:HasDerivAt (fun s:ℝ=>p i+s*(v:V→ℝ) i) ((v:V→ℝ) i) t:=by
    simpa using ((hasDerivAt_id t).mul_const ((v:V→ℝ) i)).const_add (p i)
  have he:=hc'.unique hs
  rw [NegativeVotingFanJacobian.massDerivative_apply b σ hσ hlower] at he
  simpa only [offsetJacobian_mulVec] using he

/-- The bound is for the actual response solving the Gaussian Jacobian,
not for an assumed inverse operator. -/
theorem inverse_pairing_bound (b:AffineBasis V ℝ (FSC.Coord d)) (h:V→ℝ)
    (m:ℝ) (hm:1≤ m)
    (hmass:∀i,1/(2*m)≤ mass b h i∧mass b h i≤(3/2)/m)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log m)/m)
    (u v:V→ℝ) (hu:∑i,u i=0) (hJ:offsetJacobian b h *ᵥ u=v):
    u ⬝ᵥ v≤(32768*Real.pi^2*(1+Real.log m))*(∑i,(v i)^2):=by
  let K:ℝ:=32768*Real.pi^2*(1+Real.log m)
  have hK:0< K:=by dsimp [K];positivity [Real.log_nonneg hm]
  have hg:=uniform_box_rayleigh b h m hm hmass hB u hu
  rw [hJ] at hg
  change (1/K)*(∑i,(u i)^2)≤ u ⬝ᵥ v at hg
  have hE:0≤ u ⬝ᵥ v:= (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _=>sq_nonneg _))).trans hg
  have hSu: (∑i,(u i)^2)≤ K*(u ⬝ᵥ v):=by
    have hh:=mul_le_mul_of_nonneg_left hg hK.le
    simpa only [←mul_assoc,mul_one_div_cancel hK.ne',one_mul] using hh
  have hC:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  change (u ⬝ᵥ v)^2≤(∑i,(u i)^2)*(∑i,(v i)^2) at hC
  have hh:=mul_le_mul_of_nonneg_right hSu (show 0≤∑i,(v i)^2 from Finset.sum_nonneg (fun i _=>sq_nonneg (v i)))
  by_cases hz:u ⬝ᵥ v=0
  · rw [hz]
    exact mul_nonneg hK.le (Finset.sum_nonneg (fun i _=>sq_nonneg _))
  · have hEp:0< u ⬝ᵥ v:=lt_of_le_of_ne hE (Ne.symm hz)
    have ht:(u ⬝ᵥ v)*(u ⬝ᵥ v)≤(K*(∑i,(v i)^2))*(u ⬝ᵥ v):=by nlinarith
    exact (mul_le_mul_iff_right₀ hEp).mp (by simpa only [K,mul_comm] using ht)

/-- The genuine selected mass-offset curve satisfies the uniform response
bound at every point of the balanced mass box. -/
theorem offsetLine_pairing_bound (b:AffineBasis V ℝ (FSC.Coord d))
    (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1) (m:ℝ) (hm:1≤ m)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log m)/m) (t:ℝ)
    (hbox:∀i,1/(2*m)≤ massLine p v t i∧massLine p v t i≤(3/2)/m):
    (((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ) ⬝ᵥ (v:V→ℝ))≤
      (32768*Real.pi^2*(1+Real.log m))*(∑i,((v:V→ℝ) i)^2):=by
  have hpos:∀i,0< massLine p v t i:=fun i=>lt_of_lt_of_le (by positivity) (hbox i).1
  have hmass:∀i,1/(2*m)≤ mass b (offsetLine b p v t) i∧
      mass b (offsetLine b p v t) i≤(3/2)/m:=by
    intro i
    rw [offsetLine,selectedOffsets_mass b b.ind.injective _ hpos (massLine_sum p v hp t)]
    exact hbox i
  exact inverse_pairing_bound b (offsetLine b p v t) m hm hmass hB
    ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ) v
    (deriv (offsetLine b p v) t).property (offsetLine_jacobian_response b p v hp t hpos)

end NegativeVotingBoundedOffsetResponse
