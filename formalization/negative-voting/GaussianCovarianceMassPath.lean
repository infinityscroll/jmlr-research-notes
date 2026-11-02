import GaussianCovarianceOptimizerLipschitz
import GaussianValueSemiconcavity
import GaussianFanMassConcavity
import GaussianCovarianceMixedNeighborhood

/-! The actual covariance objective along a centered prescribed-mass line,
including its genuine C2 regularity and exact offset mass derivative. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingCovarianceMassPath
open NegativeVotingCovarianceOptimizerLipschitz NegativeVotingCovarianceJointValueC2
  NegativeVotingValueSemiconcavity NegativeVotingOptimizerStability
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingCovarianceCoercivity NegativeVotingPositiveCovariance
  NegativeVotingLocalCovarianceFactor NegativeVotingFanInverse
  NegativeVotingCovarianceOffsets NegativeVotingFanMassValueGradient
  NegativeVotingFanMassConcavity NegativeVotingCovarianceMixedNeighborhood
variable {m d:ℕ} [NeZero m]

def pathValue (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (v:centeredGauge (Fin m)) (z:SymmetricOperators (FSC.Coord d)×ℝ):ℝ :=
  operatorValue b (p+z.2 • (v:Fin m→ℝ)) z.1

def pathObjective (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (v:centeredGauge (Fin m)) (z:SymmetricOperators (FSC.Coord d)×ℝ):ℝ :=
  2*pathValue b p v z-operatorTrace (z.1:FSC.Coord d→L[ℝ]FSC.Coord d)

def pathOffsets (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (v:centeredGauge (Fin m)) (z:SymmetricOperators (FSC.Coord d)×ℝ):centeredGauge (Fin m) :=
  operatorOffsets b (p+z.2 • (v:Fin m→ℝ)) z.1

theorem path_mass_sum (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m)) (t:ℝ) :
    ∑i,(p+t • (v:Fin m→ℝ)) i=1 := by
  have hv:∑i,(v:Fin m→ℝ) i=0:=v.property
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ←Finset.mul_sum,hs,hv,mul_zero,add_zero]

theorem pathValue_C2 (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 2 (pathValue b p v) (C,t) := by
  let q:=p+t • (v:Fin m→ℝ)
  let Q:SymmetricOperators (FSC.Coord d)×ℝ→
      SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m):=fun z=>(z.1,(z.2-t) • v)
  have hQ:ContDiffAt ℝ 2 Q (C,t):=contDiffAt_fst.prodMk
    ((contDiffAt_snd.sub contDiffAt_const).smul contDiffAt_const)
  have hQ0:Q (C,t)=(C,0):=by simp [Q]
  have hc:ContDiffAt ℝ 2
      (fun z:SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)=>
        operatorValue b (q+(z.2:Fin m→ℝ)) z.1) (Q (C,t)):=by
    rw [hQ0]
    exact operatorValue_joint_C2 b q hp (path_mass_sum p hs v t) C hC
  have he (s:ℝ):q+(s-t) • (v:Fin m→ℝ)=p+s • (v:Fin m→ℝ):=by dsimp [q];module
  have hh:=hc.comp (f:=Q) (C,t) hQ
  change ContDiffAt ℝ 2 (fun z:SymmetricOperators (FSC.Coord d)×ℝ=>
    operatorValue b (p+z.2 • (v:Fin m→ℝ)) z.1) (C,t)
  simpa only [Function.comp_def,Q,Submodule.coe_smul,he] using hh

theorem pathObjective_C2 (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 2 (pathObjective b p v) (C,t) := by
  have htr:ContDiffAt ℝ 2
      (fun z:SymmetricOperators (FSC.Coord d)×ℝ=>operatorTrace
        (z.1:FSC.Coord d→L[ℝ]FSC.Coord d)) (C,t):=
    (traceFunctional d).contDiff.contDiffAt.comp (C,t)
      ((selfAdjoint.submodule ℝ (FSC.Coord d→L[ℝ]FSC.Coord d)).subtypeL.contDiff.contDiffAt.comp (C,t) contDiffAt_fst)
  exact (contDiffAt_const.mul (pathValue_C2 b p hs v C t hp hC)).sub htr

theorem pathOffsets_C1 (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 1 (pathOffsets b p v) (C,t) := by
  let q:=p+t • (v:Fin m→ℝ)
  let Q:SymmetricOperators (FSC.Coord d)×ℝ→
      SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m):=fun z=>(z.1,(z.2-t) • v)
  have hQ:ContDiffAt ℝ 1 Q (C,t):=contDiffAt_fst.prodMk
    ((contDiffAt_snd.sub contDiffAt_const).smul contDiffAt_const)
  have hQ0:Q (C,t)=(C,0):=by simp [Q]
  have hc:ContDiffAt ℝ 1
      (fun z:SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)=>
        operatorOffsets b (q+(z.2:Fin m→ℝ)) z.1) (Q (C,t)):=by
    rw [hQ0]
    exact operatorOffsets_joint_C1 b q hp (path_mass_sum p hs v t) C hC
  have he (s:ℝ):q+(s-t) • (v:Fin m→ℝ)=p+s • (v:Fin m→ℝ):=by dsimp [q];module
  have hh:=hc.comp (f:=Q) (C,t) hQ
  change ContDiffAt ℝ 1 (fun z:SymmetricOperators (FSC.Coord d)×ℝ=>
    operatorOffsets b (p+z.2 • (v:Fin m→ℝ)) z.1) (C,t)
  simpa only [Function.comp_def,Q,Submodule.coe_smul,he] using hh

theorem path_time_derivative (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    HasDerivAt (fun s:ℝ=>pathObjective b p v (C,s))
      (-2*∑i,(operatorOffsets b (p+t • (v:Fin m→ℝ)) C:Fin m→ℝ) i*(v:Fin m→ℝ) i) t := by
  have hd:=hasFDerivAt_operatorValue_mass b p hs (t • v) hp C hC
  have hl:HasDerivAt (fun s:ℝ=>s • v) v t:=by
    simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const v
  have hΓ:HasDerivAt (fun s:ℝ=>pathValue b p v (C,s))
      (-∑i,(operatorOffsets b (p+t • (v:Fin m→ℝ)) C:Fin m→ℝ) i*(v:Fin m→ℝ) i) t:=by
    simpa only [Function.comp_def,Submodule.coe_smul,massDerivative_apply,pathValue] using hd.comp_hasDerivAt t hl
  simpa only [pathObjective,mul_neg,neg_mul] using
    ((hΓ.const_mul 2).sub_const (operatorTrace (C:FSC.Coord d→L[ℝ]FSC.Coord d)))

theorem objective_hessian_diagonal (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone)
    (w:SymmetricOperators (FSC.Coord d)×ℝ) :
    fullHessian (pathObjective b p v) (C,t) w w=
      2*fullHessian (pathValue b p v) (C,t) w w := by
  have hΓ0:ContDiffAt ℝ 2 (pathValue b p v) ((C,t)+(0:ℝ) • w):=by
    simpa only [zero_smul,add_zero] using pathValue_C2 b p hs v C t hp hC
  have hF0:ContDiffAt ℝ 2 (pathObjective b p v) ((C,t)+(0:ℝ) • w):=by
    simpa only [zero_smul,add_zero] using pathObjective_C2 b p hs v C t hp hC
  have hL:ContDiffAt ℝ 2 (fun s:ℝ=>(C,t)+s • w) 0:=by fun_prop
  have hΓLine:=hΓ0.comp (f:=fun s:ℝ=>(C,t)+s • w) 0 hL
  have hf:∀ᶠ s in 𝓝 (0:ℝ),DifferentiableAt ℝ (fun u:ℝ=>pathValue b p v ((C,t)+u • w)) s:=
    (hΓLine.eventually (by norm_num)).mono (fun s hh=>(hh.of_le (m:=1) (by norm_num)).differentiableAt_one)
  have hΓ2:=line_second (pathValue b p v) (C,t) w 0 hΓ0
  have hF2:=line_second (pathObjective b p v) (C,t) w 0 hF0
  have hpen:=NegativeVotingOptimizerStability.line_second_affine_penalty
    (a:=2) (b:=operatorTrace (C:FSC.Coord d→L[ℝ]FSC.Coord d))
    (c:=operatorTrace (w.1:FSC.Coord d→L[ℝ]FSC.Coord d)) hf hΓ2
  have heq:(fun s:ℝ=>pathObjective b p v ((C,t)+s • w))=
      (fun s:ℝ=>2*pathValue b p v ((C,t)+s • w)-
        (operatorTrace (C:FSC.Coord d→L[ℝ]FSC.Coord d)+s*operatorTrace (w.1:FSC.Coord d→L[ℝ]FSC.Coord d))) := by
    funext s
    change 2*pathValue b p v ((C,t)+s • w)-traceFunctional d
      ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (w.1:FSC.Coord d→L[ℝ]FSC.Coord d))=_
    simp [map_add,map_smul,smul_eq_mul]
  rw [heq] at hF2
  simpa only [zero_smul,add_zero] using hF2.unique hpen

theorem objective_state_hessian (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone)
    (D:SymmetricOperators (FSC.Coord d)) :
    fullHessian (pathObjective b p v) (C,t) (D,0) (D,0)=
      2*deriv (deriv (fun s:ℝ=>operatorValue b (p+t • (v:Fin m→ℝ))
        ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)))) 0 := by
  rw [objective_hessian_diagonal b p hs v C t hp hC]
  have hΓ0:ContDiffAt ℝ 2 (pathValue b p v) ((C,t)+(0:ℝ) • (D,0)):=by
    simpa only [zero_smul,add_zero] using pathValue_C2 b p hs v C t hp hC
  have hh:=line_second (pathValue b p v) (C,t) (D,0) 0 hΓ0
  have heq:(fun s:ℝ=>pathValue b p v ((C,t)+s • (D,0)))=
      (fun s:ℝ=>operatorValue b (p+t • (v:Fin m→ℝ))
        ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d))) := by
    funext s
    simp [pathValue]
  rw [heq] at hh
  congr 1
  simpa only [zero_smul,add_zero] using hh.deriv.symm

theorem objective_time_hessian_nonpos (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    fullHessian (pathObjective b p v) (C,t) (0,1) (0,1)≤0 := by
  rw [objective_hessian_diagonal b p hs v C t hp hC]
  have hΓ0:ContDiffAt ℝ 2 (pathValue b p v) ((C,t)+(0:ℝ) • (0,1)):=by
    simpa only [zero_smul,add_zero] using pathValue_C2 b p hs v C t hp hC
  have hh:=line_second (pathValue b p v) (C,t) (0,1) 0 hΓ0
  have heq:(fun s:ℝ=>pathValue b p v ((C,t)+s • (0,1)))=
      (fun s:ℝ=>operatorValue b ((p+t • (v:Fin m→ℝ))+s • (v:Fin m→ℝ)) C) := by
    funext s
    simp only [pathValue,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,
      add_zero,smul_eq_mul,mul_one]
    congr 1
    module
  rw [heq] at hh
  have hle:=operatorValue_mass_line_second_nonpos b C hC (p+t • (v:Fin m→ℝ)) v hp
    (path_mass_sum p hs v t) v.property
  have hEq : deriv (deriv (fun s:ℝ=>operatorValue b ((p+t • (v:Fin m→ℝ))+s • (v:Fin m→ℝ)) C)) 0=
      fullHessian (pathValue b p v) (C,t) (0,1) (0,1):=by
    simpa only [zero_smul,add_zero] using hh.deriv
  rw [hEq] at hle
  linarith

omit [NeZero m] in
/-- A first time-derivative identity on a genuine neighborhood identifies the
mixed block of the actual Frechet Hessian. -/
theorem mixed_hessian_of_time_field {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F:E×ℝ→ℝ) (g:E×ℝ→ℝ) (C D:E) (t q:ℝ)
    (hf:ContDiffAt ℝ 2 F (C,t))
    (ht:∀ᶠ z in 𝓝 (C,t),HasDerivAt (fun s:ℝ=>F (z.1,s)) (g z) z.2)
    (hg:HasDerivAt (fun s:ℝ=>g (C+s • D,t)) q 0) :
    fullHessian F (C,t) (D,0) (0,1)=q := by
  have hF:∀ᶠ z in 𝓝 (C,t),HasFDerivAt F (fderiv ℝ F z) z:=
    (hf.eventually (by norm_num)).mono (fun z hz=>(hz.of_le (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt)
  have heq:∀ᶠ z in 𝓝 (C,t),(fderiv ℝ F z) (0,1)=g z:=by
    filter_upwards [hF,ht] with z hz htime
    have hline:HasDerivAt (fun s:ℝ=>(z.1,s)) (0,1) z.2:=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    exact (hz.comp_hasDerivAt z.2 hline).unique htime
  have hl:HasDerivAt (fun s:ℝ=>(C+s • D,t)) (D,0) 0:=by
    simpa only [id_eq,one_smul] using
      (((hasDerivAt_id (0:ℝ)).smul_const D).const_add C).prodMk (hasDerivAt_const 0 t)
  have hG:HasFDerivAt (fderiv ℝ F) (fullHessian F (C,t)) (C+(0:ℝ) • D,t):=by
    simpa only [zero_smul,add_zero,fullHessian] using
      (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hh:=(ContinuousLinearMap.apply ℝ ℝ ((0,1):E×ℝ)).hasFDerivAt.comp_hasDerivAt 0
    (hG.comp_hasDerivAt 0 hl)
  have htend:Tendsto (fun s:ℝ=>(C+s • D,t)) (𝓝 0) (𝓝 (C,t)):=by
    simpa only [zero_smul,add_zero] using hl.continuousAt.tendsto
  have he:(fun s:ℝ=>g (C+s • D,t))=ᶠ[𝓝 0]
      (fun s:ℝ=>(fderiv ℝ F (C+s • D,t)) (0,1)):=by
    filter_upwards [htend.eventually heq] with s hs
    exact hs.symm
  exact (hh.congr_of_eventuallyEq he).unique hg

theorem objective_mixed_hessian (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone)
    (D:SymmetricOperators (FSC.Coord d)) :
    fullHessian (pathObjective b p v) (C,t) (D,0) (0,1)=
      -2*∑i,(deriv (fun s:ℝ=>(operatorOffsets b (p+t • (v:Fin m→ℝ))
        ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)):Fin m→ℝ)) 0 i)*
          (v:Fin m→ℝ) i := by
  let g:SymmetricOperators (FSC.Coord d)×ℝ→ℝ:=fun z=>-2*∑i,(pathOffsets b p v z:Fin m→ℝ) i*(v:Fin m→ℝ) i
  have hmass:∀ᶠ z:SymmetricOperators (FSC.Coord d)×ℝ in 𝓝 (C,t),
      ∀i,0<(p+z.2 • (v:Fin m→ℝ)) i:=by
    apply eventually_all.mpr
    intro i
    have hc:ContinuousAt (fun z:SymmetricOperators (FSC.Coord d)×ℝ=>(p+z.2 • (v:Fin m→ℝ)) i) (C,t):=by fun_prop
    exact hc.eventually (Ioi_mem_nhds (hp i))
  have hpd:∀ᶠ z:SymmetricOperators (FSC.Coord d)×ℝ in 𝓝 (C,t),
      (z.1:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone:=
    (continuous_fst.tendsto (C,t)).eventually (eventually_pdCone C hC)
  have ht:∀ᶠ z in 𝓝 (C,t),HasDerivAt (fun s:ℝ=>pathObjective b p v (z.1,s)) (g z) z.2:=by
    filter_upwards [hmass,hpd] with z hzp hzc
    exact path_time_derivative b p hs v z.1 z.2 hzp hzc
  let f:ℝ→Fin m→ℝ:=fun s=>(operatorOffsets b (p+t • (v:Fin m→ℝ))
    ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)):Fin m→ℝ)
  have hOC:ContDiffAt ℝ 1 (pathOffsets b p v) (C+(0:ℝ) • D,t):=by
    simpa only [zero_smul,add_zero] using pathOffsets_C1 b p hs v C t hp hC
  have hco:ContDiffAt ℝ 1 f 0:=by
    have hsub:=((centeredGauge (Fin m)).subtypeL.contDiff.contDiffAt.comp (C+(0:ℝ) • D,t) hOC)
    have hline:ContDiffAt ℝ 1 (fun s:ℝ=>(C+s • D,t)) 0:=by fun_prop
    simpa only [Function.comp_def,pathOffsets,ContinuousLinearMap.coe_coe,Submodule.subtypeL_apply,Submodule.coe_add,Submodule.coe_smul,f] using
      hsub.comp (f:=fun s:ℝ=>(C+s • D,t)) 0 hline
  have hf:HasDerivAt f (deriv f 0) 0:=hco.differentiableAt_one.hasDerivAt
  have hi (i:Fin m):HasDerivAt (fun s:ℝ=>f s i) (deriv f 0 i) 0:=by
    simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj i:(Fin m→ℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivAt 0 hf
  have hg:HasDerivAt (fun s:ℝ=>g (C+s • D,t)) (-2*∑i,deriv f 0 i*(v:Fin m→ℝ) i) 0:=by
    exact (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>(hi i).mul_const ((v:Fin m→ℝ) i))).const_mul (-2)
  exact mixed_hessian_of_time_field (pathObjective b p v) g C D t _
    (pathObjective_C2 b p hs v C t hp hC) ht hg

/-- The literal vector offset estimate controls the actual mixed Hessian.
The factor two is from F=2 Gamma-trace. -/
theorem objective_mixed_bound (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hs:∑i,p i=1) (v:centeredGauge (Fin m))
    (C:SymmetricOperators (FSC.Coord d)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i)
    (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone)
    (D:SymmetricOperators (FSC.Coord d)) (L:ℝ)
    (hbound:(∑i,(deriv (fun s:ℝ=>(operatorOffsets b (p+t • (v:Fin m→ℝ))
      ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)):Fin m→ℝ)) 0 i)^2)≤
       L*(-deriv (deriv (fun s:ℝ=>operatorValue b (p+t • (v:Fin m→ℝ))
        ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)))) 0)) :
    (fullHessian (pathObjective b p v) (C,t) (D,0) (0,1))^2≤
      (2*L*∑i,((v:Fin m→ℝ) i)^2)*(-fullHessian (pathObjective b p v) (C,t) (D,0) (D,0)) := by
  rw [objective_mixed_hessian b p hs v C t hp hC D,
    objective_state_hessian b p hs v C t hp hC D]
  let a:Fin m→ℝ:=deriv (fun s:ℝ=>(operatorOffsets b (p+t • (v:Fin m→ℝ))
    ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+s • (D:FSC.Coord d→L[ℝ]FSC.Coord d)):Fin m→ℝ)) 0
  have hcs:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (v:Fin m→ℝ)
  have hv:0≤∑i,((v:Fin m→ℝ) i)^2:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hh:=mul_le_mul_of_nonneg_right hbound hv
  change (∑i,a i*(v:Fin m→ℝ) i)^2≤(∑i,(a i)^2)*(∑i,((v:Fin m→ℝ) i)^2) at hcs
  dsimp [a] at hcs
  nlinarith

end NegativeVotingCovarianceMassPath
