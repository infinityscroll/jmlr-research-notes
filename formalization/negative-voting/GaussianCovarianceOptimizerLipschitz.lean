import GaussianCovarianceJointValueC2
import GaussianOptimizerStability

/-! Local Lipschitz stability of the actual penalized covariance optimizer
on the fixed closed constraint C ≥ ε I. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCovarianceOptimizerLipschitz
open NegativeVotingCovarianceJointValueC2 NegativeVotingOptimizerStability
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceOptimizerContinuity
  NegativeVotingCovarianceStrict NegativeVotingPositiveCovariance
  NegativeVotingCovarianceCoercivity NegativeVotingCovarianceConcavity
  NegativeVotingLocalCovarianceFactor NegativeVotingFanInverse
variable {m d:ℕ} [NeZero m]

def traceFunctional (d:ℕ) : (FSC.Coord d→L[ℝ]FSC.Coord d)→L[ℝ]ℝ :=
  ((LinearMap.trace ℝ (FSC.Coord d)).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

@[simp] theorem traceFunctional_apply (C:FSC.Coord d→L[ℝ]FSC.Coord d) :
    traceFunctional d C=operatorTrace C := rfl

def covarianceObjective (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (q:SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)) : ℝ :=
  penalizedValue b (p+(q.2:Fin m→ℝ)) q.1

theorem covarianceObjective_C2 (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (C:SymmetricOperators (FSC.Coord d)) (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 2 (covarianceObjective b p) (C,0) := by
  have htr : ContDiffAt ℝ 2
      (fun q:SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)=>operatorTrace
        (q.1:FSC.Coord d→L[ℝ]FSC.Coord d)) (C,0) :=
    (traceFunctional d).contDiff.contDiffAt.comp (C,0)
      ((selfAdjoint.submodule ℝ (FSC.Coord d→L[ℝ]FSC.Coord d)).subtypeL.contDiff.contDiffAt.comp (C,0) contDiffAt_fst)
  exact (contDiffAt_const.mul (operatorValue_joint_C2 b p hp hs C hC)).sub htr

theorem covarianceObjective_negative_hessian (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (C:SymmetricOperators (FSC.Coord d)) (hC:(C:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone)
    (D:SymmetricOperators (FSC.Coord d)) (hD:D≠0) :
    secondGradient (covarianceObjective b p) (C,0) D D<0 := by
  have hD' : (D:FSC.Coord d→L[ℝ]FSC.Coord d)≠0:=by
    intro he
    exact hD (Subtype.ext he)
  obtain ⟨a,q,ha,hq,hq0⟩:=exists_derivatives_positive_strict b p hp hs C D hC
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp D.property) hD'
  let f:ℝ→ℝ:=fun t=>operatorValue b p ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+t • (D:FSC.Coord d→L[ℝ]FSC.Coord d))
  have hfC : ContDiffAt ℝ 2 f 0 := by
    have hline : ContDiffAt ℝ 2 (fun t:ℝ=>(C+t • D,(0:centeredGauge (Fin m)))) 0:=by fun_prop
    have hbase : ContDiffAt ℝ 2
        (fun z:SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)=>operatorValue b
          (p+(z.2:Fin m→ℝ)) (z.1:FSC.Coord d→L[ℝ]FSC.Coord d)) (C+(0:ℝ) • D,0):=by
      simpa only [zero_smul,add_zero] using operatorValue_joint_C2 b p hp hs C hC
    have hc:=hbase.comp (f:=fun t:ℝ=>(C+t • D,(0:centeredGauge (Fin m)))) 0 hline
    simpa only [Function.comp_def,Submodule.coe_zero,add_zero,Submodule.coe_add,Submodule.coe_smul] using hc
  have hf : ∀ᶠ t in 𝓝 (0:ℝ),DifferentiableAt ℝ f t:=
    (hfC.eventually (by norm_num)).mono (fun t ht=>(ht.of_le (m:=1) (by norm_num)).differentiableAt_one)
  have hg:=line_second_affine_penalty (a:=2) (b:=operatorTrace (C:FSC.Coord d→L[ℝ]FSC.Coord d))
    (c:=operatorTrace (D:FSC.Coord d→L[ℝ]FSC.Coord d)) hf hq
  have heq : (fun t:ℝ=>covarianceObjective b p (C+t • D,0))=
      (fun t:ℝ=>2*f t-(operatorTrace (C:FSC.Coord d→L[ℝ]FSC.Coord d)+
        t*operatorTrace (D:FSC.Coord d→L[ℝ]FSC.Coord d))) := by
    funext t
    change 2*operatorValue b (p+0) ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+t • (D:FSC.Coord d→L[ℝ]FSC.Coord d))-
      traceFunctional d ((C:FSC.Coord d→L[ℝ]FSC.Coord d)+t • (D:FSC.Coord d→L[ℝ]FSC.Coord d))=_
    simp [f,map_add,map_smul,smul_eq_mul]
  have hh:=secondGradient_line_second (covarianceObjective_C2 b p hp hs C hC) D
  rw [heq] at hh
  have hsame:=hh.unique hg
  rw [hsame]
  linarith

def probabilityChart (p:PositiveProbability m) (u:centeredGauge (Fin m)) : PositiveProbability m :=
  if hp:∀i,0<((p:Fin m→ℝ)+(u:Fin m→ℝ)) i then
    ⟨(p:Fin m→ℝ)+(u:Fin m→ℝ),hp,by
      have hu:∑i,(u:Fin m→ℝ) i=0:=u.property
      simp [Finset.sum_add_distrib,p.property.2,hu]⟩ else p

theorem probabilityChart_coe (p:PositiveProbability m) (u:centeredGauge (Fin m))
    (hu:∀i,0<((p:Fin m→ℝ)+(u:Fin m→ℝ)) i) :
    (probabilityChart p u:Fin m→ℝ)=(p:Fin m→ℝ)+(u:Fin m→ℝ) := by
  simp only [probabilityChart,dif_pos hu]

theorem eventually_positive_chart (p:PositiveProbability m) :
    ∀ᶠ u:centeredGauge (Fin m) in 𝓝 0,∀i,0<((p:Fin m→ℝ)+(u:Fin m→ℝ)) i := by
  apply eventually_all.mpr
  intro i
  have hc:ContinuousAt (fun u:centeredGauge (Fin m)=>(p:Fin m→ℝ) i+(u:Fin m→ℝ) i) 0:=
    continuousAt_const.add (((ContinuousLinearMap.proj i).comp (centeredGauge (Fin m)).subtypeL).continuous.continuousAt)
  exact hc.eventually (Ioi_mem_nhds (by simpa using p.property.1 i))

theorem probabilityChart_continuousAt (p:PositiveProbability m) :
    ContinuousAt (probabilityChart p) 0 := by
  apply (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr
  have hc:ContinuousAt (fun u:centeredGauge (Fin m)=>(p:Fin m→ℝ)+(u:Fin m→ℝ)) 0:=
    continuousAt_const.add (centeredGauge (Fin m)).subtypeL.continuous.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_positive_chart p] with u hu
  exact probabilityChart_coe p u hu

def selectedOperator (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε:ℝ) (hε:0<ε)
    (p:PositiveProbability m) : SymmetricOperators (FSC.Coord d) :=
  (regionPositiveCovariance b ε hε (selectedCovariance b ε hε p)).1

@[simp] theorem selectedOperator_coe (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) (p:PositiveProbability m) :
    (selectedOperator b ε hε p:FSC.Coord d→L[ℝ]FSC.Coord d)=selectedCovariance b ε hε p := rfl

theorem selectedOperator_continuous (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) : Continuous (selectedOperator b ε hε) :=
  continuous_subtype_val.comp ((continuous_regionPositiveCovariance b ε hε).comp
    (selectedCovariance_continuous b ε hε))

/-- Local Lipschitz in actual centered probability coordinates, with all
curvature and optimizer hypotheses discharged. -/
theorem selectedOperator_chart_lipschitz (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) (p:PositiveProbability m) :
    ∃ K:NNReal,∃ T∈𝓝 (0:centeredGauge (Fin m)),
      LipschitzOnWith K (fun u=>selectedOperator b ε hε (probabilityChart p u)) T := by
  let a:centeredGauge (Fin m)→SymmetricOperators (FSC.Coord d):=
    fun u=>selectedOperator b ε hε (probabilityChart p u)
  let S:Set (SymmetricOperators (FSC.Coord d)):=
    {C | (C:FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone ε}
  have hs:Convex ℝ S:=(lowerCovarianceCone_convex ε).linear_preimage
    (selfAdjoint.submodule ℝ (FSC.Coord d→L[ℝ]FSC.Coord d)).subtype
  have ha:ContinuousAt a 0:=(selectedOperator_continuous b ε hε).continuousAt.comp
    (probabilityChart_continuousAt p)
  have hC:(a 0:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone:=
    (regionPositiveCovariance b ε hε (selectedCovariance b ε hε (probabilityChart p 0))).property
  have hm : ∀ᶠ u in 𝓝 (0:centeredGauge (Fin m)),a u∈S ∧
      IsMaxOn (fun C:SymmetricOperators (FSC.Coord d)=>covarianceObjective b p (C,u)) S (a u) := by
    filter_upwards [eventually_positive_chart p] with u hu
    refine ⟨(selectedCovariance b ε hε (probabilityChart p u)).property.1,?_⟩
    intro C hC
    change penalizedValue b ((p:Fin m→ℝ)+(u:Fin m→ℝ)) C≤
      penalizedValue b ((p:Fin m→ℝ)+(u:Fin m→ℝ)) (a u)
    rw [←probabilityChart_coe p u hu]
    exact selectedCovariance_isMaxOn b ε hε (probabilityChart p u) hC
  exact local_optimizer_lipschitz (covarianceObjective b p) a 0 S hs ha
    (covarianceObjective_C2 b p p.property.1 p.property.2 (a 0) hC)
    (fun D hD=>covarianceObjective_negative_hessian b p p.property.1 p.property.2 (a 0) hC D hD) hm

/-- The actual unique maximizing covariance is locally Lipschitz on the
whole open probability simplex, in the original operator norm. -/
theorem selectedCovariance_locallyLipschitz (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) :
    LocallyLipschitz (fun p:PositiveProbability m=>
      (selectedCovariance b ε hε p:FSC.Coord d→L[ℝ]FSC.Coord d)) := by
  intro p₀
  obtain ⟨K,T,hT,hLip⟩:=selectedOperator_chart_lipschitz b ε hε p₀
  let δ:PositiveProbability m→centeredGauge (Fin m):=fun p=>
    ⟨(p:Fin m→ℝ)-(p₀:Fin m→ℝ),by
      change ∑i,((p:Fin m→ℝ) i-(p₀:Fin m→ℝ) i)=0
      rw [Finset.sum_sub_distrib,p.property.2,p₀.property.2,sub_self]⟩
  have hδ:Continuous δ:=by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const
  have hδ₀:δ p₀=0:=by apply Subtype.ext;exact sub_self _
  have hδT:Tendsto δ (𝓝 p₀) (𝓝 (0:centeredGauge (Fin m))):=by
    simpa only [hδ₀] using hδ.tendsto p₀
  have heq (p:PositiveProbability m):probabilityChart p₀ (δ p)=p := by
    have hvec:(p₀:Fin m→ℝ)+(δ p:Fin m→ℝ)=(p:Fin m→ℝ):=by dsimp [δ];abel
    apply Subtype.ext
    rw [probabilityChart_coe p₀ (δ p) (by rw [hvec];exact p.property.1),hvec]
  refine ⟨K,δ ⁻¹' T,hδT.eventually hT,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro p hp q hq
  have hh:=(lipschitzOnWith_iff_norm_sub_le.mp hLip) hp hq
  rw [heq p,heq q] at hh
  have hn:‖δ p-δ q‖=dist p q:=by
    change ‖((p:Fin m→ℝ)-(p₀:Fin m→ℝ))-((q:Fin m→ℝ)-(p₀:Fin m→ℝ))‖=dist p q
    have hv:((p:Fin m→ℝ)-(p₀:Fin m→ℝ))-((q:Fin m→ℝ)-(p₀:Fin m→ℝ))=(p:Fin m→ℝ)-(q:Fin m→ℝ):=by abel
    rw [hv]
    exact (dist_eq_norm (p:Fin m→ℝ) (q:Fin m→ℝ)).symm
  rw [hn] at hh
  rw [dist_eq_norm]
  exact hh

end NegativeVotingCovarianceOptimizerLipschitz
