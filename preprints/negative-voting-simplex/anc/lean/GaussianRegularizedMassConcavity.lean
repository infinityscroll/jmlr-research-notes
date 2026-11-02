import GaussianCovarianceMassPath
import LocalConcavity

/-! Semiconcavity of the actual positive-floor optimized Gaussian mass value.
The covariance optimizer is the unique maximizer on the whole lower cone. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingRegularizedMassConcavity
open NegativeVotingCovarianceMassPath NegativeVotingCovarianceOptimizerLipschitz
  NegativeVotingCovarianceOptimizerContinuity NegativeVotingValueSemiconcavity
  NegativeVotingCovarianceMixedNeighborhood NegativeVotingCovarianceOffsets
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceConcavity
  NegativeVotingCovarianceStrict NegativeVotingCovarianceCoercivity
  NegativeVotingPositiveCovariance NegativeVotingLocalCovarianceFactor
  NegativeVotingFanInverse NegativeVotingLocalConcavity NegativeVotingOptimizerConstants
  NegativeVotingCovarianceBoundary NegativeVotingFanMassContinuity
variable {m d:ℕ} [NeZero m]

def pathProbability (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ) : PositiveProbability m:=
  probabilityChart p (t • v)

def regularizedPathValue (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε:ℝ) (hε:0<ε)
    (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ):ℝ:=
  penalizedValue b (pathProbability p v t) (selectedCovariance b ε hε (pathProbability p v t))

theorem positive_path_eventually (p:Fin m→ℝ) (v:centeredGauge (Fin m)) (t:ℝ)
    (hp:∀i,0<(p+t • (v:Fin m→ℝ)) i) :
    ∀ᶠ s in 𝓝 t,∀i,0<(p+s • (v:Fin m→ℝ)) i := by
  apply eventually_all.mpr
  intro i
  have hc:ContinuousAt (fun s:ℝ=>(p+s • (v:Fin m→ℝ)) i) t:=by fun_prop
  exact hc.eventually (Ioi_mem_nhds (hp i))

theorem pathProbability_coe (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ)
    (hp:∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i) :
    (pathProbability p v t:Fin m→ℝ)=(p:Fin m→ℝ)+t • (v:Fin m→ℝ) := by
  simpa only [pathProbability,Submodule.coe_smul] using probabilityChart_coe p (t • v) hp

theorem pathProbability_continuousAt (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ)
    (hp:∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i) :
    ContinuousAt (pathProbability p v) t := by
  apply (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr
  have hc:ContinuousAt (fun s:ℝ=>(p:Fin m→ℝ)+s • (v:Fin m→ℝ)) t:=by fun_prop
  apply hc.congr_of_eventuallyEq
  filter_upwards [positive_path_eventually p v t hp] with s hs
  exact pathProbability_coe p v s hs

theorem regularizedPathValue_eq_objective (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ)
    (hp:∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i) :
    regularizedPathValue b ε hε p v t=
      pathObjective b p v (selectedOperator b ε hε (pathProbability p v t),t) := by
  change penalizedValue b (pathProbability p v t) (selectedCovariance b ε hε (pathProbability p v t))=
    penalizedValue b ((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) (selectedCovariance b ε hε (pathProbability p v t))
  rw [pathProbability_coe p v t hp]

theorem regularizedPathValue_continuousAt (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε:ℝ) (hε:0<ε) (p:PositiveProbability m) (v:centeredGauge (Fin m)) (t:ℝ)
    (hp:∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i) :
    ContinuousAt (regularizedPathValue b ε hε p v) t := by
  let a:ℝ→SymmetricOperators (FSC.Coord d):=fun s=>selectedOperator b ε hε (pathProbability p v s)
  have ha:ContinuousAt a t:=(selectedOperator_continuous b ε hε).continuousAt.comp
    (g:=selectedOperator b ε hε) (f:=pathProbability p v)
    (pathProbability_continuousAt p v t hp)
  have hC:(a t:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone:=
    (regionPositiveCovariance b ε hε (selectedCovariance b ε hε (pathProbability p v t))).property
  have hc:ContinuousAt (fun s:ℝ=>pathObjective b p v (a s,s)) t:=
    (pathObjective_C2 b p p.property.2 v (a t) t hp hC).continuousAt.comp
      (g:=pathObjective b p v) (f:=fun s:ℝ=>(a s,s)) (ha.prodMk continuousAt_id)
  apply hc.congr_of_eventuallyEq (g:=regularizedPathValue b ε hε p v)
  filter_upwards [positive_path_eventually p v t hp] with s hs
  exact regularizedPathValue_eq_objective b ε hε p v s hs

theorem squared_mass_direction_pos (v:centeredGauge (Fin m)) (hv:v≠0) :
    0<∑i,((v:Fin m→ℝ) i)^2 := by
  have hnonneg:0≤∑i,((v:Fin m→ℝ) i)^2:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
  by_contra hn
  have hz:(∑i,((v:Fin m→ℝ) i)^2)=0:=le_antisymm (not_lt.mp hn) hnonneg
  have hi:= (Finset.sum_eq_zero_iff_of_nonneg (fun i (_:i∈Finset.univ)=>sq_nonneg ((v:Fin m→ℝ) i))).mp hz
  apply hv
  apply Subtype.ext
  funext i
  exact (sq_eq_zero_iff).mp (hi i (Finset.mem_univ _))

/-- Actual covariance maximization preserves the corrected joint concavity.
The only analytic input is the literal offset-response inequality on one
common covariance/mass neighborhood. -/
theorem regularized_local_concavity_of_mixed_neighborhood
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε:ℝ) (hε:0<ε)
    (p:PositiveProbability m) (v:centeredGauge (Fin m)) (hv:v≠0) (t0 L:ℝ) (hL:0<L)
    (hp:∀i,0<((p:Fin m→ℝ)+t0 • (v:Fin m→ℝ)) i)
    (hN:∀ᶠ q:CovarianceMassCoordinates m d in
      𝓝 (selectedOperator b ε hε (pathProbability p v t0),0),
      (∀i,0<((p:Fin m→ℝ)+t0 • (v:Fin m→ℝ)+(q.2:Fin m→ℝ)) i) ∧
      (q.1:FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone ∧
      ∀A:FSC.Coord d→L[ℝ]FSC.Coord d,A.toLinearMap.IsSymmetric →
        (∑i,(deriv (fun s:ℝ=>(operatorOffsets b
          ((p:Fin m→ℝ)+t0 • (v:Fin m→ℝ)+(q.2:Fin m→ℝ))
          ((q.1:FSC.Coord d→L[ℝ]FSC.Coord d)+s • A):Fin m→ℝ)) 0 i)^2)≤
        L*(-deriv (deriv (fun s:ℝ=>operatorValue b
          ((p:Fin m→ℝ)+t0 • (v:Fin m→ℝ)+(q.2:Fin m→ℝ))
          ((q.1:FSC.Coord d→L[ℝ]FSC.Coord d)+s • A))) 0)) :
    ∃η:ℝ,0<η ∧ ConcaveOn ℝ (Metric.ball t0 η)
      (fun t=>regularizedPathValue b ε hε p v t-(L*∑i,((v:Fin m→ℝ) i)^2)*t^2) := by
  let a:ℝ→SymmetricOperators (FSC.Coord d):=fun t=>selectedOperator b ε hε (pathProbability p v t)
  let S:Set (SymmetricOperators (FSC.Coord d)):=
    {C | (C:FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone ε}
  have hS:Convex ℝ S:=(lowerCovarianceCone_convex ε).linear_preimage
    (selfAdjoint.submodule ℝ (FSC.Coord d→L[ℝ]FSC.Coord d)).subtype
  have ha:ContinuousAt a t0:=(selectedOperator_continuous b ε hε).continuousAt.comp
    (pathProbability_continuousAt p v t0 hp)
  have hm:∀ᶠ t in 𝓝 t0,a t∈S ∧
      IsMaxOn (fun C:SymmetricOperators (FSC.Coord d)=>pathObjective b p v (C,t)) S (a t):=by
    filter_upwards [positive_path_eventually p v t0 hp] with t ht
    refine ⟨(selectedCovariance b ε hε (pathProbability p v t)).property.1,?_⟩
    intro C hC
    change penalizedValue b ((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) C≤
      penalizedValue b ((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) (a t)
    rw [←pathProbability_coe p v t ht]
    exact selectedCovariance_isMaxOn b ε hε (pathProbability p v t) hC
  let Q:SymmetricOperators (FSC.Coord d)×ℝ→ CovarianceMassCoordinates m d:=
    fun z=>(z.1,(z.2-t0) • v)
  have hQ:Tendsto Q (𝓝 (a t0,t0)) (𝓝 (a t0,0)):=by
    have hc:Continuous Q:=by fun_prop
    simpa only [Q,sub_self,zero_smul] using hc.tendsto (a t0,t0)
  have he (t:ℝ):(p:Fin m→ℝ)+t0 • (v:Fin m→ℝ)+(t-t0) • (v:Fin m→ℝ)=
      (p:Fin m→ℝ)+t • (v:Fin m→ℝ):=by module
  let K:=2*L*∑i,((v:Fin m→ℝ) i)^2
  have hK:0<K:=mul_pos (mul_pos (by norm_num) hL) (squared_mass_direction_pos v hv)
  have hH:∀ᶠ z in 𝓝 (a t0,t0),ContDiffAt ℝ 2 (pathObjective b p v) z ∧
      fullHessian (pathObjective b p v) z (0,1) (0,1)≤0 ∧
      ∀D:SymmetricOperators (FSC.Coord d),
        (fullHessian (pathObjective b p v) z (D,0) (0,1))^2≤
        K*(-fullHessian (pathObjective b p v) z (D,0) (D,0)):=by
    filter_upwards [hQ.eventually hN] with z hz
    simp only [Q,Submodule.coe_smul,he] at hz
    refine ⟨pathObjective_C2 b p p.property.2 v z.1 z.2 hz.1 hz.2.1,
      objective_time_hessian_nonpos b p p.property.2 v z.1 z.2 hz.1 hz.2.1,?_⟩
    intro D
    exact objective_mixed_bound b p p.property.2 v z.1 z.2 hz.1 hz.2.1 D L
      (hz.2.2 D (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp D.property))
  obtain ⟨η,hη,hconc⟩:=local_penalty_value_concave (pathObjective b p v) S hS a t0 K hK ha hm hH
  obtain ⟨r,hr,hrsub⟩:=Metric.mem_nhds_iff.mp (positive_path_eventually p v t0 hp)
  let η':=min η r
  have hη':0<η':=lt_min hη hr
  have hsub:Metric.ball t0 η'⊆Metric.ball t0 η:=Metric.ball_subset_ball (min_le_left _ _)
  have hpos:∀t∈Metric.ball t0 η',∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i:=
    fun t ht=>hrsub (Metric.ball_subset_ball (min_le_right _ _) ht)
  refine ⟨η',hη',?_⟩
  apply (hconc.subset hsub (convex_ball _ _)).congr
  intro t ht
  dsimp only
  rw [regularizedPathValue_eq_objective b ε hε p v t (hpos t ht)]
  dsimp [K,a]
  ring

/-- One floor threshold works for every mass segment in the entire first
mass window. The conclusion concerns the actual attained Gaussian optimum. -/
theorem uniform_regularized_path_concavity
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hdim : 2 ≤ d) (hm : numericThreshold ≤ m) :
    ∃δ:ℝ,0<δ ∧ ∀ε:ℝ,∀hε:0<ε,ε<δ →
      ∀p:PositiveProbability m,∀v:centeredGauge (Fin m),∀a c:ℝ,
      (∀t∈Icc a c,∀i,actualMassLower (m:ℝ)≤((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i ∧
        ((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i≤2/(m:ℝ)) →
      ConcaveOn ℝ (Icc a c)
        (fun t=>regularizedPathValue b ε hε p v t-
          (mixedConstant*(1+Real.log (m:ℝ))^2*∑i,((v:Fin m→ℝ) i)^2)*t^2) := by
  obtain ⟨δ,hδ,hMixed⟩:=uniform_optimizer_mixed_neighborhood b hG hP hdim hm
  obtain ⟨hm3,_,_⟩:=numericThreshold_spec m hm
  have hm1:1≤(m:ℝ):=by exact_mod_cast (show 1≤ m by omega)
  have hm0:0<(m:ℝ):=lt_of_lt_of_le zero_lt_one hm1
  have hlo:0<actualMassLower (m:ℝ):=by unfold actualMassLower;positivity
  let L:=mixedConstant*(1+Real.log (m:ℝ))^2
  have hL:0<L:=mul_pos mixedConstant_pos (sq_pos_of_pos (by linarith [Real.log_nonneg hm1]))
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ p v a c hbox
  change ConcaveOn ℝ (Icc a c)
    (fun t=>regularizedPathValue b ε hε p v t-(L*∑i,((v:Fin m→ℝ) i)^2)*t^2)
  by_cases hv:v=0
  · subst v
    have hp (t:ℝ):∀i,0<((p:Fin m→ℝ)+t • ((0:centeredGauge (Fin m)):Fin m→ℝ)) i:=by
      simpa using p.property.1
    have hprob (t:ℝ):pathProbability p 0 t=p:=by
      apply Subtype.ext
      simpa using pathProbability_coe p 0 t (hp t)
    have heq:(fun t:ℝ=>regularizedPathValue b ε hε p 0 t-
        (L*∑i,(((0:centeredGauge (Fin m)):Fin m→ℝ) i)^2)*t^2)=
        (fun _:ℝ=>penalizedValue b p (selectedCovariance b ε hε p)):=by
      funext t
      simp [regularizedPathValue,hprob]
    rw [heq]
    exact concaveOn_const _ (convex_Icc a c)
  have hp (t:ℝ) (ht:t∈Icc a c):∀i,0<((p:Fin m→ℝ)+t • (v:Fin m→ℝ)) i:=
    fun i=>hlo.trans_le (hbox t ht i).1
  apply concaveOn_Icc_of_locally_concave
  · intro t ht
    exact ((regularizedPathValue_continuousAt b ε hε p v t (hp t ht)).sub
      (continuousAt_const.mul (continuousAt_id.pow 2))).continuousWithinAt
  · intro t ht
    have hti:t∈Icc a c:=⟨ht.1.le,ht.2.le⟩
    have hpbox:pathProbability p v t∈positiveMassBox (actualMassLower (m:ℝ)) (2/(m:ℝ)):=by
      change ∀i,actualMassLower (m:ℝ)≤(pathProbability p v t:Fin m→ℝ) i ∧
        (pathProbability p v t:Fin m→ℝ) i≤2/(m:ℝ)
      rw [pathProbability_coe p v t (hp t hti)]
      exact hbox t hti
    have hfloor:(selectedOperator b ε hε (pathProbability p v t):FSC.Coord d→L[ℝ]FSC.Coord d)∈
        lowerCovarianceCone ε:=(selectedCovariance b ε hε (pathProbability p v t)).property.1
    have hn:=hMixed ε hε hεδ (pathProbability p v t) hpbox
      (selectedOperator b ε hε (pathProbability p v t)) hfloor
      (selectedCovariance_isMaxOn b ε hε (pathProbability p v t))
    rw [pathProbability_coe p v t (hp t hti)] at hn
    obtain ⟨η,hη,hconc⟩:=regularized_local_concavity_of_mixed_neighborhood b ε hε p v hv t L hL (hp t hti) hn
    exact ⟨Metric.ball t η,Metric.ball_mem_nhds _ hη,hconc⟩

/-- The closed mass window is preserved by the actual affine mass segment. -/
theorem mass_segment_mem_window (p q:Fin m→ℝ) (lo hi:ℝ)
    (hp:∀i,p i∈Icc lo hi) (hq:∀i,q i∈Icc lo hi) :
    ∀t∈Icc (0:ℝ) 1,∀i,(p+t • (q-p)) i∈Icc lo hi := by
  intro t ht i
  have hh: (1-t) • p i+t • q i∈Icc lo hi:=
    (convex_Icc lo hi) (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have he:(p+t • (q-p)) i=(1-t)*p i+t*q i:=by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact hh

/-- The stationary anchor removes the linear term from the concrete
regularized mass-value estimate. The anchor derivative is a genuine scalar
derivative of the actual selected optimum. -/
theorem regularized_path_bound_of_stationary_anchor
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (ε:ℝ) (hε:0<ε)
    (p:PositiveProbability m) (v:centeredGauge (Fin m)) (L:ℝ)
    (hc:ConcaveOn ℝ (Icc (0:ℝ) 1)
      (fun t=>regularizedPathValue b ε hε p v t-(L*∑i,((v:Fin m→ℝ) i)^2)*t^2))
    (hd:HasDerivAt (regularizedPathValue b ε hε p v) 0 0) :
    regularizedPathValue b ε hε p v 1≤regularizedPathValue b ε hε p v 0+
      L*∑i,((v:Fin m→ℝ) i)^2 := by
  have hpoly:HasDerivAt (fun t:ℝ=>(L*∑i,((v:Fin m→ℝ) i)^2)*t^2) 0 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).pow 2).const_mul (L*∑i,((v:Fin m→ℝ) i)^2)
  have hd':HasDerivAt
      (fun t=>regularizedPathValue b ε hε p v t-(L*∑i,((v:Fin m→ℝ) i)^2)*t^2) 0 0:=by
    simpa only [sub_self,Pi.sub_def] using hd.sub hpoly
  have hslope:=hc.slope_le_of_hasDerivAt
    (show (0:ℝ)∈Icc 0 1 by constructor <;>norm_num)
    (show (1:ℝ)∈Icc 0 1 by constructor <;>norm_num) zero_lt_one hd'
  simp only [slope_def_field,sub_zero,div_one,one_pow,zero_pow (by decide : 2≠0),
    mul_one,mul_zero,sub_zero] at hslope
  linarith

end NegativeVotingRegularizedMassConcavity
