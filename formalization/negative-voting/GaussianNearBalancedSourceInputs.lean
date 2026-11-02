import GaussianStructuredResidualInputs
import GaussianNearRegularGraphGap
import GaussianNearRegularNormalizedBounds

/-! Actual near-balanced mass variation and common-smoothed source inputs.
The mass response is the derivative of the globally selected offset. Its
energy is derived from the actual Gaussian graph gap; it is not assumed.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingNearBalancedSourceInputs
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanInverse
  NegativeVotingFanSelectedOffsets NegativeVotingFanJointInverse NegativeVotingCapTail
  NegativeVotingFacetDegree NegativeVotingFanScore NegativeVotingDisintegration
  NegativeVotingNearRegularBalancedGeometry NegativeVotingFanRetained
  NegativeVotingFiniteGraph NegativeVotingNearRegularGraphGap
  NegativeVotingPathSmoothedComparison NegativeVotingStructuredResidualInputs
  NegativeVotingStructuredSwitchingMoments NegativeVotingPolynomialFacetLogBound
  NegativeVotingBoundaryHighChaosTrace NegativeVotingActualFacetOUTrace
  NegativeVotingWeightedFacet NegativeVotingBalancedMomentGeometry
  NegativeVotingBoundaryTraceAggregation NegativeVotingFanHessian
  NegativeVotingBalancedOffsetComparison NegativeVotingNearRegularNormalizedBounds
variable {V:Type*} [Fintype V] [DecidableEq V] [Nonempty V] {d:ℕ}

def massLine (p:V→ℝ) (v:centeredGauge V) (t:ℝ):V→ℝ:=p+t • (v:V→ℝ)
def offsetLine (b:V→FSC.Coord d) (p:V→ℝ)
    (v:centeredGauge V) (t:ℝ):centeredGauge V:=selectedOffsets b (massLine p v t)

omit [DecidableEq V] [Nonempty V] in
theorem massLine_sum (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1) (t:ℝ):
    ∑i,massLine p v t i=1:=by
  have hv:∑i,(v:V→ℝ) i=0:=v.property
  simp only [massLine,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,←Finset.mul_sum,hv,hp,mul_zero,add_zero]

theorem offsetLine_C1 (b:V→FSC.Coord d)
    (σ:ℝ) (hσ:0<σ) (hlower:CenteredSingularLowerBound b σ) (p:V→ℝ)
    (v:centeredGauge V) (hp:∑i,p i=1) (t:ℝ) (hpos:∀i,0< massLine p v t i):
    ContDiffAt ℝ 1 (offsetLine b p v) t:=by
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
  change ContDiffAt ℝ 1 (fun s:ℝ=> selectedOffsets b (massLine p v s)) t
  simpa only [Function.comp_def,←he] using ht

theorem offsetLine_jacobian_response (b:V→FSC.Coord d)
    (σ:ℝ) (hσ:0<σ) (hlower:CenteredSingularLowerBound b σ) (p:V→ℝ) (v:centeredGauge V) (hp:∑i,p i=1)
    (t:ℝ) (hpos:∀i,0< massLine p v t i):
    offsetJacobian b (offsetLine b p v t) *ᵥ ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)=v:=by
  classical
  have hC:=offsetLine_C1 b σ hσ hlower p v hp t hpos
  have hd:HasDerivAt (offsetLine b p v) (deriv (offsetLine b p v) t) t:=
    (hC.differentiableAt (by norm_num)).hasDerivAt
  have hD:HasDerivAt (fun s:ℝ=>(offsetLine b p v s:V→ℝ))
      ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ) t:=
    (centeredGauge V).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
  have hnear:∀ᶠs:ℝ in 𝓝 t,∀i,0< massLine p v s i:=by
    apply eventually_all.mpr
    intro i
    have hc:ContinuousAt (fun s:ℝ=> massLine p v s i) t:=by unfold massLine;fun_prop
    exact hc.eventually (Ioi_mem_nhds (hpos i))
  ext i
  have hc:HasDerivAt (fun s:ℝ=> mass b (offsetLine b p v s) i)
      (NegativeVotingFanJacobian.massDerivative b (offsetLine b p v t) i
        ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)) t:=by
    simpa only [Function.comp_def] using
      (hasFDerivAt_mass b σ hσ hlower (offsetLine b p v t) i).comp_hasDerivAt t hD
  have hc':HasDerivAt (fun s:ℝ=> p i+s*(v:V→ℝ) i)
      (NegativeVotingFanJacobian.massDerivative b (offsetLine b p v t) i
        ((deriv (offsetLine b p v) t:centeredGauge V):V→ℝ)) t:=by
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with s hs
    rw [offsetLine,selectedOffsets_mass b (fun i j he=> by
      by_contra hij
      exact centered_singular_rows_ne b σ hσ hlower i j hij he) (massLine p v s) hs (massLine_sum p v hp s)]
    rfl
  have hs:HasDerivAt (fun s:ℝ=> p i+s*(v:V→ℝ) i) ((v:V→ℝ) i) t:=by
    simpa using ((hasDerivAt_id t).mul_const ((v:V→ℝ) i)).const_add (p i)
  have he:=hc'.unique hs
  rw [NegativeVotingFanJacobian.massDerivative_apply b σ hσ hlower] at he
  simpa only [offsetJacobian_mulVec] using he


omit [Nonempty V] in
/-- Cauchy--Schwarz and the actual Jacobian gap bound the actual mass response. -/
theorem inverse_pairing_le (B:V→FSC.Coord d) (h u v:V→ℝ)
    (g:ℝ) (hg:0< g)
    (hgap: g*(∑ i,(u i)^2) ≤ u ⬝ᵥ (offsetJacobian B h *ᵥ u))
    (hJ:offsetJacobian B h *ᵥ u=v) :
    u ⬝ᵥ v ≤ g⁻¹*(∑ i,(v i)^2) := by
  rw [hJ] at hgap
  have hE:0≤ u ⬝ᵥ v := (mul_nonneg hg.le (Finset.sum_nonneg fun i _=> sq_nonneg _)).trans hgap
  have hSu:(∑ i,(u i)^2) ≤ g⁻¹*(u ⬝ᵥ v) := by
    have hh := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hg.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hg.ne',one_mul] using hh
  have hC := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  change (u ⬝ᵥ v)^2 ≤ (∑ i,(u i)^2)*(∑ i,(v i)^2) at hC
  have hh := mul_le_mul_of_nonneg_right hSu (show 0≤∑ i,(v i)^2 from
    Finset.sum_nonneg fun i _=> sq_nonneg _)
  by_cases hz:u ⬝ᵥ v=0
  · rw [hz]; positivity
  · have hp:0< u ⬝ᵥ v := lt_of_le_of_ne hE (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hC,hh]

variable {m:ℕ} [NeZero m]

def massDegree (e:ℝ):ℝ := 32*(2*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e

def massGap (m:ℕ) (α e:ℝ):ℝ :=
  retainedGapCoefficient (1/(2*(m:ℝ))) (2*α) (massDegree e)

theorem massDegree_pos (e:ℝ) (he:0< e):0< massDegree e := by
  unfold massDegree; positivity

theorem massGap_pos (α e:ℝ) (hα:0<α) (he:0< e):0< massGap m α e := by
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  exact retainedGapCoefficient_pos _ _ _ (by positivity) (by positivity) (massDegree_pos e he)

/-- The same near-regular Gram geometry controls every selected mass in the
whole box; no bound on the selected offsets is assumed. -/
theorem near_mass_degree (hm:3≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (p:Fin m→ℝ) (hp:∀ i,0< p i) (hs:∑ i,p i=1)
    (hup:∀ i,p i≤2/(m:ℝ)) (i:Fin m) :
    intrinsicWeightedDegree (α•R+D) (selectedOffsets (α•R+D) p) i≤ massDegree e := by
  let B:=α•R+D
  let h:Fin m→ℝ:=selectedOffsets B p
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hinj:Function.Injective B := fun a b heq=> by
    by_contra hab
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 a b hab heq
  have hm1:(1:ℝ)≤ m := by exact_mod_cast (show 1≤ m by omega)
  have hl:0≤ Real.log (m:ℝ):=Real.log_nonneg hm1
  have hmass:(stdGaussian (FSC.Coord d) (affineCell B h i)).toReal≤2/(m:ℝ) := by
    have hh:=congrFun (selectedOffsets_mass B hinj p hp hs) i
    rw [mass_eq_winningCell B hinj] at hh
    have hle := hh.le.trans (hup i)
    simpa only [Measure.real,winningCell,affineCell,scores,affineScore] using hle
  have hh := intrinsicWeightedDegree_uniform_of_gram B h (α/2) α (by positivity) hα
    hg.1 i e m (1+Real.log (m:ℝ)) 2 he hm1 (by linarith) (by linarith)
    (by norm_num) hscale (hg.2.1 i) hg.2.2.1 (fun j hij=> hg.2.2.2.1 j i hij) hmass
  exact hh

theorem near_mass_gap (hm:3≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (p:Fin m→ℝ) (hp:∀ i,0< p i) (hs:∑ i,p i=1)
    (hlo:∀ i,1/(2*(m:ℝ))≤ p i) (hup:∀ i,p i≤2/(m:ℝ))
    (v:Fin m→ℝ) (hv:∑ i,v i=0) :
    massGap m α e*(∑ i,(v i)^2) ≤
      v ⬝ᵥ (offsetJacobian (α•R+D) (selectedOffsets (α•R+D) p) *ᵥ v) := by
  let B:=α•R+D
  let h:Fin m→ℝ:=selectedOffsets B p
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hinj:Function.Injective B := fun a b heq=> by
    by_contra hab
    exact centered_singular_rows_ne B (α/2) (by positivity) hg.1 a b hab heq
  have hmass:∀ i,1/(2*(m:ℝ))≤ mass B h i := by
    intro i
    rw [show mass B h=p from selectedOffsets_mass B hinj p hp hs]
    exact hlo i
  have hd i:(∑ j,facetWeight B h i j)≤ massDegree e := by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),facetWeight_self,add_zero]
    exact near_mass_degree hm R D hG α hα hD e he hscale p hp hs hup i
  have hh:=gaussian_retained_rayleigh B h hinj (1/(2*(m:ℝ))) (2*α) 0 (massDegree e)
    (by positivity) (by positivity) (by norm_num) (massDegree_pos e he) hmass
    (fun i j _=> hg.2.2.2.2 i j) hd (by simp only [zero_mul]; positivity) v hv
  rw [offsetJacobian_energy]
  simpa only [massGap,retainedWeight,ite_eq_left (facetWeight_nonneg B h _ _)] using hh

/-- The whole selected mass path stays in the prescribed positive mass box. -/
theorem uniform_massLine_box (v:centeredGauge (Fin m))
    (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ))) (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
    ∀ i,1/(2*(m:ℝ))≤ massLine (fun _=>(m:ℝ)⁻¹) v t i ∧
      massLine (fun _=>(m:ℝ)⁻¹) v t i≤2/(m:ℝ) := by
  have hm0:(0:ℝ)< m := Nat.cast_pos.mpr (NeZero.pos m)
  have he:(m:ℝ)⁻¹=2*(1/(2*(m:ℝ))) := by field_simp
  have he':2/(m:ℝ)=4*(1/(2*(m:ℝ))) := by field_simp; ring
  intro i
  have hai:=abs_le.mp (hv i)
  have hti:-(1/(2*(m:ℝ)))≤ t*(v:Fin m→ℝ) i ∧
      t*(v:Fin m→ℝ) i≤1/(2*(m:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (hv i) ht.1
    have h' := mul_le_mul_of_nonneg_right ht.2 (show 0≤1/(2*(m:ℝ)) by positivity)
    apply abs_le.mp
    rw [abs_mul,abs_of_nonneg ht.1]
    exact h.trans (by simpa only [one_mul] using h')
  dsimp [massLine]
  rw [he,he']
  constructor <;> linarith [hti.1,hti.2]


/-- Actual pure mass variation at fixed near-regular rows. The velocity energy
is bounded by the graph inverse pairing, with no offset-norm hypothesis. -/
theorem near_mass_smoothed_difference_l2_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ σ q:ℝ) (hτ:0<τ) (hσ:0<σ) (hσ1:σ<1)
    (hq:2≤ q) (ht:τ^2=1/(2*q-1)) (hqlog:Real.log ((m:ℝ)/(α/2))≤ q)
    (k:ℕ) (hk:k≤3) :
    (∑ i,∫ x,(smoothedHighModes (τ*σ) k
      (cellDifference (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i) x)^2
        ∂stdGaussian (FSC.Coord d)) ≤
      8*Real.exp 1*max 1 (massDegree e)*(σ^2)^k*(massGap m α e)⁻¹*
        ∑ i,((v:Fin m→ℝ) i)^2 := by
  let B:=α•R+D
  let p₀:Fin m→ℝ:=fun _=>(m:ℝ)⁻¹
  let p:ℝ→Parameters d (Fin m):=fun t=>(B,(offsetLine B p₀ v t:Fin m→ℝ))
  let p':ℝ→Parameters d (Fin m):=fun t=>(0,((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ))
  let H:ℝ:=(massGap m α e)⁻¹*∑ i,((v:Fin m→ℝ) i)^2
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hpos:(0:ℝ)< m := Nat.cast_pos.mpr (NeZero.pos m)
  have hp₀:∑ i,p₀ i=1 := by simp [p₀,NeZero.ne m]
  have hbox t (ht':t∈Icc (0:ℝ) 1):∀ i,1/(2*(m:ℝ))≤ massLine p₀ v t i ∧
      massLine p₀ v t i≤2/(m:ℝ) := uniform_massLine_box v hv t ht'
  have hpositive t (ht':t∈Icc (0:ℝ) 1):∀ i,0< massLine p₀ v t i :=
    fun i=> lt_of_lt_of_le (by positivity) (hbox t ht' i).1
  have hp t (ht':t∈Icc (0:ℝ) 1):HasDerivAt p (p' t) t := by
    have hc:=offsetLine_C1 B (α/2) (by positivity) hg.1 p₀ v hp₀ t (hpositive t ht')
    have hd:HasDerivAt (offsetLine B p₀ v) (deriv (offsetLine B p₀ v) t) t :=
      (hc.differentiableAt (by norm_num)).hasDerivAt
    have hs:HasDerivAt (fun s:ℝ=>(offsetLine B p₀ v s:Fin m→ℝ))
        ((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ) t :=
      (centeredGauge (Fin m)).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
    exact (hasDerivAt_const t B).prodMk hs
  have hdeg t (ht':t∈Icc (0:ℝ) 1) i:
      intrinsicWeightedDegree (p t).1 (p t).2 i≤ massDegree e :=
    near_mass_degree hm R D hG α hα hD e he hscale (massLine p₀ v t)
      (hpositive t ht') (massLine_sum p₀ v hp₀ t) (fun i=>(hbox t ht' i).2) i
  have henergy t (ht':t∈Ico (0:ℝ) 1):
      quadraticForm (p t).1 (p t).2 (p' t).1 (p' t).2≤ H := by
    have htc:t∈Icc (0:ℝ) 1:=⟨ht'.1,ht'.2.le⟩
    have hJ:=offsetLine_jacobian_response B (α/2) (by positivity) hg.1 p₀ v hp₀ t (hpositive t htc)
    have hgap:=near_mass_gap hm R D hG α hα hD e he hscale (massLine p₀ v t)
      (hpositive t htc) (massLine_sum p₀ v hp₀ t) (fun i=>(hbox t htc i).1)
      (fun i=>(hbox t htc i).2) (deriv (offsetLine B p₀ v) t:centeredGauge (Fin m))
      (deriv (offsetLine B p₀ v) t).property
    have hh:=inverse_pairing_le B (offsetLine B p₀ v t)
      (deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)) v (massGap m α e) (massGap_pos α e hα he) hgap hJ
    dsimp only [p,p',Prod.fst,Prod.snd]
    change quadraticForm B (offsetLine B p₀ v t) (0:Fin m→FSC.Coord d)
      ((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ)≤ H
    rw [quadraticForm_offsets,hJ]
    exact hh
  have hH:0≤ H := by dsimp [H]; positivity [massGap_pos (m:=m) α e hα he]
  have hh:=path_smoothed_difference_l2_sq_le p p' hp (α/2) (by positivity)
    (fun _ _=> hg.1) τ σ q (massDegree e) H hτ hσ hσ1 hq ht
    (massDegree_pos e he).le hH hdeg henergy k hk
  have hc:=traceCoefficient_le_exp (ι:=Fin m) (α/2) (massDegree e) q (by positivity)
    (massDegree_pos e he).le (by linarith) (by simpa only [Fintype.card_fin] using hpos)
    (by simpa only [Fintype.card_fin] using hqlog)
  have hcoef:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤8 by norm_num))
      (pow_nonneg (sq_nonneg σ) k)) hH
  simpa only [p,offsetLine,massLine,zero_smul,one_smul,add_zero,p₀,H,mul_assoc] using hh.trans hcoef


/-- Near-balanced mass change contributes a genuinely quadratic source norm. -/
theorem near_mass_cellSource_sum_norm_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ χ q:ℝ) (hτ:0<τ) (hχ:0<χ) (hχ1:χ<1)
    (hq:2≤ q) (ht:τ^2=1/(2*q-1)) (hqlog:Real.log ((m:ℝ)/(α/2))≤ q) :
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2
      (cellSource τ χ
        (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i))^2) ≤
      8*Real.exp 1*max 1 (massDegree e)*χ^8*(massGap m α e)⁻¹*
        ∑ i,((v:Fin m→ℝ) i)^2 := by
  have hτ1:τ<1 := by
    have :1/(2*q-1)<1 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    nlinarith
  have hχsq:χ^2<1 := by nlinarith
  have hh:=near_mass_smoothed_difference_l2_sq_le hm R D hG α hα hD e he hscale v hv
    τ (χ^2) q hτ (sq_pos_of_pos hχ) hχsq hq ht hqlog 2 (by norm_num)
  simp_rw [realLp_two_sq_eq_integral (cellSource_memLp τ χ hτ hτ1 hχ hχ1 _ _ _)]
  unfold cellSource
  calc
    _ = ∑ i,∫ x,(smoothedHighModes (τ*χ^2) 2
        (cellDifference (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
          (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i) x)^2
          ∂stdGaussian (FSC.Coord d) := by
      apply Finset.sum_congr rfl
      intro i _
      exact smoothedHighModes_neg_integral_sq _ _ _
    _ ≤ _ := by convert hh using 1; ring

/-- A three-endpoint source decomposition is an exact pointwise identity.
It can therefore be used on every boundary plane. -/
theorem cellSource_add (p₀ p₁ p₂:Parameters d V)
    (s₀ s₁ s₂:ℝ) (hs₀:0< s₀) (hs₁:0< s₁) (hs₂:0< s₂)
    (h₀:CenteredSingularLowerBound p₀.1 s₀) (h₁:CenteredSingularLowerBound p₁.1 s₁)
    (h₂:CenteredSingularLowerBound p₂.1 s₂)
    (τ χ:ℝ) (hτ:0<τ) (hτ1:τ<1) (hχ:0<χ) (hχ1:χ<1) (i:V) :
    cellSource τ χ p₀ p₂ i=cellSource τ χ p₀ p₁ i+cellSource τ χ p₁ p₂ i := by
  have hr:0<τ*χ^2 := by positivity
  have hr1:τ*χ^2<1 := by nlinarith
  unfold cellSource
  rw [smoothed_cellDifference_eq_potential_difference p₀ p₂ s₀ s₂ hs₀ hs₂ h₀ h₂ i _ hr hr1,
    smoothed_cellDifference_eq_potential_difference p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i _ hr hr1,
    smoothed_cellDifference_eq_potential_difference p₁ p₂ s₁ s₂ hs₁ hs₂ h₁ h₂ i _ hr hr1]
  abel

theorem cellSource_sum_sq_triangle (p₀ p₁ p₂:Parameters d V)
    (s₀ s₁ s₂:ℝ) (hs₀:0< s₀) (hs₁:0< s₁) (hs₂:0< s₂)
    (h₀:CenteredSingularLowerBound p₀.1 s₀) (h₁:CenteredSingularLowerBound p₁.1 s₁)
    (h₂:CenteredSingularLowerBound p₂.1 s₂)
    (τ χ:ℝ) (hτ:0<τ) (hτ1:τ<1) (hχ:0<χ) (hχ1:χ<1) :
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (cellSource τ χ p₀ p₂ i))^2) ≤
      2*(∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (cellSource τ χ p₀ p₁ i))^2)+
      2*(∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (cellSource τ χ p₁ p₂ i))^2) := by
  simp_rw [realLp_two_sq_eq_integral (cellSource_memLp τ χ hτ hτ1 hχ hχ1 _ _ _)]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hf:=cellSource_memLp τ χ hτ hτ1 hχ hχ1 p₀ p₁ i
  have hg:=cellSource_memLp τ χ hτ hτ1 hχ hχ1 p₁ p₂ i
  have hh:=cellSource_memLp τ χ hτ hτ1 hχ hχ1 p₀ p₂ i
  calc
    _ ≤ ∫ x,2*(cellSource τ χ p₀ p₁ i x)^2+2*(cellSource τ χ p₁ p₂ i x)^2
        ∂stdGaussian (FSC.Coord d) := by
      apply integral_mono hh.integrable_sq ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      intro x
      rw [cellSource_add p₀ p₁ p₂ s₀ s₁ s₂ hs₀ hs₁ hs₂ h₀ h₁ h₂ τ χ hτ hτ1 hχ hχ1 i]
      change (cellSource τ χ p₀ p₁ i x+cellSource τ χ p₁ p₂ i x)^2≤
        2*(cellSource τ χ p₀ p₁ i x)^2+2*(cellSource τ χ p₁ p₂ i x)^2
      nlinarith [sq_nonneg (cellSource τ χ p₀ p₁ i x-cellSource τ χ p₁ p₂ i x)]
    _ = _ := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),integral_const_mul,integral_const_mul]

/-- Complete source estimate: both actual row perturbation and actual mass
perturbation occur, with no extra alphabet factor or assumed output norm. -/
theorem near_balanced_cellSource_sum_norm_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ χ q:ℝ) (hτ:0<τ) (hχ:0<χ) (hχ1:χ<1)
    (hq:2≤ q) (ht:τ^2=1/(2*q-1)) (hqlog:Real.log ((m:ℝ)/(α/2))≤ q) :
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2
      (cellSource τ χ
        (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i))^2) ≤
      64*Real.exp 1*max 1 (degreeBound e)*degreeBound e*quarticLogConstant 2*
        (1+Real.log (m:ℝ))^4*χ^8*(∑ i,‖D i‖^2)+
      16*Real.exp 1*max 1 (massDegree e)*χ^8*(massGap m α e)⁻¹*
        ∑ i,((v:Fin m→ℝ) i)^2 := by
  have hτ1:τ<1 := by
    have :1/(2*q-1)<1 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    nlinarith
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have htri:=cellSource_sum_sq_triangle
    (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
    (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
    (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))
    α (α/2) (α/2) hα (by positivity) (by positivity)
    (regular_scaled_singular R hG α) hg.1 hg.1 τ χ hτ hτ1 hχ hχ1
  have hrow:=selected_balanced_cellSource_sum_norm_sq_le hm R D hG α hα hD e he hscale
    τ χ q hτ hχ hχ1 hq ht hqlog
  have hmass:=near_mass_cellSource_sum_norm_sq_le hm R D hG α hα hD e he hscale v hv
    τ χ q hτ hχ hχ1 hq ht hqlog
  apply htri.trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤2 by norm_num))
    (mul_le_mul_of_nonneg_left hmass (show (0:ℝ)≤2 by norm_num))
  convert hh using 1
  dsimp only [degreeBound]
  ring


/-- Exact inverse gap and its regular-scale polylog bound. -/
theorem massGap_inv (α e:ℝ) (hα:0<α) (he:0< e) :
    (massGap m α e)⁻¹=2048*Real.pi^2*massDegree e*((m:ℝ)*α)^2 := by
  have hm0:(m:ℝ)≠0:=Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd:massDegree e≠0:=(massDegree_pos e he).ne'
  unfold massGap retainedGapCoefficient
  field_simp
  ring

theorem massGap_inv_le (α e A:ℝ) (hα:0<α) (he:0< e) (_hA:0≤ A)
    (hm:1 ≤ m) (hscale:α≤ A*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)) :
    (massGap m α e)⁻¹≤2048*Real.pi^2*massDegree e*A^2*(1+Real.log (m:ℝ)) := by
  have hmR:(1:ℝ)≤ m:=by exact_mod_cast hm
  have hm0:(0:ℝ)< m:=by linarith
  have hL:0≤1+Real.log (m:ℝ):=by positivity [Real.log_nonneg hmR]
  have hs:=(le_div_iff₀ hm0).mp hscale
  have hs2:=pow_le_pow_left₀ (mul_nonneg hα.le hm0.le) hs 2
  simp only [mul_pow,Real.sq_sqrt hL] at hs2
  rw [massGap_inv α e hα he]
  have hc:0≤2048*Real.pi^2*massDegree e:=by positivity [massDegree_pos e he]
  convert mul_le_mul_of_nonneg_left hs2 hc using 1 <;> ring

def sourceCoefficient (e A:ℝ):ℝ :=
  64*Real.exp 1*max 1 (degreeBound e)*degreeBound e*quarticLogConstant 2+
  32768*Real.exp 1*Real.pi^2*max 1 (massDegree e)*massDegree e*A^2

theorem sourceCoefficient_nonneg (e A:ℝ) (he:0< e):0≤ sourceCoefficient e A := by
  unfold sourceCoefficient quarticLogConstant
  positivity [degreeBound_pos e he,massDegree_pos e he]

/-- Actual near-balanced selected cells at the regular score scale. The source
amplitude is quadratic in both row and mass errors and has only a fourth power
of the logarithmic scale, uniformly in ambient dimension and label count. -/
theorem near_balanced_cellSource_polylog (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e A:ℝ) (he:0< e) (hA:0≤ A)
    (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (hupper:α≤ A*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ))
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ χ q:ℝ) (hτ:0<τ) (hχ:0<χ) (hχ1:χ<1)
    (hq:2≤ q) (ht:τ^2=1/(2*q-1)) (hqlog:Real.log ((m:ℝ)/(α/2))≤ q) :
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2
      (cellSource τ χ
        (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i))^2) ≤
      sourceCoefficient e A*(1+Real.log (m:ℝ))^4*χ^8*
        ((∑ i,‖D i‖^2)+(∑ i,((v:Fin m→ℝ) i)^2)) := by
  have hb:=near_balanced_cellSource_sum_norm_sq_le hm R D hG α hα hD e he hscale v hv
    τ χ q hτ hχ hχ1 hq ht hqlog
  have hgap:=massGap_inv_le α e A hα he hA (by omega) hupper
  have hmR:(1:ℝ)≤ m:=by exact_mod_cast (show 1≤ m by omega)
  have hL:1≤1+Real.log (m:ℝ):=by linarith [Real.log_nonneg hmR]
  have hLpow:1+Real.log (m:ℝ)≤(1+Real.log (m:ℝ))^4 := by
    simpa using pow_le_pow_right₀ hL (show 1≤4 by norm_num)
  let a:=64*Real.exp 1*max 1 (degreeBound e)*degreeBound e*quarticLogConstant 2
  let b:=32768*Real.exp 1*Real.pi^2*max 1 (massDegree e)*massDegree e*A^2
  let L:=1+Real.log (m:ℝ)
  let F:=∑ i,‖D i‖^2
  let Z:=∑ i,((v:Fin m→ℝ) i)^2
  have ha:0≤ a:=by dsimp [a,quarticLogConstant]; positivity [degreeBound_pos e he]
  have hb0:0≤ b:=by dsimp [b]; positivity [massDegree_pos e he]
  have hF:0≤ F:=Finset.sum_nonneg fun i _=> sq_nonneg _
  have hZ:0≤ Z:=Finset.sum_nonneg fun i _=> sq_nonneg _
  have he1:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap (show 0≤16*Real.exp 1*max 1 (massDegree e)*χ^8 by positivity)) hZ
  have he2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLpow hb0) (mul_nonneg (pow_nonneg hχ.le 8) hZ)
  have hmass:16*Real.exp 1*max 1 (massDegree e)*χ^8*(massGap m α e)⁻¹*Z≤ b*L^4*χ^8*Z := by
    calc
      _ ≤ b*L*χ^8*Z := he1.trans_eq (by dsimp only [b,L]; ring)
      _ ≤ _ := by convert he2 using 1 <;> dsimp only [L] <;> ring
  apply hb.trans
  change a*L^4*χ^8*F+_≤(a+b)*L^4*χ^8*(F+Z)
  have hcross1:0≤ a*L^4*χ^8*Z := by positivity
  have hcross2:0≤ b*L^4*χ^8*F := by positivity
  nlinarith only [hmass,hcross1,hcross2]


/-- The actual mass-offset derivative is bounded in Euclidean label norm. -/
theorem near_mass_response_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
    (∑ i,(((deriv (offsetLine (α•R+D) (fun _=>(m:ℝ)⁻¹) v) t:
      centeredGauge (Fin m)):Fin m→ℝ) i)^2) ≤
      ((massGap m α e)⁻¹)^2*∑ i,((v:Fin m→ℝ) i)^2 := by
  let B:=α•R+D
  let p₀:Fin m→ℝ:=fun _=>(m:ℝ)⁻¹
  let u:centeredGauge (Fin m):=deriv (offsetLine B p₀ v) t
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hm0:(0:ℝ)< m:=Nat.cast_pos.mpr (NeZero.pos m)
  have hp₀:∑ i,p₀ i=1:=by simp [p₀,NeZero.ne m]
  have hb:=uniform_massLine_box v hv t ht
  have hp:∀ i,0< massLine p₀ v t i:=fun i=> lt_of_lt_of_le (by positivity) (hb i).1
  have hJ:=offsetLine_jacobian_response B (α/2) (by positivity) hg.1 p₀ v hp₀ t hp
  have hgap:=near_mass_gap hm R D hG α hα hD e he hscale (massLine p₀ v t) hp
    (massLine_sum p₀ v hp₀ t) (fun i=>(hb i).1) (fun i=>(hb i).2) u u.property
  have hbound:=inverse_pairing_le B (offsetLine B p₀ v t) u v (massGap m α e)
    (massGap_pos α e hα he) hgap hJ
  have hgpos:=massGap_pos (m:=m) α e hα he
  change massGap m α e*(∑ i,((u:Fin m→ℝ) i)^2)≤
    (u:Fin m→ℝ) ⬝ᵥ (offsetJacobian B (offsetLine B p₀ v t) *ᵥ (u:Fin m→ℝ)) at hgap
  change offsetJacobian B (offsetLine B p₀ v t) *ᵥ (u:Fin m→ℝ)=(v:Fin m→ℝ) at hJ
  rw [hJ] at hgap
  have hfinal:=mul_le_mul_of_nonneg_left (hgap.trans hbound) (inv_nonneg.mpr hgpos.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hgpos.ne',one_mul,pow_two,u,B,p₀] using hfinal

/-- Finite mass-offset change obtained from the actual C1 path; no
coordinatewise mean-value estimates or alphabet factor are introduced. -/
theorem near_mass_offset_difference_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ))) :
    (∑ i,((selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)):Fin m→ℝ) i-
      (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹):Fin m→ℝ) i)^2) ≤
      ((massGap m α e)⁻¹)^2*∑ i,((v:Fin m→ℝ) i)^2 := by
  let B:=α•R+D
  let p₀:Fin m→ℝ:=fun _=>(m:ℝ)⁻¹
  let f:ℝ→EuclideanSpace ℝ (Fin m):=fun t=> offsetVector (offsetLine B p₀ v t)
  let f':ℝ→EuclideanSpace ℝ (Fin m):=fun t=> offsetVector
    (deriv (offsetLine B p₀ v) t:centeredGauge (Fin m))
  let C:=((massGap m α e)⁻¹)^2*∑ i,((v:Fin m→ℝ) i)^2
  have hC:0≤ C:=by dsimp [C]; positivity
  have hg := segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hm0:(0:ℝ)< m:=Nat.cast_pos.mpr (NeZero.pos m)
  have hp₀:∑ i,p₀ i=1:=by simp [p₀,NeZero.ne m]
  have hd t (ht:t∈Icc (0:ℝ) 1):HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t:=by
    have hb:=uniform_massLine_box v hv t ht
    have hp:∀ i,0< massLine p₀ v t i:=fun i=> lt_of_lt_of_le (by positivity) (hb i).1
    have hc:=offsetLine_C1 B (α/2) (by positivity) hg.1 p₀ v hp₀ t hp
    have hder:HasDerivAt (offsetLine B p₀ v) (deriv (offsetLine B p₀ v) t) t :=
      (hc.differentiableAt (by norm_num)).hasDerivAt
    have hder':HasDerivAt (fun s:ℝ=>(offsetLine B p₀ v s:Fin m→ℝ))
        ((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ) t :=
      (centeredGauge (Fin m)).subtypeL.hasFDerivAt.comp_hasDerivAt t hder
    have hi i:HasDerivAt (fun s:ℝ=>(offsetLine B p₀ v s:Fin m→ℝ) i)
        (((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ) i) t := by
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i:(Fin m→ℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivAt t hder'
    exact (HasDerivAt.fun_sum (u:=Finset.univ)
      (fun i _=>(hi i).smul_const (EuclideanSpace.basisFun (Fin m) ℝ i))).hasDerivWithinAt
  have hb t (ht:t∈Ico (0:ℝ) 1):‖f' t‖≤ Real.sqrt C := by
    have hh:=near_mass_response_sq_le hm R D hG α hα hD e he hscale v hv t ⟨ht.1,ht.2.le⟩
    have hsq:‖f' t‖^2≤ C:=by rw [offsetVector_norm_sq]; exact hh
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt hC]; exact hsq)
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  have hh2:=pow_le_pow_left₀ (norm_nonneg (f 1-f 0)) hh 2
  rw [Real.sq_sqrt hC] at hh2
  dsimp only [f] at hh2
  rw [offsetVector_difference_norm_sq] at hh2
  simpa only [offsetLine,massLine,zero_smul,one_smul,add_zero,p₀,B,C] using hh2

/-- The actual near-balanced selected offsets include both row and mass terms.
The second coefficient is at most a fixed multiple of log(m)^2 at the regular
scale, since massGap_inv_le has already been proved. -/
theorem near_balanced_selected_offset_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ))) :
    (∑ i,((selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)):Fin m→ℝ) i)^2) ≤
      2*offsetCoefficient m α e*(∑ i,‖D i‖^2)+
      2*((massGap m α e)⁻¹)^2*(∑ i,((v:Fin m→ℝ) i)^2) := by
  have hr:=selected_offset_sq_le hm R D hG α hα hD e he hscale 0
  simp only [sub_zero] at hr
  have hmasses:=near_mass_offset_difference_sq_le hm R D hG α hα hD e he hscale v hv
  have hpoint (a b:ℝ):a^2≤2*b^2+2*(a-b)^2:=by nlinarith [sq_nonneg (a-2*b)]
  calc
    _ ≤ ∑ i,(2*((selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹):Fin m→ℝ) i)^2+
        2*((selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)):Fin m→ℝ) i-
          (selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹):Fin m→ℝ) i)^2) :=
      Finset.sum_le_sum fun i _=> hpoint _ _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      convert add_le_add (mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤2 by norm_num))
        (mul_le_mul_of_nonneg_left hmasses (show (0:ℝ)≤2 by norm_num)) using 1
      ring

end NegativeVotingNearBalancedSourceInputs
