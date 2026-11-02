import GaussianFanMassSecondDerivative
import GaussianFanSelectedOffsets
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual second differentiability of the selected Gaussian balancing
map. The joint mass Hessian is transported through its actual local inverse;
no offset acceleration or second derivative is assumed. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical Topology RealInnerProductSpace
namespace NegativeVotingSelectedOffsetSecondDerivative
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanJointMass
  NegativeVotingFanJointInverse NegativeVotingFanSelectedOffsets NegativeVotingFanMassSecondDerivative
  NegativeVotingCapTail NegativeVotingQuadraticBulkDifferential NegativeVotingFanScore NegativeVotingFacetDegree

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem differentiableAt_fderiv_of_local_inverse (F G : E→E) (L : E→E→L[ℝ] E)
    (x c : E) (hG : ContDiffAt ℝ 1 G x)
    (hL : DifferentiableAt ℝ L (G x)) (hu : IsUnit (L (G x)))
    (hF : ∀ᶠ y in 𝓝 x,HasFDerivAt F (L (G y)) (G y))
    (hFG : ∀ᶠ y in 𝓝 x,F (G y)=y+c) :
    DifferentiableAt ℝ (fderiv ℝ G) x := by
  have hDG : DifferentiableAt ℝ G x:=hG.differentiableAt (by norm_num)
  have hnearG:∀ᶠ y in 𝓝 x,DifferentiableAt ℝ G y:=
    (hG.eventually (by norm_num)).mono fun y hy=>hy.differentiableAt (by norm_num)
  have hnearU:∀ᶠ y in 𝓝 x,IsUnit (L (G y)):=
    (hL.continuousAt.comp hG.continuousAt).eventually (Units.isOpen.mem_nhds hu)
  have he : (fun y=>fderiv ℝ G y)=ᶠ[𝓝 x] fun y=>Ring.inverse (L (G y)):=by
    filter_upwards [hnearG,hnearU,hF,hFG.eventually_nhds] with y hy huy hfy heq
    have hc:HasFDerivAt (fun z=>F (G z)) (ContinuousLinearMap.id ℝ E) y:=by
      apply ((hasFDerivAt_id y).add_const c).congr_of_eventuallyEq
      exact heq
    have hd:=hfy.comp y hy.hasFDerivAt
    have hm : L (G y)*(fderiv ℝ G y)=1:=hd.unique hc
    calc
      _ = Ring.inverse (L (G y))*(L (G y)*(fderiv ℝ G y)):=by
        rw [Ring.inverse_mul_cancel_left _ _ huy]
      _ = _:=by rw [hm,mul_one]
  exact ((hL.comp x hDG).inverse hu).congr_of_eventuallyEq he

end Inverse

section Fan
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]


def massDerivativeAssembler : (V→Parameters d V→L[ℝ] ℝ)→ₗ[ℝ] (Parameters d V→L[ℝ] (V→ℝ)) where
  toFun:=ContinuousLinearMap.pi
  map_add' f g:=by apply ContinuousLinearMap.ext;intro x;funext i;rfl
  map_smul' a f:=by apply ContinuousLinearMap.ext;intro x;funext i;rfl

def massDerivativeAssemblerCLM : (V→Parameters d V→L[ℝ] ℝ)→L[ℝ] (Parameters d V→L[ℝ] (V→ℝ)) :=
  (massDerivativeAssembler (d:=d) (V:=V)).toContinuousLinearMap

theorem differentiableAt_jointMassDerivativeAt (B : V→FSC.Coord d) (h : V→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : V) :
    DifferentiableAt ℝ (fun p:Parameters d V=>jointMassDerivativeAt p.1 p.2 i) (B,h) := by
  have hd:=(hasFDerivAt_testedCellDerivative_one B h σ hσ hlower (Classical.arbitrary V) i).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower] with p hp
  exact jointMassDerivativeAt_eq_tested p.1 p.2 (σ/2) (by positivity) hp i

theorem differentiableAt_jointMassDerivative (B : V→FSC.Coord d) (h : V→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    DifferentiableAt ℝ (fun p:Parameters d V=>jointMassDerivative p.1 p.2) (B,h) := by
  have hd : DifferentiableAt ℝ (fun p:Parameters d V=>fun i=>jointMassDerivativeAt p.1 p.2 i) (B,h):=
    differentiableAt_pi.mpr (fun i=>differentiableAt_jointMassDerivativeAt B h σ hσ hlower i)
  exact massDerivativeAssemblerCLM.differentiableAt.comp (B,h) hd

theorem differentiableAt_jointCoordinatesDerivative (B : V→FSC.Coord d) (h : centeredGauge V)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    DifferentiableAt ℝ (fun p:JointCoordinates d V=>jointCoordinatesDerivative p.1 p.2) (B,h) := by
  have hd:=(differentiableAt_jointMassDerivative B h σ hσ hlower).comp (B,h)
    (parameterEmbedding (d:=d) (ι:=V)).differentiableAt
  have hcenter : DifferentiableAt ℝ (fun _ : JointCoordinates d V=>(centering : (V→ℝ)→L[ℝ] centeredGauge V)) (B,h):=differentiableAt_const _
  have hembed : DifferentiableAt ℝ (fun _ : JointCoordinates d V=>(parameterEmbedding (d:=d) (ι:=V))) (B,h):=differentiableAt_const _
  have hc : DifferentiableAt ℝ (fun p:JointCoordinates d V=>jointCenteredMassDerivative p.1 p.2) (B,h):=
    hcenter.clm_comp (hd.clm_comp hembed)
  let L0 : JointCoordinates d V→L[ℝ] JointCoordinates d V:=
    (ContinuousLinearMap.inl ℝ (V→FSC.Coord d) (centeredGauge V)).comp (ContinuousLinearMap.fst ℝ _ _)
  let Li : centeredGauge V→L[ℝ] JointCoordinates d V:=ContinuousLinearMap.inr ℝ _ _
  have h0 : DifferentiableAt ℝ (fun _ : JointCoordinates d V=>L0) (B,h):=differentiableAt_const _
  have hi : DifferentiableAt ℝ (fun _ : JointCoordinates d V=>Li) (B,h):=differentiableAt_const _
  have hh:=h0.add (hi.clm_comp hc)
  convert hh using 1
  funext p
  apply ContinuousLinearMap.ext
  intro x
  simp [L0,Li,jointCoordinatesDerivative]

def selectedJoint (p : V→ℝ) (q : JointCoordinates d V) : centeredGauge V :=
  selectedOffsets q.1 (p+(q.2:V→ℝ))

def selectedGraph (p : V→ℝ) (q : JointCoordinates d V) : JointCoordinates d V :=
  (q.1,selectedJoint p q)

/-- The actual joint selected graph, not a postulated inverse, is twice
Frechet differentiable at every positive-mass full-rank fan. -/
theorem differentiableAt_fderiv_selectedGraph (B : V→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    DifferentiableAt ℝ (fderiv ℝ (selectedGraph (d:=d) p)) (B,0) := by
  let h₀:=selectedOffsets B p
  have hG : ContDiffAt ℝ 1 (selectedGraph (d:=d) p) (B,0):=
    contDiffAt_fst.prodMk (selectedOffsets_joint_C1 B σ hσ hlower p hp hs)
  have hbase : selectedGraph (d:=d) p (B,0)=(B,h₀):=by simp [selectedGraph,selectedJoint,h₀]
  have hL : DifferentiableAt ℝ (fun q:JointCoordinates d V=>jointCoordinatesDerivative q.1 q.2)
      (selectedGraph (d:=d) p (B,0)):=by
    rw [hbase]
    exact differentiableAt_jointCoordinatesDerivative B h₀ σ hσ hlower
  have hu:IsUnit (jointCoordinatesDerivative B h₀):=
    ⟨(jointCoordinatesDerivativeEquiv B h₀ σ hσ hlower).toUnit,rfl⟩
  have hlu:∀ᶠ q:JointCoordinates d V in 𝓝 (B,0),CenteredSingularLowerBound q.1 (σ/2):=by
    have hc:ContinuousAt (fun q:JointCoordinates d V=>(q.1,(h₀:V→ℝ))) (B,0):=by fun_prop
    exact hc.eventually (eventually_centeredSingularLowerBound B h₀ σ hσ hlower)
  have hpp:∀ᶠ q:JointCoordinates d V in 𝓝 (B,0),∀i,0<(p+(q.2:V→ℝ)) i:=by
    rw [Filter.eventually_all]
    intro i
    have hc:ContinuousAt (fun q:JointCoordinates d V=>(p+(q.2:V→ℝ)) i) (B,0):=by fun_prop
    exact hc.eventually (lt_mem_nhds (by simpa using hp i))
  apply differentiableAt_fderiv_of_local_inverse jointMassCoordinates (selectedGraph p)
    (fun q:JointCoordinates d V=>jointCoordinatesDerivative q.1 q.2)
    (B,0) (0,centering p) hG hL (by simpa only [hbase] using hu)
  · filter_upwards [hlu] with q hq
    exact hasFDerivAt_jointMassCoordinates q.1 (selectedJoint p q) (σ/2) (by positivity) hq
  · filter_upwards [hlu,hpp] with q hq hqp
    have hqi : Function.Injective q.1:=by
      intro i j he
      by_contra hij
      exact centered_singular_rows_ne q.1 (σ/2) (by positivity) hq i j hij he
    have hsum : (∑i,(p+(q.2:V→ℝ)) i)=1:=by
      have hz : (∑i,(q.2:V→ℝ) i)=0:=q.2.property
      simp only [Pi.add_apply,Finset.sum_add_distrib,hs,hz,add_zero]
    apply Prod.ext
    · simp [selectedGraph,jointMassCoordinates]
    · change centering (mass q.1 (selectedOffsets q.1 (p+(q.2:V→ℝ))))=q.2+centering p
      rw [selectedOffsets_mass q.1 hqi _ hqp hsum,map_add,centering_centered,add_comm]

/-- Actual second derivative of the centered offset selection itself. -/
theorem differentiableAt_fderiv_selectedJoint (B : V→FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (p : V→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1) :
    DifferentiableAt ℝ (fderiv ℝ (selectedJoint (d:=d) p)) (B,0) := by
  have hG : ContDiffAt ℝ 1 (selectedGraph (d:=d) p) (B,0):=
    contDiffAt_fst.prodMk (selectedOffsets_joint_C1 B σ hσ hlower p hp hs)
  have hd:=differentiableAt_fderiv_selectedGraph B σ hσ hlower p hp hs
  let T : JointCoordinates d V→L[ℝ] centeredGauge V:=ContinuousLinearMap.snd ℝ _ _
  have hc : DifferentiableAt ℝ (fun _ : JointCoordinates d V=>T) (B,0):=differentiableAt_const _
  have he : (fderiv ℝ (selectedJoint (d:=d) p))=ᶠ[𝓝 (B,0)]
      fun q=>T.comp (fderiv ℝ (selectedGraph (d:=d) p) q):=by
    filter_upwards [hG.eventually (by norm_num)] with q hq
    exact (T.hasFDerivAt.comp q ((hq.differentiableAt (by norm_num)).hasFDerivAt)).fderiv
  exact (hc.clm_comp hd).congr_of_eventuallyEq he

end Fan

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule at the derivative level only requires actual second
Frechet differentiability of the outer map. No C2 premise is substituted
for the newly proved second derivative. -/
theorem differentiableAt_deriv_comp_of_fderiv (f : E→F) (g : ℝ→E) (t : ℝ)
    (hf : ContDiffAt ℝ 1 f (g t)) (hdf : DifferentiableAt ℝ (fderiv ℝ f) (g t))
    (hg : ContDiffAt ℝ 2 g t) :
    DifferentiableAt ℝ (deriv (fun s=>f (g s))) t := by
  have hgd : DifferentiableAt ℝ g t:=hg.differentiableAt (by norm_num)
  have hgg : DifferentiableAt ℝ (deriv g) t:=
    (hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hdf.comp t hgd).clm_apply hgg
  have hnearF : ∀ᶠ s in 𝓝 t,DifferentiableAt ℝ f (g s):=
    hgd.continuousAt.eventually ((hf.eventually (by norm_num)).mono fun y hy=>hy.differentiableAt (by norm_num))
  have hnearG:∀ᶠ s in 𝓝 t,DifferentiableAt ℝ g s:=
    (hg.eventually (by norm_num)).mono fun y hy=>hy.differentiableAt (by norm_num)
  have he : (deriv (fun s=>f (g s)))=ᶠ[𝓝 t] fun s=>(fderiv ℝ f (g s)) (deriv g s):=by
    filter_upwards [hnearF,hnearG] with s hfs hgs
    exact (hfs.hasFDerivAt.comp_hasDerivAt s hgs.hasDerivAt).deriv
  exact hd.congr_of_eventuallyEq he

end Composition
end NegativeVotingSelectedOffsetSecondDerivative
