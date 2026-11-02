import GaussianSecondChaosHessian

/-! The actual Hessian through any coherent score lift.  This separates the
analytic derivative from the arbitrary choice used to prove existence, and
allows a separately constructed norm-controlled lift in quantitative bounds. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingCoherentLiftHessian
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingQuadraticBulkDifferential NegativeVotingFanJointMass
  NegativeVotingFanQuadraticSecondDerivative NegativeVotingFanMassSecondDerivative
  NegativeVotingSecondChaosHessian NegativeVotingFanQuadraticMoments
  NegativeVotingQuadraticAffineTransport NegativeVotingCapTail NegativeVotingModern
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance fieldsNormed (d : ℕ) : NormedAddCommGroup (Fields d) := inferInstance
local instance fieldsDualNormed (d : ℕ) : NormedAddCommGroup (Fields d→L[ℝ] ℝ) := inferInstance
local instance fieldsDualSpace (d : ℕ) : NormedSpace ℝ (Fields d→L[ℝ] ℝ) := inferInstance
local instance endomorphismsNormed : NormedAddCommGroup (FSC.Coord d→L[ℝ] FSC.Coord d) := inferInstance
local instance endomorphismsSpace : NormedSpace ℝ (FSC.Coord d→L[ℝ] FSC.Coord d) := inferInstance
local instance liftsNormed : NormedAddCommGroup ((ι→ℝ)→L[ℝ] FSC.Coord d) := inferInstance
local instance liftsSpace : NormedSpace ℝ ((ι→ℝ)→L[ℝ] FSC.Coord d) := inferInstance
local instance velocitiesNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] Fields d) := inferInstance
local instance velocitiesSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] Fields d) := inferInstance
local instance parameterDualNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] ℝ) := inferInstance
local instance parameterDualSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] ℝ) := inferInstance

/-- The only algebraic condition on the lift used below. -/
def CoherentLift (B : ι→FSC.Coord d) (L : (ι→ℝ)→L[ℝ] FSC.Coord d) : Prop :=
  ∀ (q:ι→ℝ) (i j:ι),inner ℝ (B i-B j) (L q)=q i-q j

def liftLinearVariation (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    Parameters d ι→L[ℝ] FSC.Coord d→L[ℝ] FSC.Coord d :=
  (ContinuousLinearMap.fst ℝ _ _).comp (velocityMap L)

def liftChart (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ p : Parameters d ι) :
    FSC.Coord d→L[ℝ] FSC.Coord d :=
  ContinuousLinearMap.id ℝ _+liftLinearVariation L (p-p₀)

@[simp] theorem liftChart_base (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι) :
    liftChart L p₀ p₀=ContinuousLinearMap.id ℝ _ := by simp [liftChart]

def movingLift (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ p : Parameters d ι) :
    (ι→ℝ)→L[ℝ] FSC.Coord d := (Ring.inverse (liftChart L p₀ p)).comp L

@[simp] theorem movingLift_base (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι) :
    movingLift L p₀ p₀=L := by
  unfold movingLift
  rw [liftChart_base]
  change (Ring.inverse (1 : FSC.Coord d→L[ℝ] FSC.Coord d)).comp _=_
  rw [Ring.inverse_one]
  rfl

theorem liftChart_pair_inner (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L)
    (p : Parameters d ι) (x : FSC.Coord d) (i j : ι) :
    inner ℝ (B i-B j) (liftChart L (B,h) p x)=inner ℝ (p.1 i-p.1 j) x := by
  have hh := hL (fun k=>inner ℝ (p.1 k-B k) x) i j
  change inner ℝ (B i-B j) (x+L (fun k=>inner ℝ (p.1 k-B k) x))=_
  rw [inner_add_right]
  simp only [inner_sub_left] at hh ⊢
  linarith

theorem movingLift_coherent (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L)
    (p : Parameters d ι) (hp : IsUnit (liftChart L (B,h) p)) :
    CoherentLift p.1 (movingLift L (B,h) p) := by
  intro q i j
  rw [← liftChart_pair_inner B h L hL p]
  change inner ℝ (B i-B j) (liftChart L (B,h) p
    (Ring.inverse (liftChart L (B,h) p) (L q)))=_
  have hc : liftChart L (B,h) p (Ring.inverse (liftChart L (B,h) p) (L q))=L q := by
    change (liftChart L (B,h) p * Ring.inverse (liftChart L (B,h) p)) (L q)=_
    rw [Ring.mul_inverse_cancel _ hp]
    rfl
  rw [hc,hL]

theorem eventually_liftChart_isUnit (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι) :
    ∀ᶠ p : Parameters d ι in 𝓝 p₀,IsUnit (liftChart L p₀ p) := by
  have hc : ContinuousAt (fun p:Parameters d ι=>‖liftLinearVariation L (p-p₀)‖) p₀ := by
    fun_prop
  filter_upwards [hc.eventually_lt continuousAt_const
    (by simp : ‖liftLinearVariation L (p₀-p₀)‖<(1:ℝ))] with p hp
  have hh := isUnit_one_sub_of_norm_lt_one (x:= -liftLinearVariation L (p-p₀))
    (by simpa only [norm_neg] using hp)
  convert! hh using 1 <;> simp only [sub_neg_eq_add,liftChart,ContinuousLinearMap.one_def]

theorem hasFDerivAt_liftChartInverse (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι) :
    HasFDerivAt (fun p=>Ring.inverse (liftChart L p₀ p)) (-liftLinearVariation L) p₀ := by
  have hl : HasFDerivAt (liftChart L p₀) (liftLinearVariation L) p₀ := by
    unfold liftChart
    convert! ((liftLinearVariation L).hasFDerivAt.comp p₀
      ((hasFDerivAt_id p₀).sub_const p₀)).const_add
        (ContinuousLinearMap.id ℝ (FSC.Coord d)) using 1
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.id ℝ (FSC.Coord d→L[ℝ] FSC.Coord d)) (liftChart L p₀ p₀) := by
    have hh := hasFDerivAt_ringInverse (𝕜:=ℝ) (1 : (FSC.Coord d→L[ℝ] FSC.Coord d)ˣ)
    convert hh using 1
    · apply ContinuousLinearMap.ext
      intro A
      simp [ContinuousLinearMap.mulLeftRight_apply]
    · simp [ContinuousLinearMap.one_def]
  convert! hi.comp p₀ hl using 1

def movingLiftDerivative (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    Parameters d ι→L[ℝ] ((ι→ℝ)→L[ℝ] FSC.Coord d) :=
  ((ContinuousLinearMap.compL ℝ (ι→ℝ) (FSC.Coord d) (FSC.Coord d)).flip L).comp
    (-liftLinearVariation L)

def movingVelocityDerivative (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] Fields d :=
  velocityLiftCLM.comp (movingLiftDerivative L)

theorem hasFDerivAt_movingVelocity (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι) :
    HasFDerivAt (fun p=>velocityMap (movingLift L p₀ p)) (movingVelocityDerivative L) p₀ := by
  have hl : HasFDerivAt (movingLift L p₀) (movingLiftDerivative L) p₀ :=
    ((ContinuousLinearMap.compL ℝ (ι→ℝ) (FSC.Coord d) (FSC.Coord d)).flip L).hasFDerivAt.comp
      p₀ (hasFDerivAt_liftChartInverse L p₀)
  exact (velocityLiftCLM (d:=d) (ι:=ι)).hasFDerivAt.comp p₀ hl

theorem movingVelocityDerivative_apply (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (ε δ : Parameters d ι) :
    movingVelocityDerivative L ε δ=
      -((velocityMap L ε).1.comp (velocityMap L δ).1,
        (velocityMap L ε).1 (velocityMap L δ).2) := by
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    rfl
  · rfl

/-- The structural Hessian for a field-linear bulk functional. -/
def transportHessian (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (K : Fields d→L[ℝ] ℝ)
    (K' : Parameters d ι→L[ℝ] Fields d→L[ℝ] ℝ) :
    Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ K).comp
    (movingVelocityDerivative L) +
  ((ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ).flip (velocityMap L)).comp K'

theorem transportHessian_apply (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (K : Fields d→L[ℝ] ℝ)
    (K' : Parameters d ι→L[ℝ] Fields d→L[ℝ] ℝ) (ε δ : Parameters d ι) :
    transportHessian L K K' ε δ=K' ε (velocityMap L δ)-
      K ((velocityMap L ε).1.comp (velocityMap L δ).1,
        (velocityMap L ε).1 (velocityMap L δ).2) := by
  change K (movingVelocityDerivative L ε δ)+K' ε (velocityMap L δ)=_
  rw [movingVelocityDerivative_apply,map_neg]
  ring

theorem hasFDerivAt_transport (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (p₀ : Parameters d ι)
    (K : Parameters d ι→Fields d→L[ℝ] ℝ)
    (K' : Parameters d ι→L[ℝ] Fields d→L[ℝ] ℝ) (hK : HasFDerivAt K K' p₀) :
    HasFDerivAt (fun p=>(K p).comp (velocityMap (movingLift L p₀ p)))
      (transportHessian L (K p₀) K') p₀ := by
  simpa only [transportHessian,movingLift_base] using hK.clm_comp (hasFDerivAt_movingVelocity L p₀)

def quadraticHessian (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι) (v y : FSC.Coord d) :=
  transportHessian L (bulkFunctional B h i v y) (bulkFunctionalDerivative B h i v y)

def constantHessian (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι) :=
  transportHessian L (massFunctional B h i) (massFunctionalDerivative B h i)

/-- Pointwise quadratic Hessian formula in the selected lift. -/
theorem quadraticHessian_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι) (v y : FSC.Coord d)
    (ε δ : Parameters d ι) :
    quadraticHessian B h L i v y ε δ=
      testedCellDerivative B h i (affineBulk v y (velocityMap L δ).1 (velocityMap L δ).2) ε-
      bulkFunctional B h i v y ((velocityMap L ε).1.comp (velocityMap L δ).1,
        (velocityMap L ε).1 (velocityMap L δ).2) := by
  rw [quadraticHessian,transportHessian_apply,
    bulkFunctionalDerivative_apply B h σ hσ hlower i v y ε]

/-- Pointwise constant-test Hessian formula in the selected lift. -/
theorem constantHessian_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι) (ε δ : Parameters d ι) :
    constantHessian B h L i ε δ=
      testedCellDerivative B h i (massBulk (velocityMap L δ).1 (velocityMap L δ).2) ε-
      massFunctional B h i ((velocityMap L ε).1.comp (velocityMap L δ).1,
        (velocityMap L ε).1 (velocityMap L δ).2) := by
  rw [constantHessian,transportHessian_apply,
    massFunctionalDerivative_apply B h σ hσ hlower i ε]

theorem hasFDerivAt_quadraticDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι) (v y : FSC.Coord d) :
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i
      (fun x=>inner ℝ v x*inner ℝ y x)) (quadraticHessian B h L i v y) (B,h) := by
  apply (hasFDerivAt_transport L (B,h) _ _
    (hasFDerivAt_bulkFunctional B h σ hσ hlower i v y)).congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower,
    eventually_liftChart_isUnit L (B,h)] with p hp hu
  apply ContinuousLinearMap.ext
  intro δ
  exact testedCellDerivative_bilinear_bulk p.1 p.2 (σ/2) (by positivity) hp
    (movingLift L (B,h) p) (movingLift_coherent B h L hL p hu) i v y δ

theorem hasFDerivAt_constantDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι) :
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i (fun _=>1))
      (constantHessian B h L i) (B,h) := by
  apply (hasFDerivAt_transport L (B,h) _ _
    (hasFDerivAt_massFunctional B h σ hσ hlower i)).congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower,
    eventually_liftChart_isUnit L (B,h)] with p hp hu
  apply ContinuousLinearMap.ext
  intro δ
  exact testedCellDerivative_one_bulk p.1 p.2 (σ/2) (by positivity) hp
    (movingLift L (B,h) p) (movingLift_coherent B h L hL p hu) i δ

def centeredHessian (B : ι→FSC.Coord d) (h : ι→ℝ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (i : ι) (v y : FSC.Coord d) :=
  quadraticHessian B h L i v y-inner ℝ v y • constantHessian B h L i

theorem hasFDerivAt_centeredDerivative (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i : ι) (v y : FSC.Coord d) :
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i (centeredBilinearTest v y))
      (centeredHessian B h L i v y) (B,h) := by
  have hd := (hasFDerivAt_quadraticDerivative B h σ hσ hlower L hL i v y).sub
    ((hasFDerivAt_constantDerivative B h σ hσ hlower L hL i).const_smul (inner ℝ v y))
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower] with p hp
  exact testedCellDerivative_centered_eq p.1 p.2 (σ/2) (by positivity) hp i v y

/-- Every coherent lift computes the same actual centered-cell Hessian. -/
theorem centeredHessian_eq_canonical (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L)
    (i₀ i : ι) (v y : FSC.Coord d) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    centeredHessian B h L i v y=centeredCellHessian B hB h i₀ i v y :=
  (hasFDerivAt_centeredDerivative B h σ hσ hlower L hL i v y).unique
    (hasFDerivAt_testedCellDerivative_centered B h σ hσ hlower i₀ i v y)

/-- Finite-sum actual second-chaos Hessian, expressed using any chosen coherent lift. -/
def energyHessian (B : ι→FSC.Coord d) (h : ι→ℝ) (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  ∑ i,∑ j,∑ k,(secondMomentTensor B h i j k • centeredHessian B h L i
    (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ k) +
    (testedCellDerivative B h i (tensorTest j k)).smulRight
      (testedCellDerivative B h i (tensorTest j k)))

theorem energyHessian_eq_canonical (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (i₀ : ι) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    energyHessian B h L=secondEnergyHessian B hB h i₀ := by
  dsimp only [energyHessian,secondEnergyHessian,tensorHessian]
  simp_rw [centeredHessian_eq_canonical B h σ hσ hlower L hL i₀]

/-- No norm bound is assumed here; a separately proved bounded lift may be substituted. -/
theorem hasFDerivAt_fderiv_actual_second_chaos_of_coherent (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    HasFDerivAt
      (fun p:Parameters d ι=>fderiv ℝ (fun q:Parameters d ι=>chaosEnergy
        (fun x:Fin d→ℝ=>weights q.1 q.2 (MeasurableEquiv.toLp 2 (Fin d→ℝ) x)) 2) p)
      (energyHessian B h L) (B,h) := by
  let i₀ : ι := Classical.arbitrary ι
  rw [energyHessian_eq_canonical B h σ hσ hlower L hL i₀]
  exact hasFDerivAt_fderiv_actual_second_chaos B h σ hσ hlower i₀

end NegativeVotingCoherentLiftHessian
