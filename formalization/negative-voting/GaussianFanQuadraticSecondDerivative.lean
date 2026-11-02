import GaussianQuadraticBulkDifferential
import GaussianFanQuadraticTransport
import GaussianFanJointMass

/-! A second derivative of the actual quadratic cell integral.  The lift is
transported by the inverse of the common affine chart; no differentiability
of the cell derivative is assumed. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingFanQuadraticSecondDerivative
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingQuadraticBulkDifferential NegativeVotingFanJointMass
  NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance fieldsNormed (d : ℕ) : NormedAddCommGroup (Fields d) := inferInstance
local instance fieldsDualNormed (d : ℕ) : NormedAddCommGroup (Fields d→L[ℝ] ℝ) := inferInstance
local instance fieldsDualSpace (d : ℕ) : NormedSpace ℝ (Fields d→L[ℝ] ℝ) := inferInstance
local instance endomorphismsNormed : NormedAddCommGroup (FSC.Coord d→L[ℝ] FSC.Coord d) :=
  inferInstance
local instance endomorphismsSpace : NormedSpace ℝ (FSC.Coord d→L[ℝ] FSC.Coord d) :=
  inferInstance
local instance liftsNormed : NormedAddCommGroup ((ι→ℝ)→L[ℝ] FSC.Coord d) := inferInstance
local instance liftsSpace : NormedSpace ℝ ((ι→ℝ)→L[ℝ] FSC.Coord d) := inferInstance
local instance velocitiesNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] Fields d) :=
  inferInstance
local instance velocitiesSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] Fields d) :=
  inferInstance

/-- The original score lift, transported to the current row configuration. -/
def transportedLift (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ : ι) (p : Parameters d ι) : (ι→ℝ)→L[ℝ] FSC.Coord d :=
  (Ring.inverse (chartLinear B hB h i₀ p)).comp (scoreLiftCLM B hB i₀)

@[simp] theorem transportedLift_base (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) :
    transportedLift B hB h i₀ (B,h)=scoreLiftCLM B hB i₀ := by
  unfold transportedLift
  rw [chartLinear_base]
  change (Ring.inverse (1 : FSC.Coord d→L[ℝ] FSC.Coord d)).comp _=_
  rw [Ring.inverse_one]
  rfl

/-- The linear part of the common affine chart transports score differences. -/
theorem chartLinear_pair_inner (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) (p : Parameters d ι) (x : FSC.Coord d) (i j : ι) :
    inner ℝ (B i-B j) (chartLinear B hB h i₀ p x)=inner ℝ (p.1 i-p.1 j) x := by
  have hh := scoreLiftCLM_pair B hB i₀ (fun k=>inner ℝ (p.1 k-B k) x) i j
  simp only [chartLinear,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    linearVariation_apply,Prod.fst_sub,Pi.sub_apply,inner_add_right]
  simp only [inner_sub_left] at hh ⊢
  linarith

/-- The inverse chart gives a valid lift throughout its invertible neighborhood. -/
theorem transportedLift_pair (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) (p : Parameters d ι)
    (hp : IsUnit (chartLinear B hB h i₀ p)) (q : ι→ℝ) (i j : ι) :
    inner ℝ (p.1 i-p.1 j) (transportedLift B hB h i₀ p q)=q i-q j := by
  rw [← chartLinear_pair_inner B hB h i₀ p]
  change inner ℝ (B i-B j)
    (chartLinear B hB h i₀ p (Ring.inverse (chartLinear B hB h i₀ p)
      (scoreLiftCLM B hB i₀ q)))=_
  have hc : chartLinear B hB h i₀ p (Ring.inverse (chartLinear B hB h i₀ p)
      (scoreLiftCLM B hB i₀ q))=scoreLiftCLM B hB i₀ q := by
    change (chartLinear B hB h i₀ p * Ring.inverse (chartLinear B hB h i₀ p))
      (scoreLiftCLM B hB i₀ q)=_
    rw [Ring.mul_inverse_cancel _ hp]
    rfl
  rw [hc,scoreLiftCLM_pair]

/-- Velocity is linear in the chosen score lift. -/
def velocityLiftLinear : ((ι→ℝ)→L[ℝ] FSC.Coord d)→ₗ[ℝ]
    (Parameters d ι→L[ℝ] Fields d) where
  toFun := velocityMap
  map_add' L K := by
    apply ContinuousLinearMap.ext
    intro δ
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro x
      simp only [velocityMap_first,ContinuousLinearMap.add_apply,Prod.fst_add]
    · simp only [velocityMap_second,ContinuousLinearMap.add_apply,Prod.snd_add]
  map_smul' c L := by
    apply ContinuousLinearMap.ext
    intro δ
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro x
      change c • L (fun j=>inner ℝ (δ.1 j) x)=c • L (fun j=>inner ℝ (δ.1 j) x)
      rfl
    · change c • L δ.2=c • L δ.2
      rfl

def velocityLiftCLM : ((ι→ℝ)→L[ℝ] FSC.Coord d)→L[ℝ]
    (Parameters d ι→L[ℝ] Fields d) := velocityLiftLinear.toContinuousLinearMap

@[simp] theorem velocityLiftCLM_apply (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    velocityLiftCLM L=velocityMap L := rfl

theorem differentiableAt_transportedLift (B : ι→FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι→ℝ) (i₀ : ι) :
    DifferentiableAt ℝ (transportedLift B hB h i₀) (B,h) := by
  exact ((contDiffAt_chartInverse B hB h i₀).differentiableAt (by simp)).clm_comp
    (differentiableAt_const (scoreLiftCLM B hB i₀))

theorem differentiableAt_transportedVelocity (B : ι→FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι→ℝ) (i₀ : ι) :
    DifferentiableAt ℝ (fun p=>velocityMap (transportedLift B hB h i₀ p)) (B,h) := by
  exact (velocityLiftCLM (d:=d) (ι:=ι)).differentiableAt.comp (B,h)
    (differentiableAt_transportedLift B hB h i₀)

/-- The inverse chart has derivative minus its linear variation at the identity. -/
theorem hasFDerivAt_chartInverse_base (B : ι→FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι→ℝ) (i₀ : ι) :
    HasFDerivAt (fun p=>Ring.inverse (chartLinear B hB h i₀ p))
      (-linearVariation B hB i₀) (B,h) := by
  have hl : HasFDerivAt (chartLinear B hB h i₀)
      (linearVariation B hB i₀) (B,h) := by
    unfold chartLinear
    convert!
      ((linearVariation B hB i₀).hasFDerivAt.comp (B,h)
        ((hasFDerivAt_id (B,h)).sub_const (B,h))).const_add
          (ContinuousLinearMap.id ℝ (FSC.Coord d)) using 1 <;> simp
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.id ℝ (FSC.Coord d→L[ℝ] FSC.Coord d))
      (chartLinear B hB h i₀ (B,h)) := by
    have hh := hasFDerivAt_ringInverse (𝕜:=ℝ)
      (1 : (FSC.Coord d→L[ℝ] FSC.Coord d)ˣ)
    convert hh using 1
    · apply ContinuousLinearMap.ext
      intro A
      simp [ContinuousLinearMap.mulLeftRight_apply]
    · simp [ContinuousLinearMap.one_def]
  convert! hi.comp (B,h) hl using 1 <;> simp

/-- Derivative of the transported score lift. -/
def liftDerivative (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι) :
    Parameters d ι→L[ℝ] ((ι→ℝ)→L[ℝ] FSC.Coord d) :=
  ((ContinuousLinearMap.compL ℝ (ι→ℝ) (FSC.Coord d) (FSC.Coord d)).flip
    (scoreLiftCLM B hB i₀)).comp (-linearVariation B hB i₀)

@[simp] theorem liftDerivative_apply (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (i₀ : ι) (ε : Parameters d ι) (q : ι→ℝ) :
    liftDerivative B hB i₀ ε q =
      -(linearVariation B hB i₀ ε (scoreLiftCLM B hB i₀ q)) := rfl

theorem hasFDerivAt_transportedLift (B : ι→FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι→ℝ) (i₀ : ι) :
    HasFDerivAt (transportedLift B hB h i₀) (liftDerivative B hB i₀) (B,h) := by
  exact ((ContinuousLinearMap.compL ℝ (ι→ℝ) (FSC.Coord d) (FSC.Coord d)).flip
    (scoreLiftCLM B hB i₀)).hasFDerivAt.comp (B,h)
      (hasFDerivAt_chartInverse_base B hB h i₀)

/-- Derivative of the affine velocity field as the rows move. -/
def velocityDerivative (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι) :
    Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] Fields d :=
  velocityLiftCLM.comp (liftDerivative B hB i₀)

theorem hasFDerivAt_transportedVelocity (B : ι→FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι→ℝ) (i₀ : ι) :
    HasFDerivAt (fun p=>velocityMap (transportedLift B hB h i₀ p))
      (velocityDerivative B hB i₀) (B,h) := by
  exact (velocityLiftCLM (d:=d) (ι:=ι)).hasFDerivAt.comp (B,h)
    (hasFDerivAt_transportedLift B hB h i₀)

/-- The correction term is the negative composition of the two affine fields. -/
theorem velocityDerivative_apply (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (i₀ : ι) (ε δ : Parameters d ι) :
    let V := velocityMap (scoreLiftCLM B hB i₀)
    velocityDerivative B hB i₀ ε δ = -((V ε).1.comp (V δ).1, (V ε).1 (V δ).2) := by
  dsimp only
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    rfl
  · rfl

/-- An explicit bilinear operator for the Hessian of a quadratic cell moment. -/
def bilinearCellHessian (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ i : ι) (v y : FSC.Coord d) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ
    (bulkFunctional B h i v y)).comp (velocityDerivative B hB i₀) +
  ((ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ).flip
    (velocityMap (scoreLiftCLM B hB i₀))).comp (bulkFunctionalDerivative B h i v y)

/-- Near the base configuration, the actual first derivative agrees with the
literal quartic bulk functional composed with the transported affine field. -/
theorem eventually_testedCellDerivative_eq (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    ∀ᶠ p : Parameters d ι in 𝓝 (B,h),
      testedCellDerivative p.1 p.2 i (fun x=>inner ℝ v x*inner ℝ y x)=
        (bulkFunctional p.1 p.2 i v y).comp
          (velocityMap (transportedLift B hB h i₀ p)) := by
  dsimp only
  let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
  filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower,
    eventually_chartLinear_isUnit B hB h i₀] with p hp hu
  apply ContinuousLinearMap.ext
  intro δ
  exact testedCellDerivative_bilinear_bulk p.1 p.2 (σ/2) (by positivity) hp
    (transportedLift B hB h i₀ p) (transportedLift_pair B hB h i₀ p hu) i v y δ

/-- Existence of the actual second derivative of every uncentered quadratic
cell moment, obtained from the bulk transport identity rather than assumed. -/
theorem differentiableAt_testedCellDerivative_bilinear (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) :
    DifferentiableAt ℝ
      (fun p : Parameters d ι=>testedCellDerivative p.1 p.2 i
        (fun x=>inner ℝ v x*inner ℝ y x)) (B,h) := by
  let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
  have hd := (hasFDerivAt_bulkFunctional B h σ hσ hlower i v y).differentiableAt.clm_comp
    (differentiableAt_transportedVelocity B hB h i₀)
  exact hd.congr_of_eventuallyEq (eventually_testedCellDerivative_eq B h σ hσ hlower i₀ i v y)

/-- The explicitly constructed operator is the derivative of the actual first
quadratic-cell derivative. -/
theorem hasFDerivAt_testedCellDerivative_bilinear (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt
      (fun p : Parameters d ι=>testedCellDerivative p.1 p.2 i
        (fun x=>inner ℝ v x*inner ℝ y x))
      (bilinearCellHessian B hB h i₀ i v y) (B,h) := by
  dsimp only
  let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
  have hd := (hasFDerivAt_bulkFunctional B h σ hσ hlower i v y).clm_comp
    (hasFDerivAt_transportedVelocity B hB h i₀)
  have he := hd.congr_of_eventuallyEq
    (eventually_testedCellDerivative_eq B h σ hσ hlower i₀ i v y)
  simpa only [bilinearCellHessian,transportedLift_base] using he

/-- Hessian formula: the differentiated quartic cell integral minus the
correction from differentiating the inverse affine chart. -/
theorem bilinearCellHessian_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i₀ i : ι) (v y : FSC.Coord d) (ε δ : Parameters d ι) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    let V := velocityMap (scoreLiftCLM B hB i₀)
    bilinearCellHessian B hB h i₀ i v y ε δ =
      testedCellDerivative B h i
        (NegativeVotingQuadraticAffineTransport.affineBulk v y (V δ).1 (V δ).2) ε -
      bulkFunctional B h i v y ((V ε).1.comp (V δ).1, (V ε).1 (V δ).2) := by
  dsimp only
  rw [bilinearCellHessian]
  change bulkFunctional B h i v y (velocityDerivative B _ i₀ ε δ) +
    bulkFunctionalDerivative B h i v y ε
      (velocityMap (scoreLiftCLM B _ i₀) δ)=_
  rw [velocityDerivative_apply,map_neg,
    bulkFunctionalDerivative_apply B h σ hσ hlower i v y ε]
  ring

end NegativeVotingFanQuadraticSecondDerivative
