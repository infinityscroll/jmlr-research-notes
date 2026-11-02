import GaussianFanQuadraticSecondDerivative

/-! The actual constant-test second derivative.  This supplies the mass term
needed when passing from uncentered quadratic moments to second-chaos tensors. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingFanMassSecondDerivative
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
  NegativeVotingFanCoherentChart NegativeVotingFanQuadraticTransport
  NegativeVotingQuadraticBulkDifferential NegativeVotingFanJointMass
  NegativeVotingFanQuadraticSecondDerivative NegativeVotingFanQuarticMoments
  NegativeVotingAffineOperatorDerivative NegativeVotingMovingCap
  NegativeVotingQuadraticAffineTransport NegativeVotingCapTail NegativeVotingFacetDegree
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance fieldsNormed (d : ℕ) : NormedAddCommGroup (Fields d) := inferInstance
local instance fieldsDualNormed (d : ℕ) : NormedAddCommGroup (Fields d→L[ℝ] ℝ) := inferInstance
local instance fieldsDualSpace (d : ℕ) : NormedSpace ℝ (Fields d→L[ℝ] ℝ) := inferInstance
local instance velocitiesNormed : NormedAddCommGroup (Parameters d ι→L[ℝ] Fields d) := inferInstance
local instance velocitiesSpace : NormedSpace ℝ (Parameters d ι→L[ℝ] Fields d) := inferInstance

/-- The Gaussian density derivative for an affine field. -/
def massBulk (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z x : FSC.Coord d) : ℝ :=
  inner ℝ x (A x)+inner ℝ z x-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap

theorem quadratic_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    Integrable (fun x=>inner ℝ x (A x)) μ := by
  have hh := integrable_finsetSum Finset.univ (fun a _=>
    ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ)
      (A (EuclideanSpace.basisFun (Fin d) ℝ a))).integrable_mul
      ((IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (EuclideanSpace.basisFun (Fin d) ℝ a)))
  exact hh.congr (Filter.Eventually.of_forall (basis_quadratic_sum A))

theorem massBulk_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) : Integrable (massBulk A z) μ :=
  ((quadratic_integrable μ A).add (IsGaussian.integrable_dual μ (innerSL ℝ z))).sub
    (integrable_const _)

theorem massBulk_growth (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    PolynomialGrowth (massBulk A z) 4 := by
  have hq := PolynomialGrowth.finsetSum Finset.univ
    (fun a:Fin d=>fun x=>inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ a)) x*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ a) x) 2
    (fun a _=>(PolynomialGrowth.inner _).mul (PolynomialGrowth.inner _))
  have he : (fun x=>∑ a:Fin d,inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ a)) x*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ a) x)=(fun x=>inner ℝ x (A x)) :=
    funext (basis_quadratic_sum A)
  rw [he] at hq
  exact ((hq.add ((PolynomialGrowth.inner z).mono_degree (by decide : 1≤2))).sub
    (PolynomialGrowth.const _ 2)).mono_degree (by decide : 2≤4)

theorem hasFDerivAt_massBulk_testedCell (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    HasFDerivAt (fun p:Parameters d ι=>∫ x in winningCell p.1 p.2 i,
      massBulk A z x ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i (massBulk A z)) (B,h) := by
  obtain ⟨C,hC,hF⟩ := (massBulk_growth A z).quartic_bound
  exact NegativeVotingFanQuarticMoments.hasFDerivAt_testedCell B h σ hσ hlower i _
    (massBulk_growth A z).1 C hC hF

theorem massBulk_add (p q : Fields d) (x : FSC.Coord d) :
    massBulk (p+q).1 (p+q).2 x=massBulk p.1 p.2 x+massBulk q.1 q.2 x := by
  simp [massBulk,inner_add_left,inner_add_right,map_add]
  ring

theorem massBulk_smul (c : ℝ) (p : Fields d) (x : FSC.Coord d) :
    massBulk (c•p).1 (c•p).2 x=c*massBulk p.1 p.2 x := by
  simp [massBulk,real_inner_smul_left,real_inner_smul_right,map_smul]
  ring

def massFunctionalLinear (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) : Fields d→ₗ[ℝ] ℝ where
  toFun p := ∫ x in winningCell B h i,massBulk p.1 p.2 x ∂stdGaussian (FSC.Coord d)
  map_add' p q := by
    simp_rw [massBulk_add]
    exact integral_add (massBulk_integrable _ p.1 p.2).restrict
      (massBulk_integrable _ q.1 q.2).restrict
  map_smul' c p := by
    change (∫ x in winningCell B h i,massBulk (c•p).1 (c•p).2 x
      ∂stdGaussian (FSC.Coord d))=_
    simp_rw [massBulk_smul]
    rw [integral_const_mul]
    rfl

def massFunctional (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) : Fields d→L[ℝ] ℝ :=
  (massFunctionalLinear B h i).toContinuousLinearMap

@[simp] theorem massFunctional_apply (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (p : Fields d) :
    massFunctional B h i p=∫ x in winningCell B h i,massBulk p.1 p.2 x
      ∂stdGaussian (FSC.Coord d) := rfl

private def fieldBasis (d : ℕ) := Module.finBasis ℝ (Fields d)
private def dualCoord (j : Fin (Module.finrank ℝ (Fields d))) : Fields d→L[ℝ] ℝ :=
  ((fieldBasis d).coord j).toContinuousLinearMap

private theorem dual_reconstruction (L : Fields d→L[ℝ] ℝ) :
    L=∑ j,L (fieldBasis d j)•dualCoord (d:=d) j := by
  apply ContinuousLinearMap.coe_injective
  apply (fieldBasis d).ext
  intro j
  simp [dualCoord,Finsupp.single_apply]

def massFunctionalDerivative (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    Parameters d ι→L[ℝ] Fields d→L[ℝ] ℝ :=
  ∑ j,(testedCellDerivative B h i (massBulk (fieldBasis d j).1 (fieldBasis d j).2)).smulRight
    (dualCoord (d:=d) j)

theorem hasFDerivAt_massFunctional (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    HasFDerivAt (fun p:Parameters d ι=>massFunctional p.1 p.2 i)
      (massFunctionalDerivative B h i) (B,h) := by
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) fun j _=>
    (hasFDerivAt_massBulk_testedCell B h σ hσ hlower i
      (fieldBasis d j).1 (fieldBasis d j).2).smul_const (dualCoord (d:=d) j)
  change HasFDerivAt
    (fun p:Parameters d ι=>∑ j,massFunctional p.1 p.2 i (fieldBasis d j)•dualCoord (d:=d) j)
    (massFunctionalDerivative B h i) (B,h) at hs
  simpa only [←dual_reconstruction] using hs

theorem massFunctionalDerivative_apply (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (i : ι) (δ : Parameters d ι) (q : Fields d) :
    massFunctionalDerivative B h i δ q=testedCellDerivative B h i (massBulk q.1 q.2) δ := by
  let ev : (Fields d→L[ℝ] ℝ)→L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ q
  have hd := ev.hasFDerivAt.comp (B,h) (hasFDerivAt_massFunctional B h σ hσ hlower i)
  have he := hasFDerivAt_massBulk_testedCell B h σ hσ hlower i q.1 q.2
  have hid : ev.comp (massFunctionalDerivative B h i)=testedCellDerivative B h i
      (massBulk q.1 q.2) := hd.unique he
  exact congrArg (fun L:Parameters d ι→L[ℝ] ℝ=>L δ) hid

omit [Nonempty ι] in
/-- The literal constant-test affine transport formula, including its trace term. -/
theorem capJointDerivative_one_affine_bulk (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    capJointDerivative w b (fun _=>1) (affineVelocity w A z)=
      ∫ x in FSC.cap w b,massBulk A z x ∂stdGaussian (FSC.Coord d) := by
  rw [capJointDerivative_affine w hw b hb]
  have hq := (quadratic_integrable (stdGaussian (FSC.Coord d)) A).restrict (s:=FSC.cap w b)
  have hz : Integrable (fun x=>inner ℝ z x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) :=
    (IsGaussian.integrable_dual (stdGaussian (FSC.Coord d)) (innerSL ℝ z)).restrict
  have hs : Integrable (fun x=>inner ℝ x (A x)+inner ℝ z x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := hq.add hz
  unfold massBulk
  rw [integral_sub hs (integrable_const _),integral_add hq hz,integral_const]
  simp only [Measure.real_def,Measure.restrict_apply_univ,smul_eq_mul,FSC.capMass]
  ring

theorem testedCellDerivative_one_bulk (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d)
    (hL : ∀ (q:ι→ℝ) (i j:ι),inner ℝ (B i-B j) (L q)=q i-q j)
    (i : ι) (δ : Parameters d ι) :
    testedCellDerivative B h i (fun _=>1) δ=massFunctional B h i (velocityMap L δ) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i)
    (fun _=>1) (fanParameterMap B i δ)=_
  rw [fanParameterMap_eq_affineVelocity B L hL,
    capJointDerivative_one_affine_bulk _ (cellNormals_unit B σ hσ hlower i) _
      (cellNormals_noCoincident B h σ hσ hlower i)]
  have hB : Function.Injective B := fun j k he=>by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have he := normalized_cap_eq_winningCell B hB i (B,h)
  rw [fanParameterMap_base] at he
  rw [he]
  rfl

def massCellHessian (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ i : ι) : Parameters d ι→L[ℝ] Parameters d ι→L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ
    (massFunctional B h i)).comp (velocityDerivative B hB i₀) +
  ((ContinuousLinearMap.compL ℝ (Parameters d ι) (Fields d) ℝ).flip
    (velocityMap (scoreLiftCLM B hB i₀))).comp (massFunctionalDerivative B h i)

theorem hasFDerivAt_testedCellDerivative_one (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i₀ i : ι) :
    let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
    HasFDerivAt (fun p:Parameters d ι=>testedCellDerivative p.1 p.2 i (fun _=>1))
      (massCellHessian B hB h i₀ i) (B,h) := by
  dsimp only
  let hB := NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower
  have he : ∀ᶠ p : Parameters d ι in 𝓝 (B,h),
      testedCellDerivative p.1 p.2 i (fun _=>1)=
        (massFunctional p.1 p.2 i).comp (velocityMap (transportedLift B hB h i₀ p)) := by
    filter_upwards [eventually_centeredSingularLowerBound B h σ hσ hlower,
      eventually_chartLinear_isUnit B hB h i₀] with p hp hu
    apply ContinuousLinearMap.ext
    intro δ
    exact testedCellDerivative_one_bulk p.1 p.2 (σ/2) (by positivity) hp
      (transportedLift B hB h i₀ p) (transportedLift_pair B hB h i₀ p hu) i δ
  have hd := (hasFDerivAt_massFunctional B h σ hσ hlower i).clm_comp
    (hasFDerivAt_transportedVelocity B hB h i₀)
  simpa only [massCellHessian,transportedLift_base] using hd.congr_of_eventuallyEq he

end NegativeVotingFanMassSecondDerivative
