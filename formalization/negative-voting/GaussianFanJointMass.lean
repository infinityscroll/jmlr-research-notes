import GaussianMovingFaceMoments
import GaussianCapSecondMoment

/-! Actual joint Gaussian fan mass derivatives and their regularity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators Topology

namespace NegativeVotingFanJointMass
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanMovingCells
open NegativeVotingMovingFaceMoments NegativeVotingMovingCap NegativeVotingDisintegration
open NegativeVotingFacetDegree NegativeVotingCapTail NegativeVotingWeightedFacet
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ambient rest-face transport for a general unit-normal cap. -/
theorem tangentFace_integral_eq_restFace (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (j : ι) (G : FSC.Coord d → ℝ) (hG : Continuous G) :
    (∫ y in tangentFace w b j, G ((y : FSC.Coord d)+b j•w j)
      ∂stdGaussian (tangentSpace (w j))) =
    ∫ x in {x | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k}, G x ∂FSC.sliceLaw (w j) (b j) := by
  have hlaw : FSC.sliceLaw (w j) (b j) =
      (stdGaussian (tangentSpace (w j))).map (fun y : tangentSpace (w j) => (y : FSC.Coord d)+b j•w j) := by
    unfold FSC.sliceLaw
    rw [gaussian_affine_slice_map _ (hw j)]
    congr 1
    funext y
    exact add_comm _ _
  have hs : MeasurableSet {x : FSC.Coord d | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) measurable_const
  rw [hlaw, setIntegral_map hs hG.measurable.aestronglyMeasurable (by fun_prop)]
  rfl

/-- Integrating the literal normal velocity uses only the actual zeroth and
first moments of the pinned face. -/
theorem capJointDerivative_one_apply (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1)
    (b : ι → ℝ) (δ : Parameters d ι) :
    capJointDerivative w b (fun _ => 1) δ = ∑ j, WeakSimplex.normalPDF (b j) *
      (FSC.sliceMass w b j * δ.2 j - inner ℝ (δ.1 j) (sliceFirstMoment w b j)) := by
  have hF (x : FSC.Coord d) : |(1:ℝ)| ≤ 1*(1+‖x‖) := by simp
  rw [capJointDerivative_apply w hw b _ continuous_const 1 (by norm_num) hF δ]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_mul]
  rw [tangentFace_integral_eq_restFace w hw b j
    (fun x => δ.2 j-inner ℝ (δ.1 j) x) (by fun_prop)]
  congr 1
  let S : Set (FSC.Coord d) := {x | ∀ k, k ≠ j → inner ℝ (w k) x ≤ b k}
  haveI : IsGaussian (FSC.sliceLaw (w j) (b j)) :=
    NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
  have hid : Integrable (fun x : FSC.Coord d => x) ((FSC.sliceLaw (w j) (b j)).restrict S) :=
    IsGaussian.integrable_id.integrableOn
  rw [integral_sub (integrable_const _) (hid.const_inner (𝕜 := ℝ) (δ.1 j)),
    setIntegral_const, integral_inner hid (δ.1 j)]
  rfl

/-- The joint cap-mass derivative, written entirely in actual moment data. -/
def capMassJointLinear (w : ι → FSC.Coord d) (b : ι → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∑ j, WeakSimplex.normalPDF (b j) •
    (FSC.sliceMass w b j • ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (ι → FSC.Coord d) (ι → ℝ))) -
    (innerSL ℝ (sliceFirstMoment w b j)).comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ))))

theorem capMassJointLinear_apply (w : ι → FSC.Coord d) (b : ι → ℝ) (δ : Parameters d ι) :
    capMassJointLinear w b δ = ∑ j, WeakSimplex.normalPDF (b j) *
      (FSC.sliceMass w b j * δ.2 j - inner ℝ (δ.1 j) (sliceFirstMoment w b j)) := by
  simp only [capMassJointLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, innerSL_apply_apply]
  change (∑ j, WeakSimplex.normalPDF (b j) *
    (FSC.sliceMass w b j * δ.2 j - inner ℝ (sliceFirstMoment w b j) (δ.1 j))) = _
  simp only [real_inner_comm]

theorem capMassJointLinear_eq (w : ι → FSC.Coord d) (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) :
    capMassJointLinear w b = capJointDerivative w b (fun _ => 1) := by
  apply ContinuousLinearMap.ext
  intro δ
  rw [capMassJointLinear_apply, capJointDerivative_one_apply w hw]

/-- Continuity of the full operator follows from the proved actual moment
continuity, not from a supplied regularity premise. -/
theorem continuousAt_capMassJointLinear (w : ι → FSC.Coord d)
    (hw : ∀ k, ‖w k‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b) :
    ContinuousAt (fun p : Parameters d ι => capMassJointLinear p.1 p.2) (w,b) := by
  unfold capMassJointLinear
  apply (show Continuous (fun f : ι → (Parameters d ι →L[ℝ] ℝ) => ∑ j, f j) from
    continuous_finsetSum Finset.univ (fun j _ => continuous_apply j)).continuousAt.comp
  apply continuousAt_pi.mpr
  intro j
  have hpdf : ContinuousAt (fun p : Parameters d ι => WeakSimplex.normalPDF (p.2 j)) (w,b) := by
    unfold WeakSimplex.normalPDF gaussianPDFReal
    fun_prop
  have hmass := continuousAt_sliceMass_joint w hw b hb j
  have hmoment := continuousAt_sliceFirstMoment_joint w hw b hb j
  exact hpdf.smul ((hmass.smul continuousAt_const).sub
    (((innerSL ℝ).continuous.continuousAt.comp hmoment).clm_comp continuousAt_const))

section Fan
variable [Nonempty ι]

/-- Actual joint derivative of a single Gaussian fan mass. -/
def jointMassDerivativeAt (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Parameters d ι →L[ℝ] ℝ :=
  (capMassJointLinear (cellNormals B i) (cellSupports B h i)).comp (fanParameterMap B i)

/-- The whole actual mass vector's candidate derivative is a concrete
finite family of the Gaussian moment operators above. -/
def jointMassDerivative (B : ι → FSC.Coord d) (h : ι → ℝ) :
    Parameters d ι →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi (jointMassDerivativeAt B h)

theorem jointMassDerivativeAt_eq_tested (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    jointMassDerivativeAt B h i = testedCellDerivative B h i (fun _ => 1) := by
  unfold jointMassDerivativeAt testedCellDerivative
  rw [capMassJointLinear_eq _ (cellNormals_unit B σ hσ hlower i)]

/-- Distinct base rows stay distinct on an actual open neighborhood. -/
theorem eventually_injective_rows (B : ι → FSC.Coord d) (hB : Function.Injective B) (h : ι → ℝ) :
    ∀ᶠ p : Parameters d ι in 𝓝 (B,h), Function.Injective p.1 := by
  have he : ∀ i j, ∀ᶠ p : Parameters d ι in 𝓝 (B,h), i ≠ j → p.1 i ≠ p.1 j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hh => (hh hij).elim
    · have hi : ContinuousAt (fun p : Parameters d ι => p.1 i) (B,h) := by fun_prop
      have hj : ContinuousAt (fun p : Parameters d ι => p.1 j) (B,h) := by fun_prop
      exact ((hi.ne_iff_eventually_ne hj).mp (hB.ne hij)).mono fun _ hh _ => hh
  have he' := eventually_all.mpr (fun i => eventually_all.mpr (he i))
  filter_upwards [he'] with p hp
  intro i j hij
  by_contra hne
  exact hp i j hne hij

/-- Actual joint Frechet derivative of every mass component; equality with
the cell integral is proved on the required neighborhood of distinct rows. -/
theorem hasFDerivAt_mass_joint_component (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    HasFDerivAt (fun p : Parameters d ι => mass p.1 p.2 i)
      (jointMassDerivativeAt B h i) (B,h) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hd := hasFDerivAt_testedCell B h σ hσ hlower i (fun _ => 1) continuous_const
    1 (by norm_num) (fun x => by simp)
  rw [← jointMassDerivativeAt_eq_tested B h σ hσ hlower i] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_injective_rows B hB h] with p hp
  rw [mass_eq_winningCell p.1 hp p.2 i]
  simp

/-- Actual simultaneous row/offset derivative of the full Gaussian mass map. -/
theorem hasFDerivAt_mass_joint (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    HasFDerivAt (fun p : Parameters d ι => mass p.1 p.2)
      (jointMassDerivative B h) (B,h) :=
  hasFDerivAt_pi.mpr (hasFDerivAt_mass_joint_component B h σ hσ hlower)

/-- Normalized fan normals and supports depend continuously on the actual
rows and offsets wherever the base rows are distinct. -/
theorem continuousAt_cellData (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hB : Function.Injective B) (i : ι) :
    ContinuousAt (fun p : Parameters d ι =>
      (cellNormals p.1 i, cellSupports p.1 p.2 i)) (B,h) := by
  have hrow (j : {j : ι // j ≠ i}) :
      ContinuousAt (fun p : Parameters d ι => p.1 j.1-p.1 i) (B,h) := by fun_prop
  have hn (j : {j : ι // j ≠ i}) : ‖B j.1-B i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hB.ne j.property))
  apply ContinuousAt.prodMk
  · apply continuousAt_pi.mpr
    intro j
    exact ((hrow j).norm.inv₀ (hn j)).smul (hrow j)
  · apply continuousAt_pi.mpr
    intro j
    exact (show ContinuousAt (fun p : Parameters d ι => p.2 i-p.2 j.1) (B,h) by fun_prop).div
      (hrow j).norm (hn j)

/-- The full fixed-base normalization operator also varies continuously
with its base rows; the denominators are nonzero by actual distinctness. -/
theorem continuousAt_fanParameterMap (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hB : Function.Injective B) (i : ι) :
    ContinuousAt (fun p : Parameters d ι => fanParameterMap p.1 i) (B,h) := by
  let A (j : {j : ι // j ≠ i}) : Parameters d ι →L[ℝ] FSC.Coord d :=
    (((ContinuousLinearMap.proj j.1 : (ι → FSC.Coord d) →L[ℝ] FSC.Coord d) -
      ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (ι → FSC.Coord d) (ι → ℝ)))
  let C (j : {j : ι // j ≠ i}) : Parameters d ι →L[ℝ] ℝ :=
    (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j.1).comp
      (ContinuousLinearMap.snd ℝ (ι → FSC.Coord d) (ι → ℝ)))
  have hinv (j : {j : ι // j ≠ i}) :
      ContinuousAt (fun p : Parameters d ι => ‖p.1 j.1-p.1 i‖⁻¹) (B,h) :=
    (show ContinuousAt (fun p : Parameters d ι => ‖p.1 j.1-p.1 i‖) (B,h) by fun_prop).inv₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hB.ne j.property)))
  have hA : ContinuousAt (fun p : Parameters d ι =>
      ContinuousLinearMap.pi (fun j : {j : ι // j ≠ i} => ‖p.1 j.1-p.1 i‖⁻¹ • A j)) (B,h) :=
    (ContinuousLinearMap.piEquivL ℝ (Parameters d ι) (fun _ : {j : ι // j ≠ i} => FSC.Coord d)).continuous.continuousAt.comp
      (continuousAt_pi.mpr (fun j => (hinv j).smul continuousAt_const))
  have hC : ContinuousAt (fun p : Parameters d ι =>
      ContinuousLinearMap.pi (fun j : {j : ι // j ≠ i} => ‖p.1 j.1-p.1 i‖⁻¹ • C j)) (B,h) :=
    (ContinuousLinearMap.piEquivL ℝ (Parameters d ι) (fun _ : {j : ι // j ≠ i} => ℝ)).continuous.continuousAt.comp
      (continuousAt_pi.mpr (fun j => (hinv j).smul continuousAt_const))
  exact (ContinuousLinearMap.prodL ℝ).continuous.continuousAt.comp (hA.prodMk hC)

/-- Joint continuity of the actual mass derivative, in operator norm. -/
theorem continuousAt_jointMassDerivativeAt (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    ContinuousAt (fun p : Parameters d ι => jointMassDerivativeAt p.1 p.2 i) (B,h) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hc : ContinuousAt (fun p : Parameters d ι =>
      capMassJointLinear (cellNormals p.1 i) (cellSupports p.1 p.2 i)) (B,h) := by
    exact (continuousAt_capMassJointLinear (cellNormals B i)
      (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
      (cellNormals_noCoincident B h σ hσ hlower i)).comp
        (f := fun p : Parameters d ι => (cellNormals p.1 i, cellSupports p.1 p.2 i))
        (x := (B,h)) (continuousAt_cellData B h hB i)
  exact hc.clm_comp (continuousAt_fanParameterMap B h hB i)


/-- Simultaneous operator-norm continuity of all actual Gaussian mass derivatives. -/
theorem continuousAt_jointMassDerivative (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContinuousAt (fun p : Parameters d ι => jointMassDerivative p.1 p.2) (B,h) :=
  (ContinuousLinearMap.piEquivL ℝ (Parameters d ι) (fun _ : ι => ℝ)).continuous.continuousAt.comp
    (continuousAt_pi.mpr (continuousAt_jointMassDerivativeAt B h σ hσ hlower))

/-- A concrete row-sup perturbation bound preserves the centered singular
lower bound. No openness or full-rank persistence premise is supplied. -/
theorem centeredSingularLowerBound_of_close (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (A : ι → FSC.Coord d)
    (hclose : ‖A-B‖ < σ/(2*(Fintype.card ι : ℝ))) :
    CenteredSingularLowerBound A (σ/2) := by
  intro c hc
  let q := Real.sqrt (∑ i, c i ^ 2)
  have hS : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2 = ∑ i, c i^2 := Real.sq_sqrt hS
  have hci (i : ι) : |c i| ≤ q := by
    have hi : c i^2 ≤ ∑ j, c j^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [sq_abs (c i), abs_nonneg (c i)]
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have he : (Fintype.card ι : ℝ)*‖A-B‖ ≤ σ/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(Fintype.card ι : ℝ))).mp hclose
    nlinarith
  have hpert : ‖∑ i, c i • (A i-B i)‖ ≤ (σ/2)*q := by
    calc
      _ ≤ ∑ i, ‖c i • (A i-B i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, q*‖A-B‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hci i) (norm_le_pi_norm (A-B) i) (norm_nonneg _) hq
      _ = ((Fintype.card ι : ℝ)*‖A-B‖)*q := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ (σ/2)*q := mul_le_mul_of_nonneg_right he hq
  have hbase : σ*q ≤ ‖∑ i, c i • B i‖ := by
    apply (sq_le_sq₀ (mul_nonneg hσ.le hq) (norm_nonneg _)).mp
    rw [mul_pow,hq2]
    exact hlower c hc
  have htri : ‖∑ i, c i • B i‖ ≤ ‖∑ i, c i • A i‖ + ‖∑ i, c i • (A i-B i)‖ := by
    have heq : (∑ i, c i • B i) = (∑ i, c i • A i) - (∑ i, c i • (A i-B i)) := by
      simp_rw [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [heq]
    exact norm_sub_le _ _
  have hnew : (σ/2)*q ≤ ‖∑ i, c i • A i‖ := by linarith
  have hsquare := (sq_le_sq₀ (mul_nonneg (by linarith : 0≤σ/2) hq) (norm_nonneg _)).mpr hnew
  simpa only [mul_pow,hq2] using hsquare

/-- The quantitative perturbation bound gives the actual required neighborhood. -/
theorem eventually_centeredSingularLowerBound (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ∀ᶠ p : Parameters d ι in 𝓝 (B,h), CenteredSingularLowerBound p.1 (σ/2) := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnear : ∀ᶠ p : Parameters d ι in 𝓝 (B,h),
      ‖p.1-B‖ < σ/(2*(Fintype.card ι : ℝ)) :=
    (show ContinuousAt (fun p : Parameters d ι => ‖p.1-B‖) (B,h) by fun_prop).eventually_lt
      continuousAt_const (by simp only [sub_self, norm_zero]; positivity)
  exact hnear.mono fun p hp => centeredSingularLowerBound_of_close B σ hσ hlower p.1 hp

/-- The actual Gaussian mass map is jointly C1 in all rows and offsets
near every positive centered singular bound. Both the local differentiability
and continuous actual derivative have been established above. -/
theorem contDiffAt_mass_joint (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    ContDiffAt ℝ 1 (fun p : Parameters d ι => mass p.1 p.2) (B,h) := by
  have hh : 0 < σ/2 := by linarith
  apply contDiffAt_one_iff.mpr
  refine ⟨fun p => jointMassDerivative p.1 p.2,
    {p : Parameters d ι | CenteredSingularLowerBound p.1 (σ/2)},
    eventually_centeredSingularLowerBound B h σ hσ hlower, ?_, ?_⟩
  · intro p hp
    exact (continuousAt_jointMassDerivative p.1 p.2 (σ/2) hh hp).continuousWithinAt
  · intro p hp
    exact hasFDerivAt_mass_joint p.1 p.2 (σ/2) hh hp

end Fan
end NegativeVotingFanJointMass
