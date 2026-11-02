import GaussianRegularOrbitRepresentation
import GaussianFanSelectedOffsets

/-! Exact invariance of the literal Gaussian cell second energy under
orthogonal changes, spectator padding, equal Gram realizations and positive
score scaling. No dimension restriction or replacement moment is assumed. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingSecondEnergyCovarianceLaw
open NegativeVoting NegativeVotingModern NegativeVotingFan NegativeVotingFanQuadraticMoments
  NegativeVotingSecondChaosFacetGradient NegativeVotingQuadraticMomentIsometry
  NegativeVotingQuadraticMomentPadding NegativeVotingRegularSpectatorRepresentation
  NegativeVotingRegularOrbitRepresentation NegativeVotingFanSelectedOffsets
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingBalancedReference
  OAI.MinUncut.GaussianHermite
variable {d e s D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem secondEnergy_eq_integral_test (B : ι→FSC.Coord d) (h : ι→ℝ) :
    secondEnergy B h=(1/2:ℝ)*∑i,∫x in winningCell B h i,
      quadraticLabelTest B h i x ∂stdGaussian (FSC.Coord d) := by
  simp only [integral_quadraticLabelTest,secondEnergy,pow_two]

theorem secondEnergy_isometry (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (B : ι→FSC.Coord d) (h : ι→ℝ) :
    secondEnergy (fun i=>T (B i)) h=secondEnergy B h := by
  rw [secondEnergy_eq_integral_test,secondEnergy_eq_integral_test]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hp : MeasurePreserving T (stdGaussian (FSC.Coord d)) (stdGaussian (FSC.Coord d)) :=
    ⟨T.continuous.measurable,stdGaussian_map T⟩
  have hh := hp.integral_comp T.toHomeomorph.measurableEmbedding
    ((winningCell (fun j=>T (B j)) h i).indicator (quadraticLabelTest (fun j=>T (B j)) h i))
  have he : (fun x=>(winningCell (fun j=>T (B j)) h i).indicator
      (quadraticLabelTest (fun j=>T (B j)) h i) (T x))=
      (winningCell B h i).indicator (quadraticLabelTest B h i) := by
    funext x
    by_cases hx : x∈winningCell B h i
    · have hTx := (winningCell_isometry_mem T B h i x).mpr hx
      simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hTx,quadraticLabelTest_isometry]
    · have hTx : T x∉winningCell (fun j=>T (B j)) h i :=
        fun hh=>hx ((winningCell_isometry_mem T B h i x).mp hh)
      simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem hTx]
  change (∫x,(winningCell (fun j=>T (B j)) h i).indicator
    (quadraticLabelTest (fun j=>T (B j)) h i) (T x) ∂stdGaussian (FSC.Coord d))=_ at hh
  rw [he,integral_indicator (winningCell_measurable B h i),
    integral_indicator (winningCell_measurable (fun j=>T (B j)) h i)] at hh
  exact hh.symm

theorem secondEnergy_eq_of_equal_gram_same_dimension (B C : ι→FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) (h : ι→ℝ) :
    secondEnergy B h=secondEnergy C h := by
  obtain ⟨T,hT⟩ := exists_orthogonal_of_equal_gram B C hG
  have hh := secondEnergy_isometry T B h
  simpa only [hT] using hh.symm

theorem secondEnergy_padVector (f : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) :
    secondEnergy (fun i=>padVector f (B i)) h=secondEnergy B h := by
  unfold secondEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑a,∑b,(quadraticMoment (liftWeight (cellWeight B h i)) a b)^2 := by
      rw [←f.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      rw [←f.sum_comp]
      apply Finset.sum_congr rfl
      intro b _
      rw [secondMomentTensor_padVector]
    _ = _ := by
      simp only [Fintype.sum_sum_type,quadraticMoment_lift,quadraticMoment_cellWeight,
        zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

/-- Arbitrary source and target ambient dimensions, including proper row
spans, are covered by exact Gaussian spectator integration. -/
theorem secondEnergy_eq_of_equal_gram (B : ι→FSC.Coord d) (C : ι→FSC.Coord e)
    (hG : ∀i j,inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) (h : ι→ℝ) :
    secondEnergy B h=secondEnergy C h := by
  let f : Fin d⊕Fin e≃Fin (d+e) := finSumFinEquiv
  let g : Fin e⊕Fin d≃Fin (d+e) := (Equiv.sumComm (Fin e) (Fin d)).trans finSumFinEquiv
  have hh := secondEnergy_eq_of_equal_gram_same_dimension
    (fun i=>padVector f (B i)) (fun i=>padVector g (C i))
    (fun i j=>by rw [padVector_inner_padVector,padVector_inner_padVector];exact hG i j) h
  simpa only [secondEnergy_padVector] using hh

theorem selected_secondEnergy_eq_of_equal_gram
    (B : ι→FSC.Coord d) (C : ι→FSC.Coord e) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (hG : ∀i j,inner ℝ (B i) (B j)=inner ℝ (C i) (C j))
    (p : ι→ℝ) (hp : ∀i,0 < p i) (hs : ∑i,p i=1) :
    secondEnergy B (selectedOffsets B p)=secondEnergy C (selectedOffsets C p) := by
  rw [selectedOffsets_eq_of_gram B C σ hσ hlower hG p hp hs]
  exact secondEnergy_eq_of_equal_gram B C hG _

theorem winningCell_scaled (B : ι→FSC.Coord d) (h : ι→ℝ)
    (α : ℝ) (hα : 0 < α) (i : ι) :
    winningCell (α • B) (α • h) i=winningCell B h i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,NegativeVotingFan.scores,Pi.smul_apply,
    real_inner_smul_left,smul_eq_mul,←mul_add,mul_le_mul_iff_right₀ hα]

theorem secondEnergy_scaled (B : ι→FSC.Coord d) (h : ι→ℝ)
    (α : ℝ) (hα : 0 < α) :
    secondEnergy (α • B) (α • h)=secondEnergy B h := by
  simp only [secondEnergy,secondMomentTensor,winningCell_scaled B h α hα]

theorem weights_scaled (B : ι→FSC.Coord d) (h : ι→ℝ)
    (α : ℝ) (hα : 0 < α) (x : FSC.Coord d) (i : ι) :
    weights (α • B) (α • h) x i=weights B h x i := by
  unfold weights
  have he : NegativeVotingFan.scores (α • B) (α • h) x=
      fun j=>α*NegativeVotingFan.scores B h x j := by
    funext j
    simp only [NegativeVotingFan.scores,Pi.smul_apply,real_inner_smul_left,smul_eq_mul,mul_add]
  rw [he]
  exact maxWeights_mul_pos _ α hα i

theorem singular_scaled (B : ι→FSC.Coord d) (σ : ℝ)
    (hlower : CenteredSingularLowerBound B σ) (α : ℝ) :
    CenteredSingularLowerBound (α • B) (α*σ) := by
  intro c hc
  have hh := mul_le_mul_of_nonneg_left (hlower c hc) (sq_nonneg α)
  have he : (∑i,c i • (α • B) i)=α • ∑i,c i • B i := by
    simp only [Pi.smul_apply,Finset.smul_sum,smul_smul]
    congr 1
    funext i
    rw [mul_comm]
  rw [he,norm_smul,Real.norm_eq_abs]
  simp only [mul_pow,sq_abs]
  nlinarith only [hh]

theorem selectedOffsets_scaled (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (α : ℝ) (hα : 0 < α)
    (p : ι→ℝ) (hp : ∀i,0 < p i) (hs : ∑i,p i=1) :
    selectedOffsets (α • B) p=α • selectedOffsets B p := by
  have hB : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  apply selectedOffsets_eq (α • B) p (α*σ) (mul_pos hα hσ) (singular_scaled B σ hlower α)
  funext i
  change mass (α • B) (α • (selectedOffsets B p : ι→ℝ)) i=p i
  simp only [mass,weights_scaled B _ α hα]
  exact congrFun (selectedOffsets_mass B hB p hp hs) i

/-- Radial normalization changes neither the selected cells nor their actual
second-chaos energy. The mass and singular-value hypotheses are literal. -/
theorem selected_secondEnergy_scaled (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (α : ℝ) (hα : 0 < α)
    (p : ι→ℝ) (hp : ∀i,0 < p i) (hs : ∑i,p i=1) :
    secondEnergy (α • B) (selectedOffsets (α • B) p)=secondEnergy B (selectedOffsets B p) := by
  rw [selectedOffsets_scaled B σ hσ hlower α hα p hp hs]
  exact secondEnergy_scaled B _ α hα

end NegativeVotingSecondEnergyCovarianceLaw
