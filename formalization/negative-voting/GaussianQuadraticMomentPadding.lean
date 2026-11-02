import GaussianRegularSpectatorRepresentation

/-! Exact zero-padding invariance of literal Gaussian cell quadratic tests.
The proof factors the Gaussian measure and integrates out centered spectator
moments; there is no dimension or injectivity premise on the row family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical RealInnerProductSpace

namespace NegativeVotingQuadraticMomentPadding
open NegativeVoting NegativeVotingModern NegativeVotingFan
  NegativeVotingFanQuadraticMoments NegativeVotingSecondChaosFacetGradient
  NegativeVotingRegularSpectatorRepresentation OAI.MinUncut.GaussianHermite
variable {d s D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def padVector (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord d) : FSC.Coord D :=
  WithLp.toLp 2 (fun a=>match e.symm a with | .inl j=>x j | .inr _=>0)

def mainVector (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord D) : FSC.Coord d :=
  WithLp.toLp 2 (fun j=>x (e (.inl j)))

theorem padVector_inl (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord d) (j : Fin d) :
    padVector e x (e (.inl j))=x j := by simp [padVector]

theorem padVector_inr (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord d) (j : Fin s) :
    padVector e x (e (.inr j))=0 := by simp [padVector]

theorem mainVector_padVector (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord d) :
    mainVector e (padVector e x)=x := by ext j;simp [mainVector,padVector_inl]

theorem padVector_inner (e : Fin d⊕Fin s≃Fin D) (x : FSC.Coord d) (y : FSC.Coord D) :
    inner ℝ (padVector e x) y=inner ℝ x (mainVector e y) := by
  simp only [PiLp.inner_apply,Real.inner_apply]
  rw [←e.sum_comp]
  simp only [Fintype.sum_sum_type,padVector_inl,padVector_inr,zero_mul,
    Finset.sum_const_zero,add_zero,mainVector,WithLp.ofLp_toLp]

theorem padVector_inner_padVector (e : Fin d⊕Fin s≃Fin D) (x y : FSC.Coord d) :
    inner ℝ (padVector e x) (padVector e y)=inner ℝ x y := by
  rw [padVector_inner,mainVector_padVector]

theorem winningCell_padVector_mem (e : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (y : FSC.Coord D) :
    y∈winningCell (fun j=>padVector e (B j)) h i ↔ mainVector e y∈winningCell B h i := by
  simp only [winningCell,Set.mem_setOf_eq,scores,padVector_inner]

def cellWeight (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : Fin d→ℝ) : ℝ :=
  (winningCell B h i).indicator (fun _=>1) (WithLp.toLp 2 x)

theorem quadraticMoment_cellWeight (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι)
    (a b : Fin d) : quadraticMoment (cellWeight B h i) a b=secondMomentTensor B h i a b := by
  unfold quadraticMoment
  change (∫ x,cellWeight B h i x*quadraticCoordinate a b x ∂standardGaussian (Fin d))=_
  rw [integral_standardGaussian_eq_euclidean]
  change (∫ x,(winningCell B h i).indicator (fun _=>(1:ℝ)) x*tensorTest a b x
    ∂stdGaussian (FSC.Coord d))=∫ x in winningCell B h i,tensorTest a b x ∂stdGaussian (FSC.Coord d)
  rw [←integral_indicator (winningCell_measurable B h i)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈winningCell B h i <;>simp [hx]

theorem cellWeight_padVector (e : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (y : Fin D→ℝ) :
    cellWeight (fun j=>padVector e (B j)) h i y=
      liftWeight (cellWeight B h i) (fun a=>y (e a)) := by
  have hm : mainVector e (WithLp.toLp 2 y)=WithLp.toLp 2 (fun a=>y (e (.inl a))) := rfl
  have he:=winningCell_padVector_mem e B h i (WithLp.toLp 2 y)
  rw [hm] at he
  unfold cellWeight liftWeight
  by_cases hy : WithLp.toLp 2 (fun a=>y (e (.inl a)))∈winningCell B h i
  · simp only [Set.indicator_of_mem hy,Set.indicator_of_mem (he.mpr hy)]
  · have hn : WithLp.toLp 2 y∉winningCell (fun j=>padVector e (B j)) h i := fun h=>hy (he.mp h)
    simp only [Set.indicator_of_notMem hy,Set.indicator_of_notMem hn]

theorem secondMomentTensor_padVector (e : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (a b : Fin d⊕Fin s) :
    secondMomentTensor (fun j=>padVector e (B j)) h i (e a) (e b)=
      quadraticMoment (liftWeight (cellWeight B h i)) a b := by
  rw [←quadraticMoment_cellWeight]
  have he : cellWeight (fun j=>padVector e (B j)) h i=
      (fun y=>liftWeight (cellWeight B h i) (fun a=>y (e a))) :=
    funext (cellWeight_padVector e B h i)
  rw [he,quadraticMoment_reindex]

/-- No spectator-coordinate terms remain in the actual Gaussian test, even
when the ambient query vector itself has arbitrary spectator coordinates. -/
theorem quadraticLabelTest_padVector (e : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (y : FSC.Coord D) :
    quadraticLabelTest (fun j=>padVector e (B j)) h i y=
      quadraticLabelTest B h i (mainVector e y) := by
  calc
    _ = ∑ a,∑ b,quadraticMoment (liftWeight (cellWeight B h i)) a b*
        quadraticCoordinate a b (fun k=>y (e k)) := by
      unfold quadraticLabelTest
      rw [←e.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      rw [←e.sum_comp]
      apply Finset.sum_congr rfl
      intro b _
      rw [secondMomentTensor_padVector]
      simp only [tensorTest,quadraticCoordinate,e.injective.eq_iff]
    _ = _ := by
      simp only [Fintype.sum_sum_type,quadraticMoment_lift,zero_mul,
        Finset.sum_const_zero,add_zero,quadraticMoment_cellWeight,
        quadraticLabelTest,quadraticCoordinate,tensorTest,Sum.inl.injEq,
        mainVector,WithLp.ofLp_toLp]

theorem quadraticLabelTest_padVector_at_padVector (e : Fin d⊕Fin s≃Fin D)
    (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : FSC.Coord d) :
    quadraticLabelTest (fun j=>padVector e (B j)) h i (padVector e x)=
      quadraticLabelTest B h i x := by
  rw [quadraticLabelTest_padVector,mainVector_padVector]

end NegativeVotingQuadraticMomentPadding
