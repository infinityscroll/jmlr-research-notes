import GaussianCoherentLiftHessian
import GaussianOperatorHSNorm

/-! A coherent score lift with the exact inverse singular-value bound in any
ambient dimension. Projection onto the row-difference span removes the
uncontrolled component of the existence-based lift. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBoundedCoherentLift
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanCoherentChart
  NegativeVotingFanQuadraticTransport NegativeVotingCoherentLiftHessian
  NegativeVotingCapTail NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def rowDifferenceSpan (B : ι→FSC.Coord d) : Submodule ℝ (FSC.Coord d) :=
  Submodule.span ℝ (Set.range (fun ij:ι×ι=>B ij.1-B ij.2))

theorem difference_mem (B : ι→FSC.Coord d) (i j : ι) : B i-B j∈rowDifferenceSpan B :=
  Submodule.subset_span ⟨(i,j),rfl⟩

/-- Every vector in the difference span has a centered row representation. -/
theorem centered_coefficients (B : ι→FSC.Coord d) (x : FSC.Coord d)
    (hx : x∈rowDifferenceSpan B) :
    ∃ c : ι→ℝ,(∑ i,c i)=0 ∧ (∑ i,c i • B i)=x := by
  change x∈Submodule.span ℝ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨⟨i,j⟩,rfl⟩
      refine ⟨fun k=>(if k=i then (1:ℝ) else 0)-(if k=j then (1:ℝ) else 0),?_,?_⟩
      · simp [Finset.sum_sub_distrib]
      · simp [sub_smul,Finset.sum_sub_distrib]
  | zero =>
      exact ⟨0,by simp,by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨c,hc,he⟩
      rcases ihy with ⟨e,hd,hf⟩
      refine ⟨c+e,?_,?_⟩
      · simp only [Pi.add_apply,Finset.sum_add_distrib,hc,hd,add_zero]
      · simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib,he,hf]
  | smul a x hx ih =>
      rcases ih with ⟨c,hc,he⟩
      refine ⟨a•c,?_,?_⟩
      · simp only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,hc,mul_zero]
      · simp only [Pi.smul_apply,smul_eq_mul,mul_smul,←Finset.smul_sum,he]

def projectedLift (B : ι→FSC.Coord d) (L : (ι→ℝ)→L[ℝ] FSC.Coord d) :
    (ι→ℝ)→L[ℝ] FSC.Coord d := (rowDifferenceSpan B).starProjection.comp L

theorem projectedLift_mem (B : ι→FSC.Coord d) (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (q : ι→ℝ) :
    projectedLift B L q∈rowDifferenceSpan B :=
  (rowDifferenceSpan B).starProjection_apply_mem (L q)

theorem projectedLift_coherent (B : ι→FSC.Coord d)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) :
    CoherentLift B (projectedLift B L) := by
  intro q i j
  change inner ℝ (B i-B j) ((rowDifferenceSpan B).starProjection (L q))=_
  rw [←Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (difference_mem B i j)]
  exact hL q i j

/-- Centered singular values control every score-realizing vector in the
row-difference span. The arbitrary shift a makes the bound gauge-invariant. -/
theorem score_vector_norm_sq (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ) (q : ι→ℝ) (x : FSC.Coord d)
    (hx : x∈rowDifferenceSpan B)
    (hscore : ∀ i j,inner ℝ (B i-B j) x=q i-q j) (a : ℝ) :
    ‖x‖^2≤(∑ i,(q i-a)^2)/σ^2 := by
  obtain ⟨c,hc,he⟩ := centered_coefficients B x hx
  have hlo := hlower c hc
  rw [he] at hlo
  let i₀ : ι := Classical.arbitrary ι
  have hs (i : ι) : inner ℝ (B i) x=(q i-a)+(inner ℝ (B i₀) x-q i₀+a) := by
    have hh := hscore i i₀
    rw [inner_sub_left] at hh
    linarith
  have hi : ‖x‖^2=∑ i,c i*(q i-a) := by
    calc
      _ = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
      _ = inner ℝ (∑ i,c i • B i) x := by rw [he]
      _ = ∑ i,c i*inner ℝ (B i) x := by simp only [sum_inner,real_inner_smul_left]
      _ = ∑ i,c i*((q i-a)+(inner ℝ (B i₀) x-q i₀+a)) :=
        Finset.sum_congr rfl (fun i _=>congrArg (fun t:ℝ=>c i*t) (hs i))
      _ = _ := by
        simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hc,zero_mul,add_zero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun i=>q i-a)
  rw [←hi] at hcs
  have hq2 : 0≤∑ i,(q i-a)^2 := Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hm1 := mul_le_mul_of_nonneg_left hcs (sq_nonneg σ)
  have hm2 := mul_le_mul_of_nonneg_right hlo hq2
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  by_cases hx0 : ‖x‖=0
  · simpa [hx0] using hq2
  · have hx2 : 0<‖x‖^2 := sq_pos_of_ne_zero hx0
    have hh : ‖x‖^2*(‖x‖^2*σ^2)≤‖x‖^2*(∑ i,(q i-a)^2) := by nlinarith
    exact (mul_le_mul_iff_right₀ hx2).mp hh

theorem projectedLift_norm_sq (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ)
    (L : (ι→ℝ)→L[ℝ] FSC.Coord d) (hL : CoherentLift B L) (q : ι→ℝ) (a : ℝ) :
    ‖projectedLift B L q‖^2≤(∑ i,(q i-a)^2)/σ^2 :=
  score_vector_norm_sq B σ hσ hlower q _ (projectedLift_mem B L q)
    (projectedLift_coherent B L hL q) a

/-- A concrete bounded lift constructed from the existing existence theorem. -/
def boundedScoreLift (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) : (ι→ℝ)→L[ℝ] FSC.Coord d :=
  projectedLift B (scoreLiftCLM B
    (NegativeVotingFanJacobian.affineIndependent_of_centered_lower B σ hσ hlower) i₀)

theorem boundedScoreLift_coherent (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) :
    CoherentLift B (boundedScoreLift B σ hσ hlower i₀) :=
  projectedLift_coherent B _ (scoreLiftCLM_pair B _ i₀)

theorem boundedScoreLift_norm_sq (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) (q : ι→ℝ) (a : ℝ) :
    ‖boundedScoreLift B σ hσ hlower i₀ q‖^2≤(∑ i,(q i-a)^2)/σ^2 :=
  projectedLift_norm_sq B σ hσ hlower _ (scoreLiftCLM_pair B _ i₀) q a

/-- The actual affine velocity has a dimension-free Hilbert--Schmidt bound,
with any common row translation U and common offset shift c removed. -/
theorem bounded_velocity_energy_le (B : ι→FSC.Coord d) (σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound B σ) (i₀ : ι) (δ : Parameters d ι)
    (U : FSC.Coord d) (c : ℝ) :
    let V := velocityMap (boundedScoreLift B σ hσ hlower i₀) δ
    operatorHilbertSchmidt V.1^2+‖V.2‖^2 ≤
      ((∑ i,‖δ.1 i-U‖^2)+(∑ i,(δ.2 i-c)^2))/σ^2 := by
  dsimp only
  have hs : operatorHilbertSchmidt (velocityMap (boundedScoreLift B σ hσ hlower i₀) δ).1^2 ≤
      (∑ i,‖δ.1 i-U‖^2)/σ^2 := by
    rw [operatorHilbertSchmidt_sq]
    calc
      _ ≤ ∑ j:Fin d,(∑ i,(inner ℝ (δ.1 i) (EuclideanSpace.basisFun (Fin d) ℝ j)-
          inner ℝ U (EuclideanSpace.basisFun (Fin d) ℝ j))^2)/σ^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact boundedScoreLift_norm_sq B σ hσ hlower i₀ _ _
      _ = _ := by
        rw [←Finset.sum_div,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [←inner_sub_left]
        exact (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_inner_left (δ.1 i-U)
  have hz := boundedScoreLift_norm_sq B σ hσ hlower i₀ δ.2 c
  change ‖(velocityMap (boundedScoreLift B σ hσ hlower i₀) δ).2‖^2≤_ at hz
  simpa only [add_div] using add_le_add hs hz

end NegativeVotingBoundedCoherentLift
