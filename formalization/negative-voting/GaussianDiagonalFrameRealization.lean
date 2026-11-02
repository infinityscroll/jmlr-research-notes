import GaussianDiagonalCovarianceSupport
import GaussianCenteredParsevalBasis

/-! A literal positive covariance realization of independent Gaussian scores
projected onto the centered label subspace. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingDiagonalFrameRealization
open NegativeVotingDiagonalWinnerIntegral NegativeVotingPositiveCovariance
  NegativeVotingDiagonalCovarianceSupport
variable {m d : ℕ} [NeZero m]

def frameOperator (b : Fin m→FSC.Coord d) (v : Fin m→ℝ) : FSC.Coord d→L[ℝ]FSC.Coord d :=
  ∑i,v i • InnerProductSpace.rankOne ℝ (b i) (b i)

lemma frameOperator_apply (b : Fin m→FSC.Coord d) (v : Fin m→ℝ) (x : FSC.Coord d) :
    frameOperator b v x=∑i,(v i*inner ℝ (b i) x) • b i := by
  simp [frameOperator,smul_smul]

lemma frameOperator_pairing (b : Fin m→FSC.Coord d) (v : Fin m→ℝ) (x y : FSC.Coord d) :
    inner ℝ x (frameOperator b v y)=∑i,v i*inner ℝ (b i) x*inner ℝ (b i) y := by
  rw [frameOperator_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right,real_inner_comm x (b i)]
  ring

lemma frameOperator_symmetric (b : Fin m→FSC.Coord d) (v : Fin m→ℝ) :
    (frameOperator b v).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (frameOperator b v x) y=inner ℝ x (frameOperator b v y)
  rw [real_inner_comm,frameOperator_pairing,frameOperator_pairing]
  apply Finset.sum_congr rfl
  intro i _;ring

theorem frameOperator_positive (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x) (v : Fin m→ℝ) (hv : ∀i,0<v i) :
    frameOperator b v∈pdCone := by
  refine ⟨frameOperator_symmetric b v,?_⟩
  intro x hx
  rw [frameOperator_pairing]
  have he:∃i,inner ℝ (b i) x≠0:=by
    by_contra hh
    push_neg at hh
    have hhx:=hP x
    simp only [hh,zero_smul,Finset.sum_const_zero] at hhx
    exact hx hhx.symm
  obtain ⟨i,hi⟩:=he
  apply Finset.sum_pos'
  · intro j _
    have hh:=mul_nonneg (hv j).le (sq_nonneg (inner ℝ (b j) x))
    nlinarith
  · refine ⟨i,Finset.mem_univ i,?_⟩
    have hh:=mul_pos (hv i) (sq_pos_of_ne_zero hi)
    nlinarith

def scoreCenter (σ : Fin m→ℝ) : FSC.Coord m := WithLp.toLp 2 (fun k=>σ k/(m:ℝ))

lemma centered_diagonal_coordinate (σ : Fin m→ℝ) (i k : Fin m) :
    (diagonalRows σ i-scoreCenter σ) k=σ k*((if k=i then 1 else 0)-1/(m:ℝ)) := by
  by_cases hki:k=i
  · subst k
    simp [diagonalRows,scoreCenter,PiLp.sub_apply,PiLp.single_apply]
    ring
  · simp [diagonalRows,scoreCenter,PiLp.sub_apply,PiLp.single_apply,hki,Ne.symm hki]
    ring

theorem frameOperator_diagonal_gram (b : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (σ : Fin m→ℝ) (i j : Fin m) :
    inner ℝ (b i) (frameOperator b (fun k=>(σ k)^2) (b j))=
      inner ℝ (diagonalRows σ i-scoreCenter σ) (diagonalRows σ j-scoreCenter σ) := by
  rw [frameOperator_pairing,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [centered_diagonal_coordinate,centered_diagonal_coordinate,hG,hG]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

/-- Positive score variances and the Parseval frame discharge every support
covariance hypothesis in the actual hazard supporting theorem. -/
theorem covariance_le_diagonal_support {n : ℕ}
    (b : AffineBasis (Fin (n+1)) ℝ (FSC.Coord d))
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+1))
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (σ : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i)
    (C : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈psdCone) :
    NegativeVotingCovarianceConcavity.operatorValue b p C ≤ (1/2:ℝ)*∑i,
      NegativeVotingDiagonalIntegratedLaplacian.integratedRowSum σ
        (NegativeVotingFanSelectedOffsets.selectedOffsets (diagonalRows σ) p) i*
        (inner ℝ (b i) (C (b i))+inner ℝ (b i) (frameOperator b (fun k=>(σ k)^2) (b i))) := by
  apply operatorValue_le_diagonal_hazard_support b p hp hs σ hσ (scoreCenter σ)
    C (frameOperator b (fun k=>(σ k)^2)) hC
    (frameOperator_positive b hP _ (fun k=>sq_pos_of_pos (hσ k)))
  exact frameOperator_diagonal_gram b (by simpa only [Nat.cast_add,Nat.cast_one] using hG) σ

end NegativeVotingDiagonalFrameRealization
