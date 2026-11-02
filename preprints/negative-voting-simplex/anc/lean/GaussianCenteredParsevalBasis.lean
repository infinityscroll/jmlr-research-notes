import GaussianFanMassJacobian
import NegativeVoting.RegularSimplexExistence
import NegativeVoting.RegularSimplexCentroid

/-! An actual centered Parseval affine basis of the minimal score space.
The Gram normalization is derived from the existing regular simplex existence
construction, and Parseval is proved rather than assumed of an affine basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCenteredParseval
open NegativeVoting NegativeVotingCapTail NegativeVotingFanJacobian

variable {d m : ℕ} [NeZero m]

/-- Inner products of a regular Gram combination recover its centered
coefficients exactly. -/
theorem weighted_inner (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (c : Fin m → ℝ) (i : Fin m) :
    inner ℝ (∑ j, c j • B j) (B i)=c i-(∑ j,c j)/(m:ℝ) := by
  rw [sum_inner]
  simp_rw [real_inner_smul_left,hG,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul]
  ring

/-- The centered coefficient map is an isometry on the zero-sum gauge. -/
theorem weighted_norm_sq (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (c : Fin m → ℝ) :
    ‖∑ j,c j • B j‖^2=(∑ j,c j^2)-(∑ j,c j)^2/(m:ℝ) := by
  rw [← real_inner_self_eq_norm_sq,inner_sum]
  simp_rw [real_inner_smul_right,weighted_inner B hG,mul_sub,Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  simp only [← sq]
  ring

theorem centered_singular_one (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    CenteredSingularLowerBound B 1 := by
  intro c hc
  rw [weighted_norm_sq B hG,hc]
  simp

theorem regularGram_affineIndependent (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    AffineIndependent ℝ B :=
  affineIndependent_of_centered_lower B 1 (by norm_num) (centered_singular_one B hG)

/-- The finite frame operator, defined on the actual Euclidean space. -/
def frameOperator (B : Fin m → FSC.Coord d) : FSC.Coord d →L[ℝ] FSC.Coord d :=
  ∑ i, (innerSL ℝ (B i)).smulRight (B i)

@[simp] theorem frameOperator_apply (B : Fin m → FSC.Coord d) (x : FSC.Coord d) :
    frameOperator B x=∑ i,inner ℝ (B i) x • B i := by
  simp [frameOperator,ContinuousLinearMap.sum_apply]

theorem frameOperator_row (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hzero : (∑ i,B i)=0) (i : Fin m) : frameOperator B (B i)=B i := by
  rw [frameOperator_apply]
  simp_rw [hG,sub_smul,Finset.sum_sub_distrib]
  simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.smul_sum,hzero,smul_zero,sub_zero]

/-- Centering, the exact regular Gram matrix, and actual full affine span
force the frame operator to be the identity. -/
theorem parseval_of_regularGram (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hzero : (∑ i,B i)=0) (hspan : affineSpan ℝ (range B)=⊤) (x : FSC.Coord d) :
    (∑ i,inner ℝ (B i) x • B i)=x := by
  have he : (frameOperator B).toLinearMap.toAffineMap=AffineMap.id ℝ (FSC.Coord d) := by
    apply AffineMap.ext_on hspan
    rintro _ ⟨i,rfl⟩
    exact frameOperator_row B hG hzero i
  have hx := congrArg (fun A : FSC.Coord d →ᵃ[ℝ] FSC.Coord d => A x) he
  change frameOperator B x=x at hx
  simpa only [frameOperator_apply] using hx

/-- The pointwise Parseval identity implies the exact scalar energy identity. -/
theorem parseval_energy (B : Fin m → FSC.Coord d)
    (hP : ∀ x, (∑ i,inner ℝ (B i) x • B i)=x) (x : FSC.Coord d) :
    (∑ i,(inner ℝ (B i) x)^2)=‖x‖^2 := by
  have hx := congrArg (fun y => inner ℝ y x) (hP x)
  simpa only [sum_inner,real_inner_smul_left,← sq,real_inner_self_eq_norm_sq] using hx

/-- Exact trace normalization for every linear operator, without an
orthogonality assumption on the affine basis itself. -/
theorem parseval_trace (B : Fin m → FSC.Coord d)
    (hP : ∀ x, (∑ i,inner ℝ (B i) x • B i)=x)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap=∑ i,inner ℝ (B i) (A (B i)) := by
  have hA : A.toLinearMap=∑ i,(innerSL ℝ (B i)).toLinearMap.smulRight (A (B i)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply,LinearMap.smulRight_apply,ContinuousLinearMap.coe_coe]
    change A x=∑ i,inner ℝ (B i) x • A (B i)
    have hx := congrArg A (hP x)
    simpa only [map_sum,map_smul] using hx.symm
  rw [hA,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_smulRight]
  rfl

/-- In particular the energy of transformed rows is exactly the covariance
trace. This is the normalization used by the covariance optimization. -/
theorem parseval_square_trace {d₂ : ℕ} (B : Fin m → FSC.Coord d)
    (hP : ∀ x, (∑ i,inner ℝ (B i) x • B i)=x)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d₂) :
    LinearMap.trace ℝ (FSC.Coord d) (A.adjoint.comp A).toLinearMap=∑ i,‖A (B i)‖^2 := by
  rw [parseval_trace B hP]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

theorem regularGram_row_energy (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ)) :
    (∑ i,‖B i‖^2)=(m:ℝ)-1 := by
  simp_rw [← real_inner_self_eq_norm_sq,hG,ite_true]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hm : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  field_simp

/-- Existence in dimension exactly m-1, including the singleton/zero-dimensional
case. The returned object is an actual affine basis with the exact Parseval
normalization; no arbitrary affine basis is substituted. -/
theorem exists_centered_parseval_affineBasis (m : ℕ) (hm : 1 ≤ m) :
    ∃ b : AffineBasis (Fin m) ℝ (FSC.Coord (m-1)),
      (∑ i,b i)=0 ∧
      (∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ)) ∧
      ∀ x, (∑ i,inner ℝ (b i) x • b i)=x := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨rows,hrows⟩ := exists_regularSimplexGram_minimal hm
  let B : Fin m → FSC.Coord (m-1) := simplexRow rows
  have hG : ∀ i j, inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ) :=
    simplexRow_gram rows hrows
  have hi := regularGram_affineIndependent B hG
  have hs : affineSpan ℝ (range B)=⊤ := by
    apply hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp only [Fintype.card_fin,FSC.Coord,finrank_euclideanSpace_fin]
    omega
  have hz : (∑ i,B i)=0 := simplexRows_sum_zero rows hrows
  let b : AffineBasis (Fin m) ℝ (FSC.Coord (m-1)) := ⟨B,hi,hs⟩
  exact ⟨b,hz,hG,parseval_of_regularGram B hG hz hs⟩

/-- A fixed choice of the proved normalized basis. -/
def centeredParsevalBasis (m : ℕ) (hm : 1 ≤ m) : AffineBasis (Fin m) ℝ (FSC.Coord (m-1)) :=
  (exists_centered_parseval_affineBasis m hm).choose

theorem centeredParsevalBasis_spec (m : ℕ) (hm : 1 ≤ m) :
    (∑ i,centeredParsevalBasis m hm i)=0 ∧
    (∀ i j,inner ℝ (centeredParsevalBasis m hm i) (centeredParsevalBasis m hm j)=
      (if i=j then 1 else 0)-1/(m:ℝ)) ∧
    ∀ x, (∑ i,inner ℝ (centeredParsevalBasis m hm i) x • centeredParsevalBasis m hm i)=x :=
  (exists_centered_parseval_affineBasis m hm).choose_spec

end NegativeVotingCenteredParseval
