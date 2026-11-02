import GaussianCenteredParsevalBasis
import GaussianCentroidEnergyAttainment
import GaussianCovarianceStrictConcavity

/-! Actual covariance/row realization on a centered Parseval score frame.
Singular covariance matrices are retained; square roots need not be invertible.
The maximizer correspondence uses actual Gaussian assignment duality. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCovarianceRealization
open NegativeVoting NegativeVotingCenteredParseval NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingPositiveCovariance
  NegativeVotingCovariancePath NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict NegativeVotingFanValue

section Factors
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Every genuine PSD operator has a genuine PSD square root, also at rank loss. -/
theorem exists_psd_factor (C : E →L[ℝ] E) (hC : C∈psdCone) :
    ∃ R : E →L[ℝ] E, R∈psdCone ∧ R.comp R=C := by
  classical
  let e := hC.1.eigenvectorBasis (n:=Module.finrank ℝ E) rfl
  let ev := hC.1.eigenvalues (n:=Module.finrank ℝ E) rfl
  have heq : diagonal e ev=C := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    change diagonal e ev (e i)=C (e i)
    rw [diagonal_basis]
    exact (hC.1.apply_eigenvectorBasis rfl i).symm
  have hev (i) : 0≤ev i := by
    have hp := hC.2 (e i)
    rw [←heq,diagonal_basis] at hp
    simpa only [real_inner_smul_right,e.inner_eq_ite,ite_true,mul_one] using hp
  let R := diagonal e (fun i=>Real.sqrt (ev i))
  refine ⟨R,⟨diagonal_symmetric e _,?_⟩,?_⟩
  · intro x
    rw [real_inner_comm (R x) x]
    change 0 ≤ inner ℝ (diagonal e (fun i=>Real.sqrt (ev i)) x) x
    rw [inner_diagonal]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [Real.sqrt_nonneg (ev i),sq_nonneg (inner ℝ (e i) x)]
  · dsimp [R]
    rw [diagonal_comp,←heq]
    congr 1
    funext i
    simpa only [←sq] using Real.sq_sqrt (hev i)

theorem adjoint_square_psd (A : E →L[ℝ] F) : A.adjoint.comp A∈psdCone := by
  refine ⟨?_,?_⟩
  · intro x y
    change inner ℝ (A.adjoint (A x)) y=inner ℝ x (A.adjoint (A y))
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  · intro x
    change 0 ≤ inner ℝ x (A.adjoint (A x))
    rw [ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq]
    positivity

end Factors
variable {m d e : ℕ} [NeZero m]

/-- The actual linear reconstruction of arbitrary centered rows from the
normalized score frame. The output dimension can differ from the frame dimension. -/
def reconstruction (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e) :
    FSC.Coord d →L[ℝ] FSC.Coord e := ∑ i,(innerSL ℝ (b i)).smulRight (B i)

@[simp] theorem reconstruction_apply (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e)
    (x : FSC.Coord d) : reconstruction b B x=∑ i,inner ℝ (b i) x • B i := by
  simp [reconstruction,ContinuousLinearMap.sum_apply]

theorem reconstruction_row (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hB : (∑ i,B i)=0) (i : Fin m) : reconstruction b B (b i)=B i := by
  rw [reconstruction_apply]
  simp_rw [hG,sub_smul,Finset.sum_sub_distrib]
  simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Finset.smul_sum,hB,smul_zero,sub_zero]

theorem adjoint_factor_gram (b : Fin m → FSC.Coord d) (A : FSC.Coord d →L[ℝ] FSC.Coord e) :
    gramVelocity b (A.adjoint.comp A)=Matrix.gram ℝ (fun i=>A (b i)) := by
  ext i j
  change inner ℝ (b i) (A.adjoint (A (b j)))=inner ℝ (A (b i)) (A (b j))
  exact ContinuousLinearMap.adjoint_inner_right A (b i) (A (b j))

/-- The intrinsic covariance value is exactly the actual dual assignment value
for every rectangular factor, without a full-rank premise. -/
theorem operatorValue_factor (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (A : FSC.Coord d →L[ℝ] FSC.Coord e) :
    operatorValue b p (A.adjoint.comp A)=optimizedValue (fun i=>A (b i)) p := by
  unfold operatorValue
  rw [adjoint_factor_gram,covarianceValue_gram]

theorem penalizedValue_factor (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (A : FSC.Coord d →L[ℝ] FSC.Coord e) :
    penalizedValue b p (A.adjoint.comp A)=rowObjective (fun i=>A (b i)) p := by
  unfold penalizedValue rowObjective rowEnergy
  rw [operatorValue_factor,parseval_square_trace b hP]

def rowCovariance (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e) :
    FSC.Coord d →L[ℝ] FSC.Coord d := (reconstruction b B).adjoint.comp (reconstruction b B)

theorem rowCovariance_psd (b : Fin m → FSC.Coord d) (B : Fin m → FSC.Coord e) :
    rowCovariance b B∈psdCone := adjoint_square_psd _

theorem rowCovariance_value (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord e) (hB : (∑ i,B i)=0) (p : Fin m → ℝ) :
    operatorValue b p (rowCovariance b B)=optimizedValue B p := by
  rw [rowCovariance,operatorValue_factor]
  congr 1
  funext i
  exact reconstruction_row b B hG hB i

theorem rowCovariance_trace (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : (∑ i,B i)=0) :
    LinearMap.trace ℝ (FSC.Coord d) (rowCovariance b B).toLinearMap=rowEnergy B := by
  rw [rowCovariance,parseval_square_trace b hP]
  simp_rw [reconstruction_row b B hG hB]
  rfl

theorem rowCovariance_objective (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (B : Fin m → FSC.Coord e) (hB : (∑ i,B i)=0) (p : Fin m → ℝ) :
    penalizedValue b p (rowCovariance b B)=rowObjective B p := by
  unfold penalizedValue rowObjective
  rw [rowCovariance_value b hG B hB,rowCovariance_trace b hG hP B hB]

/-- A global covariance optimum bounds every feasible centroid energy in every
finite ambient dimension, through its actual reconstructed covariance. -/
theorem centroidEnergy_le_covariance_maximum
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hmax : ∀ D, D∈psdCone → penalizedValue b p D≤penalizedValue b p C)
    (g : FSC.Coord e → Fin m → ℝ) (hg : Feasible p g) :
    centroidEnergy g≤penalizedValue b p C := by
  calc
    _ ≤ rowObjective (centroidRows g) p := centroidEnergy_le_rowObjective p g hg
    _ = penalizedValue b p (rowCovariance b (centroidRows g)) :=
      (rowCovariance_objective b hG hP _ (centroidRows_sum_zero p g hg) p).symm
    _ ≤ _ := hmax _ (rowCovariance_psd _ _)

/-- Every PSD covariance maximizer is realized by an actual optimal fractional
Gaussian assignment whose centroids are its square-root rows. -/
theorem covariance_maximizer_centroid_assignment
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈psdCone)
    (hmax : ∀ D,D∈psdCone → penalizedValue b p D≤penalizedValue b p C) :
    ∃ (R : FSC.Coord d →L[ℝ] FSC.Coord d) (f : FSC.Coord d → Fin m → ℝ),
      R∈psdCone ∧ R.comp R=C ∧ Feasible p f ∧
      (∀ i,Measurable (fun x=>f x i)) ∧ (∀ x,SimplexWeights (f x)) ∧
      (fun i=>R (b i))=centroidRows f ∧
      operatorValue b p C=LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap ∧
      penalizedValue b p C=centroidEnergy f ∧
      ∀ (e : ℕ) (g : FSC.Coord e → Fin m → ℝ),Feasible p g→centroidEnergy g≤centroidEnergy f := by
  obtain ⟨R,hR,hRC⟩ := exists_psd_factor C hC
  have hRC' : R.adjoint.comp R=C := by rw [hR.1.clm_adjoint_eq,hRC]
  let B : Fin m → FSC.Coord d := fun i=>R (b i)
  obtain ⟨h,f,hfm,hfp,hfmass,hval,_⟩ := exists_assignment_and_offsets B p hp hs
  have hf : Feasible p f := ⟨fun i=>(hfm i).aemeasurable,ae_of_all _ hfp,hfmass⟩
  have hobj : penalizedValue b p C=rowObjective B p := by
    rw [←hRC']; exact penalizedValue_factor b hP p R
  have hcomp := assignment_square_completion B p f hf
  rw [hval] at hcomp
  change rowObjective B p=centroidEnergy f-rowEnergy (B-centroidRows f) at hcomp
  have hupper := centroidEnergy_le_covariance_maximum b hG hP p C hmax f hf
  have herr : rowEnergy (B-centroidRows f)=0 := by
    have hn := rowEnergy_nonneg (B-centroidRows f)
    linarith
  have hBc : B=centroidRows f := (rowEnergy_sub_zero_iff B (centroidRows f)).mp herr
  have hW : penalizedValue b p C=centroidEnergy f := by rw [hobj,hcomp,herr,sub_zero]
  have htr : LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap=centroidEnergy f := by
    rw [←hRC',parseval_square_trace b hP]
    change rowEnergy B=centroidEnergy f
    rw [hBc]; rfl
  have hΓ : operatorValue b p C=LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap := by
    unfold penalizedValue at hW
    linarith
  refine ⟨R,f,hR,hRC,hf,hfm,hfp,hBc,hΓ,hW,?_⟩
  intro e g hg
  rw [←hW]
  exact centroidEnergy_le_covariance_maximum b hG hP p C hmax g hg

/-- Existence at epsilon=0 follows from the proved actual row optimizer;
there is no invertibility or strict-concavity assumption at the PSD boundary. -/
theorem exists_covariance_maximizer
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ∃ C : FSC.Coord d →L[ℝ] FSC.Coord d,
      C∈psdCone ∧ ∀ D,D∈psdCone → penalizedValue b p D≤penalizedValue b p C := by
  obtain ⟨B,f,_,_,_,_,hB0,_,_,hBmax,_⟩ :=
    exists_centroid_optimal_assignment (d:=d) p hp hs
  refine ⟨rowCovariance b B,rowCovariance_psd _ _,?_⟩
  intro D hD
  obtain ⟨R,hR,hRD⟩ := exists_psd_factor D hD
  have hv := penalizedValue_factor b hP p R
  rw [hR.1.clm_adjoint_eq,hRD] at hv
  rw [hv,rowCovariance_objective b hG hP B hB0]
  exact hBmax _

/-- The covariance maximum equals an attained actual centroid-energy maximum,
including comparison with completed-measurable rules in every ambient dimension. -/
theorem exists_covariance_and_centroid_maximizers
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ∃ (C R : FSC.Coord d →L[ℝ] FSC.Coord d) (f : FSC.Coord d → Fin m → ℝ),
      C∈psdCone ∧
      (∀ D,D∈psdCone → penalizedValue b p D≤penalizedValue b p C) ∧
      R∈psdCone ∧ R.comp R=C ∧ Feasible p f ∧
      (∀ i,Measurable (fun x=>f x i)) ∧ (∀ x,SimplexWeights (f x)) ∧
      (fun i=>R (b i))=centroidRows f ∧
      operatorValue b p C=LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap ∧
      penalizedValue b p C=centroidEnergy f ∧
      ∀ (e : ℕ) (g : FSC.Coord e → Fin m → ℝ),Feasible p g→centroidEnergy g≤centroidEnergy f := by
  obtain ⟨C,hC,hmax⟩ := exists_covariance_maximizer b hG hP p hp hs
  obtain ⟨R,f,hR,hRC,hf,hfm,hfp,hcent,hval,hobj,hglobal⟩ :=
    covariance_maximizer_centroid_assignment b hG hP p hp hs C hC hmax
  exact ⟨C,R,f,hC,hmax,hR,hRC,hf,hfm,hfp,hcent,hval,hobj,hglobal⟩

end NegativeVotingCovarianceRealization
