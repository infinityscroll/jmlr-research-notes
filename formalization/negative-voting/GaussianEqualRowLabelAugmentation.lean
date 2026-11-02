import GaussianEqualDiagonalOperatorProjection

/-! Exact label-space augmentation of a core covariance factor. The added
constant direction is fixed, so equal core row norms become unit label row
norms and the actual free maximum admits the common-noise representation. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingEqualRowLabelAugmentation
open NegativeVotingCovarianceRealization NegativeVotingProcrustes
  NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl
  NegativeVotingEqualDiagonalOperatorProjection
variable {m d : ℕ} [NeZero m]

def synthesis (b : Fin m→FSC.Coord d) : FSC.Coord m→L[ℝ]FSC.Coord d :=
  reconstruction (EuclideanSpace.basisFun (Fin m) ℝ) b

def analysis (b : Fin m→FSC.Coord d) : FSC.Coord d→L[ℝ]FSC.Coord m :=
  (synthesis b).adjoint

def liftOperator (b : Fin m→FSC.Coord d)
    (F : FSC.Coord d→L[ℝ]FSC.Coord d) : FSC.Coord m→L[ℝ]FSC.Coord m :=
  (analysis b).comp (F.comp (synthesis b))

def augmentedFactor (b : Fin m→FSC.Coord d)
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) : FSC.Coord m→L[ℝ]FSC.Coord m :=
  ContinuousLinearMap.id ℝ (FSC.Coord m)+
    liftOperator b (T-ContinuousLinearMap.id ℝ (FSC.Coord d))

theorem synthesis_apply (b : Fin m→FSC.Coord d) (x : FSC.Coord m) :
    synthesis b x=∑i,x i • b i := by
  simp only [synthesis,reconstruction_apply,EuclideanSpace.basisFun_inner]

theorem synthesis_basis (b : Fin m→FSC.Coord d) (i : Fin m) :
    synthesis b (EuclideanSpace.basisFun (Fin m) ℝ i)=b i := by
  rw [synthesis_apply]
  simp [EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_smul]

theorem analysis_apply (b : Fin m→FSC.Coord d) (x : FSC.Coord d) (i : Fin m) :
    analysis b x i=inner ℝ (b i) x := by
  rw [←EuclideanSpace.basisFun_inner (Fin m) ℝ (analysis b x) i]
  change inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ i) ((synthesis b).adjoint x)=_
  rw [ContinuousLinearMap.adjoint_inner_right,synthesis_basis]

theorem synthesis_analysis (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x) (x : FSC.Coord d) :
    synthesis b (analysis b x)=x := by
  rw [synthesis_apply]
  simp only [analysis_apply,hP]

theorem analysis_inner (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x) (x y : FSC.Coord d) :
    inner ℝ (analysis b x) (analysis b y)=inner ℝ x y := by
  change inner ℝ ((synthesis b).adjoint x) (analysis b y)=_
  rw [ContinuousLinearMap.adjoint_inner_left,synthesis_analysis b hP]

theorem liftOperator_entry (b : Fin m→FSC.Coord d)
    (F : FSC.Coord d→L[ℝ]FSC.Coord d) (i j : Fin m) :
    (liftOperator b F (EuclideanSpace.basisFun (Fin m) ℝ j)) i=
      inner ℝ (b i) (F (b j)) := by
  simp only [liftOperator,ContinuousLinearMap.comp_apply,synthesis_basis,analysis_apply]

theorem liftOperator_symmetric (b : Fin m→FSC.Coord d)
    (F : FSC.Coord d→L[ℝ]FSC.Coord d) (hF : F.toLinearMap.IsSymmetric) :
    (liftOperator b F).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ ((synthesis b).adjoint (F (synthesis b x))) y=
    inner ℝ x ((synthesis b).adjoint (F (synthesis b y)))
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  exact hF _ _

theorem liftOperator_HilbertSchmidt (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (F : FSC.Coord d→L[ℝ]FSC.Coord d) :
    operatorHilbertSchmidt (liftOperator b F)=operatorHilbertSchmidt F := by
  apply (sq_eq_sq₀ (operatorHilbertSchmidt_nonneg _) (operatorHilbertSchmidt_nonneg _)).mp
  rw [operatorHilbertSchmidt_sq,parseval_operator_HilbertSchmidt_sq b hP]
  apply Finset.sum_congr rfl
  intro i _
  simp only [liftOperator,ContinuousLinearMap.comp_apply,synthesis_basis]
  rw [←real_inner_self_eq_norm_sq,analysis_inner b hP,real_inner_self_eq_norm_sq]

theorem liftOperator_ones (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (F : FSC.Coord d→L[ℝ]FSC.Coord d) :
    liftOperator b F (WithLp.toLp 2 (fun _ : Fin m=>(1:ℝ)))=0 := by
  change analysis b (F (synthesis b (WithLp.toLp 2 (fun _ : Fin m=>(1:ℝ)))))=0
  rw [synthesis_apply]
  change analysis b (F (∑i,(1:ℝ) • b i))=0
  simp only [one_smul,hb,map_zero]

theorem augmentedFactor_symmetric (b : Fin m→FSC.Coord d)
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric) :
    (augmentedFactor b T).toLinearMap.IsSymmetric :=
  (show (ContinuousLinearMap.id ℝ (FSC.Coord m)).toLinearMap.IsSymmetric from fun _ _=>rfl).add
    (liftOperator_symmetric b _ (hT.sub (fun _ _=>rfl)))

theorem augmentedFactor_ones (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) :
    augmentedFactor b T (WithLp.toLp 2 (fun _ : Fin m=>(1:ℝ)))=
      WithLp.toLp 2 (fun _ : Fin m=>(1:ℝ)) := by
  simp only [augmentedFactor,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    liftOperator_ones b hb,add_zero]

theorem augmentedFactor_gram (b : Fin m→FSC.Coord d)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (i j : Fin m) :
    inner ℝ (augmentedFactor b T (EuclideanSpace.basisFun (Fin m) ℝ i))
      (augmentedFactor b T (EuclideanSpace.basisFun (Fin m) ℝ j))=
        inner ℝ (T (b i)) (T (b j))+1/(m:ℝ) := by
  have ha k : augmentedFactor b T (EuclideanSpace.basisFun (Fin m) ℝ k)=
      EuclideanSpace.basisFun (Fin m) ℝ k+analysis b (T (b k)-b k) := by
    simp only [augmentedFactor,liftOperator,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,synthesis_basis,
      ContinuousLinearMap.sub_apply]
  rw [ha i,ha j,inner_add_left,inner_add_right,inner_add_right,
    analysis_inner b hP,(EuclideanSpace.basisFun (Fin m) ℝ).inner_eq_ite,
    EuclideanSpace.basisFun_inner,EuclideanSpace.inner_basisFun_real,analysis_apply,analysis_apply]
  simp only [inner_sub_left,inner_sub_right]
  rw [real_inner_comm (b j) (T (b i)),real_inner_comm (b j) (b i),hG]
  by_cases hij : i=j
  · subst j;simp only [ite_true];ring
  · simp only [ite_false,hij,Ne.symm hij];ring

/-- The endpoint needed by the full-rank free-CDF path. Its row law is
exactly the core score law with a common variance-1/m Gaussian added. -/
theorem augmented_path_data (b : Fin m→FSC.Coord d) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (T : FSC.Coord d→L[ℝ]FSC.Coord d) (hT : T.toLinearMap.IsSymmetric)
    (hnorm : ∀i,‖T (b i)‖^2=1-1/(m:ℝ)) :
    let F:=liftOperator b (T-ContinuousLinearMap.id ℝ (FSC.Coord d))
    F.toLinearMap.IsSymmetric ∧ F (WithLp.toLp 2 (fun _ : Fin m=>(1:ℝ)))=0 ∧
      operatorHilbertSchmidt F=operatorHilbertSchmidt (T-ContinuousLinearMap.id ℝ (FSC.Coord d)) ∧
      ∀i,‖(ContinuousLinearMap.id ℝ (FSC.Coord m)+F)
        (EuclideanSpace.basisFun (Fin m) ℝ i)‖^2=1 := by
  dsimp only
  refine ⟨liftOperator_symmetric b _ (hT.sub (fun _ _=>rfl)),liftOperator_ones b hb _,
    liftOperator_HilbertSchmidt b hP _,?_⟩
  intro i
  change ‖augmentedFactor b T (EuclideanSpace.basisFun (Fin m) ℝ i)‖^2=1
  rw [←real_inner_self_eq_norm_sq,augmentedFactor_gram b hP hG,real_inner_self_eq_norm_sq,hnorm]
  ring

end NegativeVotingEqualRowLabelAugmentation
