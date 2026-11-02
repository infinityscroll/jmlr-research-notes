import MulgundGaussianComparison
import GaussianFanCovarianceValue
import GaussianRegularScoreLaw
import GaussianRegularSpectatorRepresentation

/-! Actual singular Gaussian score laws and the common-noise transform for
centered equal-row maxima. The added Gaussian is only a product-measure
comparison device; no extra original ambient coordinate is assumed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Classical ENNReal NNReal MatrixOrder
namespace NegativeVotingEqualRowMaximumLaw
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingFanCovarianceValue
  NegativeVotingRegularSpectatorRepresentation
variable {m d : ℕ} [NeZero m]

/-- Identification with the actual multivariate Gaussian law, including
singular covariance. -/
theorem scoreLaw_eq_multivariateGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : Fin m→E) :
    NegativeVotingFanCovarianceLaw.scoreLaw B=
      multivariateGaussian (0:EuclideanSpace ℝ (Fin m)) (Matrix.gram ℝ B) := by
  let G := Matrix.gram ℝ B
  have hG : G.PosSemidef := Matrix.posSemidef_gram ℝ B
  have he := NegativeVotingFanCovarianceLaw.scoreLaw_eq_of_gram B (covarianceRows G)
    (fun i j=>(congrFun (congrFun (covarianceRows_gram G hG) i) j).symm)
  rw [he]
  unfold NegativeVotingFanCovarianceLaw.scoreLaw multivariateGaussian
  congr 1
  funext x
  ext i
  simp only [NegativeVotingFanCovarianceLaw.scoreVector_apply,covarianceRows,
    PiLp.inner_apply,Real.inner_apply,zero_add]
  rw [Matrix.ofLp_toEuclideanCLM]
  rfl

/-- Exact CDF comparison for a Gaussian row system satisfying precisely the
external theorem's unit marginal and rank-one domination assumptions. -/
theorem score_maximum_cdf_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : Fin m→E) (hdiag : ∀ i,inner ℝ (B i) (B i)=1)
    (hrank : ((Matrix.gram ℝ B)-Matrix.of (fun (_ _ : Fin m)=>(1:ℝ)/(m:ℝ))).PosSemidef)
    (t : ℝ) :
    (standardGaussian (Fin m)) {y | maximum y ≤ t} ≤
      (stdGaussian E) {x | maxScore (fun i=>inner ℝ (B i) x) ≤ t} := by
  have hh := NegativeVotingDependencies.equalThreshold_gaussian_comparison
    (NeZero.pos m) (Matrix.gram ℝ B) (Matrix.posSemidef_gram ℝ B) hdiag hrank t
  rw [←scoreLaw_eq_multivariateGaussian B] at hh
  rw [NegativeVotingFanCovarianceLaw.scoreLaw,Measure.map_apply
    (NegativeVotingFanCovarianceLaw.continuous_scoreVector B).measurable
    (by
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter (fun i=>measurableSet_le (by fun_prop) measurable_const))] at hh
  have hy : {y : Fin m→ℝ | maximum y ≤ t}=Set.pi Set.univ (fun _=>Iic t) := by
    ext y;simp [maximum,maxScore,Finset.sup'_le_iff];rfl
  have hx : (NegativeVotingFanCovarianceLaw.scoreVector B) ⁻¹' {x | ∀ i,x i ≤ t}=
      {x | maxScore (fun i=>inner ℝ (B i) x) ≤ t} := by
    ext x;simp [maxScore,Finset.sup'_le_iff]
  rw [hx] at hh
  rw [hy,standardGaussian,Measure.pi_pi]
  simpa using hh

/-- Raw coordinates for the independent common Gaussian transform. -/
def addedRows (B : Fin m→FSC.Coord d) (c : ℝ) (i : Fin m) : Fin d⊕Fin 1→ℝ :=
  Sum.elim (fun j=>B i j) (fun _=>c)

def addedMaximum (B : Fin m→FSC.Coord d) (c : ℝ) (x : Fin d⊕Fin 1→ℝ) : ℝ :=
  maxScore (NegativeVotingRegularScoreLaw.coordinateScores (addedRows B c) x)

theorem addedRows_gram (B : Fin m→FSC.Coord d) (c : ℝ) (i j : Fin m) :
    inner ℝ (WithLp.toLp 2 (addedRows B c i)) (WithLp.toLp 2 (addedRows B c j))=
      inner ℝ (B i) (B j)+c^2 := by
  simp [PiLp.inner_apply,Real.inner_apply,addedRows,Fintype.sum_sum_type,pow_two,mul_comm]

/-- The product-measure common-noise transform has the exact required CDF
order whenever the original squared row norm is `1-1/m`. -/
theorem addedMaximum_cdf_ge (B : Fin m→FSC.Coord d)
    (hB : ∀ i,inner ℝ (B i) (B i)=1-1/(m:ℝ))
    (c : ℝ) (hc : c^2=1/(m:ℝ)) (t : ℝ) :
    (standardGaussian (Fin m)) {y | maximum y ≤ t} ≤
      (standardGaussian (Fin d⊕Fin 1)) {x | addedMaximum B c x ≤ t} := by
  let C : Fin m→EuclideanSpace ℝ (Fin d⊕Fin 1) := fun i=>WithLp.toLp 2 (addedRows B c i)
  have hdiag i : inner ℝ (C i) (C i)=1 := by rw [addedRows_gram,hB,hc];ring
  have hmat : Matrix.gram ℝ C-Matrix.of (fun (_ _ : Fin m)=>(1:ℝ)/(m:ℝ))=Matrix.gram ℝ B := by
    ext i j
    change inner ℝ (C i) (C j)-1/(m:ℝ)=inner ℝ (B i) (B j)
    rw [addedRows_gram,hc];ring
  have hh := score_maximum_cdf_ge C hdiag (by rw [hmat];exact Matrix.posSemidef_gram ℝ B) t
  have hset : MeasurableSet {x | maxScore (fun i=>inner ℝ (C i) x) ≤ t} := by
    simp only [maxScore,Finset.sup'_le_iff,Finset.mem_univ,forall_const]
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i=>measurableSet_le (by fun_prop) measurable_const)
  rw [←map_pi_eq_stdGaussian,Measure.map_apply (by fun_prop) hset] at hh
  convert hh using 1
  congr 1
  ext x
  change addedMaximum B c x ≤ t ↔ maxScore (fun i=>inner ℝ (C i) (WithLp.toLp 2 x)) ≤ t
  have he : (fun i=>inner ℝ (C i) (WithLp.toLp 2 x))=
      NegativeVotingRegularScoreLaw.coordinateScores (addedRows B c) x := by
    funext i
    simp only [PiLp.inner_apply,Real.inner_apply]
    rfl
  rw [he]
  rfl



/-- The original row maximum in unbundled standard Gaussian coordinates. -/
def rowMaximum (B : Fin m→FSC.Coord d) (x : Fin d→ℝ) : ℝ :=
  maxScore (NegativeVotingRegularScoreLaw.coordinateScores (fun i=>(B i).ofLp) x)

private theorem finite_max_memLp_two {κ : Type*} [Fintype κ]
    (A : Fin m→κ→ℝ) :
    MemLp (fun x : κ→ℝ=>maxScore (NegativeVotingRegularScoreLaw.coordinateScores A x))
      2 (standardGaussian κ) := by
  have hi (i : Fin m) : MemLp (fun x : κ→ℝ=>∑ j,A i j*x j) 2 (standardGaussian κ) := by
    exact memLp_finsetSum _ (fun j _=>
      ((memLp_id_gaussianReal 2).comp_measurePreserving
        (measurePreserving_eval (μ:=fun _:κ=>gaussianReal 0 1) j)).const_mul (A i j))
  have hh (s : Finset (Fin m)) (hs : s.Nonempty) :
      MemLp (fun x : κ→ℝ=>s.sup' hs (fun i=>∑ j,A i j*x j)) 2 (standardGaussian κ) := by
    induction s using Finset.induction_on with
    | empty=>simp at hs
    | @insert a s ha ih=>
      by_cases hne : s.Nonempty
      · simpa only [Finset.sup'_insert hne,Pi.sup_def] using (hi a).sup (ih hne)
      · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst s
        simpa using hi a
  exact hh Finset.univ Finset.univ_nonempty

theorem rowMaximum_memLp_two (B : Fin m→FSC.Coord d) :
    MemLp (rowMaximum B) 2 (standardGaussian (Fin d)) := finite_max_memLp_two _

theorem addedMaximum_memLp_two (B : Fin m→FSC.Coord d) (c : ℝ) :
    MemLp (addedMaximum B c) 2 (standardGaussian (Fin d⊕Fin 1)) := finite_max_memLp_two _

theorem rowMaximum_measurable (B : Fin m→FSC.Coord d) : Measurable (rowMaximum B) :=
  measurable_finite_max _ Finset.univ Finset.univ_nonempty (fun i _=>by
    unfold NegativeVotingRegularScoreLaw.coordinateScores
    fun_prop)

theorem addedMaximum_measurable (B : Fin m→FSC.Coord d) (c : ℝ) : Measurable (addedMaximum B c) :=
  measurable_finite_max _ Finset.univ Finset.univ_nonempty (fun i _=>by
    unfold NegativeVotingRegularScoreLaw.coordinateScores
    fun_prop)

theorem addedMaximum_split (B : Fin m→FSC.Coord d) (c : ℝ)
    (x : Fin d→ℝ) (g : Fin 1→ℝ) :
    addedMaximum B c (Sum.elim x g)=rowMaximum B x+c*g 0 := by
  unfold addedMaximum rowMaximum NegativeVotingRegularScoreLaw.coordinateScores
  simp only [addedRows,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_one]
  have he : (fun i=> (∑ j,(B i).ofLp j*x j)+c*g 0)=
      (fun i=> (∑ j,(B i).ofLp j*x j)-(-c*g 0)) := by funext i;ring
  rw [he,NegativeVotingRegularMaximum.maxScore_sub_const]
  ring

theorem addedMaximum_mean (B : Fin m→FSC.Coord d) (c : ℝ) :
    (∫ x,addedMaximum B c x ∂standardGaussian (Fin d⊕Fin 1))=
      ∫ x,rowMaximum B x ∂standardGaussian (Fin d) := by
  have hi := (rowMaximum_memLp_two B).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hg : Integrable (fun g : Fin 1→ℝ=>g 0) (standardGaussian (Fin 1)) :=
    gaussian_product_coordinate_integrable (fun _=>0) (fun _=>1) 0
  rw [gaussian_sum_integral]
  simp_rw [addedMaximum_split]
  rw [integral_add (hi.comp_fst _) ((hg.const_mul c).comp_snd _),
    integral_fun_fst,integral_const_mul,integral_fun_snd (fun g:Fin 1→ℝ=>g 0),
    NegativeVotingRegularMaximum.standardGaussian_coordinate_integral]
  simp

theorem standard_coordinate_square {κ : Type*} [Fintype κ] (i : κ) :
    (∫ x : κ→ℝ,(x i)^2 ∂standardGaussian κ)=1 := by
  have he := integral_map (μ:=standardGaussian κ) (φ:=fun x:κ→ℝ=>x i)
    (f:=fun z:ℝ=>z^2) (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [(measurePreserving_eval (μ:=fun _:κ=>gaussianReal 0 1) i).map_eq] at he
  rw [←he]
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  change Var[fun y:ℝ=>y;gaussianReal 0 1]=(∫ y:ℝ,y^2 ∂gaussianReal 0 1)-
    (∫ y:ℝ,y ∂gaussianReal 0 1)^2 at hv
  rw [variance_fun_id_gaussianReal,integral_id_gaussianReal] at hv
  norm_num at hv
  exact hv.symm

theorem addedMaximum_second_moment (B : Fin m→FSC.Coord d) (c : ℝ) :
    (∫ x,(addedMaximum B c x)^2 ∂standardGaussian (Fin d⊕Fin 1))=
      (∫ x,(rowMaximum B x)^2 ∂standardGaussian (Fin d))+c^2 := by
  have hi := (rowMaximum_memLp_two B).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hi2 := (rowMaximum_memLp_two B).integrable_sq
  have hg2 : MemLp (fun g : Fin 1→ℝ=>g 0) 2 (standardGaussian (Fin 1)) :=
    (memLp_id_gaussianReal 2).comp_measurePreserving
      (measurePreserving_eval (μ:=fun _:Fin 1=>gaussianReal 0 1) 0)
  have hg := hg2.integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [gaussian_sum_integral]
  simp_rw [addedMaximum_split]
  have he (p : (Fin d→ℝ)×(Fin 1→ℝ)) : (rowMaximum B p.1+c*p.2 0)^2=
      (rowMaximum B p.1)^2+2*c*(rowMaximum B p.1*p.2 0)+c^2*(p.2 0)^2 := by ring
  simp_rw [he]
  have hcross : Integrable (fun p : (Fin d→ℝ)×(Fin 1→ℝ)=>2*c*(rowMaximum B p.1*p.2 0))
      ((standardGaussian (Fin d)).prod (standardGaussian (Fin 1))) := (hi.mul_prod hg).const_mul _
  have hadd : Integrable (fun p : (Fin d→ℝ)×(Fin 1→ℝ)=>
      (rowMaximum B p.1)^2+2*c*(rowMaximum B p.1*p.2 0))
      ((standardGaussian (Fin d)).prod (standardGaussian (Fin 1))) := (hi2.comp_fst _).add hcross
  have hlast : Integrable (fun p : (Fin d→ℝ)×(Fin 1→ℝ)=>c^2*(p.2 0)^2)
      ((standardGaussian (Fin d)).prod (standardGaussian (Fin 1))) :=
    (hg2.integrable_sq.const_mul (c^2)).comp_snd _
  rw [integral_add hadd hlast,
    integral_add (hi2.comp_fst _) hcross,integral_fun_fst (fun x=>(rowMaximum B x)^2),integral_const_mul,
    integral_prod_mul (rowMaximum B) (fun g:Fin 1→ℝ=>g 0),NegativeVotingRegularMaximum.standardGaussian_coordinate_integral,
    integral_const_mul,integral_fun_snd (fun g:Fin 1→ℝ=>(g 0)^2),standard_coordinate_square]
  simp

end NegativeVotingEqualRowMaximumLaw
