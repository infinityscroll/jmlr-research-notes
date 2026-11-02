import GaussianRegularHighTailCrossAggregation
import GaussianRegularHighTailInputs
import GaussianPathSmoothedComparison

/-! Actual regular high-tail sources in the winning-facet cross estimate.
The normal symmetry and rare-label norm are discharged from the reference
regular cells. The remaining bounds concern only current geometry and path
coefficient energies. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NegativeVotingRegularHighTailCrossPath
open NegativeVotingRegularHighTailCrossAggregation NegativeVotingRegularHighTailInputs
  NegativeVotingRegularCellReflection NegativeVotingRegularTransportProducts
  NegativeVotingRegularTransportBound NegativeVotingFan NegativeVotingFanJacobian
  NegativeVotingDisintegration NegativeVotingWeightedFacet NegativeVotingFanHessian
  NegativeVotingActualFacetOUTrace NegativeVotingNearRegularBalancedGeometry
  NegativeVotingPathSmoothedComparison NegativeVotingGlobalTensorTransport
  NegativeVotingProjection NegativeVotingRareLabelHighChaos NegativeVotingCellOUContinuity
  NegativeVotingPolynomialFacetLogBound NegativeVotingHypercontractivity
  NegativeVotingQuadraticMomentPadding NegativeVotingCapTail NegativeVotingFacetDegree
variable {d m : ℕ} [NeZero m]

theorem pairNormal_pos_scale (R : Fin m→FSC.Coord d) (α : ℝ) (hα : 0 < α) (i j : Fin m) :
    pairNormal (α • R) i j=pairNormal R i j := by
  simp only [pairNormal,Pi.smul_apply,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hα,
    mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ hα.ne',mul_one]

theorem regular_scaled_edge_lower (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (i j : Fin m) (hij : i≠j) : α ≤ ‖(α • R) i-(α • R) j‖ := by
  have hsq : ‖R i-R j‖^2=2 := by
    rw [norm_sub_sq_real,←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,
      hG i i,hG j j,hG i j]
    simp only [ite_true,ite_false,hij,↓reduceIte]
    ring
  have hn : 1 ≤ ‖R i-R j‖ := by nlinarith [norm_nonneg (R i-R j)]
  simp only [Pi.smul_apply,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hα]
  nlinarith

/-- A uniform coefficient for all current offsets with a logarithmic bound. -/
theorem quotientNormFactor_log_le (τ q A Ac L : ℝ)
    (hτ : 0 < τ) (hq : 2 ≤ q) (hL : 0 ≤ L)
    (ht : τ^2*L ≤ 1) (hA : A^2 ≤ Ac^2*L) :
    quotientNormFactor τ q A ≤ 8*τ*Real.exp (Ac^2/2) := by
  have hs : Real.sqrt (8*τ^2) ≤ 4*τ := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg τ]
  have he : Real.exp (τ^2*A^2/2) ≤ Real.exp (Ac^2/2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hA (sq_nonneg τ)
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg Ac)
    nlinarith
  have hq0 : 0 < q := by linarith
  have hqinv : 1/q ≤ 1 := (div_le_one hq0).mpr (by linarith)
  have hpow : (2:ℝ)^(1/q) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hqinv
  unfold quotientNormFactor
  have hh := mul_le_mul (mul_le_mul hs he (Real.exp_pos _).le (by positivity)) hpow
    (Real.rpow_nonneg (by norm_num) _) (by positivity : 0≤4*τ*Real.exp (Ac^2/2))
  convert hh using 1 <;> ring

theorem probability_log_le_of_power (p m q : ℝ) (hm : 1 ≤ m)
    (hp : m^(-4096:ℝ) ≤ p) (hq : 4096*Real.log m ≤ q) : -Real.log p ≤ q := by
  have hm0 : 0 < m := by linarith
  have hpp : 0 < m^(-4096:ℝ) := Real.rpow_pos_of_pos hm0 _
  have hh := Real.log_le_log hpp hp
  rw [Real.log_rpow hm0] at hh
  linarith

/-- The ordered cross estimate specialized to genuine regular winning-cell
high-mode potentials. No symmetry or source-norm premise remains. -/
theorem regular_ordered_cross_abs_le (B R Z : Fin m→FSC.Coord d) (h k : Fin m→ℝ)
    (hB : Function.Injective B)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim : 2 ≤ Module.finrank ℝ (FSC.Coord d))
    (α τ σ q Ac C J degree : ℝ) (hα : 0 < α) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hscale : τ^2*Real.log (m:ℝ) ≤ C) (hJ : 0 ≤ J) (hdegree0 : 0 ≤ degree)
    (hdegree : ∀ i,∑ j,facetWeight B h i j ≤ degree)
    (hprob : ∀ i j,i≠j→(m:ℝ)^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal)
    (hlog : ∀ i j,i≠j→-Real.log
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal ≤ q)
    (hA : ∀ i j,i≠j→|pairOffset B h i j| ≤ Ac*Real.sqrt (1+Real.log (m:ℝ)))
    (hJnorm : ∀ i j,i≠j→quotientNormFactor τ q (pairOffset B h i j) ≤ J)
    (e v : FSC.Coord d) (b c : ℝ) :
    |∑ i,∑ j,surfaceIntegral B h i j (fun x=>linearScore (Z i-Z j) (k i-k j) x*
      (gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight R 0 i)) x.ofLp-
        gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight R 0 j)) x.ofLp))| ≤
      32*Real.exp 1*degree*Real.sqrt (quarticLogConstant Ac*(1+Real.log (m:ℝ))^4)*
        (J*(2*σ^3*(Real.exp C/(m:ℝ)))/α)*
        Real.sqrt (rowScoreEnergy (fun i=>B i-α • R i) h e b)*
          Real.sqrt (rowScoreEnergy Z k v c) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  have hRi : Function.Injective (α • R) := by
    intro i j he
    by_contra hij
    have he0 : ‖(α • R) i-(α • R) j‖=0 := by rw [he,sub_self,norm_zero]
    have hl := regular_scaled_edge_lower R hG α hα i j hij
    rw [he0] at hl
    exact (not_le_of_gt hα) hl
  have hh := ordered_cross_abs_le B (α • R) Z h k hB hRi hdim τ q Ac (m:ℝ)
    (2*σ^3*(Real.exp C/(m:ℝ))) J α degree hτ hq hqt hm (by positivity) hJ hα hdegree0
    hdegree (regular_scaled_edge_lower R hG α hα) hprob hlog hA hJnorm
    (regularGapInput R τ σ)
    (fun i j=>(regularGapInput_memLp_norm R hG τ σ C hτ hτ1 hσ hσ1 hscale i j).1)
    (fun i j=>(regularGapInput_memLp_norm R hG τ σ C hτ hτ1 hσ hσ1 hscale i j).2.1)
    (fun i j _=>(regularGapInput_memLp_norm R hG τ σ C hτ hτ1 hσ hσ1 hscale i j).2.2)
    (by
      intro i j hij x
      rw [pairNormal_pos_scale R α hα]
      have ho := regularGapInput_average_odd R hG τ σ hτ hτ1 hσ hσ1 i j hij x
      rw [labelReflection_normal_formula R (1/(m:ℝ)) hG i j hij] at ho
      exact ho) e v b c
  simpa only [regularGapInput_average R hG τ σ hτ hτ1 hσ hσ1,Pi.smul_apply] using hh

def regularTailPotential (R : Fin m→FSC.Coord d) (τ σ : ℝ)
    (i : Fin m) (x : FSC.Coord d) : ℝ :=
  gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight R 0 i)) x.ofLp

theorem regularTailPotential_regular (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1) (i : Fin m) :
    Continuous (regularTailPotential R τ σ i) ∧
      ∃ C:ℝ,0 ≤ C ∧ ∀ x,|regularTailPotential R τ σ i x| ≤ C*(1+‖x‖^2) := by
  have hlower : CenteredSingularLowerBound R 1 := by
    simpa only [one_smul] using regular_scaled_singular R hG 1
  have hρ : |-(τ^2*σ)| < 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    nlinarith [mul_pos (sq_pos_of_pos hτ) hσ]
  have hc := gaussianAverage_cellWeight_continuous R 1 (by norm_num) hlower 0 i _ hρ
  exact highModes_continuous_quadratic_of_average (-(τ^2*σ)) hρ.le 3 (by rfl)
    (cellWeight R 0 i) (cellWeight_measurable R 0 i) hc 1 (by norm_num) (cellWeight_abs_le R 0 i)

theorem quadratic_growth_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (F : FSC.Coord d→ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x,|F x| ≤ C*(1+‖x‖^2)) : MemLp F 2 μ := by
  have hh := (IsGaussian.memLp_id μ 4 (by norm_num)).norm
  letI : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hn : MemLp (fun x:FSC.Coord d=>‖x‖^2) 2 μ := by
    simpa only [pow_two,Pi.mul_def,id_eq] using hh.mul hh
  have hb := ((memLp_const (1:ℝ)).add hn).const_mul C
  apply hb.mono hFc.measurable.aestronglyMeasurable
  filter_upwards with x
  change |F x| ≤ |C*(1+‖x‖^2)|
  rw [abs_of_nonneg (by positivity : 0 ≤ C*(1+‖x‖^2))]
  exact hF x

/-- Opposite current facets are paired before applying a quantitative bound. -/
theorem testedFanDerivative_half_gap (B : Fin m→FSC.Coord d) (h : Fin m→ℝ)
    (ell0 : ℝ) (hell0 : 0 < ell0) (hlower : CenteredSingularLowerBound B ell0)
    (F : Fin m→FSC.Coord d→ℝ) (hFc : ∀ i,Continuous (F i))
    (C : Fin m→ℝ) (hC : ∀ i,0 ≤ C i) (hF : ∀ i x,|F i x| ≤ C i*(1+‖x‖^2))
    (δ : NegativeVotingFanScore.Parameters d (Fin m)) :
    testedFanDerivative B h F δ=(1/2:ℝ)*∑ i,∑ j,surfaceIntegral B h i j
      (fun x=>linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x*(F i x-F j x)) := by
  rw [testedFanDerivative_apply B h ell0 hell0 hlower F hFc C hC hF δ]
  have hfull : (∑ i,∑ j∈Finset.univ.erase i,surfaceIntegral B h i j
      (fun x=>F i x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)))=
      ∑ i,∑ j,surfaceIntegral B h i j
        (fun x=>F i x*linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),surfaceIntegral_diagonal,add_zero]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext x
    simp only [affineScore,linearScore,inner_sub_left]
    ring
  rw [hfull]
  have hg : ∀ i j x,linearScore (δ.1 j-δ.1 i) (δ.2 j-δ.2 i) x=
      -linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x := by
    intro i j x
    simp only [linearScore,inner_sub_left]
    ring
  have hI (i j k : Fin m) : Integrable (fun x=>F k x*linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j) x)
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
    let μ := FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)
    letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
    exact (quadratic_growth_memLp_two μ (F k) (hFc k) (C k) (hC k) (hF k)).integrable_mul
      (linearScore_memLp μ _ _ 2 (by norm_num))
  rw [surface_sum_label_gap B h F (fun i j=>linearScore (δ.1 i-δ.1 j) (δ.2 i-δ.2 j)) hg hI]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext x
  ring

/-- Finite actual C1 path comparison against the fixed regular high-tail
potential. Its assumptions bound only current fan geometry and coefficient
energies; the cross-term derivative estimate is proved inside. -/
theorem regular_path_cross_abs_le
    (p p' : ℝ→NegativeVotingFanScore.Parameters d (Fin m))
    (hp : ∀ t∈Icc (0:ℝ) 1,HasDerivAt p (p' t) t)
    (ell0 : ℝ) (hell0 : 0 < ell0)
    (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (p t).1 ell0)
    (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim : 2 ≤ Module.finrank ℝ (FSC.Coord d))
    (α τ σ q Ac C J degree HE HD : ℝ) (hα : 0 < α) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (hscale : τ^2*Real.log (m:ℝ) ≤ C) (hJ : 0 ≤ J) (hdegree0 : 0 ≤ degree)
    (hHE : 0 ≤ HE) (hHD : 0 ≤ HD)
    (hdegree : ∀ t∈Icc (0:ℝ) 1,∀ i,∑ j,facetWeight (p t).1 (p t).2 i j ≤ degree)
    (hprob : ∀ t∈Icc (0:ℝ) 1,∀ i j,i≠j→(m:ℝ)^(-4096:ℝ) ≤
      (stdGaussian (tangentSpace (pairNormal (p t).1 i j)) (intrinsicFacet (p t).1 (p t).2 i j)).toReal)
    (hlog : ∀ t∈Icc (0:ℝ) 1,∀ i j,i≠j→-Real.log
      (stdGaussian (tangentSpace (pairNormal (p t).1 i j)) (intrinsicFacet (p t).1 (p t).2 i j)).toReal ≤ q)
    (hA : ∀ t∈Icc (0:ℝ) 1,∀ i j,i≠j→|pairOffset (p t).1 (p t).2 i j| ≤
      Ac*Real.sqrt (1+Real.log (m:ℝ)))
    (hJnorm : ∀ t∈Icc (0:ℝ) 1,∀ i j,i≠j→quotientNormFactor τ q (pairOffset (p t).1 (p t).2 i j) ≤ J)
    (e v : ℝ→FSC.Coord d) (b c : ℝ→ℝ)
    (herror : ∀ t∈Ico (0:ℝ) 1,rowScoreEnergy (fun i=>(p t).1 i-α • R i) (p t).2 (e t) (b t) ≤ HE)
    (hspeed : ∀ t∈Ico (0:ℝ) 1,rowScoreEnergy (p' t).1 (p' t).2 (v t) (c t) ≤ HD) :
    |testedFan (p 1) (regularTailPotential R τ σ)-testedFan (p 0) (regularTailPotential R τ σ)| ≤
      32*Real.exp 1*degree*Real.sqrt (quarticLogConstant Ac*(1+Real.log (m:ℝ))^4)*
        (J*(2*σ^3*(Real.exp C/(m:ℝ)))/α)*Real.sqrt HE*Real.sqrt HD := by
  let F := regularTailPotential R τ σ
  have hFc (i : Fin m) : Continuous (F i) := (regularTailPotential_regular R hG τ σ hτ hτ1 hσ hσ1 i).1
  choose Ctest hCtest hFtest using fun i=>(regularTailPotential_regular R hG τ σ hτ hτ1 hσ hσ1 i).2
  let K := 32*Real.exp 1*degree*Real.sqrt (quarticLogConstant Ac*(1+Real.log (m:ℝ))^4)*
    (J*(2*σ^3*(Real.exp C/(m:ℝ)))/α)
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hbound : ∀ t∈Ico (0:ℝ) 1,‖testedFanDerivative (p t).1 (p t).2 F (p' t)‖ ≤
      K*Real.sqrt HE*Real.sqrt HD := by
    intro t ht
    have htc : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hinj : Function.Injective (p t).1 := by
      intro i j hh
      by_contra hij
      exact centered_singular_rows_ne (p t).1 ell0 hell0 (hlower t htc) i j hij hh
    have hh := regular_ordered_cross_abs_le (p t).1 R (p' t).1 (p t).2 (p' t).2
      hinj hG hdim α τ σ q Ac C J degree hα hτ hτ1 hσ hσ1 hq hqt hscale hJ hdegree0
      (hdegree t htc) (hprob t htc) (hlog t htc) (hA t htc) (hJnorm t htc) (e t) (v t) (b t) (c t)
    change |∑ i,∑ j,surfaceIntegral (p t).1 (p t).2 i j
      (fun x=>linearScore ((p' t).1 i-(p' t).1 j) ((p' t).2 i-(p' t).2 j) x*(F i x-F j x))| ≤
        K*Real.sqrt (rowScoreEnergy (fun i=>(p t).1 i-α • R i) (p t).2 (e t) (b t))*
          Real.sqrt (rowScoreEnergy (p' t).1 (p' t).2 (v t) (c t)) at hh
    rw [testedFanDerivative_half_gap (p t).1 (p t).2 ell0 hell0 (hlower t htc) F hFc Ctest hCtest hFtest,
      Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    apply (show (1/2:ℝ)*|∑ i,∑ j,surfaceIntegral (p t).1 (p t).2 i j
      (fun x=>linearScore ((p' t).1 i-(p' t).1 j) ((p' t).2 i-(p' t).2 j) x*(F i x-F j x))| ≤
      |∑ i,∑ j,surfaceIntegral (p t).1 (p t).2 i j
      (fun x=>linearScore ((p' t).1 i-(p' t).1 j) ((p' t).2 i-(p' t).2 j) x*(F i x-F j x))| by
        nlinarith [abs_nonneg (∑ i,∑ j,surfaceIntegral (p t).1 (p t).2 i j
          (fun x=>linearScore ((p' t).1 i-(p' t).1 j) ((p' t).2 i-(p' t).2 j) x*(F i x-F j x)))]).trans
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (herror t ht)) hK)
      (Real.sqrt_le_sqrt (hspeed t ht)) (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _)))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hasDerivAt_testedFan_path p (p' t) t (hp t ht) ell0 hell0 (hlower t ht)
      F hFc Ctest hCtest hFtest).hasDerivWithinAt) hbound
  simpa only [Real.norm_eq_abs] using hm

end NegativeVotingRegularHighTailCrossPath
