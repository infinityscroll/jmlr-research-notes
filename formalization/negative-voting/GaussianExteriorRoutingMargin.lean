import GaussianRegularReferenceNormalization
import GaussianRegularNoiseRoutingIntegral
import GaussianFanMarginBounds

/-! Actual regular-fan margin probabilities and fractional routing.
The small-gap event is a union of true one-label exit events, with no
pairwise-union loss. The routing cost and mismatch are literal integrals. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingExteriorRoutingMargin
open NegativeVoting NegativeVotingFan NegativeVotingFanMarginBounds
  NegativeVotingNearRegularBalancedGeometry NegativeVotingRegularReferenceNormalization
  NegativeVotingRegularNoiseIntegral NegativeVotingCapTail NegativeVotingFacetDegree
variable {d m : ℕ} [NeZero m]

def smallGap (B : Fin m→FSC.Coord d) (a : ℝ) : Set (FSC.Coord d) :=
  ⋃ i,sourceExitSublevel B 0 i a

theorem smallGap_measurable (B : Fin m→FSC.Coord d) (a : ℝ) :
    MeasurableSet (smallGap B a) :=
  MeasurableSet.iUnion fun i=>sourceExitSublevel_measurable B 0 i a

def regularMarginConstant : ℝ :=
  max 1 (32*(shiftedMassConstant 1 1*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹))

theorem regularMarginConstant_ge_one : 1 ≤ regularMarginConstant := le_max_left _ _

/-- Uniform actual top-two margin bound for scaled regular rows. -/
theorem regular_smallGap_measure_le (hm : 2 ≤ m)
    (R : Fin m→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hscale : Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α)
    (a : ℝ) (ha : 0 ≤ a) :
    (stdGaussian (FSC.Coord d)).real (smallGap (α•R) a) ≤
      regularMarginConstant*(m:ℝ)*a := by
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hL : 1 ≤ 1+Real.log (m:ℝ) := by linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ m)]
  by_cases haSmall : a ≤ 1/(m:ℝ)
  · have hi (i:Fin m) : (stdGaussian (FSC.Coord d)).real
        (sourceExitSublevel (α•R) 0 i a) ≤ regularMarginConstant*a := by
      have hdiag (j:Fin m) : inner ℝ ((α•R) j) ((α•R) j)=α^2*(1-1/(m:ℝ)) := by
        simp only [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right,hG,ite_true]
        ring
      have hinv : 1/(m:ℝ) ≤ (1/2:ℝ) := (div_le_div_iff₀ hm0 (by norm_num)).mpr (by linarith)
      have hinv0 : 0 ≤ 1/(m:ℝ) := by positivity
      have hdl : α^2/2 ≤ inner ℝ ((α•R) i) ((α•R) i) := by
        rw [hdiag];nlinarith [sq_nonneg α,mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hinv)]
      have hdu : ∀j,inner ℝ ((α•R) j) ((α•R) j) ≤ 2*α^2 := by
        intro j;rw [hdiag];nlinarith [sq_nonneg α,mul_nonneg (sq_nonneg α) hinv0]
      have hcross : ∀j,j≠i→inner ℝ ((α•R) j) ((α•R) i) ≤ α^2/4 := by
        intro j hji
        simp only [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right,hG,ite_false,zero_sub,hji]
        nlinarith [sq_nonneg α,mul_nonneg (sq_nonneg α) hinv0]
      have hmass : mass (α•R) 0 i ≤ 1/(m:ℝ) := by
        rw [regular_scaled_mass_zero R hG α hα];simp only [one_div,le_refl]
      have hh := (one_label_margin_measures_le_of_initial_gram (α•R) 0 α α hα hα
        (regular_scaled_singular R hG α) i 1 (m:ℝ) (1+Real.log (m:ℝ)) 1
        (by norm_num) (by linarith) hL (by linarith) (by norm_num)
        (by simpa only [one_mul] using hscale) hdl hdu hcross hmass a ha haSmall).2
      exact hh.trans (mul_le_mul_of_nonneg_right (by
        simpa only [div_one,regularMarginConstant] using le_max_right 1
          (32*(shiftedMassConstant 1 1*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹))) ha)
    calc
      _ ≤ ∑i:Fin m,(stdGaussian (FSC.Coord d)).real (sourceExitSublevel (α•R) 0 i a) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑i:Fin m,regularMarginConstant*a := Finset.sum_le_sum fun i _=>hi i
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  · have hprob : (stdGaussian (FSC.Coord d)).real (smallGap (α•R) a) ≤ 1 := by
      simpa using measureReal_mono (μ:=stdGaussian (FSC.Coord d)) (subset_univ (smallGap (α•R) a))
    have hma : 1 ≤ (m:ℝ)*a := by
      have hh := (div_lt_iff₀ hm0).mp (lt_of_not_ge haSmall)
      nlinarith
    have hh := mul_le_mul_of_nonneg_right regularMarginConstant_ge_one (mul_nonneg hm0.le ha)
    exact hprob.trans (hma.trans (by simpa only [one_mul,mul_assoc] using hh))

/-- Exact total-variation distance from a pure winner. -/
theorem simplex_abs_distance_pure (p : Fin m→ℝ) (hp : SimplexWeights p) (i:Fin m) :
    (∑j,|p j-(if j=i then 1 else 0)|)=2*(1-p i) := by
  have ht (j:Fin m) : |p j-(if j=i then 1 else 0)|=
      p j+(if j=i then 1-2*p i else 0) := by
    by_cases hj:j=i
    · subst j
      simp only [ite_true,abs_of_nonpos (sub_nonpos.mpr (simplex_weight_le_one p hp i))]
      ring
    · simp only [ite_false,hj,sub_zero,add_zero,abs_of_nonneg (hp.1 j)]
  simp_rw [ht]
  rw [Finset.sum_add_distrib,hp.2]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

/-- Pointwise margin-to-mismatch estimate; ties belong to the small-gap event. -/
theorem fractional_mismatch_pointwise (B : Fin m→FSC.Coord d) (p:Fin m→ℝ)
    (hp:SimplexWeights p) (x:FSC.Coord d) (a:ℝ) (ha:0 < a)
    (hinj:Function.Injective (scores B 0 x)) :
    (∑i,|p i-weights B 0 x i|) ≤
      2*(smallGap B a).indicator (fun _=>1) x+
      2/a*(maxScore (scores B 0 x)-∑i,p i*scores B 0 x i) := by
  let i := chosenWinner (scores B 0 x)
  have hi (j:Fin m) (hji:j≠i) : scores B 0 x j < scores B 0 x i :=
    lt_of_le_of_ne (chosenWinner_max _ j) (fun he=>hji (hinj he))
  have hw (j:Fin m) : weights B 0 x j=if j=i then 1 else 0 :=
    maxWeights_eq_indicator_of_strict_max _ i hi j
  simp_rw [hw]
  rw [simplex_abs_distance_pure p hp i]
  have hmax : maxScore (scores B 0 x)=scores B 0 x i := finite_max_eq_chosenWinner _
  have hloss : 0 ≤ maxScore (scores B 0 x)-∑j,p j*scores B 0 x j := by
    rw [hmax];exact routingLoss_nonneg p _ i hp (chosenWinner_max _)
  by_cases hx:x∈smallGap B a
  · rw [Set.indicator_of_mem hx]
    have hz : 0 ≤ 2/a*(maxScore (scores B 0 x)-∑j,p j*scores B 0 x j) :=
      mul_nonneg (by positivity) hloss
    nlinarith [hp.1 i]
  · rw [Set.indicator_of_notMem hx, mul_zero, zero_add]
    have hmargin (j:Fin m) (hji:j≠i) : a ≤ scores B 0 x i-scores B 0 x j := by
      by_contra hh
      apply hx
      exact Set.mem_iUnion.mpr ⟨i,chosenWinner_max _,j,hji,(lt_of_not_ge hh).le⟩
    have hh := routingLoss_margin_bound p (scores B 0 x) i a hp hmargin
    change a*(1-p i) ≤ scores B 0 x i-∑j,p j*scores B 0 x j at hh
    rw [←hmax] at hh
    have h := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2/a by positivity)
    convert h using 1 <;> field_simp <;> ring


def fanScoreLoss (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ) (x:FSC.Coord d) : ℝ :=
  maxScore (scores B 0 x)-∑i,f x i*scores B 0 x i

def mismatch (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ) (x:FSC.Coord d) : ℝ :=
  ∑i,|f x i-weights B 0 x i|

theorem fanScoreLoss_nonneg (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ)
    (x:FSC.Coord d) (hp:SimplexWeights (f x)) : 0 ≤ fanScoreLoss B f x := by
  unfold fanScoreLoss
  rw [show maxScore (scores B 0 x)=scores B 0 x (chosenWinner (scores B 0 x)) from finite_max_eq_chosenWinner _]
  exact routingLoss_nonneg _ _ _ hp (chosenWinner_max _)

theorem fanScoreLoss_integrable (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (stdGaussian (FSC.Coord d)))
    (hp:∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    Integrable (fanScoreLoss B f) (stdGaussian (FSC.Coord d)) := by
  have hs (i:Fin m) : Integrable (fun x=>scores B 0 x i) (stdGaussian (FSC.Coord d)) := by
    convert (IsGaussian.integrable_dual (stdGaussian (FSC.Coord d)) (innerSL ℝ (B i))) using 1
    funext x
    simp only [scores,Pi.zero_apply,add_zero,innerSL_apply_apply]
  exact (integrable_finite_max _ _ Finset.univ Finset.univ_nonempty (fun i _=>hs i)).sub
    (integrable_score_mixture _ f _ hp hf hs)

theorem mismatch_integrable (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (stdGaussian (FSC.Coord d)))
    (hp:∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    Integrable (mismatch B f) (stdGaussian (FSC.Coord d)) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have hi : Integrable (fun x=>f x i) (stdGaussian (FSC.Coord d)) :=
    Integrable.of_mem_Icc (a:=0) (b:=1) (hf i) (hp.mono fun x hx=>
      ⟨hx.1 i,simplex_weight_le_one _ hx i⟩)
  convert (hi.sub (weights_integrable B 0 i)).norm using 1

theorem mismatch_integral_le_two (B : Fin m→FSC.Coord d) (f:FSC.Coord d→Fin m→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (stdGaussian (FSC.Coord d)))
    (hp:∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    (∫x,mismatch B f x ∂stdGaussian (FSC.Coord d)) ≤ 2 := by
  have hh := integral_mono_ae (mismatch_integrable B f hf hp) (integrable_const (2:ℝ)) (show
      ∀ᵐx ∂stdGaussian (FSC.Coord d),mismatch B f x ≤ 2 from ?_)
  · simpa using hh
  filter_upwards [hp] with x hx
  have hg := weights_simplex B 0 x
  calc
    _ ≤ ∑i,(f x i+weights B 0 x i) := Finset.sum_le_sum fun i _=>
      (abs_sub _ _).trans (by rw [abs_of_nonneg (hx.1 i),abs_of_nonneg (hg.1 i)])
    _ = 2 := by rw [Finset.sum_add_distrib,hx.2,hg.2];norm_num

/-- Integrated margin splitting for arbitrary completed-measurable fractional
assignments. All integrability and tie-nullness facts are derived. -/
theorem mismatch_integral_margin_bound (B : Fin m→FSC.Coord d) (hB:Function.Injective B)
    (f:FSC.Coord d→Fin m→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (stdGaussian (FSC.Coord d)))
    (hp:∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) (a:ℝ) (ha:0 < a) :
    (∫x,mismatch B f x ∂stdGaussian (FSC.Coord d)) ≤
      2*(stdGaussian (FSC.Coord d)).real (smallGap B a)+
      2/a*(∫x,fanScoreLoss B f x ∂stdGaussian (FSC.Coord d)) := by
  have hs := smallGap_measurable B a
  have hi := (integrable_const (μ:=stdGaussian (FSC.Coord d)) (1:ℝ)).indicator hs
  have hL := fanScoreLoss_integrable B f hf hp
  have hh := integral_mono_ae (mismatch_integrable B f hf hp)
    ((hi.const_mul 2).add (hL.const_mul (2/a))) (show
      ∀ᵐx ∂stdGaussian (FSC.Coord d),mismatch B f x ≤
        2*(smallGap B a).indicator (fun _=>1) x+2/a*fanScoreLoss B f x from ?_)
  · simp only [Pi.add_apply] at hh
    rw [integral_add (hi.const_mul 2) (hL.const_mul (2/a)),integral_const_mul,
      integral_const_mul,integral_indicator_const (1:ℝ) hs] at hh
    simp only [smul_eq_mul,mul_one] at hh
    exact hh
  filter_upwards [hp,ae_scores_injective B hB 0] with x hx hinj
  exact fractional_mismatch_pointwise B (f x) hx x a ha hinj

/-- The actual regular reference gives the expected square-root routing law. -/
theorem regular_mismatch_integral_sqrt (hm:2 ≤ m) (R:Fin m→FSC.Coord d)
    (hG:∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0 < α) (hscale:Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α)
    (f:FSC.Coord d→Fin m→ℝ)
    (hf:∀i,AEMeasurable (fun x=>f x i) (stdGaussian (FSC.Coord d)))
    (hp:∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    (∫x,mismatch (α•R) f x ∂stdGaussian (FSC.Coord d)) ≤
      2*(regularMarginConstant+1)*Real.sqrt ((m:ℝ)*
        (∫x,fanScoreLoss (α•R) f x ∂stdGaussian (FSC.Coord d))) := by
  let L := ∫x,fanScoreLoss (α•R) f x ∂stdGaussian (FSC.Coord d)
  have hL : 0 ≤ L := integral_nonneg_of_ae (hp.mono fun x hx=>fanScoreLoss_nonneg _ f x hx)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hB : Function.Injective (α•R) := by
    intro i j hij
    by_contra hne
    exact centered_singular_rows_ne _ α hα (regular_scaled_singular R hG α) i j hne hij
  have hb (a:ℝ) (ha:0 < a) : (∫x,mismatch (α•R) f x ∂stdGaussian (FSC.Coord d)) ≤
      2*regularMarginConstant*(m:ℝ)*a+2/a*L := by
    have hh := mismatch_integral_margin_bound (α•R) hB f hf hp a ha
    exact hh.trans (by nlinarith [regular_smallGap_measure_le hm R hG α hα hscale a ha.le])
  by_cases hzero:L=0
  · have hmismatch : (∫x,mismatch (α•R) f x ∂stdGaussian (FSC.Coord d)) ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hK : 0 < regularMarginConstant := lt_of_lt_of_le (by norm_num) regularMarginConstant_ge_one
      have ha : 0 < ε/(2*regularMarginConstant*(m:ℝ)) := by positivity
      have hh := hb _ ha
      rw [hzero,mul_zero,add_zero] at hh
      have he : 2*regularMarginConstant*(m:ℝ)*(ε/(2*regularMarginConstant*(m:ℝ)))=ε := by field_simp
      simpa only [he,zero_add] using hh
    simpa only [show (∫x,fanScoreLoss (α•R) f x ∂stdGaussian (FSC.Coord d))=0 from hzero,
      mul_zero,Real.sqrt_zero] using hmismatch
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    let a := Real.sqrt (L/(m:ℝ))
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a^2=L/(m:ℝ) := Real.sq_sqrt (by positivity)
    have heL : L=(m:ℝ)*a^2 := by
      have hh := (eq_div_iff (ne_of_gt hm0)).mp ha2
      nlinarith
    have hsqrt : Real.sqrt ((m:ℝ)*L)=(m:ℝ)*a := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      rw [heL];ring
    have hh := hb a ha
    change _ ≤ 2*(regularMarginConstant+1)*Real.sqrt ((m:ℝ)*L)
    rw [hsqrt]
    refine hh.trans_eq ?_
    rw [heL]
    field_simp

end NegativeVotingExteriorRoutingMargin
