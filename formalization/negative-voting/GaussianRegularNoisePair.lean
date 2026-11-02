import GaussianRegularScoreProjection
import GaussianRegularOUPotential
import GaussianRegularMassSeparation

/-! Quantitative regular negative-noise comparison on the actual score span.
The exponential weight excludes every unused ambient Gaussian coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingRegularNoisePair
open NegativeVoting NegativeVotingFan NegativeVotingBalancedReference
  NegativeVotingFacetConditionalPlane NegativeVotingRegularOU
  NegativeVotingCenteredParseval NegativeVotingRegularScoreProjection
  NegativeVotingRegularMassSeparation NegativeVotingRegularFacetGaussianLower
  NegativeVotingRegularMassSymmetry
variable {d m : ℕ} [NeZero m]

theorem noise_ratio_bounds (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) :
    0<r/Real.sqrt (1-r^2) ∧ r ≤ r/Real.sqrt (1-r^2) ∧
      (r/Real.sqrt (1-r^2))^2 ≤ 2*r^2 := by
  have hr1 : r<1 := by linarith
  have ha := negative_noise_scale_pos r hr hr1
  have hr2 : r^2 ≤ (1/2:ℝ)^2 :=
    (sq_le_sq₀ hr.le (by norm_num : (0:ℝ) ≤ 1/2)).mpr hrhalf
  have hsq : (Real.sqrt (1-r^2))^2=1-r^2 :=
    Real.sq_sqrt (by nlinarith)
  have haup : Real.sqrt (1-r^2) ≤ 1 := by nlinarith
  refine ⟨div_pos hr ha,?_,?_⟩
  · apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left haup hr.le]
  · rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hh : 0 ≤ 2*(Real.sqrt (1-r^2))^2-1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg r) hh]

theorem scoreOffsets_frame_smul (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (x : FSC.Coord d) (a : ℝ) :
    scoreOffsets B (a • frameOperator B x)=scoreOffsets B (a • x) := by
  funext i
  simp only [scoreOffsets,real_inner_smul_right,frame_preserves_scores B hG]

/-- The negative OU potential depends only on the actual score projection. -/
theorem gaussianNoiseOperator_negative_projected (B : Fin m → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (r : ℝ) (hr : 0<r) (hr1 : r<1) (x : FSC.Coord d) :
    gaussianNoiseOperator (-r) (regularAssignment (fun j => (B j).ofLp)) x.ofLp=
      mass B (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • frameOperator B x)) := by
  rw [gaussianNoiseOperator_negative_regularAssignment B r hr hr1 x,
    scoreOffsets_frame_smul B hG]

variable {n : ℕ}

/-- The explicit comparison weight contains only the regular score projection. -/
def projectedNoiseWeight (B : Fin (n+2) → FSC.Coord d) (r : ℝ) (x : FSC.Coord d) : ℝ :=
  referenceScale n*r*Real.exp (-1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
    r^2*‖frameOperator B x‖^2)

theorem projectedNoiseWeight_pos (B : Fin (n+2) → FSC.Coord d)
    (r : ℝ) (hr : 0<r) (x : FSC.Coord d) : 0<projectedNoiseWeight B r x := by
  unfold projectedNoiseWeight
  exact mul_pos (mul_pos (referenceScale_pos n) hr) (Real.exp_pos _)

/-- Actual regular negative-noise pair comparison. Larger original score has
smaller negative-noise potential. Unused ambient coordinates do not enter the
Gaussian exponential. -/
theorem regular_noise_pair_separation (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hgap : 0 ≤ inner ℝ (B i-B j) x) :
    referenceScale n*r*Real.exp (-1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
      r^2*‖frameOperator B x‖^2)*inner ℝ (B i-B j) x ≤
    gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp j-
      gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp i := by
  by_cases hij : i=j
  · subst j
    simp
  have hr1 : r<1 := by linarith
  have hG' : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  let τ := r/Real.sqrt (1-r^2)
  obtain ⟨hτ,hrτ,hτ2⟩ := noise_ratio_bounds r hr hrhalf
  change 0<τ at hτ
  change r ≤ τ at hrτ
  change τ^2 ≤ 2*r^2 at hτ2
  have hs : inner ℝ (B j-B i) (-τ • frameOperator B x)=
      τ*inner ℝ (B i-B j) x := by
    simp only [real_inner_smul_right,inner_sub_left,frame_preserves_scores B hG']
    ring
  have hsgap : 0 ≤ inner ℝ (B j-B i) (-τ • frameOperator B x) := by
    rw [hs]
    exact mul_nonneg hτ.le hgap
  have hm := regular_mass_separation hn hmean B hG (-τ • frameOperator B x)
    j i (Ne.symm hij) hsgap
  have hnorm : ‖-τ • frameOperator B x‖^2=τ^2*‖frameOperator B x‖^2 := by
    simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hτ,mul_pow]
  rw [hs,hnorm] at hm
  have hL : 0 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by
      have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    linarith
  have he : Real.exp (-1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
      r^2*‖frameOperator B x‖^2) ≤
      Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
        (τ^2*‖frameOperator B x‖^2)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hτ2
      (mul_nonneg (mul_nonneg facetGaussianConstant_pos.le hL)
        (sq_nonneg ‖frameOperator B x‖))
    nlinarith
  rw [gaussianNoiseOperator_negative_projected B hG' r hr hr1 x]
  change _ ≤ mass B (scoreOffsets B (-τ • frameOperator B x)) j-
    mass B (scoreOffsets B (-τ • frameOperator B x)) i
  calc
    _ ≤ referenceScale n*τ*
        Real.exp (-1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
          r^2*‖frameOperator B x‖^2)*inner ℝ (B i-B j) x := by
      apply mul_le_mul_of_nonneg_right _ hgap
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrτ (referenceScale_pos n).le) (Real.exp_pos _).le
    _ ≤ referenceScale n*τ*
        Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
          (τ^2*‖frameOperator B x‖^2))*inner ℝ (B i-B j) x := by
      apply mul_le_mul_of_nonneg_right _ hgap
      exact mul_le_mul_of_nonneg_left he (mul_nonneg (referenceScale_pos n).le hτ.le)
    _ = referenceScale n*
        Real.exp (-1-facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*
          (τ^2*‖frameOperator B x‖^2))*(τ*inner ℝ (B i-B j) x) := by ring
    _ ≤ _ := hm

/-- Summing the literal pair comparison against any fractional label weights
bounds their actual noise-potential excess by their actual score-routing loss. -/
theorem regular_noise_routing_lower (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) (x : FSC.Coord d)
    (p : Fin (n+2) → ℝ) (hp : SimplexWeights p) (t : Fin (n+2))
    (ht : ∀i,inner ℝ (B i) x ≤ inner ℝ (B t) x) :
    projectedNoiseWeight B r x*routingLoss p (fun i => inner ℝ (B i) x) t ≤
      (∑i,p i*gaussianNoiseOperator (-r)
        (regularAssignment (fun k => (B k).ofLp)) x.ofLp i)-
        gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp t := by
  have hi (i : Fin (n+2)) := mul_le_mul_of_nonneg_left
    (regular_noise_pair_separation hn hmean B hG r hr hrhalf x t i
      (by rw [inner_sub_left];exact sub_nonneg.mpr (ht i))) (hp.1 i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [inner_sub_left] at hh
  rw [routingLoss_eq_sum p _ t hp,Finset.mul_sum]
  have hleft : (∑i,p i*(referenceScale n*r*
      Real.exp (-1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*r^2*
        ‖frameOperator B x‖^2)*(inner ℝ (B t) x-inner ℝ (B i) x)))=
      ∑i,projectedNoiseWeight B r x*(p i*(inner ℝ (B t) x-inner ℝ (B i) x)) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold projectedNoiseWeight
    ring
  rw [hleft] at hh
  have hright (F : Fin (n+2) → ℝ) :
      (∑i,p i*(F i-F t))=(∑i,p i*F i)-F t := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hp.2,one_mul]
  rw [hright] at hh
  exact hh

/-- Actual reference-relative pointwise routing estimate for arbitrary
fractional label weights. The regular assignment itself, including its exact
tie splitting, occurs on the right-hand side. -/
theorem regular_noise_fractional_loss_lower (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) (x : FSC.Coord d)
    (p : Fin (n+2) → ℝ) (hp : SimplexWeights p) :
    projectedNoiseWeight B r x*
      (maxScore (fun i => inner ℝ (B i) x)-∑i,p i*inner ℝ (B i) x) ≤
    ∑i,(p i-regularAssignment (fun k => (B k).ofLp) x.ofLp i)*
      gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp i := by
  let s : Fin (n+2) → ℝ := fun i => inner ℝ (B i) x
  let t := chosenWinner s
  let P := gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp
  have ht : ∀i,s i ≤ s t := chosenWinner_max s
  have hmax : maxScore s=s t := finite_max_eq_chosenWinner s
  have hg : regularAssignment (fun k => (B k).ofLp) x.ofLp=maxWeights s := by
    funext i
    rw [regularAssignment_ofLp_eq_weights]
    unfold weights
    congr 1
    funext k
    simp only [scores,Pi.zero_apply,add_zero,s]
  have hP (i : Fin (n+2)) (hi : s i=s t) : P i=P t := by
    dsimp only [P]
    rw [gaussianNoiseOperator_negative_regularAssignment B r hr (by linarith) x]
    apply regular_mass_eq_of_offset_eq B (1/((n:ℝ)+2)) hG
    simp only [scoreOffsets,real_inner_smul_right]
    exact congrArg (fun z => -(r/Real.sqrt (1-r^2))*z) hi
  have hterm (i : Fin (n+2)) : maxWeights s i*P i=maxWeights s i*P t := by
    by_cases hi : s i=maxScore s
    · rw [hP i (hi.trans hmax)]
    · simp [maxWeights,maxIndicator,hi]
  have hsum : (∑i,maxWeights s i*P i)=P t := by
    simp_rw [hterm]
    rw [←Finset.sum_mul,(maxWeights_simplex s).2,one_mul]
  have hh := regular_noise_routing_lower hn hmean B hG r hr hrhalf x p hp t ht
  change projectedNoiseWeight B r x*(s t-∑i,p i*s i) ≤ (∑i,p i*P i)-P t at hh
  rw [←hmax] at hh
  change projectedNoiseWeight B r x*(maxScore s-∑i,p i*s i) ≤
    ∑i,(p i-regularAssignment (fun k => (B k).ofLp) x.ofLp i)*P i
  rw [hg]
  simp only [sub_mul,Finset.sum_sub_distrib,hsum]
  exact hh

end NegativeVotingRegularNoisePair
