import GaussianFanMarginBounds
import GaussianSwitchingMarginSeparation
import GaussianSwitchingOrderedIntegral

/-!
# Actual moderate-amplitude Gaussian switching cap

The closed-cell cap agrees with the unique-winner cap almost everywhere.
Separate its source and target maximum margins before integration, restrict to
the actual old cell or its complement, and apply the finite-label Lq estimate.
No ordered-pair multiplicity or L32 premise is introduced.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingSwitchingModerateIntegral
open NegativeVotingFan NegativeVotingFanMarginBounds NegativeVotingSwitchingOrdered
  NegativeVotingSwitchingSeparation NegativeVotingSwitchingLabelSum NegativeVotingCapTail
  NegativeVotingWeightedFacet NegativeVotingFacetDegree
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

local instance otherLabelsNonempty (i : V) : Nonempty {j : V // j ≠ i} :=
  let ⟨j,hj⟩ := exists_ne i
  ⟨⟨j,hj⟩⟩

/-- The actual source margin, clipped only away from its old cell. -/
def sourceCost (B : V → FSC.Coord d) (h : V → ℝ) (i : V) (x : FSC.Coord d) : ℝ :=
  max (sourceExitMargin B h i x) 0

def sourceReward (B : V → FSC.Coord d) (h : V → ℝ) (v : FSC.Coord d → V → ℝ)
    (θ : ℝ) (i : V) (x : FSC.Coord d) : ℝ :=
  max (2*θ*v x i-sourceCost B h i x) 0

def targetReward (B : V → FSC.Coord d) (h : V → ℝ) (v : FSC.Coord d → V → ℝ)
    (θ : ℝ) (i : V) (x : FSC.Coord d) : ℝ :=
  max (2*θ*v x i-targetEntryMargin B h i x) 0

def separatedMarginMajorant (B : V → FSC.Coord d) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ : ℝ) (x : FSC.Coord d) : ℝ :=
  ((∑ i, (winningCell B h i).indicator (sourceReward B h v θ i) x) +
    ∑ i, (winningCell B h i)ᶜ.indicator (targetReward B h v θ i) x)/2

theorem sourceCost_measurable (B : V → FSC.Coord d) (h : V → ℝ) (i : V) :
    Measurable (sourceCost B h i) :=
  (sourceExitMargin_measurable B h i).max measurable_const

theorem sourceCost_nonneg (B : V → FSC.Coord d) (h : V → ℝ) (i : V)
    (x : FSC.Coord d) : 0 ≤ sourceCost B h i x := le_max_right _ _

theorem sourceCost_eq_on_cell (B : V → FSC.Coord d) (h : V → ℝ) (i : V)
    (x : FSC.Coord d) (hx : x ∈ winningCell B h i) :
    sourceCost B h i x = sourceExitMargin B h i x :=
  max_eq_left (sourceExitMargin_nonneg_on_cell B h i x hx)

theorem sourceCost_le_gap_on_cell (B : V → FSC.Coord d) (h : V → ℝ) (i j : V)
    (x : FSC.Coord d) (hx : x ∈ winningCell B h i) (hji : j ≠ i) :
    sourceCost B h i x ≤ scores B h x i-scores B h x j := by
  rw [sourceCost_eq_on_cell B h i x hx]
  unfold sourceExitMargin
  have hh := Finset.le_sup' (f := fun j : {j : V // j ≠ i} => scores B h x j.1)
    (Finset.mem_univ (⟨j,hji⟩ : {j : V // j ≠ i}))
  change scores B h x j ≤ NegativeVoting.maxScore _ at hh
  linarith

/-- The full closed-cell sum loses all tie multiplicity on the actual
Gaussian full-measure set of distinct scores. -/
theorem closedCellCap_le_separated_of_injective (B : V → FSC.Coord d) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ : ℝ) (x : FSC.Coord d)
    (hinj : Function.Injective (scores B h x)) :
    closedCellCap B h v θ x ≤ separatedMarginMajorant B h v θ x := by
  let i := NegativeVoting.chosenWinner (scores B h x)
  have hi (j : V) : scores B h x j ≤ scores B h x i :=
    NegativeVoting.chosenWinner_max _ j
  have hcell : x ∈ winningCell B h i := hi
  have hiff (j : V) : x ∈ winningCell B h j ↔ j=i := by
    constructor
    · intro hj
      exact hinj (le_antisymm (hi j) (hj i))
    · rintro rfl; exact hcell
  have hclosed : closedCellCap B h v θ x = switchingCap (scores B h x) (v x) θ i := by
    unfold closedCellCap
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hcell _
    · intro j _ hji
      exact Set.indicator_of_notMem (fun hx => hji ((hiff j).mp hx)) _
    · simp
  have hsource : (∑ j, (winningCell B h j).indicator (sourceReward B h v θ j) x) =
      sourceReward B h v θ i x := by
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hcell _
    · intro j _ hji
      exact Set.indicator_of_notMem (fun hx => hji ((hiff j).mp hx)) _
    · simp
  have htarget : (∑ j, (winningCell B h j)ᶜ.indicator (targetReward B h v θ j) x) =
      ∑ j ∈ Finset.univ.erase i, targetReward B h v θ j x := by
    have hz : (winningCell B h i)ᶜ.indicator (targetReward B h v θ i) x = 0 :=
      Set.indicator_of_notMem (by simpa using hcell) _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hz,add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    apply Set.indicator_of_mem
    exact fun hx => (Finset.ne_of_mem_erase hj) ((hiff j).mp hx)
  rw [hclosed]
  unfold separatedMarginMajorant
  rw [hsource,htarget]
  exact switchingCap_le_max_margin_terms (scores B h x) (v x) θ (sourceCost B h i x) i
    hi (fun j hj => sourceCost_le_gap_on_cell B h i j x hcell hj)

theorem closedCellCap_le_separated_ae (B : V → FSC.Coord d) (hB : Function.Injective B)
    (h : V → ℝ) (v : FSC.Coord d → V → ℝ) (θ : ℝ) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), closedCellCap B h v θ x ≤ separatedMarginMajorant B h v θ x := by
  filter_upwards [ae_scores_injective B hB h] with x hx
  exact closedCellCap_le_separated_of_injective B h v θ x hx

/-- Elementary domination used to integrate the actual rewards. -/
theorem integrable_nonnegative_cost_reward {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (u c : X → ℝ) (hu : Integrable u μ)
    (hcM : Measurable c) (hc : ∀ x,0 ≤ c x) :
    Integrable (fun x => max (u x-c x) 0) μ := by
  apply hu.norm.mono'
    ((hu.aestronglyMeasurable.sub hcM.aestronglyMeasurable).sup aestronglyMeasurable_const)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
  change max (u x-c x) 0 ≤ |u x|
  exact max_le (by linarith [le_abs_self (u x),hc x]) (abs_nonneg _)

theorem sourceReward_integrable (B : V → FSC.Coord d) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ : ℝ) (i : V)
    (hv : Integrable (fun x => v x i) (stdGaussian (FSC.Coord d))) :
    Integrable (sourceReward B h v θ i) (stdGaussian (FSC.Coord d)) :=
  integrable_nonnegative_cost_reward _ _ (hv.const_mul (2*θ))
    (sourceCost_measurable B h i) (sourceCost_nonneg B h i)

theorem targetReward_integrable (B : V → FSC.Coord d) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ : ℝ) (i : V)
    (hv : Integrable (fun x => v x i) (stdGaussian (FSC.Coord d))) :
    Integrable (targetReward B h v θ i) (stdGaussian (FSC.Coord d)) :=
  integrable_nonnegative_cost_reward _ _ (hv.const_mul (2*θ))
    (targetEntryMargin_measurable B h i) (targetEntryMargin_nonneg B h i)

theorem separatedMarginMajorant_integrable (B : V → FSC.Coord d) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ : ℝ)
    (hv : ∀ i, Integrable (fun x => v x i) (stdGaussian (FSC.Coord d))) :
    Integrable (separatedMarginMajorant B h v θ) (stdGaussian (FSC.Coord d)) := by
  exact ((integrable_finsetSum Finset.univ (fun i _ =>
    (sourceReward_integrable B h v θ i (hv i)).indicator (winningCell_measurable B h i))).add
    (integrable_finsetSum Finset.univ (fun i _ =>
    (targetReward_integrable B h v θ i (hv i)).indicator (winningCell_measurable B h i).compl))).div_const 2

theorem integral_closedCellCap_le_separated (B : V → FSC.Coord d) (hB : Function.Injective B)
    (h : V → ℝ) (v : FSC.Coord d → V → ℝ) (θ : ℝ)
    (hvM : ∀ i,Measurable (fun x => v x i))
    (hv : ∀ i,Integrable (fun x => v x i) (stdGaussian (FSC.Coord d))) :
    (∫ x, closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤
      ((∑ i, ∫ x in winningCell B h i, sourceReward B h v θ i x ∂stdGaussian (FSC.Coord d)) +
        ∑ i, ∫ x in (winningCell B h i)ᶜ, targetReward B h v θ i x ∂stdGaussian (FSC.Coord d))/2 := by
  have hmaj := separatedMarginMajorant_integrable B h v θ hv
  have hle := closedCellCap_le_separated_ae B hB h v θ
  have hcap : Integrable (closedCellCap B h v θ) (stdGaussian (FSC.Coord d)) := by
    apply hmaj.mono' (measurable_closedCellCap B h v θ hvM).aestronglyMeasurable
    filter_upwards [hle] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (closedCellCap_nonneg B h v θ x)]
    exact hx
  have hh := integral_mono_ae hcap hmaj hle
  unfold separatedMarginMajorant at hh
  rw [integral_div,integral_add,
    integral_finsetSum _ (fun i _ => (sourceReward_integrable B h v θ i (hv i)).indicator
      (winningCell_measurable B h i)),
    integral_finsetSum _ (fun i _ => (targetReward_integrable B h v θ i (hv i)).indicator
      (winningCell_measurable B h i).compl)] at hh
  · simpa only [integral_indicator (winningCell_measurable B h _),
      integral_indicator (winningCell_measurable B h _).compl] using hh
  · exact integrable_finsetSum _ (fun i _ =>
      (sourceReward_integrable B h v θ i (hv i)).indicator (winningCell_measurable B h i))
  · exact integrable_finsetSum _ (fun i _ =>
      (targetReward_integrable B h v θ i (hv i)).indicator (winningCell_measurable B h i).compl)

/-- Restriction and multiplication preserve the honest ambient norm bound. -/
theorem scaled_restrict_norm_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : X → ℝ) (q θ W : ℝ) (hθ : 0 ≤ θ)
    (hnorm : eLpNorm v (ENNReal.ofReal q) μ ≤ ENNReal.ofReal W) (S : Set X) :
    eLpNorm (fun x => 2*θ*v x) (ENNReal.ofReal q) (μ.restrict S) ≤ ENNReal.ofReal (2*θ*W) := by
  have hc : 0 ≤ 2*θ := by positivity
  change eLpNorm ((2*θ) • v) (ENNReal.ofReal q) (μ.restrict S) ≤ _
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_nonneg hc,ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl ((eLpNorm_mono_measure v
    (Measure.restrict_le_self (μ:=μ) (s:=S))).trans hnorm)

/-- Actual cap integration from the two true maximum-margin sublevel laws.
The Lq hypotheses are ambient, and the only alphabet factor is m^(1/(q+1)). -/
theorem integral_closedCellCap_le_lq_of_sublevels
    (B : V → FSC.Coord d) (hB : Function.Injective B) (h : V → ℝ)
    (v : FSC.Coord d → V → ℝ) (θ q aStar C R : ℝ) (W : V → ℝ)
    (hθ : 0 ≤ θ) (hq : 2 ≤ q) (haStar : 0 < aStar) (hC : 1 ≤ C)
    (hW : ∀ i,0 ≤ W i) (hR : 0 ≤ R) (henergy : (∑ i,(W i)^2) ≤ R^2)
    (hvM : ∀ i,Measurable (fun x => v x i))
    (hv : ∀ i,MemLp (fun x => v x i) (ENNReal.ofReal q) (stdGaussian (FSC.Coord d)))
    (hnorm : ∀ i,eLpNorm (fun x => v x i) (ENNReal.ofReal q) (stdGaussian (FSC.Coord d)) ≤
      ENNReal.ofReal (W i))
    (hsub : ∀ i a,0<a → a≤aStar →
      (stdGaussian (FSC.Coord d)).real
        {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} ≤ C*a ∧
      (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) ≤ C*a) :
    (∫ x,closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤
      (C+1)*(Fintype.card V:ℝ)^(1/(q+1))*(2*θ*R)^(2*q/(q+1)) +
        (2*θ*R)^q/aStar^(q-1) := by
  have hq1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal q := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ q by linarith)
  have hvI (i : V) : Integrable (fun x => v x i) (stdGaussian (FSC.Coord d)) :=
    (hv i).integrable hq1
  have hW' (i : V) : 0 ≤ 2*θ*W i := mul_nonneg (by positivity) (hW i)
  have hR' : 0 ≤ 2*θ*R := by positivity
  have henergy' : (∑ i,(2*θ*W i)^2) ≤ (2*θ*R)^2 := by
    calc
      _ = (2*θ)^2*∑ i,(W i)^2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ (2*θ)^2*R^2 := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = _ := by ring
  have hsource := sum_integral_reward_lq
    (fun i => (stdGaussian (FSC.Coord d)).restrict (winningCell B h i))
    (fun i x => 2*θ*v x i) (sourceCost B h) (fun i => 2*θ*W i)
    q aStar C (2*θ*R) hq haStar hC hW' hR' henergy'
    (fun i => ((hv i).const_mul (2*θ)).restrict _)
    (sourceCost_measurable B h) (sourceCost_nonneg B h)
    (fun i a ha haa => by
      change ((stdGaussian (FSC.Coord d)).restrict (winningCell B h i)).real
        {x | max (sourceExitMargin B h i x) 0 ≤ a} ≤ C*a
      rw [clipped_source_sublevel_restrict B h i a ha.le]
      exact (hsub i a ha haa).2)
    (fun i => scaled_restrict_norm_le _ _ q θ (W i) hθ (hnorm i) _)
  have htarget := sum_integral_reward_lq
    (fun i => (stdGaussian (FSC.Coord d)).restrict (winningCell B h i)ᶜ)
    (fun i x => 2*θ*v x i) (targetEntryMargin B h) (fun i => 2*θ*W i)
    q aStar C (2*θ*R) hq haStar hC hW' hR' henergy'
    (fun i => ((hv i).const_mul (2*θ)).restrict _)
    (targetEntryMargin_measurable B h) (targetEntryMargin_nonneg B h)
    (fun i a ha haa => by
      change ((stdGaussian (FSC.Coord d)).restrict (winningCell B h i)ᶜ).real
        {x | targetEntryMargin B h i x ≤ a} ≤ C*a
      rw [target_sublevel_restrict B h i a]
      exact (hsub i a ha haa).1)
    (fun i => scaled_restrict_norm_le _ _ q θ (W i) hθ (hnorm i) _)
  have hsplit := integral_closedCellCap_le_separated B hB h v θ hvM hvI
  change (∑ i,∫ x in winningCell B h i,sourceReward B h v θ i x ∂stdGaussian (FSC.Coord d)) ≤ _ at hsource
  change (∑ i,∫ x in (winningCell B h i)ᶜ,targetReward B h v θ i x ∂stdGaussian (FSC.Coord d)) ≤ _ at htarget
  linarith

/-- The constant needed by the scalar cap lemma, enlarged to be at least one. -/
def moderateMarginConstant (e C₀ : ℝ) : ℝ :=
  max (32*(shiftedMassConstant e C₀*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e) 1

/-- Actual moderate cap bound under initial rare-cell masses, singular scale,
and Gram geometry. No margin-probability, shifted-mass, or final cap estimate
is supplied as a premise. -/
theorem integral_closedCellCap_le_lq_of_initial_gram
    (B : V → FSC.Coord d) (h : V → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B σ) (e m L C₀ : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC₀ : 0 ≤ C₀)
    (hScale : e*Real.sqrt L/m ≤ σ)
    (hDiagLower : ∀ i,α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ i,inner ℝ (B i) (B i) ≤ 2*α^2)
    (hCross : ∀ i j,j≠i → inner ℝ (B j) (B i) ≤ α^2/4)
    (hmass : ∀ i,mass B h i ≤ C₀/m)
    (v : FSC.Coord d → V → ℝ) (θ q R : ℝ) (W : V → ℝ)
    (hθ : 0 ≤ θ) (hq : 2 ≤ q) (hW : ∀ i,0 ≤ W i) (hR : 0 ≤ R)
    (henergy : (∑ i,(W i)^2) ≤ R^2)
    (hvM : ∀ i,Measurable (fun x => v x i))
    (hv : ∀ i,MemLp (fun x => v x i) (ENNReal.ofReal q) (stdGaussian (FSC.Coord d)))
    (hnorm : ∀ i,eLpNorm (fun x => v x i) (ENNReal.ofReal q) (stdGaussian (FSC.Coord d)) ≤
      ENNReal.ofReal (W i)) :
    (∫ x,closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤
      (moderateMarginConstant e C₀+1)*(Fintype.card V:ℝ)^(1/(q+1))*(2*θ*R)^(2*q/(q+1)) +
        (2*θ*R)^q/(1/m)^(q-1) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hB : Function.Injective B := fun i j hh => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij hh
  apply integral_closedCellCap_le_lq_of_sublevels B hB h v θ q (1/m)
    (moderateMarginConstant e C₀) R W hθ hq (by positivity) (le_max_right _ _)
    hW hR henergy hvM hv hnorm
  intro i a ha haa
  have hh := one_label_margin_measures_le_of_initial_gram B h σ α hσ hα hlower i e m L C₀
    he hm hL hlog hC₀ hScale (hDiagLower i) hDiagUpper (hCross i) (hmass i) a ha.le haa
  have hb := mul_le_mul_of_nonneg_right
    (le_max_left (32*(shiftedMassConstant e C₀*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e) 1) ha.le
  exact ⟨hh.1.trans hb,hh.2.trans hb⟩

end NegativeVotingSwitchingModerateIntegral
