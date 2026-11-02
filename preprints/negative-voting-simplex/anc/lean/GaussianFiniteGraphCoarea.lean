import Mathlib

/-! Finite weighted cut expansion implies an ordered L1 graph inequality.
The coarea identity is proved by integrating literal threshold-cut indicators. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NegativeVotingFiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

def cutWeight (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑i ∈ S, ∑j ∈ Sᶜ, w i j

def thresholdCut (g : V → ℝ) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun i => g i≤t)

theorem cut_threshold_indicator (w : V → V → ℝ) (g : V → ℝ) (t : ℝ) :
    cutWeight w (thresholdCut g t) =
      ∑i, ∑j, w i j*(Ico (g i) (g j)).indicator (fun _ : ℝ => (1:ℝ)) t := by
  have hc : (thresholdCut g t)ᶜ = Finset.univ.filter (fun j => t<g j) := by
    ext j
    simp [thresholdCut,not_le]
  unfold cutWeight
  rw [hc]
  unfold thresholdCut
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hgi : g i≤t
  · simp only [if_pos hgi]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Set.indicator,Set.mem_Ico,hgi]
  · simp [hgi,Set.indicator,Set.mem_Ico]

theorem integrable_interval_indicator (a b : ℝ) :
    Integrable ((Ico a b).indicator (fun _ : ℝ => (1:ℝ))) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact (integrableOn_const_iff (by finiteness)).mpr (Or.inr (by simp [Real.volume_Ico]))

theorem integral_interval_indicator (a b : ℝ) :
    (∫t : ℝ, (Ico a b).indicator (fun _ : ℝ => (1:ℝ)) t) = max (b-a) 0 := by
  rw [integral_indicator measurableSet_Ico,integral_const]
  simp [Measure.restrict_apply_univ,Real.volume_Ico,ENNReal.toReal_ofReal']

theorem integrable_cut_threshold (w : V → V → ℝ) (g : V → ℝ) :
    Integrable (fun t => cutWeight w (thresholdCut g t)) := by
  simp_rw [cut_threshold_indicator]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  exact (integrable_interval_indicator (g i) (g j)).const_mul (w i j)

/-- A literal finite coarea identity, with arbitrary real edge weights. -/
theorem integral_cut_threshold (w : V → V → ℝ) (g : V → ℝ) :
    (∫t : ℝ, cutWeight w (thresholdCut g t)) =
      ∑i, ∑j, w i j*max (g j-g i) 0 := by
  simp_rw [cut_threshold_indicator]
  rw [integral_finsetSum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (integrable_interval_indicator (g i) (g j)).const_mul (w i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_interval_indicator (g i) (g j)).const_mul (w i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,integral_interval_indicator]

theorem cutWeight_one (S : Finset V) :
    cutWeight (fun _ _ => 1) S = (S.card:ℝ)*(Sᶜ.card:ℝ) := by
  simp [cutWeight,Finset.sum_const,nsmul_eq_mul]

theorem cut_count_le_card_mul_min (S : Finset V) :
    (S.card:ℝ)*(Sᶜ.card:ℝ) ≤ (Fintype.card V:ℝ)*min (S.card:ℝ) (Sᶜ.card:ℝ) := by
  have ha : (S.card:ℝ)≤(Fintype.card V:ℝ) := by exact_mod_cast Finset.card_le_univ S
  have hb : (Sᶜ.card:ℝ)≤(Fintype.card V:ℝ) := by exact_mod_cast Finset.card_le_univ Sᶜ
  by_cases hh : (S.card:ℝ)≤(Sᶜ.card:ℝ)
  · rw [min_eq_left hh]
    nlinarith [show (0:ℝ)≤S.card by positivity]
  · rw [min_eq_right (le_of_not_ge hh)]
    nlinarith [show (0:ℝ)≤Sᶜ.card by positivity]

theorem integrated_cut_comparison (w : V → V → ℝ) (κ : ℝ) (hκ : 0≤κ)
    (hcut : ∀S : Finset V, κ*min (S.card:ℝ) (Sᶜ.card:ℝ)≤cutWeight w S)
    (g : V → ℝ) :
    κ*(∑i,∑j,max (g j-g i) 0) ≤
      (Fintype.card V:ℝ)*(∑i,∑j,w i j*max (g j-g i) 0) := by
  have hp (t : ℝ) : κ*cutWeight (fun _ _ => 1) (thresholdCut g t) ≤
      (Fintype.card V:ℝ)*cutWeight w (thresholdCut g t) := by
    rw [cutWeight_one]
    calc
      _ ≤ κ*((Fintype.card V:ℝ)*min ((thresholdCut g t).card:ℝ)
          ((thresholdCut g t)ᶜ.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (cut_count_le_card_mul_min _) hκ
      _ = (Fintype.card V:ℝ)*(κ*min ((thresholdCut g t).card:ℝ)
          ((thresholdCut g t)ᶜ.card:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcut _) (by positivity)
  have hh := integral_mono ((integrable_cut_threshold (fun _ _ => 1) g).const_mul κ)
    ((integrable_cut_threshold w g).const_mul (Fintype.card V:ℝ)) hp
  rw [integral_const_mul,integral_const_mul,integral_cut_threshold,integral_cut_threshold] at hh
  simpa only [one_mul] using hh

theorem abs_sub_positive_parts (a b : ℝ) :
    |a-b|=max (b-a) 0+max (a-b) 0 := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),max_eq_left (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h),
      max_eq_left (sub_nonneg.mpr h)]
    ring

theorem weighted_absolute_sum_eq_twice (w : V → V → ℝ)
    (hsym : ∀i j,w i j=w j i) (g : V → ℝ) :
    (∑i,∑j,w i j*|g i-g j|)=2*(∑i,∑j,w i j*max (g j-g i) 0) := by
  simp_rw [abs_sub_positive_parts,mul_add,Finset.sum_add_distrib]
  have he : (∑i,∑j,w i j*max (g i-g j) 0)=∑i,∑j,w i j*max (g j-g i) 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  rw [he]
  ring

/-- Cut expansion yields the ordered L1 comparison needed for a quantitative
Rayleigh bound. There is no assumed median, coarea, or Poincare estimate. -/
theorem weighted_l1_of_cut [Nonempty V] (w : V → V → ℝ) (κ : ℝ) (hκ : 0≤κ)
    (hsym : ∀i j,w i j=w j i)
    (hcut : ∀S : Finset V, κ*min (S.card:ℝ) (Sᶜ.card:ℝ)≤cutWeight w S)
    (g : V → ℝ) :
    (κ/(Fintype.card V:ℝ))*(∑i,∑j,|g i-g j|) ≤ ∑i,∑j,w i j*|g i-g j| := by
  have hh := integrated_cut_comparison w κ hκ hcut g
  have h1 := weighted_absolute_sum_eq_twice (fun _ _ : V => (1:ℝ)) (fun _ _ => rfl) g
  simp only [one_mul] at h1
  have hw := weighted_absolute_sum_eq_twice w hsym g
  have hc : (0:ℝ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hc).mpr
  rw [h1,hw]
  nlinarith

end NegativeVotingFiniteGraph
