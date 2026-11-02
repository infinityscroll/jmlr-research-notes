import GaussianSwitchingLabelSum

/-! Separate the actual maximum switching reward into one source-exit term
and target-entry terms. This avoids an alphabet-sized union of pair margins. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators Classical
namespace NegativeVotingSwitchingSeparation
open NegativeVotingFan
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem positive_part_split (a b c : ℝ) :
    max (a+b-c) 0  ≤  (max (2*a-c) 0+max (2*b-c) 0)/2 := by
  apply max_le
  · linarith [le_max_left (2*a-c) 0,le_max_left (2*b-c) 0]
  · positivity

/-- No alphabet multiplier is introduced when separating the source cost.
`g` need only be a lower bound for the off-diagonal source gaps. -/
theorem switchingCap_le_source_targets (s v : V → ℝ) (θ g : ℝ) (i : V)
    (hg : ∀ j, j ≠ i → g ≤ s i-s j) :
    switchingCap s v θ i  ≤ 
      (max (2*θ*v i-g) 0+
        ∑ j ∈ Finset.univ.erase i, max (2*θ*v j-(s i-s j)) 0)/2 := by
  unfold switchingCap NegativeVoting.maxScore
  apply Finset.sup'_le
  intro j hj
  by_cases hji : j=i
  · rw [ite_eq_left hji]
    positivity
  · rw [ite_eq_right hji]
    have ht := positive_part_split (θ*v i) (θ*v j) (s i-s j)
    have hs : max (2*(θ*v i)-(s i-s j)) 0 ≤ max (2*θ*v i-g) 0 := by
      apply max_le_max _ le_rfl
      linarith [hg j hji]
    have hjb : max (2*(θ*v j)-(s i-s j)) 0  ≤ 
        ∑ k ∈ Finset.univ.erase i, max (2*θ*v k-(s i-s k)) 0 := by
      simpa only [mul_assoc] using Finset.single_le_sum
        (s:=Finset.univ.erase i) (f:=fun k=>max (2*θ*v k-(s i-s k)) 0)
        (fun k _=>le_max_right _ _) (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
    change max (θ*(v i+v j)-(s i-s j)) 0 ≤ _
    rw [mul_add]
    linarith

/-- At a winning label, the target cost is exactly max score minus that
target's score; the source and target gaps have not been replaced by pair sums. -/
theorem switchingCap_le_max_margin_terms (s v : V → ℝ) (θ g : ℝ) (i : V)
    (hi : ∀ j, s j ≤ s i) (hg : ∀ j, j ≠ i → g ≤ s i-s j) :
    switchingCap s v θ i  ≤ 
      (max (2*θ*v i-g) 0+
        ∑ j ∈ Finset.univ.erase i, max (2*θ*v j-(NegativeVoting.maxScore s-s j)) 0)/2 := by
  have he : NegativeVoting.maxScore s=s i := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _=>hi j)
    · exact Finset.le_sup' s (Finset.mem_univ i)
  rw [he]
  exact switchingCap_le_source_targets s v θ g i hg

theorem switchingCap_zero_on_winner (s v : V → ℝ) (i : V)
    (hi : ∀ j, s j ≤ s i) : switchingCap s v 0 i=0 := by
  apply le_antisymm _ (switchingCap_nonneg s v 0 i)
  unfold switchingCap NegativeVoting.maxScore
  apply Finset.sup'_le
  intro j hj
  split_ifs
  · exact le_rfl
  · unfold orderedReward
    simp only [zero_mul,zero_sub]
    exact max_le (by linarith [hi j]) le_rfl

end NegativeVotingSwitchingSeparation
