import GaussianSwitchingPairBound

/-! Integration of the literal off-diagonal switching cap.  Closed old cells
are used only for an upper bound, so ties cannot invalidate the comparison.
The main term remains the ordered sum of actual facet traces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal
namespace NegativeVotingSwitchingOrdered
open NegativeVotingFan NegativeVotingSwitchingCell NegativeVotingSwitchingPair
  NegativeVotingWeightedFacet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Sum of the off-diagonal caps on the closed winning cells. -/
def closedCellCap (B : V → E) (h : V → ℝ) (v : E → V → ℝ) (θ : ℝ) : E → ℝ :=
  fun x => ∑ i, (affineCell B h i).indicator
    (fun y => switchingCap (fun k => affineScore B h k y) (v y) θ i) x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem closedCellCap_nonneg (B : V → E) (h : V → ℝ) (v : E → V → ℝ)
    (θ : ℝ) (x : E) : 0 ≤ closedCellCap B h v θ x := by
  apply Finset.sum_nonneg
  intro i hi
  by_cases hx : x ∈ affineCell B h i
  · simp only [Set.indicator_of_mem hx]
    exact switchingCap_nonneg _ _ _ _
  · simp only [Set.indicator_of_notMem hx, le_refl]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cap of the actual winner is bounded pointwise, including at ties. -/
theorem actualCap_le_closedCellCap (B : V → E) (h : V → ℝ) (v : E → V → ℝ)
    (θ : ℝ) (x : E) :
    switchingCap (fun k => affineScore B h k x) (v x) θ (affineWinner B h x) ≤
      closedCellCap B h v θ x := by
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun i => (affineCell B h i).indicator
      (fun y => switchingCap (fun k => affineScore B h k y) (v y) θ i) x)
    (fun i _ => by
      by_cases hx : x ∈ affineCell B h i
      · simp only [Set.indicator_of_mem hx]
        exact switchingCap_nonneg _ _ _ _
      · simp only [Set.indicator_of_notMem hx, le_refl])
    (Finset.mem_univ (affineWinner B h x))
  simpa only [closedCellCap, Set.indicator_of_mem (affineWinner_mem_cell B h x)] using hi

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem closedCellCap_le_orderedRewards (B : V → E) (h : V → ℝ)
    (v : E → V → ℝ) (θ : ℝ) (x : E) :
    closedCellCap B h v θ x ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, cellReward B h i j v θ x := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : x ∈ affineCell B h i
  · simpa only [cellReward, Set.indicator_of_mem hx] using
      switchingCap_le_selected_sum (fun k => affineScore B h k x) (v x) θ i
  · simp only [Set.indicator_of_notMem hx, cellReward, Finset.sum_const_zero, le_refl]

omit [FiniteDimensional ℝ E] in
theorem measurable_closedCellCap (B : V → E) (h : V → ℝ) (v : E → V → ℝ)
    (θ : ℝ) (hv : ∀ i, Measurable (fun x => v x i)) :
    Measurable (closedCellCap B h v θ) := by
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.indicator _ (isClosed_affineCell B h i).measurableSet
  apply NegativeVoting.measurable_finite_max _ Finset.univ Finset.univ_nonempty
  intro j hj
  by_cases hji : j = i
  · simp only [ite_eq_left hji]
    exact measurable_const
  · simp only [ite_eq_right hji, orderedReward]
    have hs : Measurable (fun x => affineScore B h i x - affineScore B h j x) := by
      have hc : Continuous (fun x => affineScore B h i x - affineScore B h j x) := by
        unfold affineScore
        fun_prop
      exact hc.measurable
    exact ((measurable_const.mul ((hv i).add (hv j))).sub hs).max measurable_const

omit [Nonempty V] in
theorem integrable_orderedRewards (B : V → E) (h : V → ℝ) (v : E → V → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hv : ∀ i j, i ≠ j → MemLp (fun x => v x i + v x j) 32 (stdGaussian E)) :
    Integrable (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i,
      cellReward B h i j v θ x) (stdGaussian E) := by
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact cellReward_integrable B h i j v θ hθ
    (hv i j (Finset.ne_of_mem_erase hj).symm)

theorem integrable_closedCellCap (B : V → E) (h : V → ℝ) (v : E → V → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hvM : ∀ i, Measurable (fun x => v x i))
    (hv : ∀ i j, i ≠ j → MemLp (fun x => v x i + v x j) 32 (stdGaussian E)) :
    Integrable (closedCellCap B h v θ) (stdGaussian E) := by
  apply (integrable_orderedRewards B h v θ hθ hv).mono'
    (measurable_closedCellCap B h v θ hvM).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (closedCellCap_nonneg B h v θ x)]
  exact closedCellCap_le_orderedRewards B h v θ x

/-- Integration does not multiply the leading facet term by the alphabet size. -/
theorem integral_closedCellCap_le_ordered (B : V → E) (h : V → ℝ)
    (v : E → V → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hvM : ∀ i, Measurable (fun x => v x i))
    (hv : ∀ i j, i ≠ j → MemLp (fun x => v x i + v x j) 32 (stdGaussian E)) :
    (∫ x, closedCellCap B h v θ x ∂stdGaussian E) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, cellReward B h i j v θ x ∂stdGaussian E := by
  have hb := integral_mono (integrable_closedCellCap B h v θ hθ hvM hv)
    (integrable_orderedRewards B h v θ hθ hv)
    (closedCellCap_le_orderedRewards B h v θ)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j hj =>
    cellReward_integrable B h i j v θ hθ (hv i j (Finset.ne_of_mem_erase hj).symm)))] at hb
  simpa only [integral_finsetSum _ (fun j hj =>
    cellReward_integrable B h _ j v θ hθ (hv _ j (Finset.ne_of_mem_erase hj).symm))] using hb

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A fractional reassignment is controlled by this same integrable cap. -/
theorem fractional_gain_le_closedCellCap (B : V → E) (h : V → ℝ)
    (v perturbation p : E → V → ℝ) (θ : ℝ) (x : E)
    (hp : NegativeVoting.SimplexWeights (p x))
    (hperturb : ∀ j, |perturbation x j| ≤ θ * v x j) :
    (∑ j, p x j * ((perturbation x j - perturbation x (affineWinner B h x)) -
      (affineScore B h (affineWinner B h x) x - affineScore B h j x))) ≤
      closedCellCap B h v θ x :=
  (fractional_perturbation_gain_le_cap _ _ _ _ θ _ hp hperturb).trans
    (actualCap_le_closedCellCap B h v θ x)

end NegativeVotingSwitchingOrdered
