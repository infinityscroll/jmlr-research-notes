import GaussianFanMassGradient
import GaussianFanMassMinimizer

/-! Prescribed positive Gaussian masses for an actual finite affine fan.
Distinct sites suffice; no full-rank or mass-existence premise is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace BigOperators Topology

namespace NegativeVotingFan
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

def winningCell (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) : Set (FSC.Coord d) :=
  {x | ∀ j, scores B h x j ≤ scores B h x i}

theorem winningCell_measurable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    MeasurableSet (winningCell B h i) := by
  unfold winningCell
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  unfold scores
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem mass_eq_winningCell (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) :
    mass B h i = (stdGaussian (FSC.Coord d)).real (winningCell B h i) := by
  classical
  have hae : (fun x => weights B h x i) =ᵐ[stdGaussian (FSC.Coord d)]
      (winningCell B h i).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_scores_injective B hB h] with x hx
    let a := NegativeVoting.chosenWinner (scores B h x)
    have ha (j : ι) (hj : j ≠ a) : scores B h x j < scores B h x a :=
      lt_of_le_of_ne (NegativeVoting.chosenWinner_max (scores B h x) j)
        (fun he => hj (hx he))
    have hw : weights B h x i = if i = a then 1 else 0 :=
      NegativeVoting.maxWeights_eq_indicator_of_strict_max (scores B h x) a ha i
    by_cases hi : i = a
    · have hmem : x ∈ winningCell B h i := by
        subst i
        exact fun j => NegativeVoting.chosenWinner_max (scores B h x) j
      rw [hw]
      simp only [if_pos hi, Set.indicator_of_mem hmem]
    · have hnot : x ∉ winningCell B h i := by
        intro hmem
        exact not_le_of_gt (ha i hi) (hmem a)
      rw [hw]
      simp [hi, hnot]
  unfold mass
  rw [integral_congr_ae hae, integral_indicator (winningCell_measurable B h i)]
  simp

/-- The first-order condition is forced by the squared mass discrepancy.
No Lagrange-multiplier, differentiability, or gradient-identity premise is needed. -/
theorem masses_eq_of_minimizer (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (p h : ι → ℝ) (hs : ∑ i, p i = 1) (hh : ∑ i, h i = 0)
    (hmin : ∀ k : ι → ℝ, (∑ i, k i = 0) → potential B p h ≤ potential B p k) :
    ∀ i, mass B h i = p i := by
  let v : ι → ℝ := fun i => mass B h i - p i
  have hv : ∑ i, v i = 0 := by simp [v, Finset.sum_sub_distrib, mass_sum, hs]
  have hc (t : ℝ) : ∑ i, (h i + t * v i) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hh, hv]
    ring
  have hlocal : IsLocalMin (fun t : ℝ => potential B p (fun i => h i + t * v i)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0,
      potential B p (fun i => h i + 0 * v i) ≤ potential B p (fun i => h i + t * v i)
    exact Eventually.of_forall (fun t => by simpa using hmin _ (hc t))
  have hz := hlocal.hasDerivAt_eq_zero (hasDerivAt_potential B hB p h v)
  have hsq : ∑ i, (mass B h i - p i) ^ 2 = 0 := by
    simpa only [v, pow_two] using hz
  intro i
  have hi : (mass B h i - p i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (mass B h j - p j))).mp
      hsq i (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- Every strictly positive probability vector is realized by an affine Gaussian
fan with these fixed distinct sites and zero-sum offsets. -/
theorem exists_offsets_with_prescribed_masses
    (B : ι → FSC.Coord d) (hB : Function.Injective B) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : ι → ℝ, (∑ i, h i = 0) ∧ ∀ i, mass B h i = p i := by
  obtain ⟨h, hh, hmin⟩ := exists_potential_minimizer B p hp hs
  exact ⟨h, hh, masses_eq_of_minimizer B hB p h hs hh hmin⟩

/-- The same existence statement uses literal Gaussian measures of closed
polyhedral winning cells; their boundary ties have Gaussian measure zero. -/
theorem exists_affine_fan_with_prescribed_gaussian_masses
    (B : ι → FSC.Coord d) (hB : Function.Injective B) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : ι → ℝ, (∑ i, h i = 0) ∧ ∀ i,
      (stdGaussian (FSC.Coord d)).real
        {x | ∀ j, inner ℝ (B j) x + h j ≤ inner ℝ (B i) x + h i} = p i := by
  obtain ⟨h, hh, hm⟩ := exists_offsets_with_prescribed_masses B hB p hp hs
  refine ⟨h, hh, fun i => ?_⟩
  rw [← hm i, mass_eq_winningCell B hB h i]
  rfl

end NegativeVotingFan
