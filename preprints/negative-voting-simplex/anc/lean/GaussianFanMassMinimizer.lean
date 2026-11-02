import GaussianFanMassBase
import Mathlib.Topology.Order.Compact

/-! Coercive minimization of the actual Gaussian fan dual on the zero-sum gauge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NegativeVotingFan
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

theorem norm_le_card_mul_max_of_sum_zero (h : ι → ℝ) (hh : ∑ i, h i = 0) :
    ‖h‖ ≤ (Fintype.card ι : ℝ) * NegativeVoting.maxScore h := by
  classical
  let M := NegativeVoting.maxScore h
  have hi (i : ι) : h i ≤ M := Finset.le_sup' (f := h) (Finset.mem_univ i)
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * M := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simpa [hh] using hs
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_right hsum hm
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hgap : M - h i ≤ ∑ j : ι, (M - h j) :=
    Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hi j)) (Finset.mem_univ i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hh, sub_zero] at hgap
  have hupper : M ≤ (Fintype.card ι : ℝ) * M := by nlinarith
  exact abs_le.mpr ⟨by linarith, (hi i).trans hupper⟩

/-- A strictly positive target mass lower bound gives a coercive bound for the
concrete Gaussian dual; the offset gauge is the only constraint. -/
theorem potential_ge_massLower_mul_norm (B : ι → FSC.Coord d) (p h : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hp : ∀ i, δ ≤ p i) (hs : ∑ i, p i = 1)
    (hh : ∑ i, h i = 0) : δ * ‖h‖ ≤ potential B p h := by
  classical
  let M := NegativeVoting.maxScore h
  have hmax (i : ι) : h i ≤ M := Finset.le_sup' (f := h) (Finset.mem_univ i)
  have hmean : M ≤ expectedMax B h := by
    apply Finset.sup'_le
    intro i _
    exact offset_le_expectedMax B h i
  calc
    δ * ‖h‖ ≤ δ * ((Fintype.card ι : ℝ) * M) :=
      mul_le_mul_of_nonneg_left (norm_le_card_mul_max_of_sum_zero h hh) hδ
    _ = ∑ i, δ * (M - h i) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [hh]
    _ ≤ ∑ i, p i * (M - h i) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hp i) (sub_nonneg.mpr (hmax i))
    _ = M - ∑ i, p i * h i := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    _ ≤ potential B p h := sub_le_sub_right hmean _

/-- The prescribed-mass dual attains its minimum on the zero-sum hyperplane.
The proof uses an actual compact sublevel set; no existence or coercivity
certificate is an input. Pairwise distinct score rows are not needed here. -/
theorem exists_potential_minimizer (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : ι → ℝ, (∑ i, h i = 0) ∧
      ∀ k : ι → ℝ, (∑ i, k i = 0) → potential B p h ≤ potential B p k := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  let δ := p i
  have hδ : 0 < δ := hp i
  have hbound (j : ι) : δ ≤ p j := hi j (Finset.mem_univ j)
  let K : Set (ι → ℝ) := {h | (∑ j, h j = 0) ∧ potential B p h ≤ potential B p 0}
  have hclosed : IsClosed K :=
    (isClosed_eq (by fun_prop : Continuous fun h : ι → ℝ => ∑ j, h j)
      continuous_const).inter
        (isClosed_le (potential_continuous B p) continuous_const)
  have hsubset : K ⊆ Metric.closedBall 0 (potential B p 0 / δ) := by
    intro h hh
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (le_div_iff₀ hδ).mpr
    have hb := potential_ge_massLower_mul_norm B p h hδ.le hbound hs hh.1
    nlinarith [hh.2]
  have hcompact : IsCompact K :=
    (isCompact_closedBall (0 : ι → ℝ) (potential B p 0 / δ)).of_isClosed_subset
      hclosed hsubset
  have hzero : (0 : ι → ℝ) ∈ K := by simp [K]
  obtain ⟨h, hh, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩
    (potential_continuous B p).continuousOn
  refine ⟨h, hh.1, ?_⟩
  intro k hk
  by_cases hkF : potential B p k ≤ potential B p 0
  · exact hmin ⟨hk, hkF⟩
  · exact hh.2.trans (le_of_lt (lt_of_not_ge hkF))

end NegativeVotingFan
