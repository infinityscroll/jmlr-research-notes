import GaussianCapTailAndStrip
import NegativeVoting.RegularSimplex

/-!
# Geometric covering of an actual affine fan

A projected point outside its actual pairwise facet is covered by third-label
strips. The strip probability is under the entire intrinsic Gaussian plane;
no normalization by the probability of the facet is used. Normal disintegration
and integration of the weighted facet energy are separate obligations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators Classical
namespace NegativeVotingFan
open NegativeVotingCapTail NegativeVotingSmallCap

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineScore (rows : ι → E) (offsets : ι → ℝ) (i : ι) (x : E) : ℝ :=
  inner ℝ (rows i) x + offsets i

def affineCell (rows : ι → E) (offsets : ι → ℝ) (i : ι) : Set E :=
  {x | ∀ k, affineScore rows offsets k x ≤ affineScore rows offsets i x}

def affineFacet (rows : ι → E) (offsets : ι → ℝ) (i j : ι) : Set E :=
  {y | affineScore rows offsets i y = affineScore rows offsets j y ∧ y ∈ affineCell rows offsets i}

omit [Fintype ι] [DecidableEq ι] in
theorem affineScore_gap_add (rows : ι → E) (offsets : ι → ℝ) (i j : ι) (x y : E) :
    affineScore rows offsets i (x + y) - affineScore rows offsets j (x + y) =
      (affineScore rows offsets i x - affineScore rows offsets j x) + inner ℝ (rows i - rows j) y := by
  simp only [affineScore, inner_add_right, inner_sub_left]
  ring


/-- The oriented unit normal for the i-winning side of a comparison plane. -/
def pairNormal (rows : ι → E) (i j : ι) : E :=
  ‖rows i - rows j‖⁻¹ • (rows i - rows j)

omit [Fintype ι] [DecidableEq ι] in
theorem pairNormal_norm (rows : ι → E) (i j : ι) (hij : rows i ≠ rows j) :
    ‖pairNormal rows i j‖ = 1 := by
  have hnorm : ‖rows i - rows j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  simp only [pairNormal, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ hnorm

omit [Fintype ι] [DecidableEq ι] in
/-- The genuine affine score gap is exactly the linear normal cost, including
the affine offsets through the comparison-plane hypothesis. -/
theorem affine_gap_along_pairNormal (rows : ι → E) (offsets : ι → ℝ) (i j : ι)
    (y : E) (z : ℝ) (hplane : affineScore rows offsets i y = affineScore rows offsets j y) :
    affineScore rows offsets i (y + z • pairNormal rows i j) -
      affineScore rows offsets j (y + z • pairNormal rows i j) = ‖rows i - rows j‖ * z := by
  rw [affineScore_gap_add, hplane, sub_self, zero_add, real_inner_smul_right]
  simp only [pairNormal, real_inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases hn : ‖rows i - rows j‖ = 0
  · simp [hn]
  · field_simp


omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_affineCell (rows : ι → E) (offsets : ι → ℝ) (i : ι) :
    IsClosed (affineCell rows offsets i) := by
  have heq : affineCell rows offsets i =
      ⋂ k, {x | affineScore rows offsets k x ≤ affineScore rows offsets i x} := by
    ext x
    simp [affineCell]
  rw [heq]
  apply isClosed_iInter
  intro k
  apply isClosed_le <;> unfold affineScore <;> fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_affineFacet (rows : ι → E) (offsets : ι → ℝ) (i j : ι) :
    IsClosed (affineFacet rows offsets i j) := by
  change IsClosed ({y | affineScore rows offsets i y = affineScore rows offsets j y} ∩ affineCell rows offsets i)
  exact (isClosed_eq (by unfold affineScore; fun_prop) (by unfold affineScore; fun_prop)).inter
    (isClosed_affineCell rows offsets i)

omit [Fintype ι] [DecidableEq ι] in
/-- The actual escape implication. The normal is only required to have norm
at most one; the normalized pair normal is therefore an admissible instance. -/
theorem outside_facet_has_third_strip (rows : ι → E) (offsets : ι → ℝ)
    (i j : ι) (y n : E) (z η : ℝ) (hn : ‖n‖ ≤ 1) (hz : 0 ≤ z) (hzη : z ≤ η)
    (hplane : affineScore rows offsets i y = affineScore rows offsets j y)
    (hout : y ∉ affineFacet rows offsets i j)
    (hcell : y + z • n ∈ affineCell rows offsets i) :
    ∃ k, k ≠ i ∧ k ≠ j ∧
      -(η * ‖rows i - rows k‖) ≤ affineScore rows offsets i y - affineScore rows offsets k y ∧
      affineScore rows offsets i y - affineScore rows offsets k y < 0 := by
  have hnot : ¬ ∀ k, affineScore rows offsets k y ≤ affineScore rows offsets i y :=
    fun hall => hout ⟨hplane, hall⟩
  obtain ⟨k, hk⟩ := not_forall.mp hnot
  have hlt : affineScore rows offsets i y < affineScore rows offsets k y := lt_of_not_ge hk
  have hki : k ≠ i := by intro heq; subst k; exact lt_irrefl _ hlt
  have hkj : k ≠ j := by intro heq; subst k; linarith
  have hwin : 0 ≤ affineScore rows offsets i (y + z • n) -
      affineScore rows offsets k (y + z • n) := sub_nonneg.mpr (hcell k)
  rw [affineScore_gap_add, real_inner_smul_right] at hwin
  have hdot : inner ℝ (rows i - rows k) n ≤ ‖rows i - rows k‖ :=
    (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hn)
  have hmove : z * inner ℝ (rows i - rows k) n ≤ η * ‖rows i - rows k‖ :=
    (mul_le_mul_of_nonneg_left hdot hz).trans
      (mul_le_mul_of_nonneg_right hzη (norm_nonneg _))
  exact ⟨k, hki, hkj, by linarith, sub_neg.mpr hlt⟩

def thirdLabels (i j : ι) : Finset ι := (Finset.univ.erase i).erase j

theorem mem_thirdLabels (i j k : ι) : k ∈ thirdLabels i j ↔ k ≠ i ∧ k ≠ j := by
  simp only [thirdLabels, Finset.mem_erase, Finset.mem_univ, and_true]
  exact and_comm

theorem thirdLabels_card (i j : ι) (hij : i ≠ j) :
    (thirdLabels i j).card = Fintype.card ι - 2 := by
  rw [thirdLabels, Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  omega

/-- Coordinates on the entire comparison plane, based at p. -/
def projectedEscape (rows : ι → E) (offsets : ι → ℝ) (i j : ι)
    (p n : E) (η : ℝ) : Set ((ℝ ∙ (rows i - rows j))ᗮ) :=
  {x | (p + (x : E)) ∉ affineFacet rows offsets i j ∧
    ∃ z, 0 ≤ z ∧ z ≤ η ∧ p + (x : E) + z • n ∈ affineCell rows offsets i}

def thirdStrip (rows : ι → E) (offsets : ι → ℝ) (i j k : ι)
    (p : E) (η : ℝ) : Set ((ℝ ∙ (rows i - rows j))ᗮ) :=
  {x | affineScore rows offsets i p - affineScore rows offsets k p ≤ inner ℝ (rows k - rows i) (x : E) ∧
    inner ℝ (rows k - rows i) (x : E) ≤
      affineScore rows offsets i p - affineScore rows offsets k p + η * ‖rows i - rows k‖}

/-- The entire projected escape set is covered by the m−2 genuine third-label
strips. The endpoints include affine offsets and the chosen plane basepoint. -/
theorem projectedEscape_subset_strips (rows : ι → E) (offsets : ι → ℝ)
    (i j : ι) (p n : E) (η : ℝ) (hn : ‖n‖ ≤ 1)
    (hp : affineScore rows offsets i p = affineScore rows offsets j p) :
    projectedEscape rows offsets i j p n η ⊆
      ⋃ k ∈ thirdLabels i j, thirdStrip rows offsets i j k p η := by
  intro x hx
  obtain ⟨hout, z, hz, hzη, hcell⟩ := hx
  have hxorth : inner ℝ (rows i - rows j) (x : E) = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.property
  have hplane : affineScore rows offsets i (p + (x : E)) = affineScore rows offsets j (p + (x : E)) := by
    apply sub_eq_zero.mp
    rw [affineScore_gap_add, hp, sub_self, hxorth, add_zero]
  obtain ⟨k, hki, hkj, hlow, hhigh⟩ := outside_facet_has_third_strip rows offsets i j
    (p + (x : E)) n z η hn hz hzη hplane hout hcell
  refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨(mem_thirdLabels i j k).mpr ⟨hki, hkj⟩, ?_⟩⟩
  have heq : affineScore rows offsets i (p + (x : E)) - affineScore rows offsets k (p + (x : E)) =
      (affineScore rows offsets i p - affineScore rows offsets k p) - inner ℝ (rows k - rows i) (x : E) := by
    rw [affineScore_gap_add, inner_sub_left, inner_sub_left]
    ring
  change _ ≤ _ ∧ _ ≤ _
  constructor <;> linarith

end Geometry

section GaussianCover
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
/-- The existential normal displacement is measurable: its parameter lies in
a compact interval and the old cell is closed. Thus the escape bound below
concerns a genuine Borel event, not just an arbitrary outer-measure set. -/
theorem measurableSet_projectedEscape (rows : ι → E) (offsets : ι → ℝ)
    (i j : ι) (p n : E) (η : ℝ) :
    MeasurableSet (projectedEscape rows offsets i j p n η) := by
  let T := (ℝ ∙ (rows i - rows j))ᗮ
  let Z := Icc (0 : ℝ) η
  have : CompactSpace Z := isCompact_iff_compactSpace.mp isCompact_Icc
  let C : Set (T × Z) := {q | p + (q.1 : E) + (q.2 : ℝ) • n ∈ affineCell rows offsets i}
  have hC : IsClosed C := (isClosed_affineCell rows offsets i).preimage (by fun_prop)
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have heq : Prod.fst '' C = {x : T | ∃ z, 0 ≤ z ∧ z ≤ η ∧ p + (x : E) + z • n ∈ affineCell rows offsets i} := by
    ext x
    constructor
    · rintro ⟨⟨x', z⟩, hz, hxx⟩
      change x' = x at hxx
      subst x'
      exact ⟨z, z.property.1, z.property.2, hz⟩
    · rintro ⟨z, hz0, hzη, hz⟩
      exact ⟨(x, ⟨z, ⟨hz0, hzη⟩⟩), hz, rfl⟩
  rw [heq] at hproj
  have hfacet : IsClosed {x : T | p + (x : E) ∈ affineFacet rows offsets i j} :=
    (isClosed_affineFacet rows offsets i j).preimage (by fun_prop)
  exact hfacet.measurableSet.compl.inter hproj.measurableSet

/-- Intrinsic Gaussian escape bound, before replacing the individual row-gap
norms by a common bound. Every distinct third label is counted once. -/
theorem projectedEscape_gaussian_sum_bound (rows : ι → E) (offsets : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ)
    (i j : ι) (hij : i ≠ j) (p n : E) (η : ℝ) (hη : 0 ≤ η) (hn : ‖n‖ ≤ 1)
    (hp : affineScore rows offsets i p = affineScore rows offsets j p) :
    (stdGaussian ((ℝ ∙ (rows i - rows j))ᗮ)
      (projectedEscape rows offsets i j p n η)).toReal ≤
      ∑ k ∈ thirdLabels i j, (η * ‖rows i - rows k‖) /
        (Real.sqrt (2 * Real.pi) * σ * Real.sqrt (3 / 2)) := by
  let μ := stdGaussian ((ℝ ∙ (rows i - rows j))ᗮ)
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hsubset := projectedEscape_subset_strips rows offsets i j p n η hn hp
  change μ.real (projectedEscape rows offsets i j p n η) ≤ _
  calc
    _ ≤ μ.real (⋃ k ∈ thirdLabels i j, thirdStrip rows offsets i j k p η) :=
      measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ ∑ k ∈ thirdLabels i j, μ.real (thirdStrip rows offsets i j k p η) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hki, hkj⟩ := (mem_thirdLabels i j k).mp hk
      exact third_label_tangent_strip_probability rows σ hσ hlower i j k hij hki.symm hkj.symm
        (affineScore rows offsets i p - affineScore rows offsets k p)
        (η * ‖rows i - rows k‖) (mul_nonneg hη (norm_nonneg _))

/-- With a common upper row-gap bound D, precisely m−2 strips suffice. -/
theorem projectedEscape_gaussian_bound (rows : ι → E) (offsets : ι → ℝ)
    (σ D : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ)
    (i j : ι) (hij : i ≠ j) (p n : E) (η : ℝ) (hη : 0 ≤ η) (hn : ‖n‖ ≤ 1)
    (hp : affineScore rows offsets i p = affineScore rows offsets j p)
    (hD : ∀ k ∈ thirdLabels i j, ‖rows i - rows k‖ ≤ D) :
    (stdGaussian ((ℝ ∙ (rows i - rows j))ᗮ)
      (projectedEscape rows offsets i j p n η)).toReal ≤
      ((Fintype.card ι - 2 : ℕ) : ℝ) * (η * D) /
        (Real.sqrt (2 * Real.pi) * σ * Real.sqrt (3 / 2)) := by
  apply (projectedEscape_gaussian_sum_bound rows offsets σ hσ hlower i j hij p n η hη hn hp).trans
  calc
    _ ≤ ∑ k ∈ thirdLabels i j, (η * D) / (Real.sqrt (2 * Real.pi) * σ * Real.sqrt (3 / 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hD k hk) hη) (by positivity)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, thirdLabels_card i j hij]
      ring

end GaussianCover


section RewardReduction
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A single ordered transition's positive reward. -/
def orderedReward (scores forcing : ι → ℝ) (θ : ℝ) (i j : ι) : ℝ :=
  max (θ * (forcing i + forcing j) - (scores i - scores j)) 0

/-- Maximum switching reward, with the diagonal explicitly set to zero. -/
def switchingCap (scores forcing : ι → ℝ) (θ : ℝ) (winner : ι) : ℝ :=
  NegativeVoting.maxScore (fun j => if j = winner then 0 else orderedReward scores forcing θ winner j)

theorem switchingCap_nonneg (scores forcing : ι → ℝ) (θ : ℝ) (winner : ι) :
    0 ≤ switchingCap scores forcing θ winner := by
  have hh := Finset.le_sup' (fun j => if j = winner then 0 else orderedReward scores forcing θ winner j)
    (Finset.mem_univ winner)
  simpa only [ite_true, switchingCap, NegativeVoting.maxScore] using hh

/-- A convex fractional reassignment is controlled by the same cap. The
forcing hypothesis bounds actual perturbation magnitudes; it is not a cap estimate. -/
theorem fractional_perturbation_gain_le_cap (scores forcing perturbation p : ι → ℝ)
    (θ : ℝ) (winner : ι) (hp : NegativeVoting.SimplexWeights p)
    (hperturb : ∀ j, |perturbation j| ≤ θ * forcing j) :
    (∑ j, p j * ((perturbation j - perturbation winner) - (scores winner - scores j))) ≤
      switchingCap scores forcing θ winner := by
  have hpoint (j : ι) :
      (perturbation j - perturbation winner) - (scores winner - scores j) ≤
        switchingCap scores forcing θ winner := by
    by_cases hj : j = winner
    · subst j
      simpa only [sub_self] using switchingCap_nonneg scores forcing θ winner
    · have hforce : perturbation j - perturbation winner ≤ θ * (forcing winner + forcing j) := by
        have hjabs := le_abs_self (perturbation j)
        have hiabs := neg_le_abs (perturbation winner)
        have hjbound := hperturb j
        have hibound := hperturb winner
        linarith
      have hterm : orderedReward scores forcing θ winner j ≤ switchingCap scores forcing θ winner := by
        have hh := Finset.le_sup' (fun k => if k = winner then 0 else orderedReward scores forcing θ winner k)
          (Finset.mem_univ j)
        simpa only [hj, ite_false, switchingCap, NegativeVoting.maxScore] using hh
      exact (sub_le_sub_right hforce _).trans ((le_max_left _ _).trans hterm)
  calc
    _ ≤ ∑ j, p j * switchingCap scores forcing θ winner :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hp.1 j))
    _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- The maximum is bounded by one copy of each off-diagonal transition from
the current winner; no diagonal term or alphabet-size multiplier is inserted. -/
theorem switchingCap_le_selected_sum (scores forcing : ι → ℝ) (θ : ℝ) (winner : ι) :
    switchingCap scores forcing θ winner ≤
      ∑ j ∈ Finset.univ.erase winner, orderedReward scores forcing θ winner j := by
  unfold switchingCap NegativeVoting.maxScore
  apply Finset.sup'_le Finset.univ_nonempty
  intro j hj
  by_cases h : j = winner
  · rw [ite_eq_left h]
    exact Finset.sum_nonneg (fun k _ => le_max_right _ _)
  · rw [ite_eq_right h]
    exact Finset.single_le_sum (s := Finset.univ.erase winner)
      (f := fun k => orderedReward scores forcing θ winner k)
      (fun k _ => le_max_right _ _) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)

omit [Nonempty ι] in
/-- Writing the selected row as ordered pairs counts every permitted pair
once. This exact identity precedes the geometric restriction to old cells. -/
theorem selected_sum_eq_ordered_sum (scores forcing : ι → ℝ) (θ : ℝ) (winner : ι) :
    (∑ j ∈ Finset.univ.erase winner, orderedReward scores forcing θ winner j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        if i = winner then orderedReward scores forcing θ i j else 0 := by
  symm
  rw [Finset.sum_eq_single winner]
  · simp
  · intro i hi hne
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_univ winner))

omit [Nonempty ι] in
/-- The total number of ordered off-diagonal transitions is m(m−1). -/
theorem ordered_pair_count :
    (∑ i : ι, (Finset.univ.erase i).card) = Fintype.card ι * (Fintype.card ι - 1) := by
  simp

end RewardReduction

section AffineRewardReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def affineWinner (rows : ι → E) (offsets : ι → ℝ) (x : E) : ι :=
  NegativeVoting.chosenWinner (fun i => affineScore rows offsets i x)

omit [DecidableEq ι] in
theorem affineWinner_mem_cell (rows : ι → E) (offsets : ι → ℝ) (x : E) :
    x ∈ affineCell rows offsets (affineWinner rows offsets x) := by
  intro j
  exact NegativeVoting.chosenWinner_max (fun i => affineScore rows offsets i x) j

/-- Pointwise reduction for the actual affine winner. Cell indicators are
measurable and preserve the ordered-pair indexing needed for normal fibres.
Ties cause no invalid lower estimate: replacing the chosen cell by all closed
winning cells only enlarges this upper bound. -/
theorem affine_switchingCap_le_ordered_cells (rows : ι → E) (offsets forcing : ι → ℝ)
    (θ : ℝ) (x : E) :
    switchingCap (fun i => affineScore rows offsets i x) forcing θ (affineWinner rows offsets x) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        if x ∈ affineCell rows offsets i then
          orderedReward (fun k => affineScore rows offsets k x) forcing θ i j else 0 := by
  classical
  apply (switchingCap_le_selected_sum _ forcing θ (affineWinner rows offsets x)).trans
  rw [selected_sum_eq_ordered_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : i = affineWinner rows offsets x
  · subst i
    simp only [ite_true, affineWinner_mem_cell, le_refl]
  · rw [ite_eq_right h]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl


omit [Nonempty ι] [Fintype ι] [DecidableEq ι] in
/-- Concrete bridge to the one-dimensional positive-part integral: the raw
ordered affine switching reward has precisely the checked fibre cost. -/
theorem orderedReward_along_pairNormal (rows : ι → E) (offsets forcing : ι → ℝ)
    (θ : ℝ) (i j : ι) (y : E) (z : ℝ)
    (hplane : affineScore rows offsets i y = affineScore rows offsets j y) :
    orderedReward (fun k => affineScore rows offsets k (y + z • pairNormal rows i j))
      forcing θ i j =
      fibreReward (θ * (forcing i + forcing j)) ‖rows i - rows j‖ z := by
  unfold orderedReward fibreReward
  rw [affine_gap_along_pairNormal rows offsets i j y z hplane]

end AffineRewardReduction


section PairMultiplicity
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Symmetric facet contributions have exactly two ordered orientations.
This identity prevents an alphabet-size factor from entering the main term. -/
theorem symmetric_ordered_sum_eq_twice_upper (R : ι → ι → ℝ)
    (hR : ∀ i j, R i j = R j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, R i j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), R i j := by
  have herase (i : ι) : Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) := by
    ext j
    simp
  have hsplit (i j : ι) : (if j ≠ i then R i j else 0) =
      (if i < j then R i j else 0) + (if j < i then R i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, (ne_of_lt hij).symm, not_lt_of_ge hij.le]
    · subst j
      simp
    · simp [hij, ne_of_lt hij, not_lt_of_ge hij.le]
  have hreverse : (∑ i, ∑ j, if j < i then R i j else 0) =
      ∑ i, ∑ j, if i < j then R i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hR j i]
  calc
    _ = ∑ i, ∑ j, if j ≠ i then R i j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [herase, Finset.sum_filter]
    _ = ∑ i, ∑ j, ((if i < j then R i j else 0) + (if j < i then R i j else 0)) := by
      simp_rw [hsplit]
    _ = (∑ i, ∑ j, if i < j then R i j else 0) +
        (∑ i, ∑ j, if j < i then R i j else 0) := by simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, if i < j then R i j else 0 := by rw [hreverse]; ring
    _ = _ := by simp_rw [Finset.sum_filter]

end PairMultiplicity
end NegativeVotingFan
