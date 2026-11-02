import GaussianFanMassJacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall

/-!
# Actual one-label margins of an affine Gaussian fan

The target-entry sublevel is exactly a raised-cell difference. The strict
source-exit sublevel is exactly a lowered-cell difference; the closed sublevel
has that identity almost everywhere, because the shifted comparison ties are
Gaussian null. Thus no ordered-pair union bound enters the probability bound.
The analytic endpoint uses the actual offset derivative and then discharges its
bound by the existing Gram/rare-cell degree theorem along the offset segment.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingFanMarginBounds
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFacetDegree
  NegativeVotingWeightedFacet NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Raise just label `i` by `t`; negative `t` lowers it. -/
def singleOffset (h : ι → ℝ) (i : ι) (t : ℝ) : ι → ℝ :=
  h + t • Pi.single i 1

@[simp] theorem singleOffset_self (h : ι → ℝ) (i : ι) (t : ℝ) :
    singleOffset h i t i = h i + t := by simp [singleOffset]

@[simp] theorem singleOffset_other (h : ι → ℝ) (i j : ι) (t : ℝ) (hji : j ≠ i) :
    singleOffset h i t j = h j := by simp [singleOffset, Pi.single_eq_of_ne hji]

@[simp] theorem singleOffset_zero (h : ι → ℝ) (i : ι) : singleOffset h i 0 = h := by
  simp [singleOffset]

@[simp] theorem score_singleOffset_self (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i : ι) (t : ℝ) (x : FSC.Coord d) :
    scores B (singleOffset h i t) x i = scores B h x i + t := by
  simp [scores]; ring

@[simp] theorem score_singleOffset_other (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i j : ι) (t : ℝ) (x : FSC.Coord d) (hji : j ≠ i) :
    scores B (singleOffset h i t) x j = scores B h x j := by simp [scores, hji]

def targetEntryMargin (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (x : FSC.Coord d) : ℝ :=
  NegativeVoting.maxScore (scores B h x) - scores B h x i

/-- An existential expression for the minimum gap to another label; unlike a
sum of pair events it records each point only once. -/
def sourceExitSublevel (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) (a : ℝ) :
    Set (FSC.Coord d) :=
  {x | x ∈ winningCell B h i ∧ ∃ j, j ≠ i ∧ scores B h x i - scores B h x j ≤ a}

def sourceExitMargin (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    [Nonempty {j : ι // j ≠ i}] (x : FSC.Coord d) : ℝ :=
  scores B h x i - NegativeVoting.maxScore (fun j : {j : ι // j ≠ i} => scores B h x j.1)

theorem sourceExitSublevel_eq_margin (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i : ι) [Nonempty {j : ι // j ≠ i}] (a : ℝ) :
    sourceExitSublevel B h i a = {x | x ∈ winningCell B h i ∧ sourceExitMargin B h i x ≤ a} := by
  ext x
  simp only [sourceExitSublevel, sourceExitMargin, mem_setOf_eq]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨j, hj, hgap⟩
    have hm := Finset.le_sup' (f := fun j : {j : ι // j ≠ i} => scores B h x j.1)
      (Finset.mem_univ (⟨j,hj⟩ : {j : ι // j ≠ i}))
    change scores B h x j ≤ NegativeVoting.maxScore _ at hm
    linarith
  · intro hgap
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j : {j : ι // j ≠ i} => scores B h x j.1)
    exact ⟨j.1, j.2, by simpa only [NegativeVoting.maxScore, hj] using hgap⟩

theorem targetEntryMargin_nonneg (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (x : FSC.Coord d) : 0 ≤ targetEntryMargin B h i x := by
  exact sub_nonneg.mpr (Finset.le_sup' (f := scores B h x) (Finset.mem_univ i))

theorem singleOffset_cell_mono (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    {s t : ℝ} (hst : s ≤ t) :
    winningCell B (singleOffset h i s) i ⊆ winningCell B (singleOffset h i t) i := by
  intro x hx j
  by_cases hji : j = i
  · subst j; exact le_rfl
  · have hh := hx j
    simp only [score_singleOffset_self, score_singleOffset_other B h i j _ _ hji] at hh ⊢
    linarith

/-- Exact closed target-entry sublevel identity, including its boundary. -/
theorem targetEntry_sublevel_eq (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (a : ℝ) (ha : 0 ≤ a) :
    {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} =
      winningCell B (singleOffset h i a) i \ winningCell B h i := by
  ext x
  constructor
  · rintro ⟨hout, hgap⟩
    refine ⟨?_, hout⟩
    intro j
    by_cases hji : j = i
    · subst j; exact le_rfl
    · rw [score_singleOffset_other B h i j a x hji, score_singleOffset_self]
      have hm := Finset.le_sup' (f := scores B h x) (Finset.mem_univ j)
      change scores B h x j ≤ NegativeVoting.maxScore (scores B h x) at hm
      unfold targetEntryMargin at hgap
      linarith
  · rintro ⟨hx, hout⟩
    refine ⟨hout, ?_⟩
    apply sub_le_iff_le_add.mpr
    apply Finset.sup'_le
    intro j _
    by_cases hji : j = i
    · subst j; linarith
    · have hh := hx j
      simpa only [score_singleOffset_other B h i j a x hji, score_singleOffset_self,
        add_comm a] using hh

/-- Exact strict source-exit identity. Closed cells at the new offset make
strictness necessary here; the closed event is handled almost everywhere below. -/
theorem sourceExit_strict_sublevel_eq (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    (a : ℝ) :
    {x | x ∈ winningCell B h i ∧ ∃ j, j ≠ i ∧ scores B h x i - scores B h x j < a} =
      winningCell B h i \ winningCell B (singleOffset h i (-a)) i := by
  ext x
  constructor
  · rintro ⟨hx, j, hji, hgap⟩
    refine ⟨hx, ?_⟩
    intro hnew
    have hh := hnew j
    simp only [score_singleOffset_self, score_singleOffset_other B h i j _ _ hji] at hh
    linarith
  · rintro ⟨hx, hnew⟩
    refine ⟨hx, ?_⟩
    change ¬ ∀ j, scores B (singleOffset h i (-a)) x j ≤
      scores B (singleOffset h i (-a)) x i at hnew
    push_neg at hnew
    obtain ⟨j, hj⟩ := hnew
    have hji : j ≠ i := by intro he; subst j; exact (lt_irrefl _ hj)
    refine ⟨j,hji,?_⟩
    simp only [score_singleOffset_self, score_singleOffset_other B h i j _ _ hji] at hj
    linarith

/-- Shifted score injectivity removes exactly the boundary omitted by the
strict identity. No measurable winner selector is used. -/
theorem sourceExit_sublevel_ae_eq (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) (a : ℝ) :
    sourceExitSublevel B h i a =ᵐ[stdGaussian (FSC.Coord d)]
      winningCell B h i \ winningCell B (singleOffset h i (-a)) i := by
  rw [← sourceExit_strict_sublevel_eq]
  filter_upwards [ae_scores_injective B hB (singleOffset h i (-a))] with x hx
  apply propext
  simp only [sourceExitSublevel, mem_setOf_eq]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨j,hji,hgap⟩
    refine ⟨j,hji,lt_of_le_of_ne hgap ?_⟩
    intro he
    apply hji
    apply hx
    simp only [score_singleOffset_other B h i j _ _ hji, score_singleOffset_self]
    linarith
  · rintro ⟨j,hji,hgap⟩
    exact ⟨j,hji,hgap.le⟩

theorem sourceExitSublevel_measurable (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i : ι) (a : ℝ) : MeasurableSet (sourceExitSublevel B h i a) := by
  have he : sourceExitSublevel B h i a = winningCell B h i ∩
      (⋃ j, ⋃ (_ : j ≠ i), {x | scores B h x i - scores B h x j ≤ a}) := by
    ext x; simp [sourceExitSublevel]
  rw [he]
  exact (winningCell_measurable B h i).inter (MeasurableSet.iUnion (fun j =>
    MeasurableSet.iUnion (fun _ =>
      measurableSet_le (by unfold scores; fun_prop) measurable_const)))

/-- The actual single-offset derivative is exactly the cap degree. -/
theorem massDerivative_single (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι) :
    massDerivative B h i (Pi.single i 1) = affineCapDegree B h i := by
  rw [massDerivative_apply B σ hσ hlower]
  unfold affineCapDegree
  simp_rw [cell_degree_summand_eq_intrinsic B h σ hσ hlower i]
  change (∑ j, facetWeight B h i j * ((Pi.single i (1 : ℝ) : ι → ℝ) i - (Pi.single i (1 : ℝ) : ι → ℝ) j)) =
    ∑ j : {j : ι // j ≠ i}, facetWeight B h i j.1
  rw [← Finset.sum_subtype (p := fun j : ι => j ≠ i) (Finset.univ.erase i)
    (fun j => by simp) (fun j => facetWeight B h i j)]
  calc
    _ = ∑ j, facetWeight B h i j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj]
    _ = _ := (Finset.sum_subset (Finset.erase_subset i Finset.univ)
      (fun j _ hj => by
        have he : j = i := by simpa using hj
        simp [he])).symm

theorem affineCapDegree_nonneg (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι) :
    0 ≤ affineCapDegree B h i := by
  rw [← massDerivative_single B σ hσ hlower, massDerivative_apply B σ hσ hlower]
  apply Finset.sum_nonneg
  intro j _
  by_cases hj : j = i
  · subst j; simp
  · simpa [Pi.single_eq_of_ne hj] using facetWeight_nonneg B h i j

theorem hasDerivAt_singleOffset_mass (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => mass B (singleOffset h i s) i)
      (affineCapDegree B (singleOffset h i t) i) t := by
  have hd : HasDerivAt (singleOffset h i) (Pi.single i 1) t := by
    convert ((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ) : ι → ℝ)).const_add h using 1
    · rfl
    · simp only [one_smul]
  convert (hasFDerivAt_mass B σ hσ hlower (singleOffset h i t) i).comp_hasDerivAt t hd using 1
  · rfl
  · exact (massDerivative_single B σ hσ hlower _ i).symm

/-- Mean-value control from the actual derivative on an arbitrary one-label
segment. The degree is geometrical, rather than a supplied mass derivative. -/
theorem singleOffset_mass_difference_le (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι)
    (s t K : ℝ) (hst : s ≤ t)
    (hdegree : ∀ u ∈ Icc s t, affineCapDegree B (singleOffset h i u) i ≤ K) :
    |mass B (singleOffset h i t) i - mass B (singleOffset h i s) i| ≤ K * (t-s) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u _ => (hasDerivAt_singleOffset_mass B σ hσ hlower h i u).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs, abs_of_nonneg (affineCapDegree_nonneg B σ hσ hlower _ i)]
      exact hdegree u ⟨hu.1,hu.2.le⟩) t (right_mem_Icc.mpr hst)
  simpa only [Real.norm_eq_abs] using hh

/-- The target event probability is the exact increase in the actual mass. -/
theorem targetEntry_sublevel_measure (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) (a : ℝ) (ha : 0 ≤ a) :
    (stdGaussian (FSC.Coord d)).real
      {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} =
      mass B (singleOffset h i a) i - mass B h i := by
  rw [targetEntry_sublevel_eq B h i a ha]
  have hs : winningCell B h i ⊆ winningCell B (singleOffset h i a) i := by
    simpa only [singleOffset_zero] using singleOffset_cell_mono B h i ha
  rw [measureReal_sdiff hs (winningCell_measurable B h i),
    ← mass_eq_winningCell B hB, ← mass_eq_winningCell B hB]

/-- The closed source event probability is the exact mass decrease, with its
shifted boundary removed only by a proved almost-everywhere equality. -/
theorem sourceExit_sublevel_measure (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) (a : ℝ) (ha : 0 ≤ a) :
    (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) =
      mass B h i - mass B (singleOffset h i (-a)) i := by
  rw [measureReal_congr (sourceExit_sublevel_ae_eq B hB h i a)]
  have hs : winningCell B (singleOffset h i (-a)) i ⊆ winningCell B h i := by
    simpa only [singleOffset_zero] using singleOffset_cell_mono B h i (neg_nonpos.mpr ha)
  rw [measureReal_sdiff hs (winningCell_measurable B _ i),
    ← mass_eq_winningCell B hB, ← mass_eq_winningCell B hB]

/-- Both true maximum-margin probabilities have one-label linear bounds.
The only analytic premise here is a bound on the actual cap degree along the
single-offset interval. This is discharged geometrically below. -/
theorem one_label_margin_measures_le (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : ι → ℝ) (i : ι)
    (a aStar K : ℝ) (ha : 0 ≤ a) (haStar : a ≤ aStar)
    (hdegree : ∀ t ∈ Icc (-aStar) aStar, affineCapDegree B (singleOffset h i t) i ≤ K) :
    (stdGaussian (FSC.Coord d)).real
      {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} ≤ K*a ∧
    (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) ≤ K*a := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  rw [targetEntry_sublevel_measure B hB h i a ha, sourceExit_sublevel_measure B hB h i a ha]
  constructor
  · have hh := singleOffset_mass_difference_le B σ hσ hlower h i 0 a K ha
      (fun t ht => hdegree t ⟨by linarith [ht.1],ht.2.trans haStar⟩)
    simp only [singleOffset_zero, sub_zero] at hh
    exact (le_abs_self _).trans hh
  · have hh := singleOffset_mass_difference_le B σ hσ hlower h i (-a) 0 K
      (neg_nonpos.mpr ha) (fun t ht => hdegree t ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    simp only [singleOffset_zero, zero_sub, neg_neg] at hh
    exact (le_abs_self _).trans hh

/-- Uniform, dimension-free margin constants from actual Gram geometry and
rare-cell bounds throughout the one-offset segment. No derivative/degree bound
is assumed by this endpoint. -/
theorem one_label_margin_measures_le_of_gram
    (B : ι → FSC.Coord d) (h : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B σ) (i : ι) (e m L C : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC : 0 ≤ C)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ j, inner ℝ (B j) (B j) ≤ 2*α^2)
    (hCross : ∀ j, j ≠ i → inner ℝ (B j) (B i) ≤ α^2/4)
    (a aStar : ℝ) (ha : 0 ≤ a) (haStar : a ≤ aStar)
    (hmass : ∀ t ∈ Icc (-aStar) aStar, mass B (singleOffset h i t) i ≤ C/m) :
    let K := 32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
    (stdGaussian (FSC.Coord d)).real
      {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} ≤ K*a ∧
    (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) ≤ K*a := by
  apply one_label_margin_measures_le B σ hσ hlower h i a aStar _ ha haStar
  intro t ht
  apply affineCapDegree_uniform_of_gram B (singleOffset h i t) σ α hσ hα hlower i
    e m L C he hm hL hlog hC hScale hDiagLower hDiagUpper hCross
  have hB : Function.Injective B := fun j k hh => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk hh
  have hh := hmass t ht
  rw [mass_eq_winningCell B hB] at hh
  exact hh

/-- Coefficients of the differential inequality for the true cell mass. -/
def degreeLinearCoefficient (e : ℝ) : ℝ := 32*Real.sqrt 2/e
def degreeConstantCoefficient (e : ℝ) : ℝ := 32*(Real.sqrt (2*Real.pi))⁻¹/e

def shiftedMassConstant (e C₀ : ℝ) : ℝ :=
  (C₀ + degreeConstantCoefficient e / degreeLinearCoefficient e) *
    Real.exp (degreeLinearCoefficient e)

theorem mass_nonneg_of_injective (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) (i : ι) : 0 ≤ mass B h i := by
  rw [mass_eq_winningCell B hB]
  exact ENNReal.toReal_nonneg

/-- The geometry gives a differential inequality at every offset, not merely
inside a region with a presumed mass bound. -/
theorem affineCapDegree_le_linear_mass_of_gram
    (B : ι → FSC.Coord d) (h : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B σ) (i : ι) (e m L : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ j, inner ℝ (B j) (B j) ≤ 2*α^2)
    (hCross : ∀ j, j ≠ i → inner ℝ (B j) (B i) ≤ α^2/4) :
    affineCapDegree B h i ≤
      (degreeLinearCoefficient e*m)*mass B h i + degreeConstantCoefficient e := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hB : Function.Injective B := fun j k hh => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk hh
  have hp := mass_nonneg_of_injective B hB h i
  have hmass : (stdGaussian (FSC.Coord d) (affineCell B h i)).toReal ≤
      (m*mass B h i)/m := by
    rw [mul_div_cancel_left₀ _ hm0.ne']
    exact (mass_eq_winningCell B hB h i).ge
  have hh := affineCapDegree_uniform_of_gram B h σ α hσ hα hlower i e m L
    (m*mass B h i) he hm hL hlog (mul_nonneg hm0.le hp) hScale
    hDiagLower hDiagUpper hCross hmass
  convert hh using 1 <;> unfold degreeLinearCoefficient degreeConstantCoefficient <;> ring

/-- Elementary majorant for a nonnegative Grönwall solution when its time is
at most `1/m`. This retains the rare-cell `1/m` factor. -/
theorem gronwall_rare_scale (A B C₀ m t : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hC : 0 ≤ C₀) (hm : 0 < m) (ht : t ≤ 1/m) :
    gronwallBound (C₀/m) (A*m) B t ≤ (C₀+B/A)*Real.exp A/m := by
  have hAm : 0 < A*m := mul_pos hA hm
  rw [gronwallBound_of_K_ne_0 hAm.ne']
  have hmt : m*t ≤ 1 := by nlinarith [(le_div_iff₀ hm).mp ht]
  have hex : Real.exp ((A*m)*t) ≤ Real.exp A := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (C₀/m+B/(A*m))*Real.exp ((A*m)*t) := by
      have hb : 0 ≤ B/(A*m) := div_nonneg hB hAm.le
      nlinarith
    _ ≤ (C₀/m+B/(A*m))*Real.exp A :=
      mul_le_mul_of_nonneg_left hex (add_nonneg (div_nonneg hC hm.le) (div_nonneg hB hAm.le))
    _ = _ := by field_simp

/-- Rare-cell mass is preserved under a one-label shift of size at most `1/m`.
The positive side follows from the actual mass ODE; negative shifts only shrink
the cell. No Cameron--Martin or path-mass assumption is supplied. -/
theorem singleOffset_mass_le_of_initial_gram
    (B : ι → FSC.Coord d) (h : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B σ) (i : ι) (e m L C₀ : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC : 0 ≤ C₀)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ j, inner ℝ (B j) (B j) ≤ 2*α^2)
    (hCross : ∀ j, j ≠ i → inner ℝ (B j) (B i) ≤ α^2/4)
    (hmass : mass B h i ≤ C₀/m) (t : ℝ) (ht : t ≤ 1/m) :
    mass B (singleOffset h i t) i ≤ shiftedMassConstant e C₀/m := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hA : 0 < degreeLinearCoefficient e := by unfold degreeLinearCoefficient; positivity
  have hD : 0 ≤ degreeConstantCoefficient e := by unfold degreeConstantCoefficient; positivity
  have hB : Function.Injective B := fun j k hh => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk hh
  have hp (u : ℝ) := mass_nonneg_of_injective B hB (singleOffset h i u) i
  have hlarge : C₀ ≤ shiftedMassConstant e C₀ := by
    have hsum : C₀ ≤ C₀+degreeConstantCoefficient e/degreeLinearCoefficient e :=
      le_add_of_nonneg_right (div_nonneg hD hA.le)
    have he1 : 1 ≤ Real.exp (degreeLinearCoefficient e) := Real.one_le_exp hA.le
    exact hsum.trans (le_mul_of_one_le_right (hC.trans hsum) he1)
  by_cases ht0 : 0 ≤ t
  · have hdiff (u : ℝ) := hasDerivAt_singleOffset_mass B σ hσ hlower h i u
    have hG := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun u => mass B (singleOffset h i u) i)
      (f' := fun u => affineCapDegree B (singleOffset h i u) i)
      (δ := C₀/m) (K := degreeLinearCoefficient e*m) (ε := degreeConstantCoefficient e)
      (a := 0) (b := t)
      (fun u _ => (hdiff u).continuousAt.continuousWithinAt)
      (fun u _ => (hdiff u).hasDerivWithinAt)
      (by rw [Real.norm_eq_abs,abs_of_nonneg (hp 0),singleOffset_zero]; exact hmass)
      (fun u _ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (affineCapDegree_nonneg B σ hσ hlower _ i),
          Real.norm_eq_abs,abs_of_nonneg (hp u)]
        exact affineCapDegree_le_linear_mass_of_gram B _ σ α hσ hα hlower i e m L
          he hm hL hlog hScale hDiagLower hDiagUpper hCross)
      t (right_mem_Icc.mpr ht0)
    rw [Real.norm_eq_abs,abs_of_nonneg (hp t),sub_zero] at hG
    exact hG.trans (gronwall_rare_scale _ _ _ m t hA hD hC hm0 ht)
  · have htm : t ≤ 0 := le_of_not_ge ht0
    have hsub : winningCell B (singleOffset h i t) i ⊆ winningCell B h i := by
      simpa only [singleOffset_zero] using singleOffset_cell_mono B h i htm
    rw [mass_eq_winningCell B hB]
    have hm0bound : (stdGaussian (FSC.Coord d)).real (winningCell B h i) ≤ C₀/m := by
      simpa only [← mass_eq_winningCell B hB] using hmass
    exact (measureReal_mono hsub).trans (hm0bound.trans
      (div_le_div_of_nonneg_right hlarge hm0.le))

/-- Full one-label margin endpoint from the initial rare-cell mass and explicit
fan geometry. The interval mass control and actual derivative estimate are
proved internally. The constant depends only on `e` and `C₀`, not on the number
of labels, ambient dimension, or offsets. -/
theorem one_label_margin_measures_le_of_initial_gram
    (B : ι → FSC.Coord d) (h : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound B σ) (i : ι) (e m L C₀ : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC : 0 ≤ C₀)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α^2/2 ≤ inner ℝ (B i) (B i))
    (hDiagUpper : ∀ j, inner ℝ (B j) (B j) ≤ 2*α^2)
    (hCross : ∀ j, j ≠ i → inner ℝ (B j) (B i) ≤ α^2/4)
    (hmass : mass B h i ≤ C₀/m) (a : ℝ) (ha : 0 ≤ a) (haStar : a ≤ 1/m) :
    let K := 32*(shiftedMassConstant e C₀*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
    (stdGaussian (FSC.Coord d)).real
      {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} ≤ K*a ∧
    (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) ≤ K*a := by
  have hC' : 0 ≤ shiftedMassConstant e C₀ := by
    have hA : 0 < degreeLinearCoefficient e := by unfold degreeLinearCoefficient; positivity
    have hD : 0 ≤ degreeConstantCoefficient e := by unfold degreeConstantCoefficient; positivity
    exact mul_nonneg (add_nonneg hC (div_nonneg hD hA.le)) (Real.exp_pos _).le
  exact one_label_margin_measures_le_of_gram B h σ α hσ hα hlower i e m L
    (shiftedMassConstant e C₀) he hm hL hlog hC' hScale hDiagLower hDiagUpper hCross
    a (1/m) ha haStar (fun t ht => singleOffset_mass_le_of_initial_gram B h σ α hσ hα
      hlower i e m L C₀ he hm hL hlog hC hScale hDiagLower hDiagUpper hCross hmass t ht.2)

/-- Measurability of the actual maximum margin. -/
theorem targetEntryMargin_measurable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) :
    Measurable (targetEntryMargin B h i) := by
  apply Measurable.sub
  · convert (Finset.measurable_sup' (f := fun j x => scores B h x j)
        Finset.univ_nonempty (fun j _ => by unfold scores; fun_prop)) using 1
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty (fun j x => scores B h x j) x).symm
  · unfold scores; fun_prop

theorem sourceExitMargin_measurable (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    [Nonempty {j : ι // j ≠ i}] : Measurable (sourceExitMargin B h i) := by
  apply Measurable.sub
  · unfold scores; fun_prop
  · convert (Finset.measurable_sup' (f := fun (j : {j : ι // j ≠ i}) x => scores B h x j.1)
        Finset.univ_nonempty (fun j _ => by unfold scores; fun_prop)) using 1
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty (fun (j : {j : ι // j ≠ i}) x => scores B h x j.1) x).symm

theorem sourceExitMargin_nonneg_on_cell (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    [Nonempty {j : ι // j ≠ i}] (x : FSC.Coord d) (hx : x ∈ winningCell B h i) :
    0 ≤ sourceExitMargin B h i x := by
  apply sub_nonneg.mpr
  exact Finset.sup'_le _ _ (fun j _ => hx j.1)

/-- Direct interface for a restricted-measure cost estimate. Clipping the
source margin away from its cell preserves the actual cost everywhere on the
cell, and avoids imposing global nonnegativity on a signed score gap. -/
theorem clipped_source_sublevel_restrict (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι)
    [Nonempty {j : ι // j ≠ i}] (a : ℝ) (ha : 0 ≤ a) :
    ((stdGaussian (FSC.Coord d)).restrict (winningCell B h i)).real
      {x | max (sourceExitMargin B h i x) 0 ≤ a} =
    (stdGaussian (FSC.Coord d)).real (sourceExitSublevel B h i a) := by
  unfold Measure.real
  rw [Measure.restrict_apply' (winningCell_measurable B h i)]
  congr 2
  rw [sourceExitSublevel_eq_margin]
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, max_le_iff, and_iff_left ha]
  exact and_comm

theorem target_sublevel_restrict (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) (a : ℝ) :
    ((stdGaussian (FSC.Coord d)).restrict (winningCell B h i)ᶜ).real
      {x | targetEntryMargin B h i x ≤ a} =
    (stdGaussian (FSC.Coord d)).real
      {x | x ∉ winningCell B h i ∧ targetEntryMargin B h i x ≤ a} := by
  unfold Measure.real
  rw [Measure.restrict_apply' (winningCell_measurable B h i).compl]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq]
  exact and_comm

end NegativeVotingFanMarginBounds
