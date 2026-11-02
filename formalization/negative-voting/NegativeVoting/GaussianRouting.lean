import Mathlib
import NegativeVoting.Routing

/-!
# Gaussian score ties and finite-product routing rigidity

These lemmas prove actual Gaussian null-set facts. The finite-product
hyperplane argument conditions on one coordinate with a nonzero coefficient;
its fiber is a singleton under a nondegenerate one-dimensional Gaussian.
No multivariate Gaussian transformation theorem or hypothesis of already
tie-free scores is substituted for that argument.
-/

namespace NegativeVoting

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Every singleton has zero mass under a Gaussian with nonzero variance. -/
theorem gaussian_singleton_null (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) (value : ℝ) :
    gaussianReal mean variance {value} = 0 := by
  exact (gaussianReal_absolutelyContinuous mean hvariance) (measure_singleton value)

/-- Nondegenerate scalar Gaussian measures are atomless. -/
theorem gaussian_noAtoms (mean : ℝ) {variance : ℝ≥0}
    (hvariance : variance ≠ 0) : NullSingletonClass (gaussianReal mean variance) :=
  ⟨gaussian_singleton_null mean hvariance⟩

/-- A proper affine linear equation has zero product-measure mass whenever
one participating coordinate is atomless. The other coordinates need only
have sigma-finite measures. -/
theorem product_linear_hyperplane_null {n : ℕ}
    (μ : Fin (n + 1) → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (a : Fin (n + 1) → ℝ) (c : ℝ) (i : Fin (n + 1))
    [NullSingletonClass (μ i)] (ha : a i ≠ 0) :
    Measure.pi μ {x | ∑ j, a j * x j = c} = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let s : Set (ℝ × (Fin n → ℝ)) :=
    {z | a i * z.1 + ∑ j, a (i.succAbove j) * z.2 j = c}
  have hs : MeasurableSet s := by
    have hm : Measurable (fun z : ℝ × (Fin n → ℝ) =>
        a i * z.1 + ∑ j, a (i.succAbove j) * z.2 j) :=
      (measurable_fst.const_mul _).add
        (Finset.measurable_sum _ (fun j _ =>
          ((measurable_pi_apply j).comp measurable_snd).const_mul _))
    exact hm (measurableSet_singleton c)
  have hfiber (y : Fin n → ℝ) :
      μ i ((fun x : ℝ => (x, y)) ⁻¹' s) = 0 := by
    have hset : ((fun x : ℝ => (x, y)) ⁻¹' s) =
        {(c - ∑ j, a (i.succAbove j) * y j) / a i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff, s]
      rw [eq_div_iff ha]
      constructor <;> intro hx <;> nlinarith
    rw [hset]
    exact measure_singleton _
  have hnull : ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) s = 0 := by
    rw [Measure.prod_apply_symm hs]
    simp_rw [hfiber]
    simp
  have he := measurePreserving_piFinSuccAbove μ i
  have hpre : e ⁻¹' s = {x | ∑ j, a j * x j = c} := by
    ext x
    change (a i * x i + ∑ j, a (i.succAbove j) * x (i.succAbove j) = c) ↔
      (∑ j, a j * x j = c)
    rw [Fin.sum_univ_succAbove (fun j => a j * x j) i]
  rw [← hpre, he.measure_preimage hs.nullMeasurableSet]
  exact hnull

/-- Every proper affine hyperplane is null for a finite product of
nondegenerate scalar Gaussians. Distinct linear scores therefore have
zero tie probability; no independence hypothesis is left to the caller
because the measure itself is the product measure. -/
theorem gaussian_product_linear_hyperplane_null {n : ℕ}
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (ha : ∃ i, a i ≠ 0 ∧ variances i ≠ 0) :
    Measure.pi (fun i => gaussianReal (means i) (variances i))
      {x | ∑ j, a j * x j = c} = 0 := by
  obtain ⟨i, hai, hvi⟩ := ha
  letI : NullSingletonClass (gaussianReal (means i) (variances i)) := gaussian_noAtoms (means i) hvi
  exact product_linear_hyperplane_null
    (fun j => gaussianReal (means j) (variances j)) a c i hai

/-- The finite linear score of a row vector. -/
def linearScore {n : ℕ} (row x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, row j * x j

/-- Distinct coefficient rows tie with probability zero under any product
Gaussian whose coordinate variances are all nonzero. -/
theorem gaussian_product_score_tie_null {n : ℕ}
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (a b : Fin (n + 1) → ℝ) (hab : a ≠ b) :
    Measure.pi (fun i => gaussianReal (means i) (variances i))
      {x | linearScore a x = linearScore b x} = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i :=
    not_forall.mp (fun h => hab (funext h))
  have hnull := gaussian_product_linear_hyperplane_null means variances
    (fun j => a j - b j) 0 ⟨i, sub_ne_zero.mpr hi, hvariance i⟩
  simpa only [linearScore, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using hnull

/-- In particular, distinct finite-dimensional Gaussian linear scores have
zero tie probability for the standard independent Gaussian measure. -/
theorem standard_gaussian_score_tie_null {n : ℕ}
    (a b : Fin (n + 1) → ℝ) (hab : a ≠ b) :
    Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
      {x | linearScore a x = linearScore b x} = 0 := by
  exact gaussian_product_score_tie_null (fun _ => 0) (fun _ => 1)
    (fun _ => one_ne_zero) a b hab

/-- A finite family of distinct coefficient rows produces pairwise distinct
scores almost everywhere for a nondegenerate product Gaussian. This derives
the no-tie property from the actual measure, rather than assuming it. -/
theorem ae_gaussian_scores_injective {n : ℕ} {ι : Type*} [Fintype ι]
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (rows : ι → Fin (n + 1) → ℝ) (hrows : Function.Injective rows) :
    ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      Function.Injective (fun i => linearScore (rows i) x) := by
  classical
  have hpairs : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i j, i ≠ j → linearScore (rows i) x ≠ linearScore (rows j) x := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · have hneq : rows i ≠ rows j := fun h => hij (hrows h)
      have hnull := gaussian_product_score_tie_null means variances hvariance
        (rows i) (rows j) hneq
      have hne : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
          linearScore (rows i) x ≠ linearScore (rows j) x := by
        apply ae_iff.mpr
        simpa only [not_not] using hnull
      exact hne.mono (fun _ hx _ => hx)
  filter_upwards [hpairs] with x hx
  intro i j hscore
  by_contra hij
  exact hx i j hij hscore

/-- A nonempty finite family of distinct Gaussian linear scores has a unique
winning label almost everywhere. No measurable winner is postulated here. -/
theorem ae_gaussian_unique_max {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (rows : ι → Fin (n + 1) → ℝ) (hrows : Function.Injective rows) :
    ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∃ t, ∀ i, i ≠ t → linearScore (rows i) x < linearScore (rows t) x := by
  classical
  filter_upwards [ae_gaussian_scores_injective means variances hvariance rows hrows]
    with x hx
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun i => linearScore (rows i) x) Finset.univ_nonempty
  refine ⟨t, fun i hi => ?_⟩
  exact lt_of_le_of_ne (ht i (Finset.mem_univ i)) (fun h => hi (hx h))

/-- Gaussian routing rigidity for actual linear scores. Almost-everywhere
uniqueness is derived from distinct coefficient rows and nondegenerate
Gaussian coordinates; only being a maximizer is assumed of `winner`. -/
theorem ae_gaussian_routing_rigidity {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (means : Fin (n + 1) → ℝ) (variances : Fin (n + 1) → ℝ≥0)
    (hvariance : ∀ j, variances j ≠ 0)
    (rows : ι → Fin (n + 1) → ℝ) (hrows : Function.Injective rows)
    (p : (Fin (n + 1) → ℝ) → ι → ℝ) (winner : (Fin (n + 1) → ℝ) → ι)
    (hp : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      SimplexWeights (p x))
    (hmax : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i, linearScore (rows i) x ≤ linearScore (rows (winner x)) x)
    (hintegrable : Integrable
      (fun x => routingLoss (p x) (fun i => linearScore (rows i) x) (winner x))
      (Measure.pi (fun j => gaussianReal (means j) (variances j))))
    (hzero : ∫ x, routingLoss (p x) (fun i => linearScore (rows i) x) (winner x)
      ∂Measure.pi (fun j => gaussianReal (means j) (variances j)) = 0) :
    ∀ᵐ x ∂Measure.pi (fun j => gaussianReal (means j) (variances j)),
      ∀ i, p x i = if i = winner x then 1 else 0 := by
  apply ae_pure_of_zero_integrated_routing_loss _ p
    (fun x i => linearScore (rows i) x) winner hp ?_ hintegrable hzero
  filter_upwards [ae_gaussian_scores_injective means variances hvariance rows hrows, hmax]
    with x hinj hmx
  intro i hi
  exact lt_of_le_of_ne (hmx i) (fun h => hi (hinj h))

end NegativeVoting
